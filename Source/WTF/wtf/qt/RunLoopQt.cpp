/*
 * Copyright (C) 2010 Apple Inc. All rights reserved.
 * Copyright (C) 2010 Nokia Corporation and/or its subsidiary(-ies)
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY APPLE INC. AND ITS CONTRIBUTORS ``AS IS''
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO,
 * THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
 * PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL APPLE INC. OR ITS CONTRIBUTORS
 * BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
 * CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 * SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
 * CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF
 * THE POSSIBILITY OF SUCH DAMAGE.
 */

#include "config.h"
#include "RunLoop.h"

#include <QCoreApplication>
#include <QEventLoop>
#include <QMetaObject>
#include <QObject>
#include <QThread>
#include <QTimerEvent>
#include <algorithm>
#include <cmath>
#include <cstdint>
#include <limits>
#include <unordered_map>
#include <utility>
#include <wtf/MonotonicTime.h>
#include <wtf/Ref.h>

namespace WTF {

// Protected by the owning RunLoop's m_loopLock. A queued operation retains
// only this cancellation state, not a raw pointer to a live TimerBase.
struct RunLoop::QtTimerState {
    TimerBase* owner { nullptr };
    uint64_t generation { 0 };
    bool active { false };
    bool repeating { false };
    Seconds interval { 0_s };
    MonotonicTime deadline;
};

class RunLoop::QtRunLoopObject final : public QObject {
    Q_OBJECT
public:
    explicit QtRunLoopObject(RunLoop& runLoop)
        : m_runLoop(runLoop)
    {
    }

    // Called with m_loopLock held, so shutdown cannot delete the QObject
    // between selecting it and posting a context-bound invocation.
    void requestTimerUpdate(const std::shared_ptr<QtTimerState>& state)
    {
        const auto generation = state->generation;
        QMetaObject::invokeMethod(this, [this, state, generation] {
            LockHolder locker(m_runLoop.m_loopLock);
            if (m_runLoop.m_qtShuttingDown || state->generation != generation)
                return;
            removeTimer(state.get());
            if (state->active && state->owner)
                installTimer(state, generation);
        }, Qt::QueuedConnection);
    }

    void requestWork()
    {
        QMetaObject::invokeMethod(this, [this] {
            {
                LockHolder locker(m_runLoop.m_loopLock);
                if (m_runLoop.m_qtShuttingDown)
                    return;
            }
            Ref<RunLoop> protectedRunLoop { m_runLoop };
            m_runLoop.performWork();
        }, Qt::QueuedConnection);
    }

    // Owning thread only, with m_loopLock held. Do not invoke user code here.
    void stopAllTimers()
    {
        for (auto& entry : m_timers) {
            killTimer(entry.first);
            entry.second.state->active = false;
            ++entry.second.state->generation;
        }
        m_timerIDs.clear();
        m_timers.clear();
    }

protected:
    void timerEvent(QTimerEvent* event) override
    {
        TimerBase* timer = nullptr;
        std::shared_ptr<QtTimerState> state;
        uint64_t generation = 0;
        bool repeating = false;
        Ref<RunLoop> protectedRunLoop { m_runLoop };
        {
            LockHolder locker(m_runLoop.m_loopLock);
            auto it = m_timers.find(event->timerId());
            if (it == m_timers.end())
                return;

            state = it->second.state;
            generation = it->second.generation;
            if (m_runLoop.m_qtShuttingDown || !state->owner || !state->active
                || generation != state->generation) {
                removeTimer(state.get());
                return;
            }

            const auto now = MonotonicTime::now();
            removeTimer(state.get());
            // Intervals larger than Qt's int-millisecond limit are armed in
            // chunks. Also do not fire early if a platform timer wakes early.
            if (state->deadline > now) {
                installTimer(state, generation);
                return;
            }

            timer = state->owner;
            repeating = state->repeating;
            if (repeating)
                state->deadline = now + state->interval;
            else
                state->active = false;
        }

        // Never hold m_loopLock while calling JSC: its timer manager has its
        // own lock and can start/stop other timers. A callback may delete its
        // own timer, so do not access timer after this call.
        // As in JSC PerVMData, destruction concurrent with firing must be
        // dispatched to this owning RunLoop; TimerBase is not ref-counted.
        timer->fired();

        // Do not rearm a repeating timer until its callback returns: a
        // nested Qt event loop must not recursively fire the same timer.
        // The callback may delete the TimerBase or initiate shutdown. Use
        // only retained state/the protected RunLoop, not timer or this.
        if (repeating) {
            auto& runLoop = protectedRunLoop.get();
            LockHolder locker(runLoop.m_loopLock);
            if (!runLoop.m_qtShuttingDown && state->owner && state->active
                && generation == state->generation)
                runLoop.m_qtRunLoopObject->installTimer(state, generation);
        }
    }

private:
    struct InstalledTimer {
        std::shared_ptr<QtTimerState> state;
        uint64_t generation;
    };

    void removeTimer(QtTimerState* state)
    {
        auto it = m_timerIDs.find(state);
        if (it == m_timerIDs.end())
            return;
        const int id = it->second;
        killTimer(id);
        m_timerIDs.erase(it);
        m_timers.erase(id);
    }

    void installTimer(const std::shared_ptr<QtTimerState>& state, uint64_t generation)
    {
        // ceil prevents positive sub-millisecond delays becoming zero timers.
        // Check before the cast: JSC legitimately schedules decade-long delays.
        const double remaining = (state->deadline - MonotonicTime::now()).milliseconds();
        const double maximum = std::numeric_limits<int>::max();
        const int milliseconds = !(remaining > 0) ? 0
            : remaining >= maximum ? std::numeric_limits<int>::max()
            : static_cast<int>(std::ceil(remaining));
        const int id = startTimer(milliseconds, Qt::PreciseTimer);
        if (!id) {
            state->active = false;
            return;
        }
        m_timers.emplace(id, InstalledTimer { state, generation });
        m_timerIDs.emplace(state.get(), id);
    }

    RunLoop& m_runLoop;
    std::unordered_map<int, InstalledTimer> m_timers;
    std::unordered_map<QtTimerState*, int> m_timerIDs;
};

void RunLoop::run()
{
    Ref<RunLoop> protectedRunLoop { RunLoop::current() };
    auto& runLoop = protectedRunLoop.get();
    bool useApplicationLoop;
    {
        LockHolder locker(runLoop.m_loopLock);
        if (runLoop.m_qtShuttingDown)
            return;
        if (runLoop.m_stopRequested) {
            runLoop.m_stopRequested = false;
            return;
        }
        // A host application can already be inside QApplication::exec().
        // In that case use a local, nestable loop instead of exec() again.
        useApplicationLoop = WTF::isMainThread()
            && !QThread::currentThread()->loopLevel()
            && !runLoop.m_runningApplicationEventLoop;
        if (useApplicationLoop)
            runLoop.m_runningApplicationEventLoop = true;
    }

    if (useApplicationLoop) {
        QCoreApplication::exec();
        LockHolder locker(runLoop.m_loopLock);
        runLoop.m_runningApplicationEventLoop = false;
        return;
    }

    QEventLoop eventLoop;
    QEventLoop* previousEventLoop;
    {
        LockHolder locker(runLoop.m_loopLock);
        // A stop can arrive while the local QEventLoop is being constructed.
        if (runLoop.m_qtShuttingDown)
            return;
        if (runLoop.m_stopRequested) {
            runLoop.m_stopRequested = false;
            return;
        }
        previousEventLoop = runLoop.m_activeQtEventLoop;
        runLoop.m_activeQtEventLoop = &eventLoop;
    }
    eventLoop.exec();
    {
        LockHolder locker(runLoop.m_loopLock);
        runLoop.m_activeQtEventLoop = previousEventLoop;
    }
}

void RunLoop::stop()
{
    LockHolder locker(m_loopLock);
    if (m_qtShuttingDown)
        return;
    if (m_activeQtEventLoop) {
        QMetaObject::invokeMethod(m_activeQtEventLoop, "quit", Qt::QueuedConnection);
        return;
    }
    if (m_runningApplicationEventLoop) {
        if (auto* app = QCoreApplication::instance())
            QMetaObject::invokeMethod(app, "quit", Qt::QueuedConnection);
        return;
    }
    // RunLoop::create() publishes the loop before entering run().
    m_stopRequested = true;
}

RunLoop::RunLoop()
{
    QEventLoop ensureDispatcher; // Qt must also adopt native WTF threads.
    m_qtRunLoopObject = new QtRunLoopObject(*this);

    // Do the complete WTF shutdown, not just delete its QObject helpers.
    // If WTF TLS is destroyed first it disconnects this receiver. If Qt
    // finishes first, the later WTF TLS callback is an idempotent no-op.
    QObject::connect(QThread::currentThread(), &QThread::finished,
        m_qtRunLoopObject, [this] { threadWillExit(); }, Qt::DirectConnection);
}

RunLoop::~RunLoop()
{
    // Holder::threadWillExit (or Qt's earlier finished signal) must detach all
    // QObjects on the owner thread. Last Ref<RunLoop> may die on ANY thread.
    RELEASE_ASSERT(!m_qtRunLoopObject);
}

void RunLoop::prepareForQtThreadExit()
{
    LockHolder locker(m_loopLock);
    m_qtShuttingDown = true;
    if (m_qtRunLoopObject) {
        RELEASE_ASSERT(m_qtRunLoopObject->thread() == QThread::currentThread());
        m_qtRunLoopObject->stopAllTimers();
    }
}

void RunLoop::completeQtThreadExit()
{
    QtRunLoopObject* object;
    {
        LockHolder locker(m_loopLock);
        object = std::exchange(m_qtRunLoopObject, nullptr);
    }
    // No other thread can post through this pointer now. QObject destruction
    // removes its pending timer-update/work messages and the finished hook.
    delete object;
}

void RunLoop::wakeUp()
{
    LockHolder locker(m_loopLock);
    if (!m_qtShuttingDown && m_qtRunLoopObject)
        m_qtRunLoopObject->requestWork();
}

RunLoop::CycleResult RunLoop::cycle(RunLoopMode)
{
    QCoreApplication::processEvents(QEventLoop::WaitForMoreEvents);
    return CycleResult::Continue;
}

RunLoop::TimerBase::TimerBase(RunLoop& runLoop)
    : m_runLoop(runLoop)
    , m_qtTimerState(std::make_shared<QtTimerState>())
{
    m_qtTimerState->owner = this;
}

RunLoop::TimerBase::~TimerBase()
{
    LockHolder locker(m_runLoop->m_loopLock);
    m_qtTimerState->owner = nullptr;
    m_qtTimerState->active = false;
    ++m_qtTimerState->generation;
    if (!m_runLoop->m_qtShuttingDown && m_runLoop->m_qtRunLoopObject)
        m_runLoop->m_qtRunLoopObject->requestTimerUpdate(m_qtTimerState);
}

void RunLoop::TimerBase::start(Seconds interval, bool repeat)
{
    LockHolder locker(m_runLoop->m_loopLock);
    ++m_qtTimerState->generation;
    if (m_runLoop->m_qtShuttingDown) {
        m_qtTimerState->active = false;
        return;
    }
    interval = std::max(0_s, interval);
    m_qtTimerState->active = true;
    m_qtTimerState->repeating = repeat;
    m_qtTimerState->interval = interval;
    m_qtTimerState->deadline = MonotonicTime::now() + interval;
    m_runLoop->m_qtRunLoopObject->requestTimerUpdate(m_qtTimerState);
}

void RunLoop::TimerBase::stop()
{
    LockHolder locker(m_runLoop->m_loopLock);
    m_qtTimerState->active = false;
    ++m_qtTimerState->generation;
    if (!m_runLoop->m_qtShuttingDown && m_runLoop->m_qtRunLoopObject)
        m_runLoop->m_qtRunLoopObject->requestTimerUpdate(m_qtTimerState);
}

bool RunLoop::TimerBase::isActive() const
{
    LockHolder locker(m_runLoop->m_loopLock);
    return !m_runLoop->m_qtShuttingDown && m_qtTimerState->active;
}

Seconds RunLoop::TimerBase::secondsUntilFire() const
{
    LockHolder locker(m_runLoop->m_loopLock);
    if (m_runLoop->m_qtShuttingDown || !m_qtTimerState->active)
        return 0_s;
    return std::max(0_s, m_qtTimerState->deadline - MonotonicTime::now());
}

} // namespace WTF

#include "RunLoopQt.moc"
