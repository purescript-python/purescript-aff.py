# globals threading.Thread
import threading


class _Unq:
    pass


# A unique value for empty.
_EMPTY_ = _Unq()

"""

An awkward approximation. We elide evidence we would otherwise need in PS for
efficiency sake.

data Aff eff a
  = Pure a
  | Throw Error
  | Catch (Aff eff a) (Error -> Aff eff a)
  | Sync (Eff eff a)
  | Async ((Either Error a -> Eff eff Unit) -> Eff eff (Canceler eff))
  | forall b. Bind (Aff eff b) (b -> Aff eff a)
  | forall b. Bracket (Aff eff b) (BracketConditions eff b) (b -> Aff eff a)
  | forall b. Fork Boolean (Aff eff b) ?(Fiber eff b -> a)
  | Sequential (ParAff aff a)

"""
_PURE_ = "Pure"
_THROW_ = "Throw"
_CATCH_ = "Catch"
_SYNC_ = "Sync"
_ASYNC_ = "Async"
_BIND_ = "Bind"
_BRACKET_ = "Bracket"
_FORK_ = "Fork"
_SEQ_ = "Sequential"

"""

data ParAff eff a
  = forall b. Map (b -> a) (ParAff eff b)
  | forall b. Apply (ParAff eff (b -> a)) (ParAff eff b)
  | Alt (ParAff eff a) (ParAff eff a)
  | ?Par (Aff eff a)

"""
_MAP_ = "Map"
_APPLY_ = "Apply"
_ALT_ = "Alt"

# Various constructors used in interpretation
_CONS_ = "Cons"  # Cons-list, for stacks
_RESUME_ = "Resume"  # Continue indiscriminately
_RELEASE_ = "Release"  # Continue with bracket finalizers
_FINALIZER_ = "Finalizer"  # A non-interruptible effect
_FINALIZED_ = "Finalized"  # Marker for finalization
_FORKED_ = "Forked"  # Reference to a forked fiber, with resumption stack
_FIBER_ = "Fiber"  # Actual fiber reference
_THUNK_ = "Thunk"  # Primed effect, ready to invoke


class _Scheduler:
    def __init__(self):
        self.limit = 1024
        self.size = 0
        self.ix = 0
        self.queue = [None] * self.limit
        self.draining = False

    def _drain(self):
        thunk = None
        self.draining = True
        while self.size is not 0:
            self.size -= 1
            thunk = self.queue[self.ix]
            self.queue[self.ix] = None
            self.ix = (self.ix + 1) % self.limit
            thunk()
        self.draining = False

    def isDraining(self):
        return self.draining

    def enqueue(self, cb):
        tmp = None
        if self.size == self.limit:
            tmp = self.draining
            self._drain()
            self.draining = tmp

        self.queue[(self.ix + self.size) % self.limit] = cb
        self.size += 1

        if not self.draining:
            self._drain()


class _Aff:
    def __init__(self, tag, _1=None, _2=None, _3=None):
        self.tag = tag
        self._1 = _1
        self._2 = _2
        self._3 = _3


class _AffCtr:
    __slots__ = ["tag"]

    def __call__(self, _1, _2, _3):
        return _Aff(self.tag, _1, _2, _3)


class _KillAll:
    def __init__(self, killError, cb, supervisor):
        self.killCount = 0
        self.kills = {}
        self.killError = killError
        self.cb = cb
        self.supervisor = supervisor

    def __call__(self):
        if self.supervisor.count == 0:
            return self.cb()

        def kill(fid):
            def _killf(result):
                def _1():
                    del self.kills[fid]
                    self.killCount -= 1
                    if self.supervisor.util.isLeft(
                        result
                    ) and self.supervisor.util.fromLeft(result):

                        def _2():
                            raise self.supervisor.util.fromLeft(result)

                        t = threading.Thread(target=_2)
                        t.start()
                    if self.killCount == 0:
                        self.cb()

                return _1

            self.kills[fid] = self.supervisor.fibers[fid].kill(self.killError, _killf)()

        if self.supervisor.fibers:
            for k in self.supervisor.fibers.keys():
                self.killCount += 1
                kill(k)

        def _1(error):
            def _2():
                if self.kills is not None:
                    for v in self.kills.values():
                        v()

            return _Aff(_SYNC_, _2)

        return _1


class _Supervisor:
    def __init__(self, util):
        self.util = util
        self.fibers = {}
        self.fiberId = 0
        self.count = 0

    def register(self, fiber):
        fid = self.fiberId
        self.fiberId += 1

        def hf(result):
            def _1():
                self.count -= 1
                del self.fibers[fid]

            return _1

        oc = {"rethrow": True, "handler": hf}
        fiber.onComplete(oc)()
        self.fibers[fid] = fiber
        self.count += 1

    def isEmpty(self):
        return self.count == 0

    def killAll(self, killError, cb):
        return _KillAll(killError, cb, self)


class _RunParKill:
    def __init__(self, error, par, cb, runPar):
        self.error = error
        self.par = par
        self.cb = cb
        self.runPar = runPar
        self.step = par
        self.head = None
        self.tail = None
        self.count = 0
        self.kills = {}
        self.tmp = None
        self.kid = None

    def __call__(self):
        while True:
            self.tmp = None
            if self.step.tag == _FORKED_:
                if self.step._3 == _EMPTY_:
                    self.tmp = self.runPar.fibers[self.step._1]

                    def _1(result):
                        def _2():
                            self.count -= 1
                            if self.count == 0:
                                self.cb(self.runPar.result)()

                        return _2

                    self.kills[self.count] = self.tmp.kill(self.error, _1)
                    self.count += 1

                # Terminal case.
                if not self.head:
                    return self.finalizer()
                # Go down the right side of the tree.
                self.step = self.head._2
                if not self.tail:
                    self.head = None
                else:
                    self.head = self.tail._1
                    self.tail = self.tail._2
            elif self.step.tag == _MAP_:
                self.step = self.step._2
            elif (self.step.tag == _APPLY_) or (self.step.tag == _ALT_):
                if self.head:
                    self.tail = _Aff(_CONS_, self.head, self.tail)
                self.head = self.step
                self.step = self.step._1

    def finalizer(self):
        if self.count == 0:
            self.cb(self.runPar.util.right(None))()
        else:
            # Run the cancelation effects. We alias `count` because it's mutable.
            self.kid = 0
            self.tmp = self.count
            while self.kid < self.tmp:
                self.kills[self.kid] = self.kills[self.kid]()
                self.kid += 1

        return self.kills


class _RunParJoin:
    def __init__(self, result, head, tail, runPar):
        self.result = result
        self.head = head
        self.tail = tail
        self.runPar = runPar
        self.fail = None
        self.step = None
        self.lhs = None
        self.rhs = None
        self.tmp = None
        self.kid = None

    def __call__(self):
        if self.runPar.util.isLeft(self.result):
            self.fail = self.result
            self.step = None
        else:
            self.step = self.result
            self.fail = None

        while True:
            self.lhs = None
            self.rhs = None
            self.tmp = None
            self.kid = None

            # We should never continue if the entire tree has been interrupted.
            if self.runPar.interrupt:
                return

            # We've made it all the way to the root of the tree, which means
            # the tree has fully evaluated.
            if not self.head:
                self.runPar.cb(self.fail if self.fail else self.step)()
                return

            # The tree has already been computed, so we shouldn't try to do it
            # again. This should never happen.
            # TODO: Remove this?
            if self.head._3 != _EMPTY_:
                return

            if self.head.tag == _MAP_:
                if not self.fail:
                    self.head._3 = self.runPar.util.right(
                        self.head._1(self.runPar.util.fromRight(self.step))
                    )
                    self.step = self.head._3
                else:
                    self.head._3 = self.fail
            elif self.head.tag == _APPLY_:
                self.lhs = self.head._1._3
                self.rhs = self.head._2._3
                # If we have a failure we should kill the other side because we
                # can't possible yield a result anymore.
                if self.fail:
                    self.head._3 = self.fail
                    self.tmp = True
                    self.kid = self.runPar.killId
                    self.runPar.killId += 1

                    def _1(*_ignoreArgs):
                        def _2():
                            del self.runPar.kills[self.kid]
                            if self.tmp:
                                self.tmp = False
                            elif not self.tail:
                                self.runPar.join(self.fail, None, None)
                            else:
                                self.runPar.join(self.fail, self.tail._1, self.tail._2)

                        return _2

                    self.runPar.kills[self.kid] = self.runPar.kill(
                        self.runPar.early,
                        self.head._2 if self.fail == self.lhs else self.head._1,
                        _1,
                    )

                    if self.tmp:
                        self.tmp = False
                        return

                elif (self.lhs == _EMPTY_) or (self.rhs == _EMPTY_):
                    # We can only proceed if both sides have resolved.
                    return
                else:
                    self.step = self.runPar.util.right(
                        self.runPar.util.fromRight(self.lhs)(
                            self.runPar.util.fromRight(self.rhs)
                        )
                    )
                    self.head._3 = self.step

            elif self.head.tag == _ALT_:
                self.lhs = self.head._1._3
                self.rhs = self.head._2._3
                # We can only proceed if both have resolved or we have a success
                if ((self.lhs == _EMPTY_) and self.runPar.util.isLeft(self.rhs)) or (
                    self.rhs == _EMPTY_ and self.runPar.util.isLeft(self.lhs)
                ):
                    return
                # If both sides resolve with an error, we should continue with the
                # first error
                if (
                    (self.lhs != _EMPTY_)
                    and self.runPar.util.isLeft(self.lhs)
                    and (self.rhs != _EMPTY_)
                    and self.runPar.util.isLeft(self.rhs)
                ):
                    self.fail = self.rhs if self.step == self.lhs else self.lhs
                    self.step = None
                    self.head._3 = self.fail
                else:
                    self.head._3 = self.step
                    self.tmp = True
                    self.kid = self.runPar.killId
                    self.runPar.killId += 1
                    # Once a side has resolved, we need to cancel the side that is still
                    # pending before we can continue.
                    def _1(*_ignoreArgs):
                        def _2():
                            del self.runPar.kills[self.kid]
                            if self.tmp:
                                self.tmp = False
                            elif not self.tail:
                                self.runPar.join(self.step, None, None)
                            else:
                                self.runPar.join(self.step, self.tail._1, self.tail._2)

                        return _2

                    self.runPar.kills[self.kid] = self.runPar.kill(
                        self.runPar.early,
                        self.head._2 if self.step == self.lhs else self.head._1,
                        _1,
                    )

                    if self.tmp:
                        self.tmp = False
                        return

            if not self.tail:
                self.head = None
            else:
                self.head = self.tail._1
                self.tail = self.tail._2


class _RunParRun:
    def __init__(self, runPar):
        self.runPar = runPar
        self.status = _CONTINUE_
        self.step = runPar.par
        self.head = None
        self.tail = None
        self.tmp = None
        self.fid = None

    def finalizer(self):
        # Keep a reference to the tree root so it can be cancelled.
        self.runPar.root = self.step

        self.fid = 0
        while self.fid < self.runPar.fiberId:
            self.runPar.fibers[self.fid].run()
            self.fid += 1

    def __call__(self):
        while True:
            self.tmp = None
            self.fid = None

            if self.status == _CONTINUE_:
                if self.step.tag == _MAP_:
                    if self.head:
                        self.tail = _Aff(_CONS_, self.head, self.tail)
                    self.head = _Aff(_MAP_, self.step._1, _EMPTY_, _EMPTY_)
                    self.step = self.step._2
                elif self.step.tag == _APPLY_:
                    if self.head:
                        self.tail = _Aff(_CONS_, self.head, self.tail)
                    self.head = _Aff(_APPLY_, _EMPTY_, self.step._2, _EMPTY_)
                    self.step = self.step._1
                elif self.step.tag == _ALT_:
                    if self.head:
                        self.tail = _Aff(_CONS_, self.head, self.tail)
                    self.head = _Aff(_ALT_, _EMPTY_, self.step._2, _EMPTY_)
                    self.step = self.step._1
                else:
                    # When we hit a leaf value, we suspend the stack in the `_FORKED_`.
                    # When the fiber resolves, it can bubble back up the tree.
                    self.fid = self.runPar.fiberId
                    self.runPar.fiberId += 1
                    self.status = _RETURN_
                    self.tmp = self.step
                    self.step = _Aff(
                        _FORKED_, self.fid, _Aff(_CONS_, self.head, self.tail), _EMPTY_
                    )
                    self.tmp = _Fiber(
                        self.runPar.util, self.runPar.supervisor, self.tmp
                    )
                    self.tmp.onComplete(
                        {"rethrow": False, "handler": self.runPar.resolve(self.step)}
                    )()
                    self.runPar.fibers[self.fid] = self.tmp
                    if self.runPar.supervisor:
                        self.runPar.supervisor.register(self.tmp)
            elif self.status == _RETURN_:
                # Terminal case, we are back at the root.
                if not self.head:
                    return self.finalizer()
                # If we are done with the right side, we need to continue down the
                # left. Otherwise we should continue up the stack.
                if self.head._1 == _EMPTY_:
                    self.head._1 = self.step
                    self.status = _CONTINUE_
                    self.step = self.head._2
                    self.head._2 = _EMPTY_
                else:
                    self.head._2 = self.step
                    self.step = self.head
                    if self.tail == None:
                        self.head = None
                    else:
                        self.head = self.tail._1
                        self.tail = self.tail._2


class _RunParCancel:
    def __init__(self, error, cb, runPar):
        self.error = error
        self.cb = cb
        self.runPar = runPar
        self.innerKills = None
        self.newKills = None

    def __call__(self):
        self.runPar.interrupt = self.runPar.util.left(self.error)
        if self.runPar.kills:
            for kid0 in self.runPar.kills.keys():
                self.innerKills = self.runPar.kills[kid0]
                if self.innerKills:
                    for kid1 in self.innerKills.keys():
                        self.innerKills[kid1]()

        self.runPar.kills = None
        self.newKills = self.runPar.kill(self.error, self.runPar.root, self.cb)

        def _1(*_ignoreArgs0):
            def _2(*_ignoreArgs1):
                def _3():
                    if self.newKills:
                        for kid in self.newKills.keys():
                            self.newKills[kid]()
                    return __Aff.nonCanceler

                return _3

            return _Aff(_ASYNC_, _2)

        return _1


class RunPar:
    def __init__(self, util, supervisor, par, cb):
        self.util = util
        self.supervisor = supervisor
        self.par = par
        self.cb = cb
        # Table of all forked fibers.
        self.fiberId = 0
        self.fibers = {}

        # Table of currently running cancelers, as a product of `Alt` behavior.
        self.killId = 0
        self.kills = {}

        # Error used for early cancelation on Alt branches.
        self.early = Exception("[ParAff] Early exit")

        # Error used to kill the entire tree.
        self.interrupt = None

        # The root pointer of the tree.
        self.root = _EMPTY_
        self.run()

    # Walks a tree, invoking all the cancelers. Returns the table of pending
    # cancellation fibers.
    def kill(self, error, par, cb):
        return _RunParKill(error, par, cb, self)()

    # When a fiber resolves, we need to bubble back up the tree with the
    # result, computing the applicative nodes.
    def join(self, result, head, tail):
        return _RunParJoin(result, head, tail, self)()

    def resolve(self, fiber):
        def _1(result):
            def _2():
                del self.fibers[fiber._1]
                fiber._3 = result
                self.join(result, fiber._2._1, fiber._2._2)

            return _2

        return _1

    # Walks the applicative tree, substituting non-applicative nodes with
    # `_FORKED_` nodes. In this tree, all applicative nodes use the `_3` slot
    # as a mutable slot for memoization. In an unresolved state, the `_3`
    # slot is `_EMPTY_`. In the cases of `ALT` and `APPLY`, we always walk
    # the left side first, because both operations are left-associative. As
    # we `_RETURN_` from those branches, we then walk the right side.
    def run(self):
        return _RunParRun(self)()

    # Cancels the entire tree. If there are already subtrees being canceled,
    # we need to first cancel those joins. We will then add fresh joins for
    # all pending branches including those that were in the process of being
    # canceled.
    def cancel(self, error, cb):
        return _RunParCancel(error, cb, self)

    def __call__(self, killError):
        def _1(killCb):
            def _2():
                return self.cancel(killError, killCb)

            return _2

        return _Aff(_ASYNC_, _1)


# Fiber state machine
_SUSPENDED_ = 0  # Suspended, pending a join.
_CONTINUE_ = 1  # Interpret the next instruction.
_STEP_BIND_ = 2  # Apply the next bind.
_STEP_RESULT_ = 3  # Handle potential failure from a result.
_PENDING_ = 4  # An async effect is running.
_RETURN_ = 5  # The current stack has returned.
_COMPLETED_ = 6  # The entire fiber has completed.


class _Fiber:
    def __self__(self, util, supervisor, aff):
        self.util = util
        self.supervisor = supervisor
        self.aff = aff
        # Monotonically increasing tick, increased on each asynchronous turn.
        self.runTick = 0

        # The current branch of the state machine.
        self.status = _SUSPENDED_

        # The current point of interest for the state machine branch.
        self.step = aff  # Successful step
        self.fail = None  # Failure step
        self.interrupt = None  # Asynchronous interrupt

        # Stack of continuations for the current fiber.
        self.bhead = None
        self.btail = None

        # Stack of attempts and finalizers for error recovery. Every `Cons` is also
        # tagged with current `interrupt` state. We use this to track which items
        # should be ignored or evaluated as a result of a kill.
        self.attempts = None

        # A special state is needed for Bracket, because it cannot be killed. When
        # we enter a bracket acquisition or finalizer, we increment the counter,
        # and then decrement once complete.
        self.bracketCount = 0

        # Each join gets a new id so they can be revoked.
        self.joinId = 0
        self.joins = None
        self.rethrow = True

    # Each invocation of `run` requires a tick. When an asynchronous effect is
    # resolved, we must check that the local tick coincides with the fiber
    # tick before resuming. This prevents multiple async continuations from
    # accidentally resuming the same fiber. A common example may be invoking
    # the provided callback in `makeAff` more than once, but it may also be an
    # async effect resuming after the fiber was already cancelled.
    def _run(self, localRunTick):
        tmp = None
        result = None
        attempt = None
        while True:
            tmp = None
            result = None
            attempt = None
            if self.status == _STEP_BIND_:
                self.status = _CONTINUE_
                try:
                    self.step = self.bhead(self.step)
                    if not self.btail:
                        self.bhead = None
                    else:
                        self.bhead = self.btail._1
                        self.btail = self.btail._2
                except Exception as e:
                    self.status = _RETURN_
                    self.fail = self.util.left(e)
                    self.step = None

            elif self.status == _STEP_RESULT_:
                if self.util.isLeft(self.step):
                    self.status = _RETURN_
                    self.fail = self.step
                    self.step = None
                elif not self.bhead:
                    self.status = _RETURN_
                else:
                    self.status = _STEP_BIND_
                    self.step = self.util.fromRight(self.step)

            elif self.status == _CONTINUE_:
                if self.step.tag == _BIND_:
                    if self.bhead:
                        self.btail = _Aff(_CONS_, self.bhead, self.btail)

                    self.bhead = self.step._2
                    self.status = _CONTINUE_
                    self.step = self.step._1

                elif self.step.tag == _PURE_:
                    if not self.bhead:
                        self.status = _RETURN_
                        self.step = self.util.right(self.step._1)
                    else:
                        self.status = _STEP_BIND_
                        self.step = self.step._1

                elif self.step.tag == _SYNC_:
                    self.status = _STEP_RESULT_
                    self.step = __Aff.runSync(
                        self.util.left, self.util.right, self.step._1
                    )

                elif self.step.tag == _ASYNC_:
                    self.status = _PENDING_

                    def _1(result):
                        def _2():
                            if self.runTick != localRunTick:
                                return
                            self.runTick += 1

                            def _3():
                                # It's possible to interrupt the fiber between enqueuing and
                                # resuming, so we need to check that the runTick is still
                                # valid.
                                if self.runTick != localRunTick + 1:
                                    return
                                self.status = _STEP_RESULT_
                                self.step = result
                                self._run(self.runTick)

                            __Aff.Scheduler.enqueue(_3)

                        return _2

                    self.step = __Aff.runAsync(self.util.left, self.step._1, _1)
                    return

                elif self.step.tag == _THROW_:
                    self.status = _RETURN_
                    self.fail = self.util.left(self.step._1)
                    self.step = None

                # Enqueue the Catch so that we can call the error handler later on
                # in case of an exception.
                elif self.step.tag == _CATCH_:
                    if self.bhead == None:
                        self.attempts = _Aff(
                            _CONS_, self.step, self.attempts, self.interrupt
                        )
                    else:
                        self.attempts = _Aff(
                            _CONS_,
                            self.step,
                            _Aff(
                                _CONS_,
                                _Aff(_RESUME_, self.bhead, self.btail),
                                self.attempts,
                                self.interrupt,
                            ),
                            self.interrupt,
                        )

                    self.bhead = None
                    self.btail = None
                    self.status = _CONTINUE_
                    self.step = self.step._1

                # Enqueue the Bracket so that we can call the appropriate handlers
                # after resource acquisition.
                elif self.step.tag == _BRACKET_:
                    self.bracketCount += 1
                    if not self.bhead:
                        self.attempts = _Aff(
                            _CONS_, self.step, self.attempts, self.interrupt
                        )
                    else:
                        self.attempts = _Aff(
                            _CONS_,
                            self.step,
                            _Aff(
                                _CONS_,
                                _Aff(_RESUME_, self.bhead, self.btail),
                                self.attempts,
                                self.interrupt,
                            ),
                            self.interrupt,
                        )

                    self.bhead = None
                    self.btail = None
                    self.status = _CONTINUE_
                    self.step = self.step._1

                elif self.step.tag == _FORK_:
                    self.status = _STEP_RESULT_
                    tmp = _Fiber(self.util, self.supervisor, self.step._2)
                    if self.supervisor:
                        self.supervisor.register(tmp)

                    if self.step._1:
                        tmp.run()

                    self.step = self.util.right(tmp)

                elif self.step.tag == _SEQ_:
                    self.status = _CONTINUE_
                    self.step = __Aff.sequential(
                        self.util, self.supervisor, self.step._1
                    )

            elif self.status == _RETURN_:
                self.bhead = None
                self.btail = None
                # If the current stack has returned, and we have no other stacks to
                # resume or finalizers to run, the fiber has halted and we can
                # invoke all join callbacks. Otherwise we need to resume.
                if not self.attempts:
                    self.status = _COMPLETED_
                    self.step = (
                        self.interrupt
                        if self.interrupt
                        else self.fail
                        if self.fail
                        else self.step
                    )
                else:
                    # The interrupt status for the enqueued item.
                    tmp = self.attempts._3
                    attempt = self.attempts._1
                    self.attempts = self.attempts._2

                    # We cannot recover from an unmasked interrupt. Otherwise we should
                    # continue stepping, or run the exception handler if an exception
                    # was raised.
                    if attempt.tag == _CATCH_:
                        # We should compare the interrupt status as well because we
                        # only want it to apply if there has been an interrupt since
                        # enqueuing the catch.
                        if (
                            self.interrupt
                            and (self.interrupt != tmp)
                            and (self.bracketCount == 0)
                        ):
                            self.status = _RETURN_
                        elif self.fail:
                            self.status = _CONTINUE_
                            self.step = attempt._2(self.util.fromLeft(self.fail))
                            self.fail = None

                    # We cannot resume from an unmasked interrupt or exception.
                    elif attempt.tag == _RESUME_:
                        # As with Catch, we only want to ignore in the case of an
                        # interrupt since enqueing the item.
                        if (
                            self.interrupt
                            and (self.interrupt != tmp)
                            and (self.bracketCount == 0)
                            or self.fail
                        ):
                            self.status = _RETURN_
                        else:
                            self.bhead = attempt._1
                            self.btail = attempt._2
                            self.status = _STEP_BIND_
                            self.step = self.util.fromRight(self.step)

                    # If we have a bracket, we should enqueue the handlers,
                    # and continue with the success branch only if the fiber has
                    # not been interrupted. If the bracket acquisition failed, we
                    # should not run either.
                    elif attempt.tag == _BRACKET_:
                        self.bracketCount -= 1
                        if not self.fail:
                            result = self.util.fromRight(self.step)
                            # We need to enqueue the Release with the same interrupt
                            # status as the Bracket that is initiating it.
                            self.attempts = _Aff(
                                _CONS_,
                                _Aff(_RELEASE_, attempt._2, result),
                                self.attempts,
                                tmp,
                            )
                            # We should only coninue as long as the interrupt status has not changed or
                            # we are currently within a non-interruptable finalizer.
                            if (self.interrupt == tmp) or (self.bracketCount > 0):
                                self.status = _CONTINUE_
                                self.step = attempt._3(result)

                    # Enqueue the appropriate handler. We increase the bracket count
                    # because it should not be cancelled.
                    elif attempt.tag == _RELEASE_:
                        self.attempts = _Aff(
                            _CONS_,
                            _Aff(_FINALIZED_, self.step, self.fail),
                            self.attempts,
                            self.interrupt,
                        )
                        self.status = _CONTINUE_
                        # It has only been killed if the interrupt status has changed
                        # since we enqueued the item, and the bracket count is 0. If the
                        # bracket count is non-zero then we are in a masked state so it's
                        # impossible to be killed.
                        if (
                            self.interrupt
                            and (self.interrupt != tmp)
                            and (self.bracketCount == 0)
                        ):
                            self.step = attempt._1.killed(
                                self.util.fromLeft(self.interrupt)
                            )(attempt._2)
                        elif self.fail:
                            self.step = attempt._1.failed(
                                self.util.fromLeft(self.fail)
                            )(attempt._2)
                        else:
                            self.step = attempt._1.completed(
                                self.util.fromRight(self.step)
                            )(attempt._2)

                        self.fail = None
                        self.bracketCount += 1

                    elif attempt.tag == _FINALIZER_:
                        self.bracketCount += 1
                        self.attempts = _Aff(
                            _CONS_,
                            _Aff(_FINALIZED_, self.step, self.fail),
                            self.attempts,
                            self.interrupt,
                        )
                        self.status = _CONTINUE_
                        self.step = attempt._1

                    elif attempt.tag == _FINALIZED_:
                        self.bracketCount -= 1
                        self.status = _RETURN_
                        self.step = attempt._1
                        self.fail = attempt._2

            elif self.status == _COMPLETED_:
                if self.joins:
                    for v in self.joins.values():
                        self.rethrow = self.rethrow and v.rethrow
                        __Aff.runEff(v.handler(self.step))
                self.joins = None
                # If we have an interrupt and a fail, then the thread threw while
                # running finalizers. This should always rethrow in a fresh stack.
                if self.interrupt and self.fail:

                    def _2():
                        raise self.util.fromLeft(self.fail)

                    t = threading.Thread(target=_2)
                    t.start()
                # If we have an unhandled exception, and no other fiber has joined
                # then we need to throw the exception in a fresh stack.
                elif (self.util.isLeft(self.step)) and (self.rethrow):

                    def _2():
                        raise self.util.fromLeft(self.step)

                    t = threading.Thread(target=_2)
                    t.start()
                return
            elif self.status == _SUSPENDED_:
                self.status = _CONTINUE_
            elif self.status == _PENDING_:
                return

    def onComplete(self, join):
        def _1():
            if self.status == _COMPLETED_:
                self.rethrow = self.rethrow and join.rethrow
                join.handler(self.step)()

                def _2():
                    pass

                return _2

            jid = self.joinId
            self.joinId += 1
            self.joins = self.joins if self.joins else {}
            self.joins[jid] = self.join

            def _2():
                if self.joins:
                    del self.joins[jid]

            return _2

        return _1

    def kill(self, error, cb):
        def _1():
            if self.status == _COMPLETED_:
                cb(self.util.right(None))()

                def _2():
                    pass

                return _2

            def _2(*_ignoreArgs):
                return cb(self.util.right(None))

            canceler = self.onComplete({"rethrow": False, "handler": _2})()

            if self.status == _SUSPENDED_:
                self.interrupt = self.util.left(error)
                self.status = _COMPLETED_
                self.step = self.interrupt
                self._run(self.runTick)
            elif self.status == _PENDING_:
                if not self.interrupt:
                    self.interrupt = self.util.left(error)
                if self.bracketCount == 0:
                    if self.status == _PENDING_:
                        self.attempts = _Aff(
                            _CONS_,
                            _Aff(_FINALIZER_, self.step(error)),
                            self.attempts,
                            self.interrupt,
                        )
                    self.status = _RETURN_
                    self.step = None
                    self.fail = None
                    self.runTick += 1
                    self._run(self.runTick)
            else:
                if not self.interrupt:
                    self.interrupt = self.util.left(error)

                if self.bracketCount == 0:
                    self.status = _RETURN_
                    self.step = None
                    self.fail = None

            return canceler

        return _1

    def join(self, cb):
        def _1():
            canceler = self.onComplete({"rethrow": False, "handler": cb})()
            if self.status == _SUSPENDED_:
                self._run(self.runTick)
            return canceler

        return _1

    def isSuspended(self):
        return self.status == _SUSPENDED_

    def run(self):
        if self.status == _SUSPENDED_:
            if not __Aff.Scheduler.isDraining():

                def _1():
                    self._run(self.runTick)

                __Aff.Scheduler.enqueue(_1)
            else:
                self._run(self.runTick)


class __Aff:
    @staticmethod
    def AffCtr(tag):
        fn = _AffCtr()
        fn.tag = tag
        return fn

    @staticmethod
    def nonCanceler(error):
        return _Aff(_PURE_)

    @staticmethod
    def runEff(eff):
        try:
            eff()
        except Exception as error:

            def _raise():
                raise error

            t = threading.Thread(target=_raise)
            t.start()

    @staticmethod
    def runSync(left, right, eff):
        try:
            return right(eff())
        except Exception as error:
            return left(error)

    @staticmethod
    def runAsync(left, eff, k):
        try:
            return eff(k)()
        except Exception as error:
            k(left(error))()
            return __Aff.nonCanceler

    @staticmethod
    def sequential(util, supervisor, par):
        def _1(cb):
            def _2():
                return RunPar(util, supervisor, par, cb)

            return _2

        return _Aff(_ASYNC_, _1)

    EMPTY = _EMPTY_
    Pure = AffCtr(_PURE_)
    Throw = AffCtr(_THROW_)
    Catch = AffCtr(_CATCH_)
    Sync = AffCtr(_SYNC_)
    Async = AffCtr(_ASYNC_)
    Bind = AffCtr(_BIND_)
    Bracket = AffCtr(_BRACKET_)
    Fork = AffCtr(_FORK_)
    Seq = AffCtr(_SEQ_)
    ParMap = AffCtr(_MAP_)
    ParApply = AffCtr(_APPLY_)
    ParAlt = AffCtr(_ALT_)
    Fiber = _Fiber
    Scheduler = _Scheduler()
    Supervisor = _Supervisor


_pure = __Aff.Pure

_throwError = __Aff.Throw


def _catchError(aff):
    def _1(k):
        return __Aff.Catch(aff, k)

    return _1


def _map(f):
    def _1(aff):
        if aff.tag == __Aff.Pure.tag:
            return __Aff.Pure(f(aff._1))
        else:

            def _2(value):
                return __Aff.Pure(f(value))

            return __Aff.Bind(aff, _2)

    return _1


def _bind(aff):
    def _1(k):
        return __Aff.Bind(aff, k)

    return _1


def _fork(immediate):
    def _1(aff):
        return __Aff.Fork(immediate, aff)

    return _1


_liftEffect = __Aff.Sync


def _parAffMap(f):
    def _1(aff):
        return __Aff.ParMap(f, aff)

    return _1


def _parAffApply(aff1):
    def _1(aff2):
        return __Aff.ParApply(aff1, aff2)

    return _1


def _parAffAlt(aff1):
    def _1(aff2):
        return __Aff.ParAlt(aff1, aff2)

    return _1


makeAff = __Aff.Async


def generalBracket(acquire):
    def _1(options):
        def _2(k):
            return __Aff.Bracket(acquire, options, k)

        return _2

    return _1


def _makeFiber(util, aff):
    def _1():
        return __Aff.Fiber(util, None, aff)

    return _1


def _makeSupervisedFiber(util, aff):
    def _1():
        supervisor = __Aff.Supervisor(util)
        return {"fiber": __Aff.Fiber(util, supervisor, aff), "supervisor": supervisor}

    return _1


def _killAll(error, supervisor, cb):
    return supervisor.killAll(error, cb)


def _delay(right, ms):
    return _Delay()(right, ms)


class _Delay:
    def __init__(self):
        self.timer = None

    def setDelay(self, n, k):
        self.timer = threading.Timer(n * 1000, k)
        self.timer.start()

    def clearDelay(self):
        if self.timer:
            return self.timer.cancel()

    def __call__(self, right, ms):
        def _1(cb):
            def _2():
                self.setDelay(ms, cb(right()))

                def _3():
                    def _4():
                        return right(self.clearDelay())

                    return __Aff.Sync(_4)

                return _3

            return _2

        return __Aff.Async(_1)


_sequential = __Aff.Seq
