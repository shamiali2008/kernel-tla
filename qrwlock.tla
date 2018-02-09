---------------------------- MODULE qrwlock ---------------------------------
\*
\* Linux queued read-write locks model
\*
EXTENDS Naturals, Sequences, TLC

CONSTANTS READERS,		\* set of readers
	  WRITERS,		\* set of writers
	  INTERRUPTS,		\* test interrupts
	  TRYLOCK		\* test trylock

ASSUME	/\ INTERRUPTS \in BOOLEAN
	/\ TRYLOCK \in BOOLEAN

(* --algorithm locktest {
variables
	lock = [cnts |-> [readers	|-> 0,		\* readers count
			  wwaiting	|-> FALSE,	\* writer waiting
			  wlocked	|-> FALSE],	\* locked for write
		wait_lock		|-> FALSE];	\* fair spinlock

	\* trylock procedures return
	ret_read_tl	= [r \in READERS |-> FALSE];
	ret_write_tl	= [w \in WRITERS |-> FALSE];

define {
	\* cnts predicates
	ZERO(c)		== c.readers = 0 /\ ~c.wwaiting /\ ~c.wlocked
	WLOCKED(c)	== c.wlocked
	WMASK(c)	== c.wwaiting \/ c.wlocked

	\* Invariants
	TypeInv		== lock \in [cnts:	[readers:	Nat,
						 wwaiting:	BOOLEAN,
						 wlocked:	BOOLEAN],
				     wait_lock:			BOOLEAN]

	\* Safety properties
	RWExcl		== \A r \in READERS, w \in WRITERS :
				~((pc[r] = "rcs") /\ (pc[w] = "wcs"))
	WWExcl		== \A w1, w2 \in WRITERS : w1 # w2 =>
				~((pc[w1] = "wcs") /\ (pc[w2] = "wcs"))

	\* Liveness properties
	LockAny		== \E p \in READERS \cup WRITERS :
				pc[p] \notin {"rcs", "wcs"} ~> pc[p] \in {"rcs", "wcs"}
	LockAll		== \A p \in READERS \cup WRITERS :
				pc[p] \notin {"rcs", "wcs"} ~> pc[p] \in {"rcs", "wcs"}

	\* Symmetry optimisations
	Perms		== Permutations(READERS) \cup Permutations(WRITERS)
}

macro spin_lock(lock) {
	await ~lock;
	lock := TRUE;
}

macro spin_unlock(lock) {
	lock := FALSE;
}

procedure queued_read_trylock()
{
rtl1:	if (~WMASK(lock.cnts)) {
rtl2:		lock.cnts.readers := lock.cnts.readers + 1;
		if (~WMASK(lock.cnts)) {
			ret_read_tl[self] := TRUE;
			return;
		};
rtl4:		lock.cnts.readers := lock.cnts.readers - 1;
	};
rtl5:	ret_read_tl[self] := FALSE;
	return;
}

procedure queued_read_lock()
{
rl1:	lock.cnts.readers := lock.cnts.readers + 1;
	if (~WMASK(lock.cnts))
		return;
	\* slow path
rl2:	either {
		\* in interrupt
		await INTERRUPTS;
		await ~WLOCKED(lock.cnts);
		return;
	} or {
		skip;
	};
rl3:	lock.cnts.readers := lock.cnts.readers - 1;
	\* strong fairness, spin_lock() expected to make progress
rl4:+	spin_lock(lock.wait_lock);
rl5:	lock.cnts.readers := lock.cnts.readers + 1;
rl6:	await ~WLOCKED(lock.cnts);
rl7:	spin_unlock(lock.wait_lock);
	return;
}

procedure queued_read_unlock()
{
ru1:	lock.cnts.readers := lock.cnts.readers - 1;
	return;
}

procedure queued_write_trylock()
{
wtl1:	if (~ZERO(lock.cnts)) {
		ret_write_tl[self] := FALSE;
	} else {
		lock.cnts.wlocked := TRUE;
		ret_write_tl[self] := TRUE;
	};
	return;
}

procedure queued_write_lock()
{
wl1:	if (ZERO(lock.cnts)) {
		lock.cnts.wlocked := TRUE;
		return;
	};
	\* slow path; strong fairness, spin_lock() expected to make progress
wl2:+	spin_lock(lock.wait_lock);
wl3:	if (ZERO(lock.cnts)) {
		lock.cnts.wlocked := TRUE;
		goto wunlock;
	};
wl4:	lock.cnts.wwaiting := TRUE;
wl5:	await lock.cnts.readers = 0 /\ lock.cnts.wlocked = FALSE;
	lock.cnts.wwaiting := FALSE || lock.cnts.wlocked := TRUE;
wunlock:
	spin_unlock(lock.wait_lock);
	return;
}

procedure queued_write_unlock()
{
wu1:	lock.cnts.wlocked := FALSE;
	return;
}

fair process (reader \in READERS)
{
rlock:	while (TRUE) {
		either {
			call queued_read_lock();
		} or {
			await TRYLOCK;
rtl:			call queued_read_trylock();
rtlret:			if (~ret_read_tl[self])
				goto rtl;
		};
rcs:		skip;
runlock:	call queued_read_unlock();
	}
}

fair process (writer \in WRITERS)
{
wlock:	while (TRUE) {
		either {
			call queued_write_lock();
		} or {
			await TRYLOCK;
wtl:			call queued_write_trylock();
wtlret:			if (~ret_write_tl[self])
				goto wtl;
		};
wcs:		skip;
wunlock:	call queued_write_unlock();
	}
}
} *)
\* BEGIN TRANSLATION
\* Label wunlock of procedure queued_write_lock at line 60 col 9 changed to wunlock_
VARIABLES lock, ret_read_tl, ret_write_tl, pc, stack

(* define statement *)
ZERO(c)         == c.readers = 0 /\ ~c.wwaiting /\ ~c.wlocked
WLOCKED(c)      == c.wlocked
WMASK(c)        == c.wwaiting \/ c.wlocked


TypeInv         == lock \in [cnts:      [readers:       Nat,
                                         wwaiting:      BOOLEAN,
                                         wlocked:       BOOLEAN],
                             wait_lock:                 BOOLEAN]


RWExcl          == \A r \in READERS, w \in WRITERS :
                        ~((pc[r] = "rcs") /\ (pc[w] = "wcs"))
WWExcl          == \A w1, w2 \in WRITERS : w1 # w2 =>
                        ~((pc[w1] = "wcs") /\ (pc[w2] = "wcs"))


LockAny         == \E p \in READERS \cup WRITERS :
                        pc[p] \notin {"rcs", "wcs"} ~> pc[p] \in {"rcs", "wcs"}
LockAll         == \A p \in READERS \cup WRITERS :
                        pc[p] \notin {"rcs", "wcs"} ~> pc[p] \in {"rcs", "wcs"}


Perms           == Permutations(READERS) \cup Permutations(WRITERS)


vars == << lock, ret_read_tl, ret_write_tl, pc, stack >>

ProcSet == (READERS) \cup (WRITERS)

Init == (* Global variables *)
        /\ lock = [cnts |-> [readers       |-> 0,
                             wwaiting      |-> FALSE,
                             wlocked       |-> FALSE],
                   wait_lock               |-> FALSE]
        /\ ret_read_tl = [r \in READERS |-> FALSE]
        /\ ret_write_tl = [w \in WRITERS |-> FALSE]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in READERS -> "rlock"
                                        [] self \in WRITERS -> "wlock"]

rtl1(self) == /\ pc[self] = "rtl1"
              /\ IF ~WMASK(lock.cnts)
                    THEN /\ pc' = [pc EXCEPT ![self] = "rtl2"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "rtl5"]
              /\ UNCHANGED << lock, ret_read_tl, ret_write_tl, stack >>

rtl2(self) == /\ pc[self] = "rtl2"
              /\ lock' = [lock EXCEPT !.cnts.readers = lock.cnts.readers + 1]
              /\ IF ~WMASK(lock'.cnts)
                    THEN /\ ret_read_tl' = [ret_read_tl EXCEPT ![self] = TRUE]
                         /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                         /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "rtl4"]
                         /\ UNCHANGED << ret_read_tl, stack >>
              /\ UNCHANGED ret_write_tl

rtl4(self) == /\ pc[self] = "rtl4"
              /\ lock' = [lock EXCEPT !.cnts.readers = lock.cnts.readers - 1]
              /\ pc' = [pc EXCEPT ![self] = "rtl5"]
              /\ UNCHANGED << ret_read_tl, ret_write_tl, stack >>

rtl5(self) == /\ pc[self] = "rtl5"
              /\ ret_read_tl' = [ret_read_tl EXCEPT ![self] = FALSE]
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << lock, ret_write_tl >>

queued_read_trylock(self) == rtl1(self) \/ rtl2(self) \/ rtl4(self)
                                \/ rtl5(self)

rl1(self) == /\ pc[self] = "rl1"
             /\ lock' = [lock EXCEPT !.cnts.readers = lock.cnts.readers + 1]
             /\ IF ~WMASK(lock'.cnts)
                   THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "rl2"]
                        /\ stack' = stack
             /\ UNCHANGED << ret_read_tl, ret_write_tl >>

rl2(self) == /\ pc[self] = "rl2"
             /\ \/ /\ INTERRUPTS
                   /\ ~WLOCKED(lock.cnts)
                   /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                   /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                \/ /\ TRUE
                   /\ pc' = [pc EXCEPT ![self] = "rl3"]
                   /\ stack' = stack
             /\ UNCHANGED << lock, ret_read_tl, ret_write_tl >>

rl3(self) == /\ pc[self] = "rl3"
             /\ lock' = [lock EXCEPT !.cnts.readers = lock.cnts.readers - 1]
             /\ pc' = [pc EXCEPT ![self] = "rl4"]
             /\ UNCHANGED << ret_read_tl, ret_write_tl, stack >>

rl4(self) == /\ pc[self] = "rl4"
             /\ ~(lock.wait_lock)
             /\ lock' = [lock EXCEPT !.wait_lock = TRUE]
             /\ pc' = [pc EXCEPT ![self] = "rl5"]
             /\ UNCHANGED << ret_read_tl, ret_write_tl, stack >>

rl5(self) == /\ pc[self] = "rl5"
             /\ lock' = [lock EXCEPT !.cnts.readers = lock.cnts.readers + 1]
             /\ pc' = [pc EXCEPT ![self] = "rl6"]
             /\ UNCHANGED << ret_read_tl, ret_write_tl, stack >>

rl6(self) == /\ pc[self] = "rl6"
             /\ ~WLOCKED(lock.cnts)
             /\ pc' = [pc EXCEPT ![self] = "rl7"]
             /\ UNCHANGED << lock, ret_read_tl, ret_write_tl, stack >>

rl7(self) == /\ pc[self] = "rl7"
             /\ lock' = [lock EXCEPT !.wait_lock = FALSE]
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << ret_read_tl, ret_write_tl >>

queued_read_lock(self) == rl1(self) \/ rl2(self) \/ rl3(self) \/ rl4(self)
                             \/ rl5(self) \/ rl6(self) \/ rl7(self)

ru1(self) == /\ pc[self] = "ru1"
             /\ lock' = [lock EXCEPT !.cnts.readers = lock.cnts.readers - 1]
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << ret_read_tl, ret_write_tl >>

queued_read_unlock(self) == ru1(self)

wtl1(self) == /\ pc[self] = "wtl1"
              /\ IF ~ZERO(lock.cnts)
                    THEN /\ ret_write_tl' = [ret_write_tl EXCEPT ![self] = FALSE]
                         /\ lock' = lock
                    ELSE /\ lock' = [lock EXCEPT !.cnts.wlocked = TRUE]
                         /\ ret_write_tl' = [ret_write_tl EXCEPT ![self] = TRUE]
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED ret_read_tl

queued_write_trylock(self) == wtl1(self)

wl1(self) == /\ pc[self] = "wl1"
             /\ IF ZERO(lock.cnts)
                   THEN /\ lock' = [lock EXCEPT !.cnts.wlocked = TRUE]
                        /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "wl2"]
                        /\ UNCHANGED << lock, stack >>
             /\ UNCHANGED << ret_read_tl, ret_write_tl >>

wl2(self) == /\ pc[self] = "wl2"
             /\ ~(lock.wait_lock)
             /\ lock' = [lock EXCEPT !.wait_lock = TRUE]
             /\ pc' = [pc EXCEPT ![self] = "wl3"]
             /\ UNCHANGED << ret_read_tl, ret_write_tl, stack >>

wl3(self) == /\ pc[self] = "wl3"
             /\ IF ZERO(lock.cnts)
                   THEN /\ lock' = [lock EXCEPT !.cnts.wlocked = TRUE]
                        /\ pc' = [pc EXCEPT ![self] = "wunlock_"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "wl4"]
                        /\ lock' = lock
             /\ UNCHANGED << ret_read_tl, ret_write_tl, stack >>

wl4(self) == /\ pc[self] = "wl4"
             /\ lock' = [lock EXCEPT !.cnts.wwaiting = TRUE]
             /\ pc' = [pc EXCEPT ![self] = "wl5"]
             /\ UNCHANGED << ret_read_tl, ret_write_tl, stack >>

wl5(self) == /\ pc[self] = "wl5"
             /\ lock.cnts.readers = 0 /\ lock.cnts.wlocked = FALSE
             /\ lock' = [lock EXCEPT !.cnts.wwaiting = FALSE,
                                     !.cnts.wlocked = TRUE]
             /\ pc' = [pc EXCEPT ![self] = "wunlock_"]
             /\ UNCHANGED << ret_read_tl, ret_write_tl, stack >>

wunlock_(self) == /\ pc[self] = "wunlock_"
                  /\ lock' = [lock EXCEPT !.wait_lock = FALSE]
                  /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                  /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                  /\ UNCHANGED << ret_read_tl, ret_write_tl >>

queued_write_lock(self) == wl1(self) \/ wl2(self) \/ wl3(self) \/ wl4(self)
                              \/ wl5(self) \/ wunlock_(self)

wu1(self) == /\ pc[self] = "wu1"
             /\ lock' = [lock EXCEPT !.cnts.wlocked = FALSE]
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << ret_read_tl, ret_write_tl >>

queued_write_unlock(self) == wu1(self)

rlock(self) == /\ pc[self] = "rlock"
               /\ \/ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "queued_read_lock",
                                                              pc        |->  "rcs" ] >>
                                                          \o stack[self]]
                     /\ pc' = [pc EXCEPT ![self] = "rl1"]
                  \/ /\ TRYLOCK
                     /\ pc' = [pc EXCEPT ![self] = "rtl"]
                     /\ stack' = stack
               /\ UNCHANGED << lock, ret_read_tl, ret_write_tl >>

rcs(self) == /\ pc[self] = "rcs"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "runlock"]
             /\ UNCHANGED << lock, ret_read_tl, ret_write_tl, stack >>

runlock(self) == /\ pc[self] = "runlock"
                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "queued_read_unlock",
                                                          pc        |->  "rlock" ] >>
                                                      \o stack[self]]
                 /\ pc' = [pc EXCEPT ![self] = "ru1"]
                 /\ UNCHANGED << lock, ret_read_tl, ret_write_tl >>

rtl(self) == /\ pc[self] = "rtl"
             /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "queued_read_trylock",
                                                      pc        |->  "rtlret" ] >>
                                                  \o stack[self]]
             /\ pc' = [pc EXCEPT ![self] = "rtl1"]
             /\ UNCHANGED << lock, ret_read_tl, ret_write_tl >>

rtlret(self) == /\ pc[self] = "rtlret"
                /\ IF ~ret_read_tl[self]
                      THEN /\ pc' = [pc EXCEPT ![self] = "rtl"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "rcs"]
                /\ UNCHANGED << lock, ret_read_tl, ret_write_tl, stack >>

reader(self) == rlock(self) \/ rcs(self) \/ runlock(self) \/ rtl(self)
                   \/ rtlret(self)

wlock(self) == /\ pc[self] = "wlock"
               /\ \/ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "queued_write_lock",
                                                              pc        |->  "wcs" ] >>
                                                          \o stack[self]]
                     /\ pc' = [pc EXCEPT ![self] = "wl1"]
                  \/ /\ TRYLOCK
                     /\ pc' = [pc EXCEPT ![self] = "wtl"]
                     /\ stack' = stack
               /\ UNCHANGED << lock, ret_read_tl, ret_write_tl >>

wcs(self) == /\ pc[self] = "wcs"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "wunlock"]
             /\ UNCHANGED << lock, ret_read_tl, ret_write_tl, stack >>

wunlock(self) == /\ pc[self] = "wunlock"
                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "queued_write_unlock",
                                                          pc        |->  "wlock" ] >>
                                                      \o stack[self]]
                 /\ pc' = [pc EXCEPT ![self] = "wu1"]
                 /\ UNCHANGED << lock, ret_read_tl, ret_write_tl >>

wtl(self) == /\ pc[self] = "wtl"
             /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "queued_write_trylock",
                                                      pc        |->  "wtlret" ] >>
                                                  \o stack[self]]
             /\ pc' = [pc EXCEPT ![self] = "wtl1"]
             /\ UNCHANGED << lock, ret_read_tl, ret_write_tl >>

wtlret(self) == /\ pc[self] = "wtlret"
                /\ IF ~ret_write_tl[self]
                      THEN /\ pc' = [pc EXCEPT ![self] = "wtl"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "wcs"]
                /\ UNCHANGED << lock, ret_read_tl, ret_write_tl, stack >>

writer(self) == wlock(self) \/ wcs(self) \/ wunlock(self) \/ wtl(self)
                   \/ wtlret(self)

Next == (\E self \in ProcSet:  \/ queued_read_trylock(self)
                               \/ queued_read_lock(self)
                               \/ queued_read_unlock(self)
                               \/ queued_write_trylock(self)
                               \/ queued_write_lock(self)
                               \/ queued_write_unlock(self))
           \/ (\E self \in READERS: reader(self))
           \/ (\E self \in WRITERS: writer(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in READERS : /\ WF_vars(reader(self))
                                 /\ WF_vars(queued_read_lock(self))
                                 /\ SF_vars(rl4(self))                                 /\ WF_vars(queued_read_trylock(self))
                                 /\ WF_vars(queued_read_unlock(self))
        /\ \A self \in WRITERS : /\ WF_vars(writer(self))
                                 /\ WF_vars(queued_write_lock(self))
                                 /\ SF_vars(wl2(self))                                 /\ WF_vars(queued_write_trylock(self))
                                 /\ WF_vars(queued_write_unlock(self))

\* END TRANSLATION
=============================================================================
