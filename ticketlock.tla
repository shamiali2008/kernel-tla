---------------------------- MODULE ticketlock -----------------------------
\*
\* Linux ticket lock implementation (following arm64 but without exclusives)
\*
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS PROCS,
	  MAXVAL,
	  TRYLOCK

ASSUME /\ MAXVAL \in Nat \ {0}
       /\ Cardinality(PROCS) <= MAXVAL + 1
       /\ TRYLOCK \in BOOLEAN

(* --algorithm ticketlock {
variables
	lock		= [owner	|-> 0,
			   next		|-> 0];

	ret_trylock	= [p \in PROCS	|-> FALSE];

define {
	\* next/owner have a limited range
	WrapInc(val)	== IF val = MAXVAL THEN 0 ELSE val + 1
	WrapDec(val)	== IF val = 0 THEN MAXVAL ELSE val - 1

	\* Invariants
	TypeInv		== lock \in [owner:	0..MAXVAL,
				     next:	0..MAXVAL]

	\* Safety
	ExclInv		== \A p1, p2 \in PROCS :
				p1 # p2 => ~((pc[p1] = "cs") /\ (pc[p2] = "cs"))

	\* Liveness
	LockAny		== \E p \in PROCS : pc[p] # "cs" ~> pc[p] = "cs"
	LockAll		== \A p \in PROCS : pc[p] # "cs" ~> pc[p] = "cs"
}

procedure spin_lock()
	variable next;
{
l1:	next := lock.next;
	lock.next := WrapInc(lock.next);
l2:	await lock.owner = next;
	return;
}

procedure spin_unlock()
{
u1:	lock.owner := WrapInc(lock.owner);
u2:	return;
}

procedure spin_trylock()
{
tl1:	if (lock.owner # lock.next) {
		ret_trylock[self] := FALSE;
	} else {
		lock.next := WrapInc(lock.next);
		ret_trylock[self] := TRUE;
	};
tl2:	return;
}

fair process (proc \in PROCS)
{
lock:	while (TRUE) {
		either {
			call spin_lock();
		} or {
			await TRYLOCK;
tl:			call spin_trylock();
tlret:			if (~ret_trylock[self])
				goto tl;
		};
cs:		skip;
unlock:		call spin_unlock();
	}
}
} *)
\* BEGIN TRANSLATION
\* Label lock of process proc at line 68 col 9 changed to lock_
CONSTANT defaultInitValue
VARIABLES lock, ret_trylock, pc, stack

(* define statement *)
WrapInc(val)    == IF val = MAXVAL THEN 0 ELSE val + 1
WrapDec(val)    == IF val = 0 THEN MAXVAL ELSE val - 1


TypeInv         == lock \in [owner:     0..MAXVAL,
                             next:      0..MAXVAL]


ExclInv         == \A p1, p2 \in PROCS :
                        p1 # p2 => ~((pc[p1] = "cs") /\ (pc[p2] = "cs"))


LockAny         == \E p \in PROCS : pc[p] # "cs" ~> pc[p] = "cs"
LockAll         == \A p \in PROCS : pc[p] # "cs" ~> pc[p] = "cs"

VARIABLE next

vars == << lock, ret_trylock, pc, stack, next >>

ProcSet == (PROCS)

Init == (* Global variables *)
        /\ lock = [owner        |-> 0,
                   next         |-> 0]
        /\ ret_trylock = [p \in PROCS  |-> FALSE]
        (* Procedure spin_lock *)
        /\ next = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "lock_"]

l1(self) == /\ pc[self] = "l1"
            /\ next' = [next EXCEPT ![self] = lock.next]
            /\ lock' = [lock EXCEPT !.next = WrapInc(lock.next)]
            /\ pc' = [pc EXCEPT ![self] = "l2"]
            /\ UNCHANGED << ret_trylock, stack >>

l2(self) == /\ pc[self] = "l2"
            /\ lock.owner = next[self]
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ next' = [next EXCEPT ![self] = Head(stack[self]).next]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << lock, ret_trylock >>

spin_lock(self) == l1(self) \/ l2(self)

u1(self) == /\ pc[self] = "u1"
            /\ lock' = [lock EXCEPT !.owner = WrapInc(lock.owner)]
            /\ pc' = [pc EXCEPT ![self] = "u2"]
            /\ UNCHANGED << ret_trylock, stack, next >>

u2(self) == /\ pc[self] = "u2"
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << lock, ret_trylock, next >>

spin_unlock(self) == u1(self) \/ u2(self)

tl1(self) == /\ pc[self] = "tl1"
             /\ IF lock.owner # lock.next
                   THEN /\ ret_trylock' = [ret_trylock EXCEPT ![self] = FALSE]
                        /\ lock' = lock
                   ELSE /\ lock' = [lock EXCEPT !.next = WrapInc(lock.next)]
                        /\ ret_trylock' = [ret_trylock EXCEPT ![self] = TRUE]
             /\ pc' = [pc EXCEPT ![self] = "tl2"]
             /\ UNCHANGED << stack, next >>

tl2(self) == /\ pc[self] = "tl2"
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << lock, ret_trylock, next >>

spin_trylock(self) == tl1(self) \/ tl2(self)

lock_(self) == /\ pc[self] = "lock_"
               /\ \/ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "spin_lock",
                                                              pc        |->  "cs",
                                                              next      |->  next[self] ] >>
                                                          \o stack[self]]
                     /\ next' = [next EXCEPT ![self] = defaultInitValue]
                     /\ pc' = [pc EXCEPT ![self] = "l1"]
                  \/ /\ TRYLOCK
                     /\ pc' = [pc EXCEPT ![self] = "tl"]
                     /\ UNCHANGED <<stack, next>>
               /\ UNCHANGED << lock, ret_trylock >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "unlock"]
            /\ UNCHANGED << lock, ret_trylock, stack, next >>

unlock(self) == /\ pc[self] = "unlock"
                /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "spin_unlock",
                                                         pc        |->  "lock_" ] >>
                                                     \o stack[self]]
                /\ pc' = [pc EXCEPT ![self] = "u1"]
                /\ UNCHANGED << lock, ret_trylock, next >>

tl(self) == /\ pc[self] = "tl"
            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "spin_trylock",
                                                     pc        |->  "tlret" ] >>
                                                 \o stack[self]]
            /\ pc' = [pc EXCEPT ![self] = "tl1"]
            /\ UNCHANGED << lock, ret_trylock, next >>

tlret(self) == /\ pc[self] = "tlret"
               /\ IF ~ret_trylock[self]
                     THEN /\ pc' = [pc EXCEPT ![self] = "tl"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
               /\ UNCHANGED << lock, ret_trylock, stack, next >>

proc(self) == lock_(self) \/ cs(self) \/ unlock(self) \/ tl(self)
                 \/ tlret(self)

Next == (\E self \in ProcSet:  \/ spin_lock(self) \/ spin_unlock(self)
                               \/ spin_trylock(self))
           \/ (\E self \in PROCS: proc(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in PROCS : /\ WF_vars(proc(self))
                               /\ WF_vars(spin_lock(self))
                               /\ WF_vars(spin_trylock(self))
                               /\ WF_vars(spin_unlock(self))

\* END TRANSLATION
=============================================================================
