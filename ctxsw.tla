---------------------------------- MODULE ctxsw -----------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS PROCS,	\* CPUs
	  TASKS,	\* task structures
	  MMS		\* available mm structures

(* --algorithm ctxsw {
variables
	\* PROCS needed to account for the per-CPU idle tasks
	task	= [t \in TASKS \cup PROCS |->
			[mm		|-> "null",
			 active_mm	|-> "init_mm"]];
	\* current CPU task, initially idle
	current	= [p \in PROCS |-> p];
	\* mm structures available
	mm	= [m \in MMS \cup {"init_mm"} |->
			[mm_users	|-> 0,
			 mm_count	|-> IF m = "init_mm"
						THEN Cardinality(PROCS) + 1	\* idle tasks + 1
						ELSE 1]];
	\* rq->prev_mm
	prev_mm	= [p \in PROCS |-> "null"];
	\* free mm structures
	freemms	= MMS;

	\* scheduling
	running	= TASKS;
	runqueue = {};

define {
	TypeInv	== /\ task \in [TASKS \cup PROCS ->
				[mm:		MMS \cup {"null"},
				 active_mm:	MMS \cup {"null", "init_mm"}]]
		   /\ current \in [PROCS -> TASKS \cup PROCS]
		   /\ mm \in [MMS \cup {"init_mm"} ->
				[mm_users:	Nat,
				 mm_count:	Nat]]
		   /\ prev_mm \in [PROCS -> MMS \cup {"null", "init_mm"}]
		   /\ running \subseteq TASKS
		   /\ runqueue \subseteq TASKS

	\* Scheduler invariant
	SchedInv == running \cap runqueue = {}

	\* mm structure invariant
	MMInv	== /\ \A m \in MMS : mm[m].mm_users = 0 =>
			(\A t \in TASKS \cup PROCS : task[t].mm # m)
		   /\ \A m \in MMS : mm[m].mm_count = 0 =>
			(\A t \in TASKS \cup PROCS : task[t].active_mm # m)
		   /\ \A m \in MMS : mm[m].mm_users > 0 => mm[m].mm_count > 0
		   /\ mm["init_mm"].mm_count > 0

	\* Symmetry optimisations
	Perms	== Permutations(PROCS) \cup Permutations(TASKS) \cup Permutations(MMS)
}

macro mmgrab(m) {
	mm[m].mm_count := mm[m].mm_count + 1;
}

macro mmget(m) {
	mm[m].mm_users := mm[m].mm_users + 1;
}

procedure mmdrop(_mm)
{
mmd1:	mm[_mm].mm_count := mm[_mm].mm_count - 1;
	return;
}

procedure mmput(_mm)
{
mmp1:	mm[_mm].mm_users := mm[_mm].mm_users - 1;
	if (mm[_mm].mm_users = 0)
		call mmdrop(_mm);
	return;
}

procedure exec_mmap(_mm)
	variables old_mm, active_mm;
{
emap1:	old_mm := task[self].mm;
	active_mm := task[self].active_mm;
	task[self].mm := _mm || task[self].active_mm := _mm;

emap2:	if (old_mm # "null") {
		call mmput(old_mm);
		return;
	};
emap3:	call mmdrop(active_mm);
	return;
}

procedure exit_mm()
	variable _mm;
{
exm1:	_mm := task[self].mm;
exm2:	if (_mm = "null")
		return;
exm3:	mmgrab(_mm);
exm4:	task[self].mm := "null";
	call mmput(_mm);
	return;
}

procedure context_switch(prev, next)
	variables oldmm;
{
context_switch:
	oldmm := task[prev].active_mm;
	assert oldmm # "null";
	if (task[next].mm = "null") {
		task[next].active_mm := oldmm;
		mmgrab(oldmm);
	};

cs1:	if (task[prev].mm = "null") {
		task[prev].active_mm := "null";
		prev_mm[self] := oldmm;
	};

switch_to:
	\* move prev to the runqueue unless idle or exited
	if (pc[prev] # "Done")
		runqueue := runqueue \cup ({prev} \ {self});
	current[self] := next;

finish_task_switch:
	if (prev_mm[self] # "null")
		call mmdrop(prev_mm[self]);
cs2:	prev_mm[self] := "null";

ret_from_ctxsw:
	\* resume the current thread unless idle
	running := running \cup ({current[self]} \ {self});
	return;
}

process (thread \in running)
{
thread_init:
	\* create some user threads
	with (m \in MMS \cup {"null"})
		if (m # "null") {
			task[self].mm := m || task[self].active_mm := m;
			freemms := freemms \ {m};
		};

	if (task[self].mm # "null")
		mmget(task[self].mm);

	\* suspended until scheduled
	running := running \ {self};
	runqueue := runqueue \cup {self};

thread_start:
	while (TRUE) {
		either {
			\* replace the current mm
			with (m \in freemms) {
				freemms := freemms \ {m};
				mmget(m);
				call exec_mmap(m);
			}
		} or {
			call exit_mm();
t1:			goto thread_end;
		} or {
			\* do something else (paired mmget/mmput)
			if (task[self].mm # "null") {
				mmget(task[self].mm);
t2:				call mmput(task[self].mm);
			}
		}
	};

thread_end:
	skip;
}

process (sched \in PROCS)
{
sched_start:
	\* wait for all the threads to have initialised
	await running = {};

schedule:
	while (TRUE) {
		\* suspend the current thread
		running := running \ {current[self]};
		\* pick a thread in the runqueue or idle
		with (n \in runqueue \cup {self}) {
			\* prev = next can only happen for idle in this model
			if (current[self] # n) {
				runqueue := runqueue \ {n};
				call context_switch(current[self], n);
			}
		}
	}
}

} *)
\* BEGIN TRANSLATION
\* Label context_switch of procedure context_switch at line 111 col 9 changed to context_switch_
\* Procedure variable _mm of procedure exit_mm at line 96 col 18 changed to _mm_
\* Parameter _mm of procedure mmdrop at line 66 col 18 changed to _mm_m
\* Parameter _mm of procedure mmput at line 72 col 17 changed to _mm_mm
CONSTANT defaultInitValue
VARIABLES task, current, mm, prev_mm, freemms, running, runqueue, pc, stack

(* define statement *)
TypeInv == /\ task \in [TASKS \cup PROCS ->
                        [mm:            MMS \cup {"null"},
                         active_mm:     MMS \cup {"null", "init_mm"}]]
           /\ current \in [PROCS -> TASKS \cup PROCS]
           /\ mm \in [MMS \cup {"init_mm"} ->
                        [mm_users:      Nat,
                         mm_count:      Nat]]
           /\ prev_mm \in [PROCS -> MMS \cup {"null", "init_mm"}]
           /\ running \subseteq TASKS
           /\ runqueue \subseteq TASKS


SchedInv == running \cap runqueue = {}


MMInv   == /\ \A m \in MMS : mm[m].mm_users = 0 =>
                (\A t \in TASKS \cup PROCS : task[t].mm # m)
           /\ \A m \in MMS : mm[m].mm_count = 0 =>
                (\A t \in TASKS \cup PROCS : task[t].active_mm # m)
           /\ \A m \in MMS : mm[m].mm_users > 0 => mm[m].mm_count > 0
           /\ mm["init_mm"].mm_count > 0


Perms   == Permutations(PROCS) \cup Permutations(TASKS) \cup Permutations(MMS)

VARIABLES _mm_m, _mm_mm, _mm, old_mm, active_mm, _mm_, prev, next, oldmm

vars == << task, current, mm, prev_mm, freemms, running, runqueue, pc, stack, 
           _mm_m, _mm_mm, _mm, old_mm, active_mm, _mm_, prev, next, oldmm >>

ProcSet == (running) \cup (PROCS)

Init == (* Global variables *)
        /\ task = [t \in TASKS \cup PROCS |->
                        [mm             |-> "null",
                         active_mm      |-> "init_mm"]]
        /\ current = [p \in PROCS |-> p]
        /\ mm = [m \in MMS \cup {"init_mm"} |->
                      [mm_users       |-> 0,
                       mm_count       |-> IF m = "init_mm"
                                              THEN Cardinality(PROCS) + 1
                                              ELSE 1]]
        /\ prev_mm = [p \in PROCS |-> "null"]
        /\ freemms = MMS
        /\ running = TASKS
        /\ runqueue = {}
        (* Procedure mmdrop *)
        /\ _mm_m = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure mmput *)
        /\ _mm_mm = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure exec_mmap *)
        /\ _mm = [ self \in ProcSet |-> defaultInitValue]
        /\ old_mm = [ self \in ProcSet |-> defaultInitValue]
        /\ active_mm = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure exit_mm *)
        /\ _mm_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure context_switch *)
        /\ prev = [ self \in ProcSet |-> defaultInitValue]
        /\ next = [ self \in ProcSet |-> defaultInitValue]
        /\ oldmm = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in running -> "thread_init"
                                        [] self \in PROCS -> "sched_start"]

mmd1(self) == /\ pc[self] = "mmd1"
              /\ mm' = [mm EXCEPT ![_mm_m[self]].mm_count = mm[_mm_m[self]].mm_count - 1]
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ _mm_m' = [_mm_m EXCEPT ![self] = Head(stack[self])._mm_m]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << task, current, prev_mm, freemms, running, 
                              runqueue, _mm_mm, _mm, old_mm, active_mm, _mm_, 
                              prev, next, oldmm >>

mmdrop(self) == mmd1(self)

mmp1(self) == /\ pc[self] = "mmp1"
              /\ mm' = [mm EXCEPT ![_mm_mm[self]].mm_users = mm[_mm_mm[self]].mm_users - 1]
              /\ IF mm'[_mm_mm[self]].mm_users = 0
                    THEN /\ /\ _mm_m' = [_mm_m EXCEPT ![self] = _mm_mm[self]]
                            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "mmdrop",
                                                                     pc        |->  Head(stack[self]).pc,
                                                                     _mm_m     |->  _mm_m[self] ] >>
                                                                 \o Tail(stack[self])]
                         /\ pc' = [pc EXCEPT ![self] = "mmd1"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "Error"]
                         /\ UNCHANGED << stack, _mm_m >>
              /\ UNCHANGED << task, current, prev_mm, freemms, running, 
                              runqueue, _mm_mm, _mm, old_mm, active_mm, _mm_, 
                              prev, next, oldmm >>

mmput(self) == mmp1(self)

emap1(self) == /\ pc[self] = "emap1"
               /\ old_mm' = [old_mm EXCEPT ![self] = task[self].mm]
               /\ active_mm' = [active_mm EXCEPT ![self] = task[self].active_mm]
               /\ task' = [task EXCEPT ![self].mm = _mm[self],
                                       ![self].active_mm = _mm[self]]
               /\ pc' = [pc EXCEPT ![self] = "emap2"]
               /\ UNCHANGED << current, mm, prev_mm, freemms, running, 
                               runqueue, stack, _mm_m, _mm_mm, _mm, _mm_, prev, 
                               next, oldmm >>

emap2(self) == /\ pc[self] = "emap2"
               /\ IF old_mm[self] # "null"
                     THEN /\ /\ _mm_mm' = [_mm_mm EXCEPT ![self] = old_mm[self]]
                             /\ active_mm' = [active_mm EXCEPT ![self] = Head(stack[self]).active_mm]
                             /\ old_mm' = [old_mm EXCEPT ![self] = Head(stack[self]).old_mm]
                             /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "mmput",
                                                                      pc        |->  Head(stack[self]).pc,
                                                                      _mm_mm    |->  _mm_mm[self] ] >>
                                                                  \o Tail(stack[self])]
                          /\ pc' = [pc EXCEPT ![self] = "mmp1"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "emap3"]
                          /\ UNCHANGED << stack, _mm_mm, old_mm, active_mm >>
               /\ UNCHANGED << task, current, mm, prev_mm, freemms, running, 
                               runqueue, _mm_m, _mm, _mm_, prev, next, oldmm >>

emap3(self) == /\ pc[self] = "emap3"
               /\ /\ _mm_m' = [_mm_m EXCEPT ![self] = active_mm[self]]
                  /\ active_mm' = [active_mm EXCEPT ![self] = Head(stack[self]).active_mm]
                  /\ old_mm' = [old_mm EXCEPT ![self] = Head(stack[self]).old_mm]
                  /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "mmdrop",
                                                           pc        |->  Head(stack[self]).pc,
                                                           _mm_m     |->  _mm_m[self] ] >>
                                                       \o Tail(stack[self])]
               /\ pc' = [pc EXCEPT ![self] = "mmd1"]
               /\ UNCHANGED << task, current, mm, prev_mm, freemms, running, 
                               runqueue, _mm_mm, _mm, _mm_, prev, next, oldmm >>

exec_mmap(self) == emap1(self) \/ emap2(self) \/ emap3(self)

exm1(self) == /\ pc[self] = "exm1"
              /\ _mm_' = [_mm_ EXCEPT ![self] = task[self].mm]
              /\ pc' = [pc EXCEPT ![self] = "exm2"]
              /\ UNCHANGED << task, current, mm, prev_mm, freemms, running, 
                              runqueue, stack, _mm_m, _mm_mm, _mm, old_mm, 
                              active_mm, prev, next, oldmm >>

exm2(self) == /\ pc[self] = "exm2"
              /\ IF _mm_[self] = "null"
                    THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                         /\ _mm_' = [_mm_ EXCEPT ![self] = Head(stack[self])._mm_]
                         /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "exm3"]
                         /\ UNCHANGED << stack, _mm_ >>
              /\ UNCHANGED << task, current, mm, prev_mm, freemms, running, 
                              runqueue, _mm_m, _mm_mm, _mm, old_mm, active_mm, 
                              prev, next, oldmm >>

exm3(self) == /\ pc[self] = "exm3"
              /\ mm' = [mm EXCEPT ![_mm_[self]].mm_count = mm[_mm_[self]].mm_count + 1]
              /\ pc' = [pc EXCEPT ![self] = "exm4"]
              /\ UNCHANGED << task, current, prev_mm, freemms, running, 
                              runqueue, stack, _mm_m, _mm_mm, _mm, old_mm, 
                              active_mm, _mm_, prev, next, oldmm >>

exm4(self) == /\ pc[self] = "exm4"
              /\ task' = [task EXCEPT ![self].mm = "null"]
              /\ /\ _mm_' = [_mm_ EXCEPT ![self] = Head(stack[self])._mm_]
                 /\ _mm_mm' = [_mm_mm EXCEPT ![self] = _mm_[self]]
                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "mmput",
                                                          pc        |->  Head(stack[self]).pc,
                                                          _mm_mm    |->  _mm_mm[self] ] >>
                                                      \o Tail(stack[self])]
              /\ pc' = [pc EXCEPT ![self] = "mmp1"]
              /\ UNCHANGED << current, mm, prev_mm, freemms, running, runqueue, 
                              _mm_m, _mm, old_mm, active_mm, prev, next, oldmm >>

exit_mm(self) == exm1(self) \/ exm2(self) \/ exm3(self) \/ exm4(self)

context_switch_(self) == /\ pc[self] = "context_switch_"
                         /\ oldmm' = [oldmm EXCEPT ![self] = task[prev[self]].active_mm]
                         /\ Assert(oldmm'[self] # "null", 
                                   "Failure of assertion at line 112, column 9.")
                         /\ IF task[next[self]].mm = "null"
                               THEN /\ task' = [task EXCEPT ![next[self]].active_mm = oldmm'[self]]
                                    /\ mm' = [mm EXCEPT ![oldmm'[self]].mm_count = mm[oldmm'[self]].mm_count + 1]
                               ELSE /\ TRUE
                                    /\ UNCHANGED << task, mm >>
                         /\ pc' = [pc EXCEPT ![self] = "cs1"]
                         /\ UNCHANGED << current, prev_mm, freemms, running, 
                                         runqueue, stack, _mm_m, _mm_mm, _mm, 
                                         old_mm, active_mm, _mm_, prev, next >>

cs1(self) == /\ pc[self] = "cs1"
             /\ IF task[prev[self]].mm = "null"
                   THEN /\ task' = [task EXCEPT ![prev[self]].active_mm = "null"]
                        /\ prev_mm' = [prev_mm EXCEPT ![self] = oldmm[self]]
                   ELSE /\ TRUE
                        /\ UNCHANGED << task, prev_mm >>
             /\ pc' = [pc EXCEPT ![self] = "switch_to"]
             /\ UNCHANGED << current, mm, freemms, running, runqueue, stack, 
                             _mm_m, _mm_mm, _mm, old_mm, active_mm, _mm_, prev, 
                             next, oldmm >>

switch_to(self) == /\ pc[self] = "switch_to"
                   /\ IF pc[prev[self]] # "Done"
                         THEN /\ runqueue' = (runqueue \cup ({prev[self]} \ {self}))
                         ELSE /\ TRUE
                              /\ UNCHANGED runqueue
                   /\ current' = [current EXCEPT ![self] = next[self]]
                   /\ pc' = [pc EXCEPT ![self] = "finish_task_switch"]
                   /\ UNCHANGED << task, mm, prev_mm, freemms, running, stack, 
                                   _mm_m, _mm_mm, _mm, old_mm, active_mm, _mm_, 
                                   prev, next, oldmm >>

finish_task_switch(self) == /\ pc[self] = "finish_task_switch"
                            /\ IF prev_mm[self] # "null"
                                  THEN /\ /\ _mm_m' = [_mm_m EXCEPT ![self] = prev_mm[self]]
                                          /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "mmdrop",
                                                                                   pc        |->  "cs2",
                                                                                   _mm_m     |->  _mm_m[self] ] >>
                                                                               \o stack[self]]
                                       /\ pc' = [pc EXCEPT ![self] = "mmd1"]
                                  ELSE /\ pc' = [pc EXCEPT ![self] = "cs2"]
                                       /\ UNCHANGED << stack, _mm_m >>
                            /\ UNCHANGED << task, current, mm, prev_mm, 
                                            freemms, running, runqueue, _mm_mm, 
                                            _mm, old_mm, active_mm, _mm_, prev, 
                                            next, oldmm >>

cs2(self) == /\ pc[self] = "cs2"
             /\ prev_mm' = [prev_mm EXCEPT ![self] = "null"]
             /\ pc' = [pc EXCEPT ![self] = "ret_from_ctxsw"]
             /\ UNCHANGED << task, current, mm, freemms, running, runqueue, 
                             stack, _mm_m, _mm_mm, _mm, old_mm, active_mm, 
                             _mm_, prev, next, oldmm >>

ret_from_ctxsw(self) == /\ pc[self] = "ret_from_ctxsw"
                        /\ running' = (running \cup ({current[self]} \ {self}))
                        /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ oldmm' = [oldmm EXCEPT ![self] = Head(stack[self]).oldmm]
                        /\ prev' = [prev EXCEPT ![self] = Head(stack[self]).prev]
                        /\ next' = [next EXCEPT ![self] = Head(stack[self]).next]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                        /\ UNCHANGED << task, current, mm, prev_mm, freemms, 
                                        runqueue, _mm_m, _mm_mm, _mm, old_mm, 
                                        active_mm, _mm_ >>

context_switch(self) == context_switch_(self) \/ cs1(self)
                           \/ switch_to(self) \/ finish_task_switch(self)
                           \/ cs2(self) \/ ret_from_ctxsw(self)

thread_init(self) == /\ pc[self] = "thread_init"
                     /\ \E m \in MMS \cup {"null"}:
                          IF m # "null"
                             THEN /\ task' = [task EXCEPT ![self].mm = m,
                                                          ![self].active_mm = m]
                                  /\ freemms' = freemms \ {m}
                             ELSE /\ TRUE
                                  /\ UNCHANGED << task, freemms >>
                     /\ IF task'[self].mm # "null"
                           THEN /\ mm' = [mm EXCEPT ![(task'[self].mm)].mm_users = mm[(task'[self].mm)].mm_users + 1]
                           ELSE /\ TRUE
                                /\ mm' = mm
                     /\ running' = running \ {self}
                     /\ runqueue' = (runqueue \cup {self})
                     /\ pc' = [pc EXCEPT ![self] = "thread_start"]
                     /\ UNCHANGED << current, prev_mm, stack, _mm_m, _mm_mm, 
                                     _mm, old_mm, active_mm, _mm_, prev, next, 
                                     oldmm >>

thread_start(self) == /\ pc[self] = "thread_start"
                      /\ \/ /\ \E m \in freemms:
                                 /\ freemms' = freemms \ {m}
                                 /\ mm' = [mm EXCEPT ![m].mm_users = mm[m].mm_users + 1]
                                 /\ /\ _mm' = [_mm EXCEPT ![self] = m]
                                    /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "exec_mmap",
                                                                             pc        |->  "thread_start",
                                                                             old_mm    |->  old_mm[self],
                                                                             active_mm |->  active_mm[self],
                                                                             _mm       |->  _mm[self] ] >>
                                                                         \o stack[self]]
                                 /\ old_mm' = [old_mm EXCEPT ![self] = defaultInitValue]
                                 /\ active_mm' = [active_mm EXCEPT ![self] = defaultInitValue]
                                 /\ pc' = [pc EXCEPT ![self] = "emap1"]
                            /\ _mm_' = _mm_
                         \/ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "exit_mm",
                                                                     pc        |->  "t1",
                                                                     _mm_      |->  _mm_[self] ] >>
                                                                 \o stack[self]]
                            /\ _mm_' = [_mm_ EXCEPT ![self] = defaultInitValue]
                            /\ pc' = [pc EXCEPT ![self] = "exm1"]
                            /\ UNCHANGED <<mm, freemms, _mm, old_mm, active_mm>>
                         \/ /\ IF task[self].mm # "null"
                                  THEN /\ mm' = [mm EXCEPT ![(task[self].mm)].mm_users = mm[(task[self].mm)].mm_users + 1]
                                       /\ pc' = [pc EXCEPT ![self] = "t2"]
                                  ELSE /\ pc' = [pc EXCEPT ![self] = "thread_start"]
                                       /\ mm' = mm
                            /\ UNCHANGED <<freemms, stack, _mm, old_mm, active_mm, _mm_>>
                      /\ UNCHANGED << task, current, prev_mm, running, 
                                      runqueue, _mm_m, _mm_mm, prev, next, 
                                      oldmm >>

t1(self) == /\ pc[self] = "t1"
            /\ pc' = [pc EXCEPT ![self] = "thread_end"]
            /\ UNCHANGED << task, current, mm, prev_mm, freemms, running, 
                            runqueue, stack, _mm_m, _mm_mm, _mm, old_mm, 
                            active_mm, _mm_, prev, next, oldmm >>

t2(self) == /\ pc[self] = "t2"
            /\ /\ _mm_mm' = [_mm_mm EXCEPT ![self] = task[self].mm]
               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "mmput",
                                                        pc        |->  "thread_start",
                                                        _mm_mm    |->  _mm_mm[self] ] >>
                                                    \o stack[self]]
            /\ pc' = [pc EXCEPT ![self] = "mmp1"]
            /\ UNCHANGED << task, current, mm, prev_mm, freemms, running, 
                            runqueue, _mm_m, _mm, old_mm, active_mm, _mm_, 
                            prev, next, oldmm >>

thread_end(self) == /\ pc[self] = "thread_end"
                    /\ TRUE
                    /\ pc' = [pc EXCEPT ![self] = "Done"]
                    /\ UNCHANGED << task, current, mm, prev_mm, freemms, 
                                    running, runqueue, stack, _mm_m, _mm_mm, 
                                    _mm, old_mm, active_mm, _mm_, prev, next, 
                                    oldmm >>

thread(self) == thread_init(self) \/ thread_start(self) \/ t1(self)
                   \/ t2(self) \/ thread_end(self)

sched_start(self) == /\ pc[self] = "sched_start"
                     /\ running = {}
                     /\ pc' = [pc EXCEPT ![self] = "schedule"]
                     /\ UNCHANGED << task, current, mm, prev_mm, freemms, 
                                     running, runqueue, stack, _mm_m, _mm_mm, 
                                     _mm, old_mm, active_mm, _mm_, prev, next, 
                                     oldmm >>

schedule(self) == /\ pc[self] = "schedule"
                  /\ running' = running \ {current[self]}
                  /\ \E n \in runqueue \cup {self}:
                       IF current[self] # n
                          THEN /\ runqueue' = runqueue \ {n}
                               /\ /\ next' = [next EXCEPT ![self] = n]
                                  /\ prev' = [prev EXCEPT ![self] = current[self]]
                                  /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "context_switch",
                                                                           pc        |->  "schedule",
                                                                           oldmm     |->  oldmm[self],
                                                                           prev      |->  prev[self],
                                                                           next      |->  next[self] ] >>
                                                                       \o stack[self]]
                               /\ oldmm' = [oldmm EXCEPT ![self] = defaultInitValue]
                               /\ pc' = [pc EXCEPT ![self] = "context_switch_"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "schedule"]
                               /\ UNCHANGED << runqueue, stack, prev, next, 
                                               oldmm >>
                  /\ UNCHANGED << task, current, mm, prev_mm, freemms, _mm_m, 
                                  _mm_mm, _mm, old_mm, active_mm, _mm_ >>

sched(self) == sched_start(self) \/ schedule(self)

Next == (\E self \in ProcSet:  \/ mmdrop(self) \/ mmput(self)
                               \/ exec_mmap(self) \/ exit_mm(self)
                               \/ context_switch(self))
           \/ (\E self \in running: thread(self))
           \/ (\E self \in PROCS: sched(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
==============================================================================
