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
			 active_mm	|-> IF t \in PROCS THEN "init_mm" ELSE "null"]];

	\* mm structures available
	mm	= [m \in MMS \cup {"init_mm"} |->
			[mm_users	|-> 0,
			 mm_count	|-> IF m = "init_mm"
						THEN Cardinality(PROCS) + 1	\* idle tasks + 1
						ELSE 0]];

	\* cpu a thread is running on (initially only the idle tasks run)
	cpu	= [t \in TASKS \cup PROCS |-> IF t \in PROCS THEN t ELSE "none"];

	\* interrupts on by default
	interrupts = [p \in PROCS |-> "on"];

	\* rq->prev_mm
	prev_mm	= [p \in PROCS |-> "null"];

	\* free mm structures
	freemms	= MMS;

	\* scheduling
	runqueue = {};

define {
	task_struct ==
		[mm:		MMS \cup {"null"},
		 active_mm:	MMS \cup {"null", "init_mm"}]

	mm_struct ==
		[mm_users:	Nat,
		 mm_count:	Nat]

	Running(t) == cpu[t] # "none"

	TypeInv	== /\ task \in [TASKS \cup PROCS -> task_struct]
		   /\ mm \in [MMS \cup {"init_mm"} -> mm_struct]
		   /\ prev_mm \in [PROCS -> MMS \cup {"null", "init_mm"}]
		   /\ runqueue \subseteq TASKS
		   /\ cpu \in [TASKS \cup PROCS -> PROCS \cup {"none"}]

	\* Scheduler invariant
	SchedInv == /\ \A t \in runqueue : ~Running(t)
		    /\ \A t1, t2 \in TASKS \cup PROCS :
			t1 # t2 /\ Running(t1) => cpu[t1] # cpu[t2]

	\* mm structure invariant
	MMInv	== /\ \A m \in MMS : mm[m].mm_users = 0 =>
			(\A t \in TASKS \cup PROCS : task[t].mm # m)
		   /\ \A m \in MMS : mm[m].mm_count = 0 =>
			(\A t \in TASKS \cup PROCS : task[t].active_mm # m)
		   /\ \A m \in MMS : mm[m].mm_users > 0 => mm[m].mm_count > 0
		   /\ \A m \in freemms : mm[m].mm_count = 0
		   /\ mm["init_mm"].mm_count > 0

	\* Symmetry optimisations
	Perms	== Permutations(PROCS) \cup Permutations(TASKS) \cup Permutations(MMS)
}

macro sleep(t) {
	\* wait for the thread to be scheduled on a CPU
	await cpu[t] # "none";
}

macro local_irq_disable() {
	interrupts[cpu[self]] := "off";
}

macro local_irq_enable() {
	interrupts[cpu[self]] := "on";
}

macro mm_init(m) {
	mm[m].mm_users := 1 || mm[m].mm_count := 1;
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
	if (mm[_mm].mm_count = 0) {
		freemms := freemms \cup {_mm};
		return;
	} else {
		return;
	}
}

procedure mmput(_mm)
{
mmp1:	mm[_mm].mm_users := mm[_mm].mm_users - 1;
	if (mm[_mm].mm_users = 0) {
		call mmdrop(_mm);
		return;
	} else {
		return;
	}
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
	} else {
		call mmdrop(active_mm);
		return;
	}
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

\* 'prev' argument omitted as it is not used in this model
procedure finish_task_switch()
{
fts1:	\* wait for the current thread to be rescheduled
	sleep(self);

	if (prev_mm[cpu[self]] # "null")
		call mmdrop(prev_mm[cpu[self]]);
fts2:	prev_mm[cpu[self]] := "null";
	local_irq_enable();
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
		prev_mm[cpu[self]] := oldmm;
	};

switch_to:
	\* cpu[prev] will be updated when scheduled in again
	cpu[next] := cpu[prev] || cpu[prev] := "none";
	\* move prev to the runqueue unless idle or exited
	if (pc[prev] # "Done" /\ prev \notin PROCS)
		runqueue := runqueue \cup {prev};

	call finish_task_switch();
	return;
}

procedure schedule()
{
sch1:	\* pick a thread in the runqueue or idle
	with (n \in IF runqueue # {} THEN runqueue ELSE {cpu[self]}) {
		\* prev = next can only happen for idle in this model
		if (self # n) {
			runqueue := runqueue \ {n};
			call context_switch(self, n);
			return;
		} else {
			local_irq_enable();
			return;
		}
	};
}

procedure interrupt()
{
handle_irq:
	\* interrupt disabling usually done by the hardware
	local_irq_disable();
	\* tail-call; finish_task_switch() re-enables interrupts
	call schedule();
	return;
}

process (thread \in TASKS)
{
thread_init:
	\* add thread to runqueue and wait to be scheduled
	runqueue := runqueue \cup {self};
	\* schedule_tail()
	\* no need to disable interrupts since the thread isn't assigned a CPU yet
	call finish_task_switch();

thread_start:
	while (TRUE) {
		either {
			\* replace the current mm
			with (m \in freemms) {
				freemms := freemms \ {m};
				mm_init(m);
				call exec_mmap(m);
			}
		} or {
			call exit_mm();
t1:			goto thread_end;
		} or {
			\* do something else (paired mmget/mmput)
			if (task[self].mm # "null") {
				mmget(task[self].mm);
				call mmput(task[self].mm);
			}
		}
	};

thread_end:
	skip;
}

process (idle \in PROCS)
{
idle_start:
	while (TRUE)
		sleep(self);
}
} *)
------------------------------------------------------------------------------
\* BEGIN TRANSLATION
\* Label context_switch of procedure context_switch at line 164 col 9 changed to context_switch_
\* Procedure variable _mm of procedure exit_mm at line 136 col 18 changed to _mm_
\* Parameter _mm of procedure mmdrop at line 97 col 18 changed to _mm_m
\* Parameter _mm of procedure mmput at line 108 col 17 changed to _mm_mm
CONSTANT defaultInitValue
VARIABLES task, mm, cpu, interrupts, prev_mm, freemms, runqueue, pc, stack

(* define statement *)
task_struct ==
        [mm:            MMS \cup {"null"},
         active_mm:     MMS \cup {"null", "init_mm"}]

mm_struct ==
        [mm_users:      Nat,
         mm_count:      Nat]

Running(t) == cpu[t] # "none"

TypeInv == /\ task \in [TASKS \cup PROCS -> task_struct]
           /\ mm \in [MMS \cup {"init_mm"} -> mm_struct]
           /\ prev_mm \in [PROCS -> MMS \cup {"null", "init_mm"}]
           /\ runqueue \subseteq TASKS
           /\ cpu \in [TASKS \cup PROCS -> PROCS \cup {"none"}]


SchedInv == /\ \A t \in runqueue : ~Running(t)
            /\ \A t1, t2 \in TASKS \cup PROCS :
                t1 # t2 /\ Running(t1) => cpu[t1] # cpu[t2]


MMInv   == /\ \A m \in MMS : mm[m].mm_users = 0 =>
                (\A t \in TASKS \cup PROCS : task[t].mm # m)
           /\ \A m \in MMS : mm[m].mm_count = 0 =>
                (\A t \in TASKS \cup PROCS : task[t].active_mm # m)
           /\ \A m \in MMS : mm[m].mm_users > 0 => mm[m].mm_count > 0
           /\ \A m \in freemms : mm[m].mm_count = 0
           /\ mm["init_mm"].mm_count > 0


Perms   == Permutations(PROCS) \cup Permutations(TASKS) \cup Permutations(MMS)

VARIABLES _mm_m, _mm_mm, _mm, old_mm, active_mm, _mm_, prev, next, oldmm

proc_vars == << task, mm, cpu, interrupts, prev_mm, freemms, runqueue, 
           _mm_m, _mm_mm, _mm, old_mm, active_mm, _mm_, prev, next, oldmm >>

vars == << proc_vars, pc, stack >>

ProcSet == (TASKS) \cup (PROCS)

Init == (* Global variables *)
        /\ task = [t \in TASKS \cup PROCS |->
                        [mm             |-> "null",
                         active_mm      |-> IF t \in PROCS THEN "init_mm" ELSE "null"]]
        /\ mm = [m \in MMS \cup {"init_mm"} |->
                      [mm_users       |-> 0,
                       mm_count       |-> IF m = "init_mm"
                                              THEN Cardinality(PROCS) + 1
                                              ELSE 0]]
        /\ cpu = [t \in TASKS \cup PROCS |-> IF t \in PROCS THEN t ELSE "none"]
        /\ interrupts = [p \in PROCS |-> "on"]
        /\ prev_mm = [p \in PROCS |-> "null"]
        /\ freemms = MMS
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
        /\ pc = [self \in ProcSet |-> CASE self \in TASKS -> "thread_init"
                                        [] self \in PROCS -> "idle_start"]

mmd1(self) == /\ pc[self] = "mmd1"
              /\ mm' = [mm EXCEPT ![_mm_m[self]].mm_count = mm[_mm_m[self]].mm_count - 1]
              /\ IF mm'[_mm_m[self]].mm_count = 0
                    THEN /\ freemms' = (freemms \cup {_mm_m[self]})
                         /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                         /\ _mm_m' = [_mm_m EXCEPT ![self] = Head(stack[self])._mm_m]
                         /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                    ELSE /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                         /\ _mm_m' = [_mm_m EXCEPT ![self] = Head(stack[self])._mm_m]
                         /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                         /\ UNCHANGED freemms
              /\ UNCHANGED << task, cpu, interrupts, prev_mm, runqueue, _mm_mm, 
                              _mm, old_mm, active_mm, _mm_, prev, next, oldmm >>

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
                         /\ UNCHANGED _mm_mm
                    ELSE /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                         /\ _mm_mm' = [_mm_mm EXCEPT ![self] = Head(stack[self])._mm_mm]
                         /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                         /\ _mm_m' = _mm_m
              /\ UNCHANGED << task, cpu, interrupts, prev_mm, freemms, 
                              runqueue, _mm, old_mm, active_mm, _mm_, prev, 
                              next, oldmm >>

mmput(self) == mmp1(self)

emap1(self) == /\ pc[self] = "emap1"
               /\ old_mm' = [old_mm EXCEPT ![self] = task[self].mm]
               /\ active_mm' = [active_mm EXCEPT ![self] = task[self].active_mm]
               /\ task' = [task EXCEPT ![self].mm = _mm[self],
                                       ![self].active_mm = _mm[self]]
               /\ pc' = [pc EXCEPT ![self] = "emap2"]
               /\ UNCHANGED << mm, cpu, interrupts, prev_mm, freemms, runqueue, 
                               stack, _mm_m, _mm_mm, _mm, _mm_, prev, next, 
                               oldmm >>

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
                          /\ _mm_m' = _mm_m
                     ELSE /\ /\ _mm_m' = [_mm_m EXCEPT ![self] = active_mm[self]]
                             /\ active_mm' = [active_mm EXCEPT ![self] = Head(stack[self]).active_mm]
                             /\ old_mm' = [old_mm EXCEPT ![self] = Head(stack[self]).old_mm]
                             /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "mmdrop",
                                                                      pc        |->  Head(stack[self]).pc,
                                                                      _mm_m     |->  _mm_m[self] ] >>
                                                                  \o Tail(stack[self])]
                          /\ pc' = [pc EXCEPT ![self] = "mmd1"]
                          /\ UNCHANGED _mm_mm
               /\ UNCHANGED << task, mm, cpu, interrupts, prev_mm, freemms, 
                               runqueue, _mm, _mm_, prev, next, oldmm >>

exec_mmap(self) == emap1(self) \/ emap2(self)

exm1(self) == /\ pc[self] = "exm1"
              /\ _mm_' = [_mm_ EXCEPT ![self] = task[self].mm]
              /\ pc' = [pc EXCEPT ![self] = "exm2"]
              /\ UNCHANGED << task, mm, cpu, interrupts, prev_mm, freemms, 
                              runqueue, stack, _mm_m, _mm_mm, _mm, old_mm, 
                              active_mm, prev, next, oldmm >>

exm2(self) == /\ pc[self] = "exm2"
              /\ IF _mm_[self] = "null"
                    THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                         /\ _mm_' = [_mm_ EXCEPT ![self] = Head(stack[self])._mm_]
                         /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "exm3"]
                         /\ UNCHANGED << stack, _mm_ >>
              /\ UNCHANGED << task, mm, cpu, interrupts, prev_mm, freemms, 
                              runqueue, _mm_m, _mm_mm, _mm, old_mm, active_mm, 
                              prev, next, oldmm >>

exm3(self) == /\ pc[self] = "exm3"
              /\ mm' = [mm EXCEPT ![_mm_[self]].mm_count = mm[_mm_[self]].mm_count + 1]
              /\ pc' = [pc EXCEPT ![self] = "exm4"]
              /\ UNCHANGED << task, cpu, interrupts, prev_mm, freemms, 
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
              /\ UNCHANGED << mm, cpu, interrupts, prev_mm, freemms, runqueue, 
                              _mm_m, _mm, old_mm, active_mm, prev, next, oldmm >>

exit_mm(self) == exm1(self) \/ exm2(self) \/ exm3(self) \/ exm4(self)

fts1(self) == /\ pc[self] = "fts1"
              /\ cpu[self] # "none"
              /\ IF prev_mm[cpu[self]] # "null"
                    THEN /\ /\ _mm_m' = [_mm_m EXCEPT ![self] = prev_mm[cpu[self]]]
                            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "mmdrop",
                                                                     pc        |->  "fts2",
                                                                     _mm_m     |->  _mm_m[self] ] >>
                                                                 \o stack[self]]
                         /\ pc' = [pc EXCEPT ![self] = "mmd1"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "fts2"]
                         /\ UNCHANGED << stack, _mm_m >>
              /\ UNCHANGED << task, mm, cpu, interrupts, prev_mm, freemms, 
                              runqueue, _mm_mm, _mm, old_mm, active_mm, _mm_, 
                              prev, next, oldmm >>

fts2(self) == /\ pc[self] = "fts2"
              /\ prev_mm' = [prev_mm EXCEPT ![cpu[self]] = "null"]
              /\ interrupts' = [interrupts EXCEPT ![cpu[self]] = "on"]
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << task, mm, cpu, freemms, runqueue, _mm_m, _mm_mm, 
                              _mm, old_mm, active_mm, _mm_, prev, next, oldmm >>

finish_task_switch(self) == fts1(self) \/ fts2(self)

context_switch_(self) == /\ pc[self] = "context_switch_"
                         /\ oldmm' = [oldmm EXCEPT ![self] = task[prev[self]].active_mm]
                         /\ Assert(oldmm'[self] # "null", 
                                   "Failure of assertion at line 165, column 9.")
                         /\ IF task[next[self]].mm = "null"
                               THEN /\ task' = [task EXCEPT ![next[self]].active_mm = oldmm'[self]]
                                    /\ mm' = [mm EXCEPT ![oldmm'[self]].mm_count = mm[oldmm'[self]].mm_count + 1]
                               ELSE /\ TRUE
                                    /\ UNCHANGED << task, mm >>
                         /\ pc' = [pc EXCEPT ![self] = "cs1"]
                         /\ UNCHANGED << cpu, interrupts, prev_mm, freemms, 
                                         runqueue, stack, _mm_m, _mm_mm, _mm, 
                                         old_mm, active_mm, _mm_, prev, next >>

cs1(self) == /\ pc[self] = "cs1"
             /\ IF task[prev[self]].mm = "null"
                   THEN /\ task' = [task EXCEPT ![prev[self]].active_mm = "null"]
                        /\ prev_mm' = [prev_mm EXCEPT ![cpu[self]] = oldmm[self]]
                   ELSE /\ TRUE
                        /\ UNCHANGED << task, prev_mm >>
             /\ pc' = [pc EXCEPT ![self] = "switch_to"]
             /\ UNCHANGED << mm, cpu, interrupts, freemms, runqueue, stack, 
                             _mm_m, _mm_mm, _mm, old_mm, active_mm, _mm_, prev, 
                             next, oldmm >>

switch_to(self) == /\ pc[self] = "switch_to"
                   /\ cpu' = [cpu EXCEPT ![next[self]] = cpu[prev[self]],
                                         ![prev[self]] = "none"]
                   /\ IF pc[prev[self]] # "Done" /\ prev[self] \notin PROCS
                         THEN /\ runqueue' = (runqueue \cup {prev[self]})
                         ELSE /\ TRUE
                              /\ UNCHANGED runqueue
                   /\ /\ oldmm' = [oldmm EXCEPT ![self] = Head(stack[self]).oldmm]
                      /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "finish_task_switch",
                                                               pc        |->  Head(stack[self]).pc ] >>
                                                           \o Tail(stack[self])]
                   /\ pc' = [pc EXCEPT ![self] = "fts1"]
                   /\ UNCHANGED << task, mm, interrupts, prev_mm, freemms, 
                                   _mm_m, _mm_mm, _mm, old_mm, active_mm, _mm_, 
                                   prev, next >>

context_switch(self) == context_switch_(self) \/ cs1(self)
                           \/ switch_to(self)

sch1(self) == /\ pc[self] = "sch1"
              /\ \E n \in IF runqueue # {} THEN runqueue ELSE {cpu[self]}:
                   IF self # n
                      THEN /\ runqueue' = runqueue \ {n}
                           /\ /\ next' = [next EXCEPT ![self] = n]
                              /\ prev' = [prev EXCEPT ![self] = self]
                              /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "context_switch",
                                                                       pc        |->  Head(stack[self]).pc,
                                                                       oldmm     |->  oldmm[self],
                                                                       prev      |->  prev[self],
                                                                       next      |->  next[self] ] >>
                                                                   \o Tail(stack[self])]
                           /\ oldmm' = [oldmm EXCEPT ![self] = defaultInitValue]
                           /\ pc' = [pc EXCEPT ![self] = "context_switch_"]
                           /\ UNCHANGED interrupts
                      ELSE /\ interrupts' = [interrupts EXCEPT ![cpu[self]] = "on"]
                           /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                           /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                           /\ UNCHANGED << runqueue, prev, next, oldmm >>
              /\ UNCHANGED << task, mm, cpu, prev_mm, freemms, _mm_m, _mm_mm, 
                              _mm, old_mm, active_mm, _mm_ >>

schedule(self) == sch1(self)

handle_irq(self) == /\ pc[self] = "handle_irq"
                    /\ interrupts' = [interrupts EXCEPT ![cpu[self]] = "off"]
                    /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "schedule",
                                                             pc        |->  Head(stack[self]).pc ] >>
                                                         \o Tail(stack[self])]
                    /\ pc' = [pc EXCEPT ![self] = "sch1"]
                    /\ UNCHANGED << task, mm, cpu, prev_mm, freemms, runqueue, 
                                    _mm_m, _mm_mm, _mm, old_mm, active_mm, 
                                    _mm_, prev, next, oldmm >>

interrupt(self) == handle_irq(self)

thread_init(self) == /\ pc[self] = "thread_init"
                     /\ runqueue' = (runqueue \cup {self})
                     /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "finish_task_switch",
                                                              pc        |->  "thread_start" ] >>
                                                          \o stack[self]]
                     /\ pc' = [pc EXCEPT ![self] = "fts1"]
                     /\ UNCHANGED << task, mm, cpu, interrupts, prev_mm, 
                                     freemms, _mm_m, _mm_mm, _mm, old_mm, 
                                     active_mm, _mm_, prev, next, oldmm >>

thread_start(self) == /\ pc[self] = "thread_start"
                      /\ \/ /\ \E m \in freemms:
                                 /\ freemms' = freemms \ {m}
                                 /\ mm' = [mm EXCEPT ![m].mm_users = 1,
                                                     ![m].mm_count = 1]
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
                            /\ UNCHANGED <<_mm_mm, _mm_>>
                         \/ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "exit_mm",
                                                                     pc        |->  "t1",
                                                                     _mm_      |->  _mm_[self] ] >>
                                                                 \o stack[self]]
                            /\ _mm_' = [_mm_ EXCEPT ![self] = defaultInitValue]
                            /\ pc' = [pc EXCEPT ![self] = "exm1"]
                            /\ UNCHANGED <<mm, freemms, _mm_mm, _mm, old_mm, active_mm>>
                         \/ /\ IF task[self].mm # "null"
                                  THEN /\ mm' = [mm EXCEPT ![(task[self].mm)].mm_users = mm[(task[self].mm)].mm_users + 1]
                                       /\ /\ _mm_mm' = [_mm_mm EXCEPT ![self] = task[self].mm]
                                          /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "mmput",
                                                                                   pc        |->  "thread_start",
                                                                                   _mm_mm    |->  _mm_mm[self] ] >>
                                                                               \o stack[self]]
                                       /\ pc' = [pc EXCEPT ![self] = "mmp1"]
                                  ELSE /\ pc' = [pc EXCEPT ![self] = "thread_start"]
                                       /\ UNCHANGED << mm, stack, _mm_mm >>
                            /\ UNCHANGED <<freemms, _mm, old_mm, active_mm, _mm_>>
                      /\ UNCHANGED << task, cpu, interrupts, prev_mm, runqueue, 
                                      _mm_m, prev, next, oldmm >>

t1(self) == /\ pc[self] = "t1"
            /\ pc' = [pc EXCEPT ![self] = "thread_end"]
            /\ UNCHANGED << task, mm, cpu, interrupts, prev_mm, freemms, 
                            runqueue, stack, _mm_m, _mm_mm, _mm, old_mm, 
                            active_mm, _mm_, prev, next, oldmm >>

thread_end(self) == /\ pc[self] = "thread_end"
                    /\ TRUE
                    /\ pc' = [pc EXCEPT ![self] = "Done"]
                    /\ UNCHANGED << task, mm, cpu, interrupts, prev_mm, 
                                    freemms, runqueue, stack, _mm_m, _mm_mm, 
                                    _mm, old_mm, active_mm, _mm_, prev, next, 
                                    oldmm >>

thread(self) == thread_init(self) \/ thread_start(self) \/ t1(self)
                   \/ thread_end(self)

idle_start(self) == /\ pc[self] = "idle_start"
                    /\ cpu[self] # "none"
                    /\ pc' = [pc EXCEPT ![self] = "idle_start"]
                    /\ UNCHANGED << task, mm, cpu, interrupts, prev_mm, 
                                    freemms, runqueue, stack, _mm_m, _mm_mm, 
                                    _mm, old_mm, active_mm, _mm_, prev, next, 
                                    oldmm >>

idle(self) == idle_start(self)

Next == (\E self \in ProcSet:  \/ mmdrop(self) \/ mmput(self)
                               \/ exec_mmap(self) \/ exit_mm(self)
                               \/ finish_task_switch(self)
                               \/ context_switch(self) \/ schedule(self)
                               \/ interrupt(self))
           \/ (\E self \in TASKS: thread(self))
           \/ (\E self \in PROCS: idle(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION
------------------------------------------------------------------------------

Interrupt(self) ==
	\* only interrupt running tasks with interrupts enabled
	/\ Running(self)
	/\ interrupts[cpu[self]] = "on"
	\* non-reentrant handler
	/\ pc[self] # "handle_irq"
	\* IRQ handler call; save the return pc on the stack
	/\ stack' = [stack EXCEPT ![self] = << [procedure	|->  "interrupt",
						pc	|->  pc[self]] >>
						\o stack[self]]
	/\ pc' = [pc EXCEPT ![self] = "handle_irq"]
	/\ UNCHANGED proc_vars

PreemptNext == (\E self \in ProcSet : Interrupt(self)) \/ Next

PreemptSpec == Init /\ [][PreemptNext]_vars
==============================================================================
