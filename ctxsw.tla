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
			 active_mm	|-> IF t \in PROCS THEN "init_mm" ELSE "null",
			 cpu		|-> IF t \in PROCS THEN t ELSE "none",
			 state		|-> "running"]];

	\* mm structures available
	mm	= [m \in MMS \cup {"init_mm"} |->
			[mm_users	|-> 0,
			 mm_count	|-> IF m = "init_mm"
						THEN Cardinality(PROCS) + 1	\* idle tasks + 1
						ELSE 0]];

	proc_mm	= [p \in PROCS |-> "init_mm"];

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
		 active_mm:	MMS \cup {"null", "init_mm"},
		 cpu:		PROCS \cup {"none"},
		 state:		{"running", "dead"}]

	mm_struct ==
		[mm_users:	Nat,
		 mm_count:	Nat]

	Running(t) == task[t].cpu # "none"

	TypeInv	== /\ task \in [TASKS \cup PROCS -> task_struct]
		   /\ mm \in [MMS \cup {"init_mm"} -> mm_struct]
		   /\ prev_mm \in [PROCS -> MMS \cup {"null", "init_mm"}]
		   /\ runqueue \subseteq TASKS
		   /\ proc_mm \in [PROCS -> MMS \cup {"init_mm"}]

	\* Scheduler invariant
	SchedInv == /\ \A t \in runqueue : ~Running(t)
		    /\ \A t1, t2 \in TASKS \cup PROCS :
			t1 # t2 /\ Running(t1) => task[t1].cpu # task[t2].cpu

	\* mm structure invariant
	MMInv	== /\ \A m \in MMS : mm[m].mm_users = 0 =>
			(\A t \in TASKS \cup PROCS : task[t].mm # m)
		   /\ \A m \in MMS : mm[m].mm_count = 0 =>
			(\A t \in TASKS \cup PROCS : task[t].active_mm # m)
		   /\ \A m \in MMS : mm[m].mm_users > 0 => mm[m].mm_count > 0
		   /\ \A m \in freemms : mm[m].mm_count = 0
		   /\ \A p \in PROCS : proc_mm[p] \notin freemms
		   /\ mm["init_mm"].mm_count > 0

	\* Symmetry optimisations
	Perms	== Permutations(PROCS) \cup Permutations(TASKS) \cup Permutations(MMS)
}

macro local_irq_disable() {
	interrupts[task[self].cpu] := "off";
}

macro local_irq_enable() {
	interrupts[task[self].cpu] := "on";
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

macro switch_mm(m) {
	proc_mm[task[self].cpu] := m;
}

macro switch_to(prev, next) {
	\* task[prev].cpu will be updated when scheduled in again
	task[next].cpu := task[prev].cpu || task[prev].cpu := "none";
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
{
emap1:	with (old_mm = task[self].mm, active_mm = task[self].active_mm) {
		task[self].mm := _mm || task[self].active_mm := _mm;
		switch_mm(_mm);		\* activate_mm()
		if (old_mm # "null") {
			call mmput(old_mm);
			return;
		} else {
			call mmdrop(active_mm);
			return;
		}
	}
}

procedure exit_mm()
{
exm1:	with (m = task[self].mm) {
		if (m = "null") {
			return;
		} else {
			mmgrab(m);
			task[self].mm := "null";
			call mmput(m);
			return;
		}
	}
}

\* 'prev' argument omitted as it is not used in this model
procedure finish_task_switch()
{
fts1:	\* wait for the current thread to be rescheduled
	await Running(self);

	if (prev_mm[task[self].cpu] # "null")
		call mmdrop(prev_mm[task[self].cpu]);
fts2:	prev_mm[task[self].cpu] := "null";
	local_irq_enable();
	return;
}

procedure context_switch(prev, next)
	variables oldmm;
{
cs1:	oldmm := task[prev].active_mm;
	if (task[next].mm = "null") {
		task[next].active_mm := oldmm;
		mmgrab(oldmm);
	} else {
		switch_mm(task[next].mm);
	};

cs2:	if (task[prev].mm = "null") {
		task[prev].active_mm := "null";
		prev_mm[task[self].cpu] := oldmm;
	};

cs3:	switch_to(prev, next);

	\* move prev to the runqueue unless idle or dead
	if (task[prev].state = "running" /\ prev \notin PROCS)
		runqueue := runqueue \cup {prev};

	call finish_task_switch();
	return;
}

procedure schedule()
{
sch1:	\* pick a thread in the runqueue or idle
	with (n \in IF runqueue # {} THEN runqueue ELSE {task[self].cpu}) {
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
	task[self].state := "dead";
}

process (idle \in PROCS)
{
idle_start:
	while (TRUE)
		await Running(self);
}
} *)
------------------------------------------------------------------------------
\* BEGIN TRANSLATION
\* Parameter _mm of procedure mmdrop at line 105 col 18 changed to _mm_
\* Parameter _mm of procedure mmput at line 116 col 17 changed to _mm_m
CONSTANT defaultInitValue
VARIABLES task, mm, proc_mm, interrupts, prev_mm, freemms, runqueue, pc, 
          stack

(* define statement *)
task_struct ==
        [mm:            MMS \cup {"null"},
         active_mm:     MMS \cup {"null", "init_mm"},
         cpu:           PROCS \cup {"none"},
         state:         {"running", "dead"}]

mm_struct ==
        [mm_users:      Nat,
         mm_count:      Nat]

Running(t) == task[t].cpu # "none"

TypeInv == /\ task \in [TASKS \cup PROCS -> task_struct]
           /\ mm \in [MMS \cup {"init_mm"} -> mm_struct]
           /\ prev_mm \in [PROCS -> MMS \cup {"null", "init_mm"}]
           /\ runqueue \subseteq TASKS
           /\ proc_mm \in [PROCS -> MMS \cup {"init_mm"}]


SchedInv == /\ \A t \in runqueue : ~Running(t)
            /\ \A t1, t2 \in TASKS \cup PROCS :
                t1 # t2 /\ Running(t1) => task[t1].cpu # task[t2].cpu


MMInv   == /\ \A m \in MMS : mm[m].mm_users = 0 =>
                (\A t \in TASKS \cup PROCS : task[t].mm # m)
           /\ \A m \in MMS : mm[m].mm_count = 0 =>
                (\A t \in TASKS \cup PROCS : task[t].active_mm # m)
           /\ \A m \in MMS : mm[m].mm_users > 0 => mm[m].mm_count > 0
           /\ \A m \in freemms : mm[m].mm_count = 0
           /\ \A p \in PROCS : proc_mm[p] \notin freemms
           /\ mm["init_mm"].mm_count > 0


Perms   == Permutations(PROCS) \cup Permutations(TASKS) \cup Permutations(MMS)

VARIABLES _mm_, _mm_m, _mm, prev, next, oldmm

proc_vars == << task, mm, proc_mm, interrupts, prev_mm, freemms, runqueue, 
           _mm_, _mm_m, _mm, prev, next, oldmm >>

vars == << proc_vars, pc, stack >>

ProcSet == (TASKS) \cup (PROCS)

Init == (* Global variables *)
        /\ task = [t \in TASKS \cup PROCS |->
                        [mm             |-> "null",
                         active_mm      |-> IF t \in PROCS THEN "init_mm" ELSE "null",
                         cpu            |-> IF t \in PROCS THEN t ELSE "none",
                         state          |-> "running"]]
        /\ mm = [m \in MMS \cup {"init_mm"} |->
                      [mm_users       |-> 0,
                       mm_count       |-> IF m = "init_mm"
                                              THEN Cardinality(PROCS) + 1
                                              ELSE 0]]
        /\ proc_mm = [p \in PROCS |-> "init_mm"]
        /\ interrupts = [p \in PROCS |-> "on"]
        /\ prev_mm = [p \in PROCS |-> "null"]
        /\ freemms = MMS
        /\ runqueue = {}
        (* Procedure mmdrop *)
        /\ _mm_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure mmput *)
        /\ _mm_m = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure exec_mmap *)
        /\ _mm = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure context_switch *)
        /\ prev = [ self \in ProcSet |-> defaultInitValue]
        /\ next = [ self \in ProcSet |-> defaultInitValue]
        /\ oldmm = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in TASKS -> "thread_init"
                                        [] self \in PROCS -> "idle_start"]

mmd1(self) == /\ pc[self] = "mmd1"
              /\ mm' = [mm EXCEPT ![_mm_[self]].mm_count = mm[_mm_[self]].mm_count - 1]
              /\ IF mm'[_mm_[self]].mm_count = 0
                    THEN /\ freemms' = (freemms \cup {_mm_[self]})
                         /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                         /\ _mm_' = [_mm_ EXCEPT ![self] = Head(stack[self])._mm_]
                         /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                    ELSE /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                         /\ _mm_' = [_mm_ EXCEPT ![self] = Head(stack[self])._mm_]
                         /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                         /\ UNCHANGED freemms
              /\ UNCHANGED << task, proc_mm, interrupts, prev_mm, runqueue, 
                              _mm_m, _mm, prev, next, oldmm >>

mmdrop(self) == mmd1(self)

mmp1(self) == /\ pc[self] = "mmp1"
              /\ mm' = [mm EXCEPT ![_mm_m[self]].mm_users = mm[_mm_m[self]].mm_users - 1]
              /\ IF mm'[_mm_m[self]].mm_users = 0
                    THEN /\ /\ _mm_' = [_mm_ EXCEPT ![self] = _mm_m[self]]
                            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "mmdrop",
                                                                     pc        |->  Head(stack[self]).pc,
                                                                     _mm_      |->  _mm_[self] ] >>
                                                                 \o Tail(stack[self])]
                         /\ pc' = [pc EXCEPT ![self] = "mmd1"]
                         /\ _mm_m' = _mm_m
                    ELSE /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                         /\ _mm_m' = [_mm_m EXCEPT ![self] = Head(stack[self])._mm_m]
                         /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                         /\ _mm_' = _mm_
              /\ UNCHANGED << task, proc_mm, interrupts, prev_mm, freemms, 
                              runqueue, _mm, prev, next, oldmm >>

mmput(self) == mmp1(self)

emap1(self) == /\ pc[self] = "emap1"
               /\ LET old_mm == task[self].mm IN
                    LET active_mm == task[self].active_mm IN
                      /\ task' = [task EXCEPT ![self].mm = _mm[self],
                                              ![self].active_mm = _mm[self]]
                      /\ proc_mm' = [proc_mm EXCEPT ![task'[self].cpu] = _mm[self]]
                      /\ IF old_mm # "null"
                            THEN /\ /\ _mm_m' = [_mm_m EXCEPT ![self] = old_mm]
                                    /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "mmput",
                                                                             pc        |->  Head(stack[self]).pc,
                                                                             _mm_m     |->  _mm_m[self] ] >>
                                                                         \o Tail(stack[self])]
                                 /\ pc' = [pc EXCEPT ![self] = "mmp1"]
                                 /\ _mm_' = _mm_
                            ELSE /\ /\ _mm_' = [_mm_ EXCEPT ![self] = active_mm]
                                    /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "mmdrop",
                                                                             pc        |->  Head(stack[self]).pc,
                                                                             _mm_      |->  _mm_[self] ] >>
                                                                         \o Tail(stack[self])]
                                 /\ pc' = [pc EXCEPT ![self] = "mmd1"]
                                 /\ _mm_m' = _mm_m
               /\ UNCHANGED << mm, interrupts, prev_mm, freemms, runqueue, _mm, 
                               prev, next, oldmm >>

exec_mmap(self) == emap1(self)

exm1(self) == /\ pc[self] = "exm1"
              /\ LET m == task[self].mm IN
                   IF m = "null"
                      THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                           /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                           /\ UNCHANGED << task, mm, _mm_m >>
                      ELSE /\ mm' = [mm EXCEPT ![m].mm_count = mm[m].mm_count + 1]
                           /\ task' = [task EXCEPT ![self].mm = "null"]
                           /\ /\ _mm_m' = [_mm_m EXCEPT ![self] = m]
                              /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "mmput",
                                                                       pc        |->  Head(stack[self]).pc,
                                                                       _mm_m     |->  _mm_m[self] ] >>
                                                                   \o Tail(stack[self])]
                           /\ pc' = [pc EXCEPT ![self] = "mmp1"]
              /\ UNCHANGED << proc_mm, interrupts, prev_mm, freemms, runqueue, 
                              _mm_, _mm, prev, next, oldmm >>

exit_mm(self) == exm1(self)

fts1(self) == /\ pc[self] = "fts1"
              /\ Running(self)
              /\ IF prev_mm[task[self].cpu] # "null"
                    THEN /\ /\ _mm_' = [_mm_ EXCEPT ![self] = prev_mm[task[self].cpu]]
                            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "mmdrop",
                                                                     pc        |->  "fts2",
                                                                     _mm_      |->  _mm_[self] ] >>
                                                                 \o stack[self]]
                         /\ pc' = [pc EXCEPT ![self] = "mmd1"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "fts2"]
                         /\ UNCHANGED << stack, _mm_ >>
              /\ UNCHANGED << task, mm, proc_mm, interrupts, prev_mm, freemms, 
                              runqueue, _mm_m, _mm, prev, next, oldmm >>

fts2(self) == /\ pc[self] = "fts2"
              /\ prev_mm' = [prev_mm EXCEPT ![task[self].cpu] = "null"]
              /\ interrupts' = [interrupts EXCEPT ![task[self].cpu] = "on"]
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << task, mm, proc_mm, freemms, runqueue, _mm_, 
                              _mm_m, _mm, prev, next, oldmm >>

finish_task_switch(self) == fts1(self) \/ fts2(self)

cs1(self) == /\ pc[self] = "cs1"
             /\ oldmm' = [oldmm EXCEPT ![self] = task[prev[self]].active_mm]
             /\ IF task[next[self]].mm = "null"
                   THEN /\ task' = [task EXCEPT ![next[self]].active_mm = oldmm'[self]]
                        /\ mm' = [mm EXCEPT ![oldmm'[self]].mm_count = mm[oldmm'[self]].mm_count + 1]
                        /\ UNCHANGED proc_mm
                   ELSE /\ proc_mm' = [proc_mm EXCEPT ![task[self].cpu] = task[next[self]].mm]
                        /\ UNCHANGED << task, mm >>
             /\ pc' = [pc EXCEPT ![self] = "cs2"]
             /\ UNCHANGED << interrupts, prev_mm, freemms, runqueue, stack, 
                             _mm_, _mm_m, _mm, prev, next >>

cs2(self) == /\ pc[self] = "cs2"
             /\ IF task[prev[self]].mm = "null"
                   THEN /\ task' = [task EXCEPT ![prev[self]].active_mm = "null"]
                        /\ prev_mm' = [prev_mm EXCEPT ![task'[self].cpu] = oldmm[self]]
                   ELSE /\ TRUE
                        /\ UNCHANGED << task, prev_mm >>
             /\ pc' = [pc EXCEPT ![self] = "cs3"]
             /\ UNCHANGED << mm, proc_mm, interrupts, freemms, runqueue, stack, 
                             _mm_, _mm_m, _mm, prev, next, oldmm >>

cs3(self) == /\ pc[self] = "cs3"
             /\ task' = [task EXCEPT ![next[self]].cpu = task[prev[self]].cpu,
                                     ![prev[self]].cpu = "none"]
             /\ IF task'[prev[self]].state = "running" /\ prev[self] \notin PROCS
                   THEN /\ runqueue' = (runqueue \cup {prev[self]})
                   ELSE /\ TRUE
                        /\ UNCHANGED runqueue
             /\ /\ oldmm' = [oldmm EXCEPT ![self] = Head(stack[self]).oldmm]
                /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "finish_task_switch",
                                                         pc        |->  Head(stack[self]).pc ] >>
                                                     \o Tail(stack[self])]
             /\ pc' = [pc EXCEPT ![self] = "fts1"]
             /\ UNCHANGED << mm, proc_mm, interrupts, prev_mm, freemms, _mm_, 
                             _mm_m, _mm, prev, next >>

context_switch(self) == cs1(self) \/ cs2(self) \/ cs3(self)

sch1(self) == /\ pc[self] = "sch1"
              /\ \E n \in IF runqueue # {} THEN runqueue ELSE {task[self].cpu}:
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
                           /\ pc' = [pc EXCEPT ![self] = "cs1"]
                           /\ UNCHANGED interrupts
                      ELSE /\ interrupts' = [interrupts EXCEPT ![task[self].cpu] = "on"]
                           /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                           /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                           /\ UNCHANGED << runqueue, prev, next, oldmm >>
              /\ UNCHANGED << task, mm, proc_mm, prev_mm, freemms, _mm_, _mm_m, 
                              _mm >>

schedule(self) == sch1(self)

handle_irq(self) == /\ pc[self] = "handle_irq"
                    /\ interrupts' = [interrupts EXCEPT ![task[self].cpu] = "off"]
                    /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "schedule",
                                                             pc        |->  Head(stack[self]).pc ] >>
                                                         \o Tail(stack[self])]
                    /\ pc' = [pc EXCEPT ![self] = "sch1"]
                    /\ UNCHANGED << task, mm, proc_mm, prev_mm, freemms, 
                                    runqueue, _mm_, _mm_m, _mm, prev, next, 
                                    oldmm >>

interrupt(self) == handle_irq(self)

thread_init(self) == /\ pc[self] = "thread_init"
                     /\ runqueue' = (runqueue \cup {self})
                     /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "finish_task_switch",
                                                              pc        |->  "thread_start" ] >>
                                                          \o stack[self]]
                     /\ pc' = [pc EXCEPT ![self] = "fts1"]
                     /\ UNCHANGED << task, mm, proc_mm, interrupts, prev_mm, 
                                     freemms, _mm_, _mm_m, _mm, prev, next, 
                                     oldmm >>

thread_start(self) == /\ pc[self] = "thread_start"
                      /\ \/ /\ \E m \in freemms:
                                 /\ freemms' = freemms \ {m}
                                 /\ mm' = [mm EXCEPT ![m].mm_users = 1,
                                                     ![m].mm_count = 1]
                                 /\ /\ _mm' = [_mm EXCEPT ![self] = m]
                                    /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "exec_mmap",
                                                                             pc        |->  "thread_start",
                                                                             _mm       |->  _mm[self] ] >>
                                                                         \o stack[self]]
                                 /\ pc' = [pc EXCEPT ![self] = "emap1"]
                            /\ _mm_m' = _mm_m
                         \/ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "exit_mm",
                                                                     pc        |->  "t1" ] >>
                                                                 \o stack[self]]
                            /\ pc' = [pc EXCEPT ![self] = "exm1"]
                            /\ UNCHANGED <<mm, freemms, _mm_m, _mm>>
                         \/ /\ IF task[self].mm # "null"
                                  THEN /\ mm' = [mm EXCEPT ![(task[self].mm)].mm_users = mm[(task[self].mm)].mm_users + 1]
                                       /\ /\ _mm_m' = [_mm_m EXCEPT ![self] = task[self].mm]
                                          /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "mmput",
                                                                                   pc        |->  "thread_start",
                                                                                   _mm_m     |->  _mm_m[self] ] >>
                                                                               \o stack[self]]
                                       /\ pc' = [pc EXCEPT ![self] = "mmp1"]
                                  ELSE /\ pc' = [pc EXCEPT ![self] = "thread_start"]
                                       /\ UNCHANGED << mm, stack, _mm_m >>
                            /\ UNCHANGED <<freemms, _mm>>
                      /\ UNCHANGED << task, proc_mm, interrupts, prev_mm, 
                                      runqueue, _mm_, prev, next, oldmm >>

t1(self) == /\ pc[self] = "t1"
            /\ pc' = [pc EXCEPT ![self] = "thread_end"]
            /\ UNCHANGED << task, mm, proc_mm, interrupts, prev_mm, freemms, 
                            runqueue, stack, _mm_, _mm_m, _mm, prev, next, 
                            oldmm >>

thread_end(self) == /\ pc[self] = "thread_end"
                    /\ task' = [task EXCEPT ![self].state = "dead"]
                    /\ pc' = [pc EXCEPT ![self] = "Done"]
                    /\ UNCHANGED << mm, proc_mm, interrupts, prev_mm, freemms, 
                                    runqueue, stack, _mm_, _mm_m, _mm, prev, 
                                    next, oldmm >>

thread(self) == thread_init(self) \/ thread_start(self) \/ t1(self)
                   \/ thread_end(self)

idle_start(self) == /\ pc[self] = "idle_start"
                    /\ Running(self)
                    /\ pc' = [pc EXCEPT ![self] = "idle_start"]
                    /\ UNCHANGED << task, mm, proc_mm, interrupts, prev_mm, 
                                    freemms, runqueue, stack, _mm_, _mm_m, _mm, 
                                    prev, next, oldmm >>

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

\* Call the given label with the return path set to the interrupted pc and stack
IntCall(self, proc, label) ==
	/\ stack' = [stack EXCEPT ![self] = << [procedure	|->  proc,
						pc		|->  pc[self]] >>
					    \o stack[self]]
	/\ pc' = [pc EXCEPT ![self] = label]

Interrupt(self) ==
	\* only interrupt running tasks with interrupts enabled
	/\ Running(self)
	/\ interrupts[task[self].cpu] = "on"
	\* non-reentrant handler
	/\ pc[self] # "handle_irq"
	/\ IntCall(self, "interrupt", "handle_irq")
	/\ UNCHANGED proc_vars

PreemptNext == (\E self \in ProcSet : Interrupt(self)) \/ Next

PreemptSpec == Init /\ [][PreemptNext]_vars
==============================================================================
