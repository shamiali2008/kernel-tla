------------------------------ MODULE fpsimd ---------------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS CPUS,		\* set of available CPUs
	  THREADS,	\* set of threads
	  VALS		\* set of register values

\* Generic helpers
Range(func) ==
	{func[e] : e \in DOMAIN func}

(* --algorithm fpsimd {
variables
	\* OS and hardware state
	\* Select distinct init threads for each CPU
	cpu		\in {c \in [THREADS -> CPUS \cup {"none"}] :
				/\ Cardinality(Range(c) \ {"none"}) = Cardinality(CPUS)
				/\ \A t1, t2 \in THREADS :
					t1 # t2 => c[t1] = "none" \/ c[t1] # c[t2]};
	\* Remove the init threads from the runqueue
	runqueue	= THREADS \ {t \in THREADS : cpu[t] # "none"};
	interrupts	= [p \in CPUS |-> "off"];
	in_interrupt	= [t \in THREADS |-> FALSE];
	mode		= [t \in THREADS |-> "user"];
	preempt_count	= [t \in THREADS |-> 0];

	\* Thread state
	thread		= [t \in THREADS |->
				[fpsimd		|-> << "zero", "zero" >>,
				 fpsimd_cpu	|-> "none",
				 flags		|-> {"TIF_FOREIGN_FPSTATE"}]];

	\* FPSIMD state tracking
	fpsimd_last_state = [p \in CPUS |-> "null"];
	fpsimd_context_busy = [p \in CPUS |-> FALSE];

	\* Hardware << FPSIMD, SVE >> vectors
	hwfpsimd		= [p \in CPUS |-> << "zero", "zero" >>];

define {
	\*
	\* Type invariants
	\*
	ThreadFlags == {"TIF_FOREIGN_FPSTATE", "TIF_SVE"}
	FPSIMDType == (VALS \cup {"zero"}) \X (VALS \cup {"zero"})
	ThreadStateType ==
		[fpsimd:	FPSIMDType,
		 fpsimd_cpu:	CPUS \cup {"none"},
		 flags:		SUBSET ThreadFlags]
	TypeInv ==
		/\ thread \in [THREADS -> ThreadStateType]
		/\ runqueue \subseteq THREADS
		/\ interrupts \in [CPUS -> {"on", "off"}]
		/\ in_interrupt \in [THREADS -> BOOLEAN]
		/\ cpu \in [THREADS -> CPUS \cup {"none"}]
		/\ preempt_count \in [THREADS -> Nat]
		/\ mode \in [THREADS -> {"user", "kernel"}]
		/\ hwfpsimd \in [CPUS -> FPSIMDType]
		/\ fpsimd_last_state \in [CPUS -> THREADS \cup {"null"}]
		/\ fpsimd_context_busy \in [CPUS -> BOOLEAN]

	\*
	\* Scheduler invariants
	\*
	SchedInv ==
		/\ Cardinality(Range(cpu) \ {"none"}) = Cardinality(CPUS)
		/\ \A t1, t2 \in THREADS :
			t1 # t2 => cpu[t1] = "none" \/ cpu[t1] # cpu[t2]
		/\ \A t \in runqueue : cpu[t] = "none"

	\* Symmetry optimisations
	Perms == Permutations(CPUS) \cup Permutations(THREADS) \cup
		 Permutations(VALS)
}

\* Interrupts enabling/disabling
macro interrupts_enable() {
	interrupts[cpu[self]] := "on";
}

macro interrupts_disable() {
	interrupts[cpu[self]] := "off";
}

macro preempt_disable() {
	preempt_count[self] := preempt_count[self] + 1;
}

macro preempt_enable() {
	preempt_count[self] := preempt_count[self] - 1;
}

\* Thread flag manipulation
macro set_thread_flag(thr, flag) {
	thread[thr].flags := thread[thr].flags \cup {flag};
}

macro clear_thread_flag(thr, flag) {
	thread[thr].flags := thread[thr].flags \ {flag};
}

\* FPSIMD/SVE register reading/writing with the expected value
\* stored in the local variable "val"
macro write_fpsimd(v, val) {
	val := << v, "zero" >>;
	hwfpsimd[cpu[self]] := val;
}

macro read_fpsimd(val) {
	assert hwfpsimd[cpu[self]][1] = val[1];
}

macro write_sve(vv, val) {
	val := vv;
	hwfpsimd[cpu[self]] := val;
}

macro read_sve(val) {
	assert hwfpsimd[cpu[self]] = val;
}

\* Update current thread for the CPU
macro cpu_switch_to(next)
{
	cpu[next] := cpu[self] ||
	cpu[self] := "none";
}

macro sleep()
{
	await cpu[self] # "none";
}

macro __get_cpu_fpsimd_context()
{
	assert ~fpsimd_context_busy[cpu[self]];
	fpsimd_context_busy[cpu[self]] := TRUE;
}

macro __put_cpu_fpsimd_context()
{
	assert fpsimd_context_busy[cpu[self]];
	fpsimd_context_busy[cpu[self]] := FALSE;
}

macro get_cpu_fpsimd_context()
{
	preempt_disable();
	__get_cpu_fpsimd_context();
}

macro put_cpu_fpsimd_context()
{
	__put_cpu_fpsimd_context();
	preempt_enable();
}

macro fpsimd_save_state() {
	thread[self].fpsimd := hwfpsimd[cpu[self]];
}

macro fpsimd_load_state() {
	hwfpsimd[cpu[self]] := thread[self].fpsimd;
}

macro fpsimd_save() {
	assert fpsimd_context_busy[cpu[self]];
	if ("TIF_FOREIGN_FPSTATE" \notin thread[self].flags)
		fpsimd_save_state();
}

macro task_fpsimd_load() {
	assert fpsimd_context_busy[cpu[self]];
	fpsimd_load_state();
}

macro fpsimd_bind_task_to_cpu() {
	fpsimd_last_state[cpu[self]] := self;
	thread[self].fpsimd_cpu := cpu[self];
}

macro fpsimd_flush_cpu_state() {
	fpsimd_last_state[cpu[self]] := "null";
	set_thread_flag(self, "TIF_FOREIGN_FPSTATE");
}

procedure kernel_neon_begin()
{
knb1:	get_cpu_fpsimd_context();
knb2:	fpsimd_save();
knb3:	fpsimd_flush_cpu_state();
	return;
}

procedure kernel_neon_end()
{
kne1:	put_cpu_fpsimd_context();
	return;
}

procedure fpsimd_restore_current_state()
{
frcs1:	get_cpu_fpsimd_context();
frcs2:	if ("TIF_FOREIGN_FPSTATE" \in thread[self].flags) {
		clear_thread_flag(self, "TIF_FOREIGN_FPSTATE");
frcs3:		task_fpsimd_load();
		fpsimd_bind_task_to_cpu();
	};
frcs4:	put_cpu_fpsimd_context();
	return;
}

\* FPSIMD/SVE state switching
procedure fpsimd_thread_switch(next)
{
fts1:	__get_cpu_fpsimd_context();
	fpsimd_save();
fts2:	\* wrong_task or wrong_cpu
	if (fpsimd_last_state[cpu[self]] # next \/
	    thread[next].fpsimd_cpu # cpu[self])
		set_thread_flag(next, "TIF_FOREIGN_FPSTATE");
	else
		clear_thread_flag(next, "TIF_FOREIGN_FPSTATE");
fts3:	__put_cpu_fpsimd_context();
	return;
}

procedure schedule()
	variables next;
{
sch1:	assert preempt_count[self] = 0;
	assert interrupts[cpu[self]] = "off";
	with (n \in runqueue \cup {"none"}) {
		if (n = "none") {
			\* Return if no new thread to schedule
			interrupts_enable();
			return;
		} else {
			\* Remove the next thread from the runqueue and schedule
			runqueue := runqueue \ {n};
			next := n;
		};
	};
sch2:	call fpsimd_thread_switch(next);
sch3:	\* Add the previous thread to the runqueue and switch to next
	runqueue := runqueue \cup {self};
	cpu_switch_to(next);
sch4:	\* Context switching done, wait to be rescheduled
	sleep();
sch5:	interrupts_enable();
	return;
}

procedure do_notify_resume()
{
dnr1:	assert interrupts[cpu[self]] = "off";
	call schedule();
dnr2:	if ("TIF_FOREIGN_FPSTATE" \in thread[self].flags)
		call fpsimd_restore_current_state();
dnr3:	interrupts_disable();
	\* repeat if more work needed
	if ("TIF_FOREIGN_FPSTATE" \in thread[self].flags)
		goto dnr1;
	else
		return;
}

\* Interrupt handler
procedure interrupt_handler()
{
handle_int:
	interrupts_disable();
	in_interrupt[self] := TRUE;
	if (mode[self] = "user")
		call do_notify_resume();
	else if (preempt_count[self] = 0)
		call schedule();
int1:	in_interrupt[self] := FALSE;
	interrupts_enable();
	return;
}

procedure kernel_neon()
	variable kval;
{
kn1:	call kernel_neon_begin();
kn2:	with (v \in VALS) write_fpsimd(v, kval);
kn3:	read_fpsimd(kval);
	call kernel_neon_end();
	return;
}

procedure syscall()
{
sys_entry:
	mode[self] := "kernel";
	\* exercise in-kernel FPSIMD
sys1:	while (TRUE) {
		either	call kernel_neon();
		or	goto ret_to_user;
	};
ret_to_user:
	interrupts_disable();
	call do_notify_resume();
sys2:	mode[self] := "user";
	interrupts_enable();
	return;
}

\* User threads
process (thread \in THREADS)
	variable val = << "zero", "zero" >>;
{
thr1:	\* wait to be scheduled (simulate thread creation)
	sleep();
	\* FPSIMD initialisation (normally done by do_notify_resume())
	call fpsimd_restore_current_state();
thr2:	interrupts_enable();
thr3:	\* user thread actions
	while (TRUE) {
		either	with (v \in VALS) write_fpsimd(v, val);
		or	read_fpsimd(val);
		or	call syscall();
	}
}
} *)
------------------------------------------------------------------------------
\* BEGIN TRANSLATION
\* Process thread at line 311 col 1 changed to thread_
\* Procedure variable next of procedure schedule at line 229 col 19 changed to next_
CONSTANT defaultInitValue
VARIABLES cpu, runqueue, interrupts, in_interrupt, mode, preempt_count, 
          thread, fpsimd_last_state, fpsimd_context_busy, hwfpsimd, pc, stack

(* define statement *)
ThreadFlags == {"TIF_FOREIGN_FPSTATE", "TIF_SVE"}
FPSIMDType == (VALS \cup {"zero"}) \X (VALS \cup {"zero"})
ThreadStateType ==
        [fpsimd:        FPSIMDType,
         fpsimd_cpu:    CPUS \cup {"none"},
         flags:         SUBSET ThreadFlags]
TypeInv ==
        /\ thread \in [THREADS -> ThreadStateType]
        /\ runqueue \subseteq THREADS
        /\ interrupts \in [CPUS -> {"on", "off"}]
        /\ in_interrupt \in [THREADS -> BOOLEAN]
        /\ cpu \in [THREADS -> CPUS \cup {"none"}]
        /\ preempt_count \in [THREADS -> Nat]
        /\ mode \in [THREADS -> {"user", "kernel"}]
        /\ hwfpsimd \in [CPUS -> FPSIMDType]
        /\ fpsimd_last_state \in [CPUS -> THREADS \cup {"null"}]
        /\ fpsimd_context_busy \in [CPUS -> BOOLEAN]




SchedInv ==
        /\ Cardinality(Range(cpu) \ {"none"}) = Cardinality(CPUS)
        /\ \A t1, t2 \in THREADS :
                t1 # t2 => cpu[t1] = "none" \/ cpu[t1] # cpu[t2]
        /\ \A t \in runqueue : cpu[t] = "none"


Perms == Permutations(CPUS) \cup Permutations(THREADS) \cup
         Permutations(VALS)

VARIABLES next, next_, kval, val

global_vars == << hwfpsimd, mode, fpsimd_last_state, preempt_count, fpsimd_context_busy, thread, cpu, in_interrupt, interrupts, runqueue >>
local_vars == << next, val, next_, kval >>
vars == << global_vars, local_vars, pc, stack >>

ProcSet == (THREADS)

Init == (* Global variables *)
        /\ cpu \in {c \in [THREADS -> CPUS \cup {"none"}] :
                       /\ Cardinality(Range(c) \ {"none"}) = Cardinality(CPUS)
                       /\ \A t1, t2 \in THREADS :
                               t1 # t2 => c[t1] = "none" \/ c[t1] # c[t2]}
        /\ runqueue = THREADS \ {t \in THREADS : cpu[t] # "none"}
        /\ interrupts = [p \in CPUS |-> "off"]
        /\ in_interrupt = [t \in THREADS |-> FALSE]
        /\ mode = [t \in THREADS |-> "user"]
        /\ preempt_count = [t \in THREADS |-> 0]
        /\ thread = [t \in THREADS |->
                          [fpsimd         |-> << "zero", "zero" >>,
                           fpsimd_cpu     |-> "none",
                           flags          |-> {"TIF_FOREIGN_FPSTATE"}]]
        /\ fpsimd_last_state = [p \in CPUS |-> "null"]
        /\ fpsimd_context_busy = [p \in CPUS |-> FALSE]
        /\ hwfpsimd = [p \in CPUS |-> << "zero", "zero" >>]
        (* Procedure fpsimd_thread_switch *)
        /\ next = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure schedule *)
        /\ next_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure kernel_neon *)
        /\ kval = [ self \in ProcSet |-> defaultInitValue]
        (* Process thread_ *)
        /\ val = [self \in THREADS |-> << "zero", "zero" >>]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "thr1"]

knb1(self) == /\ pc[self] = "knb1"
              /\ preempt_count' = [preempt_count EXCEPT ![self] = preempt_count[self] + 1]
              /\ Assert(~fpsimd_context_busy[cpu[self]], 
                        "Failure of assertion at line 136, column 9 of macro called at line 189, column 9.")
              /\ fpsimd_context_busy' = [fpsimd_context_busy EXCEPT ![cpu[self]] = TRUE]
              /\ pc' = [pc EXCEPT ![self] = "knb2"]
              /\ UNCHANGED << cpu, runqueue, interrupts, in_interrupt, mode, 
                              thread, fpsimd_last_state, hwfpsimd, stack, next, 
                              next_, kval, val >>

knb2(self) == /\ pc[self] = "knb2"
              /\ Assert(fpsimd_context_busy[cpu[self]], 
                        "Failure of assertion at line 167, column 9 of macro called at line 190, column 9.")
              /\ IF "TIF_FOREIGN_FPSTATE" \notin thread[self].flags
                    THEN /\ thread' = [thread EXCEPT ![self].fpsimd = hwfpsimd[cpu[self]]]
                    ELSE /\ TRUE
                         /\ UNCHANGED thread
              /\ pc' = [pc EXCEPT ![self] = "knb3"]
              /\ UNCHANGED << cpu, runqueue, interrupts, in_interrupt, mode, 
                              preempt_count, fpsimd_last_state, 
                              fpsimd_context_busy, hwfpsimd, stack, next, 
                              next_, kval, val >>

knb3(self) == /\ pc[self] = "knb3"
              /\ fpsimd_last_state' = [fpsimd_last_state EXCEPT ![cpu[self]] = "null"]
              /\ thread' = [thread EXCEPT ![self].flags = thread[self].flags \cup {"TIF_FOREIGN_FPSTATE"}]
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << cpu, runqueue, interrupts, in_interrupt, mode, 
                              preempt_count, fpsimd_context_busy, hwfpsimd, 
                              next, next_, kval, val >>

kernel_neon_begin(self) == knb1(self) \/ knb2(self) \/ knb3(self)

kne1(self) == /\ pc[self] = "kne1"
              /\ Assert(fpsimd_context_busy[cpu[self]], 
                        "Failure of assertion at line 142, column 9 of macro called at line 197, column 9.")
              /\ fpsimd_context_busy' = [fpsimd_context_busy EXCEPT ![cpu[self]] = FALSE]
              /\ preempt_count' = [preempt_count EXCEPT ![self] = preempt_count[self] - 1]
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << cpu, runqueue, interrupts, in_interrupt, mode, 
                              thread, fpsimd_last_state, hwfpsimd, next, next_, 
                              kval, val >>

kernel_neon_end(self) == kne1(self)

frcs1(self) == /\ pc[self] = "frcs1"
               /\ preempt_count' = [preempt_count EXCEPT ![self] = preempt_count[self] + 1]
               /\ Assert(~fpsimd_context_busy[cpu[self]], 
                         "Failure of assertion at line 136, column 9 of macro called at line 203, column 9.")
               /\ fpsimd_context_busy' = [fpsimd_context_busy EXCEPT ![cpu[self]] = TRUE]
               /\ pc' = [pc EXCEPT ![self] = "frcs2"]
               /\ UNCHANGED << cpu, runqueue, interrupts, in_interrupt, mode, 
                               thread, fpsimd_last_state, hwfpsimd, stack, 
                               next, next_, kval, val >>

frcs2(self) == /\ pc[self] = "frcs2"
               /\ IF "TIF_FOREIGN_FPSTATE" \in thread[self].flags
                     THEN /\ thread' = [thread EXCEPT ![self].flags = thread[self].flags \ {"TIF_FOREIGN_FPSTATE"}]
                          /\ pc' = [pc EXCEPT ![self] = "frcs3"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "frcs4"]
                          /\ UNCHANGED thread
               /\ UNCHANGED << cpu, runqueue, interrupts, in_interrupt, mode, 
                               preempt_count, fpsimd_last_state, 
                               fpsimd_context_busy, hwfpsimd, stack, next, 
                               next_, kval, val >>

frcs3(self) == /\ pc[self] = "frcs3"
               /\ Assert(fpsimd_context_busy[cpu[self]], 
                         "Failure of assertion at line 173, column 9 of macro called at line 206, column 17.")
               /\ hwfpsimd' = [hwfpsimd EXCEPT ![cpu[self]] = thread[self].fpsimd]
               /\ fpsimd_last_state' = [fpsimd_last_state EXCEPT ![cpu[self]] = self]
               /\ thread' = [thread EXCEPT ![self].fpsimd_cpu = cpu[self]]
               /\ pc' = [pc EXCEPT ![self] = "frcs4"]
               /\ UNCHANGED << cpu, runqueue, interrupts, in_interrupt, mode, 
                               preempt_count, fpsimd_context_busy, stack, next, 
                               next_, kval, val >>

frcs4(self) == /\ pc[self] = "frcs4"
               /\ Assert(fpsimd_context_busy[cpu[self]], 
                         "Failure of assertion at line 142, column 9 of macro called at line 209, column 9.")
               /\ fpsimd_context_busy' = [fpsimd_context_busy EXCEPT ![cpu[self]] = FALSE]
               /\ preempt_count' = [preempt_count EXCEPT ![self] = preempt_count[self] - 1]
               /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
               /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
               /\ UNCHANGED << cpu, runqueue, interrupts, in_interrupt, mode, 
                               thread, fpsimd_last_state, hwfpsimd, next, 
                               next_, kval, val >>

fpsimd_restore_current_state(self) == frcs1(self) \/ frcs2(self)
                                         \/ frcs3(self) \/ frcs4(self)

fts1(self) == /\ pc[self] = "fts1"
              /\ Assert(~fpsimd_context_busy[cpu[self]], 
                        "Failure of assertion at line 136, column 9 of macro called at line 216, column 9.")
              /\ fpsimd_context_busy' = [fpsimd_context_busy EXCEPT ![cpu[self]] = TRUE]
              /\ Assert(fpsimd_context_busy'[cpu[self]], 
                        "Failure of assertion at line 167, column 9 of macro called at line 217, column 9.")
              /\ IF "TIF_FOREIGN_FPSTATE" \notin thread[self].flags
                    THEN /\ thread' = [thread EXCEPT ![self].fpsimd = hwfpsimd[cpu[self]]]
                    ELSE /\ TRUE
                         /\ UNCHANGED thread
              /\ pc' = [pc EXCEPT ![self] = "fts2"]
              /\ UNCHANGED << cpu, runqueue, interrupts, in_interrupt, mode, 
                              preempt_count, fpsimd_last_state, hwfpsimd, 
                              stack, next, next_, kval, val >>

fts2(self) == /\ pc[self] = "fts2"
              /\ IF fpsimd_last_state[cpu[self]] # next[self] \/
                    thread[next[self]].fpsimd_cpu # cpu[self]
                    THEN /\ thread' = [thread EXCEPT ![next[self]].flags = thread[next[self]].flags \cup {"TIF_FOREIGN_FPSTATE"}]
                    ELSE /\ thread' = [thread EXCEPT ![next[self]].flags = thread[next[self]].flags \ {"TIF_FOREIGN_FPSTATE"}]
              /\ pc' = [pc EXCEPT ![self] = "fts3"]
              /\ UNCHANGED << cpu, runqueue, interrupts, in_interrupt, mode, 
                              preempt_count, fpsimd_last_state, 
                              fpsimd_context_busy, hwfpsimd, stack, next, 
                              next_, kval, val >>

fts3(self) == /\ pc[self] = "fts3"
              /\ Assert(fpsimd_context_busy[cpu[self]], 
                        "Failure of assertion at line 142, column 9 of macro called at line 224, column 9.")
              /\ fpsimd_context_busy' = [fpsimd_context_busy EXCEPT ![cpu[self]] = FALSE]
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ next' = [next EXCEPT ![self] = Head(stack[self]).next]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << cpu, runqueue, interrupts, in_interrupt, mode, 
                              preempt_count, thread, fpsimd_last_state, 
                              hwfpsimd, next_, kval, val >>

fpsimd_thread_switch(self) == fts1(self) \/ fts2(self) \/ fts3(self)

sch1(self) == /\ pc[self] = "sch1"
              /\ Assert(preempt_count[self] = 0, 
                        "Failure of assertion at line 231, column 9.")
              /\ Assert(interrupts[cpu[self]] = "off", 
                        "Failure of assertion at line 232, column 9.")
              /\ \E n \in runqueue \cup {"none"}:
                   IF n = "none"
                      THEN /\ interrupts' = [interrupts EXCEPT ![cpu[self]] = "on"]
                           /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                           /\ next_' = [next_ EXCEPT ![self] = Head(stack[self]).next_]
                           /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                           /\ UNCHANGED runqueue
                      ELSE /\ runqueue' = runqueue \ {n}
                           /\ next_' = [next_ EXCEPT ![self] = n]
                           /\ pc' = [pc EXCEPT ![self] = "sch2"]
                           /\ UNCHANGED << interrupts, stack >>
              /\ UNCHANGED << cpu, in_interrupt, mode, preempt_count, thread, 
                              fpsimd_last_state, fpsimd_context_busy, hwfpsimd, 
                              next, kval, val >>

sch2(self) == /\ pc[self] = "sch2"
              /\ /\ next' = [next EXCEPT ![self] = next_[self]]
                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "fpsimd_thread_switch",
                                                          pc        |->  "sch3",
                                                          next      |->  next[self] ] >>
                                                      \o stack[self]]
              /\ pc' = [pc EXCEPT ![self] = "fts1"]
              /\ UNCHANGED << cpu, runqueue, interrupts, in_interrupt, mode, 
                              preempt_count, thread, fpsimd_last_state, 
                              fpsimd_context_busy, hwfpsimd, next_, kval, val >>

sch3(self) == /\ pc[self] = "sch3"
              /\ runqueue' = (runqueue \cup {self})
              /\ cpu' = [cpu EXCEPT ![next_[self]] = cpu[self],
                                    ![self] = "none"]
              /\ pc' = [pc EXCEPT ![self] = "sch4"]
              /\ UNCHANGED << interrupts, in_interrupt, mode, preempt_count, 
                              thread, fpsimd_last_state, fpsimd_context_busy, 
                              hwfpsimd, stack, next, next_, kval, val >>

sch4(self) == /\ pc[self] = "sch4"
              /\ cpu[self] # "none"
              /\ pc' = [pc EXCEPT ![self] = "sch5"]
              /\ UNCHANGED << cpu, runqueue, interrupts, in_interrupt, mode, 
                              preempt_count, thread, fpsimd_last_state, 
                              fpsimd_context_busy, hwfpsimd, stack, next, 
                              next_, kval, val >>

sch5(self) == /\ pc[self] = "sch5"
              /\ interrupts' = [interrupts EXCEPT ![cpu[self]] = "on"]
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ next_' = [next_ EXCEPT ![self] = Head(stack[self]).next_]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << cpu, runqueue, in_interrupt, mode, preempt_count, 
                              thread, fpsimd_last_state, fpsimd_context_busy, 
                              hwfpsimd, next, kval, val >>

schedule(self) == sch1(self) \/ sch2(self) \/ sch3(self) \/ sch4(self)
                     \/ sch5(self)

dnr1(self) == /\ pc[self] = "dnr1"
              /\ Assert(interrupts[cpu[self]] = "off", 
                        "Failure of assertion at line 256, column 9.")
              /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "schedule",
                                                       pc        |->  "dnr2",
                                                       next_     |->  next_[self] ] >>
                                                   \o stack[self]]
              /\ next_' = [next_ EXCEPT ![self] = defaultInitValue]
              /\ pc' = [pc EXCEPT ![self] = "sch1"]
              /\ UNCHANGED << cpu, runqueue, interrupts, in_interrupt, mode, 
                              preempt_count, thread, fpsimd_last_state, 
                              fpsimd_context_busy, hwfpsimd, next, kval, val >>

dnr2(self) == /\ pc[self] = "dnr2"
              /\ IF "TIF_FOREIGN_FPSTATE" \in thread[self].flags
                    THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "fpsimd_restore_current_state",
                                                                  pc        |->  "dnr3" ] >>
                                                              \o stack[self]]
                         /\ pc' = [pc EXCEPT ![self] = "frcs1"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "dnr3"]
                         /\ stack' = stack
              /\ UNCHANGED << cpu, runqueue, interrupts, in_interrupt, mode, 
                              preempt_count, thread, fpsimd_last_state, 
                              fpsimd_context_busy, hwfpsimd, next, next_, kval, 
                              val >>

dnr3(self) == /\ pc[self] = "dnr3"
              /\ interrupts' = [interrupts EXCEPT ![cpu[self]] = "off"]
              /\ IF "TIF_FOREIGN_FPSTATE" \in thread[self].flags
                    THEN /\ pc' = [pc EXCEPT ![self] = "dnr1"]
                         /\ stack' = stack
                    ELSE /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                         /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << cpu, runqueue, in_interrupt, mode, preempt_count, 
                              thread, fpsimd_last_state, fpsimd_context_busy, 
                              hwfpsimd, next, next_, kval, val >>

do_notify_resume(self) == dnr1(self) \/ dnr2(self) \/ dnr3(self)

handle_int(self) == /\ pc[self] = "handle_int"
                    /\ interrupts' = [interrupts EXCEPT ![cpu[self]] = "off"]
                    /\ in_interrupt' = [in_interrupt EXCEPT ![self] = TRUE]
                    /\ IF mode[self] = "user"
                          THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "do_notify_resume",
                                                                        pc        |->  "int1" ] >>
                                                                    \o stack[self]]
                               /\ pc' = [pc EXCEPT ![self] = "dnr1"]
                               /\ next_' = next_
                          ELSE /\ IF preempt_count[self] = 0
                                     THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "schedule",
                                                                                   pc        |->  "int1",
                                                                                   next_     |->  next_[self] ] >>
                                                                               \o stack[self]]
                                          /\ next_' = [next_ EXCEPT ![self] = defaultInitValue]
                                          /\ pc' = [pc EXCEPT ![self] = "sch1"]
                                     ELSE /\ pc' = [pc EXCEPT ![self] = "int1"]
                                          /\ UNCHANGED << stack, next_ >>
                    /\ UNCHANGED << cpu, runqueue, mode, preempt_count, thread, 
                                    fpsimd_last_state, fpsimd_context_busy, 
                                    hwfpsimd, next, kval, val >>

int1(self) == /\ pc[self] = "int1"
              /\ in_interrupt' = [in_interrupt EXCEPT ![self] = FALSE]
              /\ interrupts' = [interrupts EXCEPT ![cpu[self]] = "on"]
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << cpu, runqueue, mode, preempt_count, thread, 
                              fpsimd_last_state, fpsimd_context_busy, hwfpsimd, 
                              next, next_, kval, val >>

interrupt_handler(self) == handle_int(self) \/ int1(self)

kn1(self) == /\ pc[self] = "kn1"
             /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "kernel_neon_begin",
                                                      pc        |->  "kn2" ] >>
                                                  \o stack[self]]
             /\ pc' = [pc EXCEPT ![self] = "knb1"]
             /\ UNCHANGED << cpu, runqueue, interrupts, in_interrupt, mode, 
                             preempt_count, thread, fpsimd_last_state, 
                             fpsimd_context_busy, hwfpsimd, next, next_, kval, 
                             val >>

kn2(self) == /\ pc[self] = "kn2"
             /\ \E v \in VALS:
                  /\ kval' = [kval EXCEPT ![self] = << v, "zero" >>]
                  /\ hwfpsimd' = [hwfpsimd EXCEPT ![cpu[self]] = kval'[self]]
             /\ pc' = [pc EXCEPT ![self] = "kn3"]
             /\ UNCHANGED << cpu, runqueue, interrupts, in_interrupt, mode, 
                             preempt_count, thread, fpsimd_last_state, 
                             fpsimd_context_busy, stack, next, next_, val >>

kn3(self) == /\ pc[self] = "kn3"
             /\ Assert(hwfpsimd[cpu[self]][1] = kval[self][1], 
                       "Failure of assertion at line 110, column 9 of macro called at line 288, column 9.")
             /\ /\ kval' = [kval EXCEPT ![self] = Head(stack[self]).kval]
                /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "kernel_neon_end",
                                                         pc        |->  Head(stack[self]).pc ] >>
                                                     \o Tail(stack[self])]
             /\ pc' = [pc EXCEPT ![self] = "kne1"]
             /\ UNCHANGED << cpu, runqueue, interrupts, in_interrupt, mode, 
                             preempt_count, thread, fpsimd_last_state, 
                             fpsimd_context_busy, hwfpsimd, next, next_, val >>

kernel_neon(self) == kn1(self) \/ kn2(self) \/ kn3(self)

sys_entry(self) == /\ pc[self] = "sys_entry"
                   /\ mode' = [mode EXCEPT ![self] = "kernel"]
                   /\ pc' = [pc EXCEPT ![self] = "sys1"]
                   /\ UNCHANGED << cpu, runqueue, interrupts, in_interrupt, 
                                   preempt_count, thread, fpsimd_last_state, 
                                   fpsimd_context_busy, hwfpsimd, stack, next, 
                                   next_, kval, val >>

sys1(self) == /\ pc[self] = "sys1"
              /\ \/ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "kernel_neon",
                                                             pc        |->  "sys1",
                                                             kval      |->  kval[self] ] >>
                                                         \o stack[self]]
                    /\ kval' = [kval EXCEPT ![self] = defaultInitValue]
                    /\ pc' = [pc EXCEPT ![self] = "kn1"]
                 \/ /\ pc' = [pc EXCEPT ![self] = "ret_to_user"]
                    /\ UNCHANGED <<stack, kval>>
              /\ UNCHANGED << cpu, runqueue, interrupts, in_interrupt, mode, 
                              preempt_count, thread, fpsimd_last_state, 
                              fpsimd_context_busy, hwfpsimd, next, next_, val >>

ret_to_user(self) == /\ pc[self] = "ret_to_user"
                     /\ interrupts' = [interrupts EXCEPT ![cpu[self]] = "off"]
                     /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "do_notify_resume",
                                                              pc        |->  "sys2" ] >>
                                                          \o stack[self]]
                     /\ pc' = [pc EXCEPT ![self] = "dnr1"]
                     /\ UNCHANGED << cpu, runqueue, in_interrupt, mode, 
                                     preempt_count, thread, fpsimd_last_state, 
                                     fpsimd_context_busy, hwfpsimd, next, 
                                     next_, kval, val >>

sys2(self) == /\ pc[self] = "sys2"
              /\ mode' = [mode EXCEPT ![self] = "user"]
              /\ interrupts' = [interrupts EXCEPT ![cpu[self]] = "on"]
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << cpu, runqueue, in_interrupt, preempt_count, 
                              thread, fpsimd_last_state, fpsimd_context_busy, 
                              hwfpsimd, next, next_, kval, val >>

syscall(self) == sys_entry(self) \/ sys1(self) \/ ret_to_user(self)
                    \/ sys2(self)

thr1(self) == /\ pc[self] = "thr1"
              /\ cpu[self] # "none"
              /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "fpsimd_restore_current_state",
                                                       pc        |->  "thr2" ] >>
                                                   \o stack[self]]
              /\ pc' = [pc EXCEPT ![self] = "frcs1"]
              /\ UNCHANGED << cpu, runqueue, interrupts, in_interrupt, mode, 
                              preempt_count, thread, fpsimd_last_state, 
                              fpsimd_context_busy, hwfpsimd, next, next_, kval, 
                              val >>

thr2(self) == /\ pc[self] = "thr2"
              /\ interrupts' = [interrupts EXCEPT ![cpu[self]] = "on"]
              /\ pc' = [pc EXCEPT ![self] = "thr3"]
              /\ UNCHANGED << cpu, runqueue, in_interrupt, mode, preempt_count, 
                              thread, fpsimd_last_state, fpsimd_context_busy, 
                              hwfpsimd, stack, next, next_, kval, val >>

thr3(self) == /\ pc[self] = "thr3"
              /\ \/ /\ \E v \in VALS:
                         /\ val' = [val EXCEPT ![self] = << v, "zero" >>]
                         /\ hwfpsimd' = [hwfpsimd EXCEPT ![cpu[self]] = val'[self]]
                    /\ pc' = [pc EXCEPT ![self] = "thr3"]
                    /\ stack' = stack
                 \/ /\ Assert(hwfpsimd[cpu[self]][1] = val[self][1], 
                              "Failure of assertion at line 110, column 9 of macro called at line 322, column 25.")
                    /\ pc' = [pc EXCEPT ![self] = "thr3"]
                    /\ UNCHANGED <<hwfpsimd, stack, val>>
                 \/ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "syscall",
                                                             pc        |->  "thr3" ] >>
                                                         \o stack[self]]
                    /\ pc' = [pc EXCEPT ![self] = "sys_entry"]
                    /\ UNCHANGED <<hwfpsimd, val>>
              /\ UNCHANGED << cpu, runqueue, interrupts, in_interrupt, mode, 
                              preempt_count, thread, fpsimd_last_state, 
                              fpsimd_context_busy, next, next_, kval >>

thread_(self) == thr1(self) \/ thr2(self) \/ thr3(self)

Next == (\E self \in ProcSet:  \/ kernel_neon_begin(self)
                               \/ kernel_neon_end(self)
                               \/ fpsimd_restore_current_state(self)
                               \/ fpsimd_thread_switch(self)
                               \/ schedule(self) \/ do_notify_resume(self)
                               \/ interrupt_handler(self)
                               \/ kernel_neon(self) \/ syscall(self))
           \/ (\E self \in THREADS: thread_(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
------------------------------------------------------------------------------

\* Inject the interrupt_handler call into the call path
Interrupt(self) ==
	\* Only interrupt running threads
	/\ cpu[self] # "none"
	/\ interrupts[cpu[self]] = "on"
	\* Non-reentrant interrupt handler
	/\ ~in_interrupt[self]
	\* Save the PC of the interrupted context on the stack.
	/\ stack' = [stack EXCEPT ![self] = << [procedure |-> "interrupt_handler",
						pc	  |-> pc[self]] >>
					    \o stack[self]]
	/\ pc' = [pc EXCEPT ![self] = "handle_int"]
	/\ UNCHANGED << global_vars, local_vars >>

OSNext == (\E self \in THREADS : Interrupt(self)) \/ Next

OSSpec == Init /\ [][OSNext]_vars
==============================================================================
