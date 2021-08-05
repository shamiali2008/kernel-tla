---------------------------- MODULE asidalloc --------------------------------
\*
\* ASID allocation algorithm (as used in the arm and arm64 Linux kernel ports)
\* together with inviariant definitions for a simplified model of the CPU TLB.
\*
\* See arch/arm64/mm/context.c for the C implementation of the algorithm.
\*
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANT	CPUS,		\* set of available CPUs
		ASIDS,		\* number of ASIDs
		GENERATIONS,	\* number of generations
		TASKS,		\* set of context ids
		TTU,		\* special task modifying the page table
		CnP		\* test CnP or not

ASSUME	/\ ASIDS \in Nat \ {0}
	/\ GENERATIONS \in Nat \ {0}
	/\ Cardinality(CPUS) < ASIDS - 1
	/\ CnP \in BOOLEAN

(* --algorithm asidalloc {
variables
	\* CPU TLB and and page table model
	tlb = {};
	pte = [t \in TASKS |-> "mapped"];
	active_mm = [c \in CPUS |-> [task |-> 0, asid |-> 0]];

	\* ASID allocation algorithm state
	cpu_asid_lock = FALSE;
	asid_generation = 1;
	asid_map = [a \in 0..ASIDS-1 |-> FALSE];
	active_asids = [c \in CPUS |-> [asid |-> 0, generation |-> 0]];
	reserved_asids = [c \in CPUS |-> [asid |-> 0, generation |-> 0]];
	tlb_flush_pending = [c \in CPUS |-> FALSE];
	cur_idx = 1;

	\* OS tasks
	mm_context_id = [t \in TASKS |-> [asid |-> 0, generation |-> 0]];

	\* PlusCal procedure return value
	ret_check_update_reserved_asid = [i \in CPUS |-> FALSE];
	ret_new_context = [c \in CPUS |-> [asid |-> 0, generation |-> 0]]

define {
	\*
	\* Various helpers
	\*
	MakeAsid(a, g) == [asid |-> a, generation |-> g]
	NULL_ASID == MakeAsid(0, 0)

	EmptySlots(map, start) == \E idx \in start..ASIDS-1 : map[idx] = FALSE
	FindEmptySlot(map, start) ==
		CHOOSE idx \in start..ASIDS-1 : map[idx] = FALSE

	AnyElem(s) == CHOOSE e \in s : TRUE

	MakeTlbEntry(t, a, c) == [task |-> t, asid |-> a, cpu |-> c]

	ActiveTask(cpu) == active_mm[cpu].task
	ActiveAsid(cpu) == active_mm[cpu].asid

	\*
	\* Type invariants
	\*
	AsidType ==	[asid: 0..ASIDS-1, generation: 0..GENERATIONS]
		\* ASID 0 not allowed in the TLB (reserved)
	TlbType ==	[task: TASKS, asid: 1..ASIDS-1, cpu: CPUS]
	TTBRType ==	[task: TASKS \cup {0}, asid: 0..ASIDS-1]
	PTEType ==	[TASKS -> {"mapped", "unmapped", "inval"}]
	TypeInv ==	/\ cpu_asid_lock \in BOOLEAN
			/\ asid_generation \in Nat \ {0}
			/\ asid_map \in [0..ASIDS-1 -> BOOLEAN]
			/\ active_asids \in [CPUS -> AsidType]
			/\ reserved_asids \in [CPUS -> AsidType]
			/\ tlb_flush_pending \in [CPUS -> BOOLEAN]
			/\ cur_idx \in 1..ASIDS-1
			/\ mm_context_id \in [TASKS -> AsidType]
			/\ active_mm \in [CPUS -> TTBRType]
			/\ tlb \subseteq TlbType
			/\ pte \in PTEType

	\*
	\* Algorithm invariants
	\*
		\* Only when checking CnP; flush_tlb_all() must be used
	UniqueASIDAllCPUs ==	\/ ~CnP
				\/ \A t1, t2 \in tlb :
					(t1.task # t2.task) <=> (t1.asid # t2.asid)
		\* Two TLB entries per CPU with the same ASID but different BADDR
	UniqueASIDPerCPU ==	\A t1, t2 \in tlb :
					/\ t1.task # t2.task
					/\ t1.cpu = t2.cpu
					=> t1.asid # t2.asid
		\* This is possible when an old task gets a new ASID; safe as
		\* long as it is not active on a different CPU (checked below)
	SameASIDPerTask ==	\A t1, t2 \in tlb :
					(t1.task = t2.task) => (t1.asid = t2.asid)
		\* Same task active on different CPUs must have the same ASID
		\* outside the context switching code
	SameASIDActiveTask ==	\A c1, c2 \in DOMAIN active_mm :
					/\ c1 # c2
					/\ pc[c1] = "sched_loop"
					/\ pc[c2] = "sched_loop"
					/\ ActiveTask(c1) # 0
					/\ ActiveTask(c1) = ActiveTask(c2)
					=> ActiveAsid(c1) = ActiveAsid(c2)
		\* Two different active tasks on different CPUs must have different ASIDs
	UniqueASIDActiveTask == \/ ~CnP
				\/ \A c1, c2 \in DOMAIN active_mm :
					/\ (c1 # c2)
					/\ ActiveTask(c1) # 0
					/\ ActiveTask(c2) # 0
					/\ ActiveTask(c1) # ActiveTask(c2)
		\* TLB empty for an active task/ASID following TLBI
	TLBEmptyTask(task) ==	\A t \in tlb :
					~(t.task = task /\ t.asid = mm_context_id[task].asid)
	TLBEmptyInvalPTE ==	\A c \in CPUS : LET t == ActiveTask(c) IN
					t # 0 /\ pte[t] = "inval" => TLBEmptyTask(t)

	\* Symmetry optimisations
	Perms == Permutations(CPUS) \cup Permutations(TASKS)

	\* We ignore generation roll-over (known to fail)
	Constr == asid_generation <= GENERATIONS
}

\* Simple locking
macro spin_lock(l) {
	await ~l;
	l := TRUE;
}

macro spin_unlock(l) {
	l := FALSE;
}

\* atomic cmpxchg
macro cmpxchg(v, o, n) {
	if (v = o)
		v := n;
	else
		o := v;
}

\* Reset the TLB apart from the entries corresponding to active tasks on
\* any CPU as such entries can be speculatively loaded
macro flush_tlb_all() {
	tlb := {MakeTlbEntry(ActiveTask(c), ActiveAsid(c), c) :
		     c \in {c1 \in DOMAIN active_mm : ActiveTask(c1) # 0}};
}

\* Remove entries for the current CPU other than the active task
macro local_flush_tlb_all() {
	tlb := {t \in tlb : t.cpu # self \/ t.task = ActiveTask(self)};
}

\* Remove entries corresponding to the given ASID
macro flush_tlb_asid(asid) {
	tlb := {t \in tlb : t.asid # asid};
}

macro cpu_switch_mm(t, a) {
	active_mm[self].task := t || active_mm[self].asid := a;
	\* A TLB entry can be speculatively loaded as soon as a new TTBR is set
	if (t # 0 /\ pte[t] = "mapped")
		tlb := tlb \cup {MakeTlbEntry(t, mm_context_id[t].asid, self)};
}

macro cpu_set_reserved_ttbr0() {
	cpu_switch_mm(0, ActiveAsid(self));
}

\*
\* ASID allocation algorithm
\*
procedure flush_context()
	variables asid; cpu; cpus;
{
flush_context:
	asid_map := [i \in 0..ASIDS-1 |-> FALSE];

	cpus := CPUS;
flush_context_for_each_cpu:
	while (cpus # {}) {
		cpu := AnyElem(cpus);
		asid := active_asids[cpu];
		active_asids[cpu] := NULL_ASID;
flush_context_asid0_check:
		if (asid = NULL_ASID)
			asid := reserved_asids[cpu];
		asid_map[asid.asid] := TRUE;
		reserved_asids[cpu] := asid;
		cpus := cpus \ {cpu};
	};

	tlb_flush_pending := [i \in CPUS |-> TRUE];
	return;
}

procedure check_update_reserved_asid(asid, newasid)
	variable cpu; cpus;
{
check_update_reserved_asid:
	ret_check_update_reserved_asid[self] := FALSE;
	cpus := CPUS;
check_update_reserved_asid_for_each_cpu:
	while (cpus # {}) {
		cpu := AnyElem(cpus);
		if (reserved_asids[cpu] = asid) {
			ret_check_update_reserved_asid[self] := TRUE;
			reserved_asids[cpu] := newasid;
		};
		cpus := cpus \ {cpu};
	};
	return;
}

procedure new_context(task = 0)
	variables asid; newasid; generation; old;
{
new_context:
	asid := mm_context_id[task];
	generation := asid_generation;

	if (asid # NULL_ASID) {
		newasid := MakeAsid(asid.asid, generation);

		call check_update_reserved_asid(asid, newasid);
new_context_ret_from_check_update_reserved_asid:
		if (ret_check_update_reserved_asid[self]) {
			ret_new_context[self] := newasid;
			return;
		};
new_context_ret_from_check_update_reserved_asid_end:
		old := asid_map[asid.asid];
		asid_map[asid.asid] := TRUE;
		if (~old) {
			ret_new_context[self] := newasid;
new_context_return:
			return;
		};
	};

new_context_allocate_free_asid:
	if (EmptySlots(asid_map, cur_idx)) {
		asid.asid := FindEmptySlot(asid_map, cur_idx);
		goto set_asid;
	};
new_context_out_of_asids:
	(* Generation roll-over not safe; commenting out
	if (asid_generation = GENERATIONS)
		asid_generation := 1;
	else *)
		asid_generation := asid_generation + 1;
	generation := asid_generation;

	call flush_context();
new_context_ret_flush_context:
	\* We have more ASIDs than CPUs, so this will always succeed
	asid.asid := FindEmptySlot(asid_map, 1);

set_asid:
	asid_map[asid.asid] := TRUE;
	cur_idx := asid.asid;
	ret_new_context[self] := MakeAsid(asid.asid, generation);
	return;
}

procedure check_and_switch_context(task = 0)
	variables asid; old_active_asid;
{
check_and_switch_context:
	\* active_asids update is racy with the TTBR0 one
	if (CnP)
		cpu_set_reserved_ttbr0();

	asid := mm_context_id[task];

	old_active_asid := active_asids[self];
check_current_generation:
	if (old_active_asid # NULL_ASID /\ asid.generation = asid_generation) {
cmpxchg_active_asids:
		cmpxchg(active_asids[self], old_active_asid, asid);
check_roll_over:
		if (old_active_asid # NULL_ASID)
			goto fast_path;
	};
slow_path:
	spin_lock(cpu_asid_lock);

	asid := mm_context_id[task];
	if (asid.generation # asid_generation) {
		call new_context(task);
check_and_switch_context_ret_new_context:
		asid := ret_new_context[self];
		mm_context_id[task] := asid;
	};
tlb_flush_pending:
	if (tlb_flush_pending[self]) {
		tlb_flush_pending[self] := FALSE;
		if (CnP)
			flush_tlb_all();
		else
			local_flush_tlb_all();
	};
set_active_asids:
	active_asids[self] := asid;

	spin_unlock(cpu_asid_lock);

fast_path:
	cpu_switch_mm(task, asid.asid);
	return;
}

\* Unmap the pte for a given task
procedure try_to_unmap(task)
	variables asid;
{
pte_clear:
	pte[task] := "unmapped";
read_asid:
	asid := mm_context_id[task].asid;
tlbi:
	flush_tlb_asid(asid);
after_tlbi:
	\* Mark pte as invalidated for invariant checking
	pte[task] := "inval";
	return;
}

\* Asynchronous process for unmapping PTEs
process (ttu = TTU)
{
ttu:
	while (TRUE) {
		with (t \in TASKS)
			call try_to_unmap(t);
	}
}

process (sched \in CPUS)
{
sched_loop:
	while (TRUE) {
		with (t \in TASKS) {
			if (t # ActiveTask(self))
				call check_and_switch_context(t);
		}
	}
}
} *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-3b4c8093cab80710385baf7e614083a3
\* Label flush_context of procedure flush_context at line 181 col 9 changed to flush_context_
\* Label check_update_reserved_asid of procedure check_update_reserved_asid at line 205 col 9 changed to check_update_reserved_asid_
\* Label new_context of procedure new_context at line 223 col 9 changed to new_context_
\* Label check_and_switch_context of procedure check_and_switch_context at line 275 col 9 changed to check_and_switch_context_
\* Label tlb_flush_pending of procedure check_and_switch_context at line 300 col 9 changed to tlb_flush_pending_
\* Label ttu of process ttu at line 337 col 9 changed to ttu_
\* Procedure variable asid of procedure flush_context at line 178 col 19 changed to asid_
\* Procedure variable cpu of procedure flush_context at line 178 col 25 changed to cpu_
\* Procedure variable cpus of procedure flush_context at line 178 col 30 changed to cpus_
\* Procedure variable asid of procedure new_context at line 220 col 19 changed to asid_n
\* Procedure variable newasid of procedure new_context at line 220 col 25 changed to newasid_
\* Procedure variable asid of procedure check_and_switch_context at line 271 col 19 changed to asid_c
\* Procedure variable asid of procedure try_to_unmap at line 319 col 19 changed to asid_t
\* Parameter task of procedure new_context at line 219 col 23 changed to task_
\* Parameter task of procedure check_and_switch_context at line 270 col 36 changed to task_c
CONSTANT defaultInitValue
VARIABLES tlb, pte, active_mm, cpu_asid_lock, asid_generation, asid_map, 
          active_asids, reserved_asids, tlb_flush_pending, cur_idx, 
          mm_context_id, ret_check_update_reserved_asid, ret_new_context, pc, 
          stack

(* define statement *)
MakeAsid(a, g) == [asid |-> a, generation |-> g]
NULL_ASID == MakeAsid(0, 0)

EmptySlots(map, start) == \E idx \in start..ASIDS-1 : map[idx] = FALSE
FindEmptySlot(map, start) ==
        CHOOSE idx \in start..ASIDS-1 : map[idx] = FALSE

AnyElem(s) == CHOOSE e \in s : TRUE

MakeTlbEntry(t, a, c) == [task |-> t, asid |-> a, cpu |-> c]

ActiveTask(cpu) == active_mm[cpu].task
ActiveAsid(cpu) == active_mm[cpu].asid




AsidType ==     [asid: 0..ASIDS-1, generation: 0..GENERATIONS]

TlbType ==      [task: TASKS, asid: 1..ASIDS-1, cpu: CPUS]
TTBRType ==     [task: TASKS \cup {0}, asid: 0..ASIDS-1]
PTEType ==      [TASKS -> {"mapped", "unmapped", "inval"}]
TypeInv ==      /\ cpu_asid_lock \in BOOLEAN
                /\ asid_generation \in Nat \ {0}
                /\ asid_map \in [0..ASIDS-1 -> BOOLEAN]
                /\ active_asids \in [CPUS -> AsidType]
                /\ reserved_asids \in [CPUS -> AsidType]
                /\ tlb_flush_pending \in [CPUS -> BOOLEAN]
                /\ cur_idx \in 1..ASIDS-1
                /\ mm_context_id \in [TASKS -> AsidType]
                /\ active_mm \in [CPUS -> TTBRType]
                /\ tlb \subseteq TlbType
                /\ pte \in PTEType





UniqueASIDAllCPUs ==    \/ ~CnP
                        \/ \A t1, t2 \in tlb :
                                (t1.task # t2.task) <=> (t1.asid # t2.asid)

UniqueASIDPerCPU ==     \A t1, t2 \in tlb :
                                /\ t1.task # t2.task
                                /\ t1.cpu = t2.cpu
                                => t1.asid # t2.asid


SameASIDPerTask ==      \A t1, t2 \in tlb :
                                (t1.task = t2.task) => (t1.asid = t2.asid)


SameASIDActiveTask ==   \A c1, c2 \in DOMAIN active_mm :
                                /\ c1 # c2
                                /\ pc[c1] = "sched_loop"
                                /\ pc[c2] = "sched_loop"
                                /\ ActiveTask(c1) # 0
                                /\ ActiveTask(c1) = ActiveTask(c2)
                                => ActiveAsid(c1) = ActiveAsid(c2)

UniqueASIDActiveTask == \/ ~CnP
                        \/ \A c1, c2 \in DOMAIN active_mm :
                                /\ (c1 # c2)
                                /\ ActiveTask(c1) # 0
                                /\ ActiveTask(c2) # 0
                                /\ ActiveTask(c1) # ActiveTask(c2)

TLBEmptyTask(task) ==   \A t \in tlb :
                                ~(t.task = task /\ t.asid = mm_context_id[task].asid)
TLBEmptyInvalPTE ==     \A c \in CPUS : LET t == ActiveTask(c) IN
                                t # 0 /\ pte[t] = "inval" => TLBEmptyTask(t)


Perms == Permutations(CPUS) \cup Permutations(TASKS)


Constr == asid_generation <= GENERATIONS

VARIABLES asid_, cpu_, cpus_, asid, newasid, cpu, cpus, task_, asid_n, 
          newasid_, generation, old, task_c, asid_c, old_active_asid, task, 
          asid_t

global_vars == << asid_map, active_asids, ret_new_context, tlb_flush_pending, reserved_asids, cur_idx, mm_context_id, cpu_asid_lock, tlb, ret_check_update_reserved_asid, asid_generation, active_mm, pte >>
local_vars == << task_, asid_, newasid_, asid, cpu_, generation, cpus_, asid_n, asid_c, newasid, task, old, cpus, cpu, old_active_asid, asid_t, task_c >>
vars == << global_vars, local_vars, pc, stack >>

ProcSet == {TTU} \cup (CPUS)

Init == (* Global variables *)
        /\ tlb = {}
        /\ pte = [t \in TASKS |-> "mapped"]
        /\ active_mm = [c \in CPUS |-> [task |-> 0, asid |-> 0]]
        /\ cpu_asid_lock = FALSE
        /\ asid_generation = 1
        /\ asid_map = [a \in 0..ASIDS-1 |-> FALSE]
        /\ active_asids = [c \in CPUS |-> [asid |-> 0, generation |-> 0]]
        /\ reserved_asids = [c \in CPUS |-> [asid |-> 0, generation |-> 0]]
        /\ tlb_flush_pending = [c \in CPUS |-> FALSE]
        /\ cur_idx = 1
        /\ mm_context_id = [t \in TASKS |-> [asid |-> 0, generation |-> 0]]
        /\ ret_check_update_reserved_asid = [i \in CPUS |-> FALSE]
        /\ ret_new_context = [c \in CPUS |-> [asid |-> 0, generation |-> 0]]
        (* Procedure flush_context *)
        /\ asid_ = [ self \in ProcSet |-> defaultInitValue]
        /\ cpu_ = [ self \in ProcSet |-> defaultInitValue]
        /\ cpus_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure check_update_reserved_asid *)
        /\ asid = [ self \in ProcSet |-> defaultInitValue]
        /\ newasid = [ self \in ProcSet |-> defaultInitValue]
        /\ cpu = [ self \in ProcSet |-> defaultInitValue]
        /\ cpus = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure new_context *)
        /\ task_ = [ self \in ProcSet |-> 0]
        /\ asid_n = [ self \in ProcSet |-> defaultInitValue]
        /\ newasid_ = [ self \in ProcSet |-> defaultInitValue]
        /\ generation = [ self \in ProcSet |-> defaultInitValue]
        /\ old = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure check_and_switch_context *)
        /\ task_c = [ self \in ProcSet |-> 0]
        /\ asid_c = [ self \in ProcSet |-> defaultInitValue]
        /\ old_active_asid = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure try_to_unmap *)
        /\ task = [ self \in ProcSet |-> defaultInitValue]
        /\ asid_t = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self = TTU -> "ttu_"
                                        [] self \in CPUS -> "sched_loop"]

flush_context_(self) == /\ pc[self] = "flush_context_"
                        /\ asid_map' = [i \in 0..ASIDS-1 |-> FALSE]
                        /\ cpus_' = [cpus_ EXCEPT ![self] = CPUS]
                        /\ pc' = [pc EXCEPT ![self] = "flush_context_for_each_cpu"]
                        /\ UNCHANGED << tlb, pte, active_mm, cpu_asid_lock, 
                                        asid_generation, active_asids, 
                                        reserved_asids, tlb_flush_pending, 
                                        cur_idx, mm_context_id, 
                                        ret_check_update_reserved_asid, 
                                        ret_new_context, stack, asid_, cpu_, 
                                        asid, newasid, cpu, cpus, task_, 
                                        asid_n, newasid_, generation, old, 
                                        task_c, asid_c, old_active_asid, task, 
                                        asid_t >>

flush_context_for_each_cpu(self) == /\ pc[self] = "flush_context_for_each_cpu"
                                    /\ IF cpus_[self] # {}
                                          THEN /\ cpu_' = [cpu_ EXCEPT ![self] = AnyElem(cpus_[self])]
                                               /\ asid_' = [asid_ EXCEPT ![self] = active_asids[cpu_'[self]]]
                                               /\ active_asids' = [active_asids EXCEPT ![cpu_'[self]] = NULL_ASID]
                                               /\ pc' = [pc EXCEPT ![self] = "flush_context_asid0_check"]
                                               /\ UNCHANGED << tlb_flush_pending, 
                                                               stack, cpus_ >>
                                          ELSE /\ tlb_flush_pending' = [i \in CPUS |-> TRUE]
                                               /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                               /\ asid_' = [asid_ EXCEPT ![self] = Head(stack[self]).asid_]
                                               /\ cpu_' = [cpu_ EXCEPT ![self] = Head(stack[self]).cpu_]
                                               /\ cpus_' = [cpus_ EXCEPT ![self] = Head(stack[self]).cpus_]
                                               /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                               /\ UNCHANGED active_asids
                                    /\ UNCHANGED << tlb, pte, active_mm, 
                                                    cpu_asid_lock, 
                                                    asid_generation, asid_map, 
                                                    reserved_asids, cur_idx, 
                                                    mm_context_id, 
                                                    ret_check_update_reserved_asid, 
                                                    ret_new_context, asid, 
                                                    newasid, cpu, cpus, task_, 
                                                    asid_n, newasid_, 
                                                    generation, old, task_c, 
                                                    asid_c, old_active_asid, 
                                                    task, asid_t >>

flush_context_asid0_check(self) == /\ pc[self] = "flush_context_asid0_check"
                                   /\ IF asid_[self] = NULL_ASID
                                         THEN /\ asid_' = [asid_ EXCEPT ![self] = reserved_asids[cpu_[self]]]
                                         ELSE /\ TRUE
                                              /\ asid_' = asid_
                                   /\ asid_map' = [asid_map EXCEPT ![asid_'[self].asid] = TRUE]
                                   /\ reserved_asids' = [reserved_asids EXCEPT ![cpu_[self]] = asid_'[self]]
                                   /\ cpus_' = [cpus_ EXCEPT ![self] = cpus_[self] \ {cpu_[self]}]
                                   /\ pc' = [pc EXCEPT ![self] = "flush_context_for_each_cpu"]
                                   /\ UNCHANGED << tlb, pte, active_mm, 
                                                   cpu_asid_lock, 
                                                   asid_generation, 
                                                   active_asids, 
                                                   tlb_flush_pending, cur_idx, 
                                                   mm_context_id, 
                                                   ret_check_update_reserved_asid, 
                                                   ret_new_context, stack, 
                                                   cpu_, asid, newasid, cpu, 
                                                   cpus, task_, asid_n, 
                                                   newasid_, generation, old, 
                                                   task_c, asid_c, 
                                                   old_active_asid, task, 
                                                   asid_t >>

flush_context(self) == flush_context_(self)
                          \/ flush_context_for_each_cpu(self)
                          \/ flush_context_asid0_check(self)

check_update_reserved_asid_(self) == /\ pc[self] = "check_update_reserved_asid_"
                                     /\ ret_check_update_reserved_asid' = [ret_check_update_reserved_asid EXCEPT ![self] = FALSE]
                                     /\ cpus' = [cpus EXCEPT ![self] = CPUS]
                                     /\ pc' = [pc EXCEPT ![self] = "check_update_reserved_asid_for_each_cpu"]
                                     /\ UNCHANGED << tlb, pte, active_mm, 
                                                     cpu_asid_lock, 
                                                     asid_generation, asid_map, 
                                                     active_asids, 
                                                     reserved_asids, 
                                                     tlb_flush_pending, 
                                                     cur_idx, mm_context_id, 
                                                     ret_new_context, stack, 
                                                     asid_, cpu_, cpus_, asid, 
                                                     newasid, cpu, task_, 
                                                     asid_n, newasid_, 
                                                     generation, old, task_c, 
                                                     asid_c, old_active_asid, 
                                                     task, asid_t >>

check_update_reserved_asid_for_each_cpu(self) == /\ pc[self] = "check_update_reserved_asid_for_each_cpu"
                                                 /\ IF cpus[self] # {}
                                                       THEN /\ cpu' = [cpu EXCEPT ![self] = AnyElem(cpus[self])]
                                                            /\ IF reserved_asids[cpu'[self]] = asid[self]
                                                                  THEN /\ ret_check_update_reserved_asid' = [ret_check_update_reserved_asid EXCEPT ![self] = TRUE]
                                                                       /\ reserved_asids' = [reserved_asids EXCEPT ![cpu'[self]] = newasid[self]]
                                                                  ELSE /\ TRUE
                                                                       /\ UNCHANGED << reserved_asids, 
                                                                                       ret_check_update_reserved_asid >>
                                                            /\ cpus' = [cpus EXCEPT ![self] = cpus[self] \ {cpu'[self]}]
                                                            /\ pc' = [pc EXCEPT ![self] = "check_update_reserved_asid_for_each_cpu"]
                                                            /\ UNCHANGED << stack, 
                                                                            asid, 
                                                                            newasid >>
                                                       ELSE /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                                            /\ cpu' = [cpu EXCEPT ![self] = Head(stack[self]).cpu]
                                                            /\ cpus' = [cpus EXCEPT ![self] = Head(stack[self]).cpus]
                                                            /\ asid' = [asid EXCEPT ![self] = Head(stack[self]).asid]
                                                            /\ newasid' = [newasid EXCEPT ![self] = Head(stack[self]).newasid]
                                                            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                                            /\ UNCHANGED << reserved_asids, 
                                                                            ret_check_update_reserved_asid >>
                                                 /\ UNCHANGED << tlb, pte, 
                                                                 active_mm, 
                                                                 cpu_asid_lock, 
                                                                 asid_generation, 
                                                                 asid_map, 
                                                                 active_asids, 
                                                                 tlb_flush_pending, 
                                                                 cur_idx, 
                                                                 mm_context_id, 
                                                                 ret_new_context, 
                                                                 asid_, cpu_, 
                                                                 cpus_, task_, 
                                                                 asid_n, 
                                                                 newasid_, 
                                                                 generation, 
                                                                 old, task_c, 
                                                                 asid_c, 
                                                                 old_active_asid, 
                                                                 task, asid_t >>

check_update_reserved_asid(self) == check_update_reserved_asid_(self)
                                       \/ check_update_reserved_asid_for_each_cpu(self)

new_context_(self) == /\ pc[self] = "new_context_"
                      /\ asid_n' = [asid_n EXCEPT ![self] = mm_context_id[task_[self]]]
                      /\ generation' = [generation EXCEPT ![self] = asid_generation]
                      /\ IF asid_n'[self] # NULL_ASID
                            THEN /\ newasid_' = [newasid_ EXCEPT ![self] = MakeAsid(asid_n'[self].asid, generation'[self])]
                                 /\ /\ asid' = [asid EXCEPT ![self] = asid_n'[self]]
                                    /\ newasid' = [newasid EXCEPT ![self] = newasid_'[self]]
                                    /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "check_update_reserved_asid",
                                                                             pc        |->  "new_context_ret_from_check_update_reserved_asid",
                                                                             cpu       |->  cpu[self],
                                                                             cpus      |->  cpus[self],
                                                                             asid      |->  asid[self],
                                                                             newasid   |->  newasid[self] ] >>
                                                                         \o stack[self]]
                                 /\ cpu' = [cpu EXCEPT ![self] = defaultInitValue]
                                 /\ cpus' = [cpus EXCEPT ![self] = defaultInitValue]
                                 /\ pc' = [pc EXCEPT ![self] = "check_update_reserved_asid_"]
                            ELSE /\ pc' = [pc EXCEPT ![self] = "new_context_allocate_free_asid"]
                                 /\ UNCHANGED << stack, asid, newasid, cpu, 
                                                 cpus, newasid_ >>
                      /\ UNCHANGED << tlb, pte, active_mm, cpu_asid_lock, 
                                      asid_generation, asid_map, active_asids, 
                                      reserved_asids, tlb_flush_pending, 
                                      cur_idx, mm_context_id, 
                                      ret_check_update_reserved_asid, 
                                      ret_new_context, asid_, cpu_, cpus_, 
                                      task_, old, task_c, asid_c, 
                                      old_active_asid, task, asid_t >>

new_context_ret_from_check_update_reserved_asid(self) == /\ pc[self] = "new_context_ret_from_check_update_reserved_asid"
                                                         /\ IF ret_check_update_reserved_asid[self]
                                                               THEN /\ ret_new_context' = [ret_new_context EXCEPT ![self] = newasid_[self]]
                                                                    /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                                                    /\ asid_n' = [asid_n EXCEPT ![self] = Head(stack[self]).asid_n]
                                                                    /\ newasid_' = [newasid_ EXCEPT ![self] = Head(stack[self]).newasid_]
                                                                    /\ generation' = [generation EXCEPT ![self] = Head(stack[self]).generation]
                                                                    /\ old' = [old EXCEPT ![self] = Head(stack[self]).old]
                                                                    /\ task_' = [task_ EXCEPT ![self] = Head(stack[self]).task_]
                                                                    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                                               ELSE /\ pc' = [pc EXCEPT ![self] = "new_context_ret_from_check_update_reserved_asid_end"]
                                                                    /\ UNCHANGED << ret_new_context, 
                                                                                    stack, 
                                                                                    task_, 
                                                                                    asid_n, 
                                                                                    newasid_, 
                                                                                    generation, 
                                                                                    old >>
                                                         /\ UNCHANGED << tlb, 
                                                                         pte, 
                                                                         active_mm, 
                                                                         cpu_asid_lock, 
                                                                         asid_generation, 
                                                                         asid_map, 
                                                                         active_asids, 
                                                                         reserved_asids, 
                                                                         tlb_flush_pending, 
                                                                         cur_idx, 
                                                                         mm_context_id, 
                                                                         ret_check_update_reserved_asid, 
                                                                         asid_, 
                                                                         cpu_, 
                                                                         cpus_, 
                                                                         asid, 
                                                                         newasid, 
                                                                         cpu, 
                                                                         cpus, 
                                                                         task_c, 
                                                                         asid_c, 
                                                                         old_active_asid, 
                                                                         task, 
                                                                         asid_t >>

new_context_ret_from_check_update_reserved_asid_end(self) == /\ pc[self] = "new_context_ret_from_check_update_reserved_asid_end"
                                                             /\ old' = [old EXCEPT ![self] = asid_map[asid_n[self].asid]]
                                                             /\ asid_map' = [asid_map EXCEPT ![asid_n[self].asid] = TRUE]
                                                             /\ IF ~old'[self]
                                                                   THEN /\ ret_new_context' = [ret_new_context EXCEPT ![self] = newasid_[self]]
                                                                        /\ pc' = [pc EXCEPT ![self] = "new_context_return"]
                                                                   ELSE /\ pc' = [pc EXCEPT ![self] = "new_context_allocate_free_asid"]
                                                                        /\ UNCHANGED ret_new_context
                                                             /\ UNCHANGED << tlb, 
                                                                             pte, 
                                                                             active_mm, 
                                                                             cpu_asid_lock, 
                                                                             asid_generation, 
                                                                             active_asids, 
                                                                             reserved_asids, 
                                                                             tlb_flush_pending, 
                                                                             cur_idx, 
                                                                             mm_context_id, 
                                                                             ret_check_update_reserved_asid, 
                                                                             stack, 
                                                                             asid_, 
                                                                             cpu_, 
                                                                             cpus_, 
                                                                             asid, 
                                                                             newasid, 
                                                                             cpu, 
                                                                             cpus, 
                                                                             task_, 
                                                                             asid_n, 
                                                                             newasid_, 
                                                                             generation, 
                                                                             task_c, 
                                                                             asid_c, 
                                                                             old_active_asid, 
                                                                             task, 
                                                                             asid_t >>

new_context_return(self) == /\ pc[self] = "new_context_return"
                            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                            /\ asid_n' = [asid_n EXCEPT ![self] = Head(stack[self]).asid_n]
                            /\ newasid_' = [newasid_ EXCEPT ![self] = Head(stack[self]).newasid_]
                            /\ generation' = [generation EXCEPT ![self] = Head(stack[self]).generation]
                            /\ old' = [old EXCEPT ![self] = Head(stack[self]).old]
                            /\ task_' = [task_ EXCEPT ![self] = Head(stack[self]).task_]
                            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                            /\ UNCHANGED << tlb, pte, active_mm, cpu_asid_lock, 
                                            asid_generation, asid_map, 
                                            active_asids, reserved_asids, 
                                            tlb_flush_pending, cur_idx, 
                                            mm_context_id, 
                                            ret_check_update_reserved_asid, 
                                            ret_new_context, asid_, cpu_, 
                                            cpus_, asid, newasid, cpu, cpus, 
                                            task_c, asid_c, old_active_asid, 
                                            task, asid_t >>

new_context_allocate_free_asid(self) == /\ pc[self] = "new_context_allocate_free_asid"
                                        /\ IF EmptySlots(asid_map, cur_idx)
                                              THEN /\ asid_n' = [asid_n EXCEPT ![self].asid = FindEmptySlot(asid_map, cur_idx)]
                                                   /\ pc' = [pc EXCEPT ![self] = "set_asid"]
                                              ELSE /\ pc' = [pc EXCEPT ![self] = "new_context_out_of_asids"]
                                                   /\ UNCHANGED asid_n
                                        /\ UNCHANGED << tlb, pte, active_mm, 
                                                        cpu_asid_lock, 
                                                        asid_generation, 
                                                        asid_map, active_asids, 
                                                        reserved_asids, 
                                                        tlb_flush_pending, 
                                                        cur_idx, mm_context_id, 
                                                        ret_check_update_reserved_asid, 
                                                        ret_new_context, stack, 
                                                        asid_, cpu_, cpus_, 
                                                        asid, newasid, cpu, 
                                                        cpus, task_, newasid_, 
                                                        generation, old, 
                                                        task_c, asid_c, 
                                                        old_active_asid, task, 
                                                        asid_t >>

new_context_out_of_asids(self) == /\ pc[self] = "new_context_out_of_asids"
                                  /\ asid_generation' = asid_generation + 1
                                  /\ generation' = [generation EXCEPT ![self] = asid_generation']
                                  /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "flush_context",
                                                                           pc        |->  "new_context_ret_flush_context",
                                                                           asid_     |->  asid_[self],
                                                                           cpu_      |->  cpu_[self],
                                                                           cpus_     |->  cpus_[self] ] >>
                                                                       \o stack[self]]
                                  /\ asid_' = [asid_ EXCEPT ![self] = defaultInitValue]
                                  /\ cpu_' = [cpu_ EXCEPT ![self] = defaultInitValue]
                                  /\ cpus_' = [cpus_ EXCEPT ![self] = defaultInitValue]
                                  /\ pc' = [pc EXCEPT ![self] = "flush_context_"]
                                  /\ UNCHANGED << tlb, pte, active_mm, 
                                                  cpu_asid_lock, asid_map, 
                                                  active_asids, reserved_asids, 
                                                  tlb_flush_pending, cur_idx, 
                                                  mm_context_id, 
                                                  ret_check_update_reserved_asid, 
                                                  ret_new_context, asid, 
                                                  newasid, cpu, cpus, task_, 
                                                  asid_n, newasid_, old, 
                                                  task_c, asid_c, 
                                                  old_active_asid, task, 
                                                  asid_t >>

new_context_ret_flush_context(self) == /\ pc[self] = "new_context_ret_flush_context"
                                       /\ asid_n' = [asid_n EXCEPT ![self].asid = FindEmptySlot(asid_map, 1)]
                                       /\ pc' = [pc EXCEPT ![self] = "set_asid"]
                                       /\ UNCHANGED << tlb, pte, active_mm, 
                                                       cpu_asid_lock, 
                                                       asid_generation, 
                                                       asid_map, active_asids, 
                                                       reserved_asids, 
                                                       tlb_flush_pending, 
                                                       cur_idx, mm_context_id, 
                                                       ret_check_update_reserved_asid, 
                                                       ret_new_context, stack, 
                                                       asid_, cpu_, cpus_, 
                                                       asid, newasid, cpu, 
                                                       cpus, task_, newasid_, 
                                                       generation, old, task_c, 
                                                       asid_c, old_active_asid, 
                                                       task, asid_t >>

set_asid(self) == /\ pc[self] = "set_asid"
                  /\ asid_map' = [asid_map EXCEPT ![asid_n[self].asid] = TRUE]
                  /\ cur_idx' = asid_n[self].asid
                  /\ ret_new_context' = [ret_new_context EXCEPT ![self] = MakeAsid(asid_n[self].asid, generation[self])]
                  /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                  /\ asid_n' = [asid_n EXCEPT ![self] = Head(stack[self]).asid_n]
                  /\ newasid_' = [newasid_ EXCEPT ![self] = Head(stack[self]).newasid_]
                  /\ generation' = [generation EXCEPT ![self] = Head(stack[self]).generation]
                  /\ old' = [old EXCEPT ![self] = Head(stack[self]).old]
                  /\ task_' = [task_ EXCEPT ![self] = Head(stack[self]).task_]
                  /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                  /\ UNCHANGED << tlb, pte, active_mm, cpu_asid_lock, 
                                  asid_generation, active_asids, 
                                  reserved_asids, tlb_flush_pending, 
                                  mm_context_id, 
                                  ret_check_update_reserved_asid, asid_, cpu_, 
                                  cpus_, asid, newasid, cpu, cpus, task_c, 
                                  asid_c, old_active_asid, task, asid_t >>

new_context(self) == new_context_(self)
                        \/ new_context_ret_from_check_update_reserved_asid(self)
                        \/ new_context_ret_from_check_update_reserved_asid_end(self)
                        \/ new_context_return(self)
                        \/ new_context_allocate_free_asid(self)
                        \/ new_context_out_of_asids(self)
                        \/ new_context_ret_flush_context(self)
                        \/ set_asid(self)

check_and_switch_context_(self) == /\ pc[self] = "check_and_switch_context_"
                                   /\ IF CnP
                                         THEN /\ active_mm' = [active_mm EXCEPT ![self].task = 0,
                                                                                ![self].asid = ActiveAsid(self)]
                                              /\ IF 0 # 0 /\ pte[0] = "mapped"
                                                    THEN /\ tlb' = (tlb \cup {MakeTlbEntry(0, mm_context_id[0].asid, self)})
                                                    ELSE /\ TRUE
                                                         /\ tlb' = tlb
                                         ELSE /\ TRUE
                                              /\ UNCHANGED << tlb, active_mm >>
                                   /\ asid_c' = [asid_c EXCEPT ![self] = mm_context_id[task_c[self]]]
                                   /\ old_active_asid' = [old_active_asid EXCEPT ![self] = active_asids[self]]
                                   /\ pc' = [pc EXCEPT ![self] = "check_current_generation"]
                                   /\ UNCHANGED << pte, cpu_asid_lock, 
                                                   asid_generation, asid_map, 
                                                   active_asids, 
                                                   reserved_asids, 
                                                   tlb_flush_pending, cur_idx, 
                                                   mm_context_id, 
                                                   ret_check_update_reserved_asid, 
                                                   ret_new_context, stack, 
                                                   asid_, cpu_, cpus_, asid, 
                                                   newasid, cpu, cpus, task_, 
                                                   asid_n, newasid_, 
                                                   generation, old, task_c, 
                                                   task, asid_t >>

check_current_generation(self) == /\ pc[self] = "check_current_generation"
                                  /\ IF old_active_asid[self] # NULL_ASID /\ asid_c[self].generation = asid_generation
                                        THEN /\ pc' = [pc EXCEPT ![self] = "cmpxchg_active_asids"]
                                        ELSE /\ pc' = [pc EXCEPT ![self] = "slow_path"]
                                  /\ UNCHANGED << tlb, pte, active_mm, 
                                                  cpu_asid_lock, 
                                                  asid_generation, asid_map, 
                                                  active_asids, reserved_asids, 
                                                  tlb_flush_pending, cur_idx, 
                                                  mm_context_id, 
                                                  ret_check_update_reserved_asid, 
                                                  ret_new_context, stack, 
                                                  asid_, cpu_, cpus_, asid, 
                                                  newasid, cpu, cpus, task_, 
                                                  asid_n, newasid_, generation, 
                                                  old, task_c, asid_c, 
                                                  old_active_asid, task, 
                                                  asid_t >>

cmpxchg_active_asids(self) == /\ pc[self] = "cmpxchg_active_asids"
                              /\ IF (active_asids[self]) = old_active_asid[self]
                                    THEN /\ active_asids' = [active_asids EXCEPT ![self] = asid_c[self]]
                                         /\ UNCHANGED old_active_asid
                                    ELSE /\ old_active_asid' = [old_active_asid EXCEPT ![self] = active_asids[self]]
                                         /\ UNCHANGED active_asids
                              /\ pc' = [pc EXCEPT ![self] = "check_roll_over"]
                              /\ UNCHANGED << tlb, pte, active_mm, 
                                              cpu_asid_lock, asid_generation, 
                                              asid_map, reserved_asids, 
                                              tlb_flush_pending, cur_idx, 
                                              mm_context_id, 
                                              ret_check_update_reserved_asid, 
                                              ret_new_context, stack, asid_, 
                                              cpu_, cpus_, asid, newasid, cpu, 
                                              cpus, task_, asid_n, newasid_, 
                                              generation, old, task_c, asid_c, 
                                              task, asid_t >>

check_roll_over(self) == /\ pc[self] = "check_roll_over"
                         /\ IF old_active_asid[self] # NULL_ASID
                               THEN /\ pc' = [pc EXCEPT ![self] = "fast_path"]
                               ELSE /\ pc' = [pc EXCEPT ![self] = "slow_path"]
                         /\ UNCHANGED << tlb, pte, active_mm, cpu_asid_lock, 
                                         asid_generation, asid_map, 
                                         active_asids, reserved_asids, 
                                         tlb_flush_pending, cur_idx, 
                                         mm_context_id, 
                                         ret_check_update_reserved_asid, 
                                         ret_new_context, stack, asid_, cpu_, 
                                         cpus_, asid, newasid, cpu, cpus, 
                                         task_, asid_n, newasid_, generation, 
                                         old, task_c, asid_c, old_active_asid, 
                                         task, asid_t >>

slow_path(self) == /\ pc[self] = "slow_path"
                   /\ ~cpu_asid_lock
                   /\ cpu_asid_lock' = TRUE
                   /\ asid_c' = [asid_c EXCEPT ![self] = mm_context_id[task_c[self]]]
                   /\ IF asid_c'[self].generation # asid_generation
                         THEN /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "new_context",
                                                                          pc        |->  "check_and_switch_context_ret_new_context",
                                                                          asid_n    |->  asid_n[self],
                                                                          newasid_  |->  newasid_[self],
                                                                          generation |->  generation[self],
                                                                          old       |->  old[self],
                                                                          task_     |->  task_[self] ] >>
                                                                      \o stack[self]]
                                 /\ task_' = [task_ EXCEPT ![self] = task_c[self]]
                              /\ asid_n' = [asid_n EXCEPT ![self] = defaultInitValue]
                              /\ newasid_' = [newasid_ EXCEPT ![self] = defaultInitValue]
                              /\ generation' = [generation EXCEPT ![self] = defaultInitValue]
                              /\ old' = [old EXCEPT ![self] = defaultInitValue]
                              /\ pc' = [pc EXCEPT ![self] = "new_context_"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "tlb_flush_pending_"]
                              /\ UNCHANGED << stack, task_, asid_n, newasid_, 
                                              generation, old >>
                   /\ UNCHANGED << tlb, pte, active_mm, asid_generation, 
                                   asid_map, active_asids, reserved_asids, 
                                   tlb_flush_pending, cur_idx, mm_context_id, 
                                   ret_check_update_reserved_asid, 
                                   ret_new_context, asid_, cpu_, cpus_, asid, 
                                   newasid, cpu, cpus, task_c, old_active_asid, 
                                   task, asid_t >>

check_and_switch_context_ret_new_context(self) == /\ pc[self] = "check_and_switch_context_ret_new_context"
                                                  /\ asid_c' = [asid_c EXCEPT ![self] = ret_new_context[self]]
                                                  /\ mm_context_id' = [mm_context_id EXCEPT ![task_c[self]] = asid_c'[self]]
                                                  /\ pc' = [pc EXCEPT ![self] = "tlb_flush_pending_"]
                                                  /\ UNCHANGED << tlb, pte, 
                                                                  active_mm, 
                                                                  cpu_asid_lock, 
                                                                  asid_generation, 
                                                                  asid_map, 
                                                                  active_asids, 
                                                                  reserved_asids, 
                                                                  tlb_flush_pending, 
                                                                  cur_idx, 
                                                                  ret_check_update_reserved_asid, 
                                                                  ret_new_context, 
                                                                  stack, asid_, 
                                                                  cpu_, cpus_, 
                                                                  asid, 
                                                                  newasid, cpu, 
                                                                  cpus, task_, 
                                                                  asid_n, 
                                                                  newasid_, 
                                                                  generation, 
                                                                  old, task_c, 
                                                                  old_active_asid, 
                                                                  task, asid_t >>

tlb_flush_pending_(self) == /\ pc[self] = "tlb_flush_pending_"
                            /\ IF tlb_flush_pending[self]
                                  THEN /\ tlb_flush_pending' = [tlb_flush_pending EXCEPT ![self] = FALSE]
                                       /\ IF CnP
                                             THEN /\ tlb' = {MakeTlbEntry(ActiveTask(c), ActiveAsid(c), c) :
                                                                  c \in {c1 \in DOMAIN active_mm : ActiveTask(c1) # 0}}
                                             ELSE /\ tlb' = {t \in tlb : t.cpu # self \/ t.task = ActiveTask(self)}
                                  ELSE /\ TRUE
                                       /\ UNCHANGED << tlb, tlb_flush_pending >>
                            /\ pc' = [pc EXCEPT ![self] = "set_active_asids"]
                            /\ UNCHANGED << pte, active_mm, cpu_asid_lock, 
                                            asid_generation, asid_map, 
                                            active_asids, reserved_asids, 
                                            cur_idx, mm_context_id, 
                                            ret_check_update_reserved_asid, 
                                            ret_new_context, stack, asid_, 
                                            cpu_, cpus_, asid, newasid, cpu, 
                                            cpus, task_, asid_n, newasid_, 
                                            generation, old, task_c, asid_c, 
                                            old_active_asid, task, asid_t >>

set_active_asids(self) == /\ pc[self] = "set_active_asids"
                          /\ active_asids' = [active_asids EXCEPT ![self] = asid_c[self]]
                          /\ cpu_asid_lock' = FALSE
                          /\ pc' = [pc EXCEPT ![self] = "fast_path"]
                          /\ UNCHANGED << tlb, pte, active_mm, asid_generation, 
                                          asid_map, reserved_asids, 
                                          tlb_flush_pending, cur_idx, 
                                          mm_context_id, 
                                          ret_check_update_reserved_asid, 
                                          ret_new_context, stack, asid_, cpu_, 
                                          cpus_, asid, newasid, cpu, cpus, 
                                          task_, asid_n, newasid_, generation, 
                                          old, task_c, asid_c, old_active_asid, 
                                          task, asid_t >>

fast_path(self) == /\ pc[self] = "fast_path"
                   /\ active_mm' = [active_mm EXCEPT ![self].task = task_c[self],
                                                     ![self].asid = asid_c[self].asid]
                   /\ IF task_c[self] # 0 /\ pte[task_c[self]] = "mapped"
                         THEN /\ tlb' = (tlb \cup {MakeTlbEntry(task_c[self], mm_context_id[task_c[self]].asid, self)})
                         ELSE /\ TRUE
                              /\ tlb' = tlb
                   /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                   /\ asid_c' = [asid_c EXCEPT ![self] = Head(stack[self]).asid_c]
                   /\ old_active_asid' = [old_active_asid EXCEPT ![self] = Head(stack[self]).old_active_asid]
                   /\ task_c' = [task_c EXCEPT ![self] = Head(stack[self]).task_c]
                   /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                   /\ UNCHANGED << pte, cpu_asid_lock, asid_generation, 
                                   asid_map, active_asids, reserved_asids, 
                                   tlb_flush_pending, cur_idx, mm_context_id, 
                                   ret_check_update_reserved_asid, 
                                   ret_new_context, asid_, cpu_, cpus_, asid, 
                                   newasid, cpu, cpus, task_, asid_n, newasid_, 
                                   generation, old, task, asid_t >>

check_and_switch_context(self) == check_and_switch_context_(self)
                                     \/ check_current_generation(self)
                                     \/ cmpxchg_active_asids(self)
                                     \/ check_roll_over(self)
                                     \/ slow_path(self)
                                     \/ check_and_switch_context_ret_new_context(self)
                                     \/ tlb_flush_pending_(self)
                                     \/ set_active_asids(self)
                                     \/ fast_path(self)

pte_clear(self) == /\ pc[self] = "pte_clear"
                   /\ pte' = [pte EXCEPT ![task[self]] = "unmapped"]
                   /\ pc' = [pc EXCEPT ![self] = "read_asid"]
                   /\ UNCHANGED << tlb, active_mm, cpu_asid_lock, 
                                   asid_generation, asid_map, active_asids, 
                                   reserved_asids, tlb_flush_pending, cur_idx, 
                                   mm_context_id, 
                                   ret_check_update_reserved_asid, 
                                   ret_new_context, stack, asid_, cpu_, cpus_, 
                                   asid, newasid, cpu, cpus, task_, asid_n, 
                                   newasid_, generation, old, task_c, asid_c, 
                                   old_active_asid, task, asid_t >>

read_asid(self) == /\ pc[self] = "read_asid"
                   /\ asid_t' = [asid_t EXCEPT ![self] = mm_context_id[task[self]].asid]
                   /\ pc' = [pc EXCEPT ![self] = "tlbi"]
                   /\ UNCHANGED << tlb, pte, active_mm, cpu_asid_lock, 
                                   asid_generation, asid_map, active_asids, 
                                   reserved_asids, tlb_flush_pending, cur_idx, 
                                   mm_context_id, 
                                   ret_check_update_reserved_asid, 
                                   ret_new_context, stack, asid_, cpu_, cpus_, 
                                   asid, newasid, cpu, cpus, task_, asid_n, 
                                   newasid_, generation, old, task_c, asid_c, 
                                   old_active_asid, task >>

tlbi(self) == /\ pc[self] = "tlbi"
              /\ tlb' = {t \in tlb : t.asid # asid_t[self]}
              /\ pc' = [pc EXCEPT ![self] = "after_tlbi"]
              /\ UNCHANGED << pte, active_mm, cpu_asid_lock, asid_generation, 
                              asid_map, active_asids, reserved_asids, 
                              tlb_flush_pending, cur_idx, mm_context_id, 
                              ret_check_update_reserved_asid, ret_new_context, 
                              stack, asid_, cpu_, cpus_, asid, newasid, cpu, 
                              cpus, task_, asid_n, newasid_, generation, old, 
                              task_c, asid_c, old_active_asid, task, asid_t >>

after_tlbi(self) == /\ pc[self] = "after_tlbi"
                    /\ pte' = [pte EXCEPT ![task[self]] = "inval"]
                    /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                    /\ asid_t' = [asid_t EXCEPT ![self] = Head(stack[self]).asid_t]
                    /\ task' = [task EXCEPT ![self] = Head(stack[self]).task]
                    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                    /\ UNCHANGED << tlb, active_mm, cpu_asid_lock, 
                                    asid_generation, asid_map, active_asids, 
                                    reserved_asids, tlb_flush_pending, cur_idx, 
                                    mm_context_id, 
                                    ret_check_update_reserved_asid, 
                                    ret_new_context, asid_, cpu_, cpus_, asid, 
                                    newasid, cpu, cpus, task_, asid_n, 
                                    newasid_, generation, old, task_c, asid_c, 
                                    old_active_asid >>

try_to_unmap(self) == pte_clear(self) \/ read_asid(self) \/ tlbi(self)
                         \/ after_tlbi(self)

ttu_ == /\ pc[TTU] = "ttu_"
        /\ \E t \in TASKS:
             /\ /\ stack' = [stack EXCEPT ![TTU] = << [ procedure |->  "try_to_unmap",
                                                        pc        |->  "ttu_",
                                                        asid_t    |->  asid_t[TTU],
                                                        task      |->  task[TTU] ] >>
                                                    \o stack[TTU]]
                /\ task' = [task EXCEPT ![TTU] = t]
             /\ asid_t' = [asid_t EXCEPT ![TTU] = defaultInitValue]
             /\ pc' = [pc EXCEPT ![TTU] = "pte_clear"]
        /\ UNCHANGED << tlb, pte, active_mm, cpu_asid_lock, asid_generation, 
                        asid_map, active_asids, reserved_asids, 
                        tlb_flush_pending, cur_idx, mm_context_id, 
                        ret_check_update_reserved_asid, ret_new_context, asid_, 
                        cpu_, cpus_, asid, newasid, cpu, cpus, task_, asid_n, 
                        newasid_, generation, old, task_c, asid_c, 
                        old_active_asid >>

ttu == ttu_

sched_loop(self) == /\ pc[self] = "sched_loop"
                    /\ \E t \in TASKS:
                         IF t # ActiveTask(self)
                            THEN /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "check_and_switch_context",
                                                                             pc        |->  "sched_loop",
                                                                             asid_c    |->  asid_c[self],
                                                                             old_active_asid |->  old_active_asid[self],
                                                                             task_c    |->  task_c[self] ] >>
                                                                         \o stack[self]]
                                    /\ task_c' = [task_c EXCEPT ![self] = t]
                                 /\ asid_c' = [asid_c EXCEPT ![self] = defaultInitValue]
                                 /\ old_active_asid' = [old_active_asid EXCEPT ![self] = defaultInitValue]
                                 /\ pc' = [pc EXCEPT ![self] = "check_and_switch_context_"]
                            ELSE /\ pc' = [pc EXCEPT ![self] = "sched_loop"]
                                 /\ UNCHANGED << stack, task_c, asid_c, 
                                                 old_active_asid >>
                    /\ UNCHANGED << tlb, pte, active_mm, cpu_asid_lock, 
                                    asid_generation, asid_map, active_asids, 
                                    reserved_asids, tlb_flush_pending, cur_idx, 
                                    mm_context_id, 
                                    ret_check_update_reserved_asid, 
                                    ret_new_context, asid_, cpu_, cpus_, asid, 
                                    newasid, cpu, cpus, task_, asid_n, 
                                    newasid_, generation, old, task, asid_t >>

sched(self) == sched_loop(self)

Next == ttu
           \/ (\E self \in ProcSet:  \/ flush_context(self)
                                     \/ check_update_reserved_asid(self)
                                     \/ new_context(self)
                                     \/ check_and_switch_context(self)
                                     \/ try_to_unmap(self))
           \/ (\E self \in CPUS: sched(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-683adfb7ed87d6f2f601f1d0e2b708b9
==============================================================================
