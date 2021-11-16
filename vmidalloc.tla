---------------------------- MODULE vmidalloc --------------------------------
\*
\* VMID allocation algorithm (as used in the arm64 Linux kernel ports)
\* together with inviariant definitions for a simplified model of the CPU TLB.
\*
\* Based on asidalloc.tla.
\*
\* See arch/arm64/kvm/vmid.c for the C implementation of the algorithm.
\*
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANT	CPUS,		\* set of available CPUs
		VMIDS,		\* number of VMIDs
		GENERATIONS,	\* number of generations
		TASKS,		\* set of context ids
		SCHED_OUT	\* special task modifying the page table

ASSUME	/\ VMIDS \in Nat \ {0}
	/\ GENERATIONS \in Nat \ {0}
	/\ Cardinality(CPUS) < VMIDS - 1

(* --algorithm vmidalloc {
variables
	\* CPU TLB and TTBR model
	tlb = {};
	active_kvm = [c \in CPUS |-> [task |-> 0, vmid |-> 0]];

	\* VMID allocation algorithm state
	cpu_vmid_lock = FALSE;
	vmid_generation = 1;
	vmid_map = [a \in 0..VMIDS-1 |-> FALSE];
	active_vmids = [c \in CPUS |-> [vmid |-> 0, generation |-> 0]];
	reserved_vmids = [c \in CPUS |-> [vmid |-> 0, generation |-> 0]];
	cur_idx = 1;

	\* OS tasks
	kvm_context_id = [t \in TASKS |-> [vmid |-> 0, generation |-> 0]];

	\* PlusCal procedure return value
	ret_check_update_reserved_vmid = [i \in CPUS |-> FALSE];
	ret_new_vmid = [c \in CPUS |-> [vmid |-> 0, generation |-> 0]]

define {
	\*
	\* Various helpers
	\*
	MakeVmid(a, g) == [vmid |-> a, generation |-> g]
	NULL_VMID == MakeVmid(0, 0)
	INVALID_VMID == MakeVmid(0, 1)

	EmptySlots(map, start) == \E idx \in start..VMIDS-1 : map[idx] = FALSE
	FindEmptySlot(map, start) ==
		CHOOSE idx \in start..VMIDS-1 : map[idx] = FALSE

	AnyElem(s) == CHOOSE e \in s : TRUE

	MakeTlbEntry(t, a, c) == [task |-> t, vmid |-> a, cpu |-> c]

	ActiveTask(cpu) == active_kvm[cpu].task
	ActiveVmid(cpu) == active_kvm[cpu].vmid

	\*
	\* Type invariants
	\*
	VmidType ==	[vmid: 0..VMIDS-1, generation: 0..GENERATIONS]
		\* VMID 0 not allowed in the TLB (reserved)
	TlbType ==	[task: TASKS, vmid: 1..VMIDS-1, cpu: CPUS]
	TTBRType ==	[task: TASKS \cup {0}, vmid: 0..VMIDS-1]
	TypeInv ==	/\ cpu_vmid_lock \in BOOLEAN
			/\ vmid_generation \in Nat \ {0}
			/\ vmid_map \in [0..VMIDS-1 -> BOOLEAN]
			/\ active_vmids \in [CPUS -> VmidType]
			/\ reserved_vmids \in [CPUS -> VmidType]
			/\ cur_idx \in 1..VMIDS-1
			/\ kvm_context_id \in [TASKS -> VmidType]
			/\ active_kvm \in [CPUS -> TTBRType]
			/\ tlb \subseteq TlbType

	\*
	\* Algorithm invariants
	\*
		\* This is possible when an old task gets a new VMID; safe as
		\* long as it is not active on a different CPU (checked below)
	SameVMIDPerTask ==	\A t1, t2 \in tlb :
					(t1.task = t2.task) => (t1.vmid = t2.vmid)
		\* Same task active on different CPUs must have the same VMID
		\* outside the context switching code
	SameVMIDActiveTask ==	\A c1, c2 \in DOMAIN active_kvm :
					/\ c1 # c2
					/\ pc[c1] = "sched_loop"
					/\ pc[c2] = "sched_loop"
					/\ ActiveTask(c1) # 0
					/\ ActiveTask(c1) = ActiveTask(c2)
					=> ActiveVmid(c1) = ActiveVmid(c2)

	\* Symmetry optimisations
	Perms == Permutations(CPUS) \cup Permutations(TASKS)

	\* We ignore generation roll-over (known to fail)
	Constr == vmid_generation <= GENERATIONS
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
	tlb := {MakeTlbEntry(ActiveTask(c), ActiveVmid(c), c) :
		     c \in {c1 \in DOMAIN active_kvm : ActiveTask(c1) # 0}};
}

macro cpu_switch_kvm(t, a) {
	active_kvm[self].task := t || active_kvm[self].vmid := a;
	\* A TLB entry can be speculatively loaded as soon as a new TTBR is set
	if (t # 0)
		tlb := tlb \cup {MakeTlbEntry(t, kvm_context_id[t].vmid, self)};
}

\*
\* VMID allocation algorithm
\*
procedure flush_context()
	variables vmid; cpu; cpus;
{
flush_context:
	vmid_map := [i \in 0..VMIDS-1 |-> FALSE];

	cpus := CPUS;
flush_context_for_each_cpu:
	while (cpus # {}) {
		cpu := AnyElem(cpus);
		vmid := active_vmids[cpu];
		active_vmids[cpu] := NULL_VMID;
flush_context_vmid0_check:
		if (vmid = NULL_VMID)
			vmid := reserved_vmids[cpu];
		vmid_map[vmid.vmid] := TRUE;
		reserved_vmids[cpu] := vmid;
		cpus := cpus \ {cpu};
	};

	flush_tlb_all();
	return;
}

procedure check_update_reserved_vmid(vmid, newvmid)
	variable cpu; cpus;
{
check_update_reserved_vmid:
	ret_check_update_reserved_vmid[self] := FALSE;
	cpus := CPUS;
check_update_reserved_vmid_for_each_cpu:
	while (cpus # {}) {
		cpu := AnyElem(cpus);
		if (reserved_vmids[cpu] = vmid) {
			ret_check_update_reserved_vmid[self] := TRUE;
			reserved_vmids[cpu] := newvmid;
		};
		cpus := cpus \ {cpu};
	};
	return;
}

procedure new_vmid(task = 0)
	variables vmid; newvmid; generation; old;
{
new_vmid:
	vmid := kvm_context_id[task];
	generation := vmid_generation;

	if (vmid # NULL_VMID) {
		newvmid := MakeVmid(vmid.vmid, generation);

		call check_update_reserved_vmid(vmid, newvmid);
new_vmid_ret_from_check_update_reserved_vmid:
		if (ret_check_update_reserved_vmid[self]) {
			ret_new_vmid[self] := newvmid;
			return;
		};
new_vmid_ret_from_check_update_reserved_vmid_end:
		old := vmid_map[vmid.vmid];
		vmid_map[vmid.vmid] := TRUE;
		if (~old) {
			ret_new_vmid[self] := newvmid;
new_vmid_return:
			return;
		};
	};

new_vmid_allocate_free_vmid:
	if (EmptySlots(vmid_map, cur_idx)) {
		vmid.vmid := FindEmptySlot(vmid_map, cur_idx);
		goto set_vmid;
	};
new_vmid_out_of_vmids:
	(* Generation roll-over not safe; commenting out
	if (vmid_generation = GENERATIONS)
		vmid_generation := 1;
	else *)
		vmid_generation := vmid_generation + 1;
	generation := vmid_generation;

	call flush_context();
new_vmid_ret_flush_context:
	\* We have more VMIDs than CPUs, so this will always succeed
	vmid.vmid := FindEmptySlot(vmid_map, 1);

set_vmid:
	vmid_map[vmid.vmid] := TRUE;
	cur_idx := vmid.vmid;
	ret_new_vmid[self] := MakeVmid(vmid.vmid, generation);
	return;
}

procedure kvm_arm_vmid_update(task = 0)
	variables vmid; old_active_vmid;
{
kvm_arm_vmid_update:
	vmid := kvm_context_id[task];

	old_active_vmid := active_vmids[self];
check_current_generation:
	if (old_active_vmid # NULL_VMID /\ vmid.generation = vmid_generation) {
cmpxchg_active_vmids:
		cmpxchg(active_vmids[self], old_active_vmid, vmid);
check_roll_over:
		if (old_active_vmid # NULL_VMID)
			goto fast_path;
	};
slow_path:
	spin_lock(cpu_vmid_lock);

	vmid := kvm_context_id[task];
	if (vmid.generation # vmid_generation) {
		call new_vmid(task);
kvm_arm_vmid_update_ret_new_vmid:
		vmid := ret_new_vmid[self];
		kvm_context_id[task] := vmid;
	};
set_active_vmids:
	active_vmids[self] := vmid;

	spin_unlock(cpu_vmid_lock);

fast_path:
	cpu_switch_kvm(task, vmid.vmid);
	return;
}

\* vCPU is scheduled out by KVM
procedure vcpu_sched_out(task)
	variables vmid;
{
clear_active_vmid:
	active_kvm[self].task := 0;
	active_vmids[self] := INVALID_VMID;
	return;
}

\* Asynchronous process for vCPU schedule out
process (sched_out = SCHED_OUT)
{
sched_out:
	while (TRUE) {
		with (t \in TASKS)
			call vcpu_sched_out(t);
	}
}

\* About to run a Guest VM
process (sched \in CPUS)
{
sched_loop:
	while (TRUE) {
		with (t \in TASKS) {
			if (t # ActiveTask(self))
				call kvm_arm_vmid_update(t);
		}
	}
}
} *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-f21ad0e8c89501fb06f50a5b8b5a9b1f
\* Label flush_context of procedure flush_context at line 142 col 9 changed to flush_context_
\* Label check_update_reserved_vmid of procedure check_update_reserved_vmid at line 166 col 9 changed to check_update_reserved_vmid_
\* Label new_vmid of procedure new_vmid at line 184 col 9 changed to new_vmid_
\* Label kvm_arm_vmid_update of procedure kvm_arm_vmid_update at line 235 col 9 changed to kvm_arm_vmid_update_
\* Label sched_out of process sched_out at line 280 col 9 changed to sched_out_
\* Procedure variable vmid of procedure flush_context at line 139 col 19 changed to vmid_
\* Procedure variable cpu of procedure flush_context at line 139 col 25 changed to cpu_
\* Procedure variable cpus of procedure flush_context at line 139 col 30 changed to cpus_
\* Procedure variable vmid of procedure new_vmid at line 181 col 19 changed to vmid_n
\* Procedure variable newvmid of procedure new_vmid at line 181 col 25 changed to newvmid_
\* Procedure variable vmid of procedure kvm_arm_vmid_update at line 232 col 19 changed to vmid_k
\* Procedure variable vmid of procedure vcpu_sched_out at line 268 col 19 changed to vmid_v
\* Parameter task of procedure new_vmid at line 180 col 20 changed to task_
\* Parameter task of procedure kvm_arm_vmid_update at line 231 col 31 changed to task_k
CONSTANT defaultInitValue
VARIABLES tlb, active_kvm, cpu_vmid_lock, vmid_generation, vmid_map, 
          active_vmids, reserved_vmids, cur_idx, kvm_context_id, 
          ret_check_update_reserved_vmid, ret_new_vmid, pc, stack

(* define statement *)
MakeVmid(a, g) == [vmid |-> a, generation |-> g]
NULL_VMID == MakeVmid(0, 0)
INVALID_VMID == MakeVmid(0, 1)

EmptySlots(map, start) == \E idx \in start..VMIDS-1 : map[idx] = FALSE
FindEmptySlot(map, start) ==
        CHOOSE idx \in start..VMIDS-1 : map[idx] = FALSE

AnyElem(s) == CHOOSE e \in s : TRUE

MakeTlbEntry(t, a, c) == [task |-> t, vmid |-> a, cpu |-> c]

ActiveTask(cpu) == active_kvm[cpu].task
ActiveVmid(cpu) == active_kvm[cpu].vmid




VmidType ==     [vmid: 0..VMIDS-1, generation: 0..GENERATIONS]

TlbType ==      [task: TASKS, vmid: 1..VMIDS-1, cpu: CPUS]
TTBRType ==     [task: TASKS \cup {0}, vmid: 0..VMIDS-1]
TypeInv ==      /\ cpu_vmid_lock \in BOOLEAN
                /\ vmid_generation \in Nat \ {0}
                /\ vmid_map \in [0..VMIDS-1 -> BOOLEAN]
                /\ active_vmids \in [CPUS -> VmidType]
                /\ reserved_vmids \in [CPUS -> VmidType]
                /\ cur_idx \in 1..VMIDS-1
                /\ kvm_context_id \in [TASKS -> VmidType]
                /\ active_kvm \in [CPUS -> TTBRType]
                /\ tlb \subseteq TlbType






SameVMIDPerTask ==      \A t1, t2 \in tlb :
                                (t1.task = t2.task) => (t1.vmid = t2.vmid)


SameVMIDActiveTask ==   \A c1, c2 \in DOMAIN active_kvm :
                                /\ c1 # c2
                                /\ pc[c1] = "sched_loop"
                                /\ pc[c2] = "sched_loop"
                                /\ ActiveTask(c1) # 0
                                /\ ActiveTask(c1) = ActiveTask(c2)
                                => ActiveVmid(c1) = ActiveVmid(c2)


Perms == Permutations(CPUS) \cup Permutations(TASKS)


Constr == vmid_generation <= GENERATIONS

VARIABLES vmid_, cpu_, cpus_, vmid, newvmid, cpu, cpus, task_, vmid_n, 
          newvmid_, generation, old, task_k, vmid_k, old_active_vmid, task, 
          vmid_v

global_vars == << vmid_generation, active_vmids, cpu_vmid_lock, reserved_vmids, cur_idx, tlb, ret_new_vmid, kvm_context_id, ret_check_update_reserved_vmid, active_kvm, vmid_map >>
local_vars == << vmid_v, task_, vmid_k, cpu_, generation, cpus_, vmid, vmid_, newvmid_, vmid_n, task_k, task, old, cpus, cpu, newvmid, old_active_vmid >>
vars == << global_vars, local_vars, pc, stack >>

ProcSet == {SCHED_OUT} \cup (CPUS)

Init == (* Global variables *)
        /\ tlb = {}
        /\ active_kvm = [c \in CPUS |-> [task |-> 0, vmid |-> 0]]
        /\ cpu_vmid_lock = FALSE
        /\ vmid_generation = 1
        /\ vmid_map = [a \in 0..VMIDS-1 |-> FALSE]
        /\ active_vmids = [c \in CPUS |-> [vmid |-> 0, generation |-> 0]]
        /\ reserved_vmids = [c \in CPUS |-> [vmid |-> 0, generation |-> 0]]
        /\ cur_idx = 1
        /\ kvm_context_id = [t \in TASKS |-> [vmid |-> 0, generation |-> 0]]
        /\ ret_check_update_reserved_vmid = [i \in CPUS |-> FALSE]
        /\ ret_new_vmid = [c \in CPUS |-> [vmid |-> 0, generation |-> 0]]
        (* Procedure flush_context *)
        /\ vmid_ = [ self \in ProcSet |-> defaultInitValue]
        /\ cpu_ = [ self \in ProcSet |-> defaultInitValue]
        /\ cpus_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure check_update_reserved_vmid *)
        /\ vmid = [ self \in ProcSet |-> defaultInitValue]
        /\ newvmid = [ self \in ProcSet |-> defaultInitValue]
        /\ cpu = [ self \in ProcSet |-> defaultInitValue]
        /\ cpus = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure new_vmid *)
        /\ task_ = [ self \in ProcSet |-> 0]
        /\ vmid_n = [ self \in ProcSet |-> defaultInitValue]
        /\ newvmid_ = [ self \in ProcSet |-> defaultInitValue]
        /\ generation = [ self \in ProcSet |-> defaultInitValue]
        /\ old = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure kvm_arm_vmid_update *)
        /\ task_k = [ self \in ProcSet |-> 0]
        /\ vmid_k = [ self \in ProcSet |-> defaultInitValue]
        /\ old_active_vmid = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure vcpu_sched_out *)
        /\ task = [ self \in ProcSet |-> defaultInitValue]
        /\ vmid_v = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self = SCHED_OUT -> "sched_out_"
                                        [] self \in CPUS -> "sched_loop"]

flush_context_(self) == /\ pc[self] = "flush_context_"
                        /\ vmid_map' = [i \in 0..VMIDS-1 |-> FALSE]
                        /\ cpus_' = [cpus_ EXCEPT ![self] = CPUS]
                        /\ pc' = [pc EXCEPT ![self] = "flush_context_for_each_cpu"]
                        /\ UNCHANGED << tlb, active_kvm, cpu_vmid_lock, 
                                        vmid_generation, active_vmids, 
                                        reserved_vmids, cur_idx, 
                                        kvm_context_id, 
                                        ret_check_update_reserved_vmid, 
                                        ret_new_vmid, stack, vmid_, cpu_, vmid, 
                                        newvmid, cpu, cpus, task_, vmid_n, 
                                        newvmid_, generation, old, task_k, 
                                        vmid_k, old_active_vmid, task, vmid_v >>

flush_context_for_each_cpu(self) == /\ pc[self] = "flush_context_for_each_cpu"
                                    /\ IF cpus_[self] # {}
                                          THEN /\ cpu_' = [cpu_ EXCEPT ![self] = AnyElem(cpus_[self])]
                                               /\ vmid_' = [vmid_ EXCEPT ![self] = active_vmids[cpu_'[self]]]
                                               /\ active_vmids' = [active_vmids EXCEPT ![cpu_'[self]] = NULL_VMID]
                                               /\ pc' = [pc EXCEPT ![self] = "flush_context_vmid0_check"]
                                               /\ UNCHANGED << tlb, stack, 
                                                               cpus_ >>
                                          ELSE /\ tlb' = {MakeTlbEntry(ActiveTask(c), ActiveVmid(c), c) :
                                                               c \in {c1 \in DOMAIN active_kvm : ActiveTask(c1) # 0}}
                                               /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                               /\ vmid_' = [vmid_ EXCEPT ![self] = Head(stack[self]).vmid_]
                                               /\ cpu_' = [cpu_ EXCEPT ![self] = Head(stack[self]).cpu_]
                                               /\ cpus_' = [cpus_ EXCEPT ![self] = Head(stack[self]).cpus_]
                                               /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                               /\ UNCHANGED active_vmids
                                    /\ UNCHANGED << active_kvm, cpu_vmid_lock, 
                                                    vmid_generation, vmid_map, 
                                                    reserved_vmids, cur_idx, 
                                                    kvm_context_id, 
                                                    ret_check_update_reserved_vmid, 
                                                    ret_new_vmid, vmid, 
                                                    newvmid, cpu, cpus, task_, 
                                                    vmid_n, newvmid_, 
                                                    generation, old, task_k, 
                                                    vmid_k, old_active_vmid, 
                                                    task, vmid_v >>

flush_context_vmid0_check(self) == /\ pc[self] = "flush_context_vmid0_check"
                                   /\ IF vmid_[self] = NULL_VMID
                                         THEN /\ vmid_' = [vmid_ EXCEPT ![self] = reserved_vmids[cpu_[self]]]
                                         ELSE /\ TRUE
                                              /\ vmid_' = vmid_
                                   /\ vmid_map' = [vmid_map EXCEPT ![vmid_'[self].vmid] = TRUE]
                                   /\ reserved_vmids' = [reserved_vmids EXCEPT ![cpu_[self]] = vmid_'[self]]
                                   /\ cpus_' = [cpus_ EXCEPT ![self] = cpus_[self] \ {cpu_[self]}]
                                   /\ pc' = [pc EXCEPT ![self] = "flush_context_for_each_cpu"]
                                   /\ UNCHANGED << tlb, active_kvm, 
                                                   cpu_vmid_lock, 
                                                   vmid_generation, 
                                                   active_vmids, cur_idx, 
                                                   kvm_context_id, 
                                                   ret_check_update_reserved_vmid, 
                                                   ret_new_vmid, stack, cpu_, 
                                                   vmid, newvmid, cpu, cpus, 
                                                   task_, vmid_n, newvmid_, 
                                                   generation, old, task_k, 
                                                   vmid_k, old_active_vmid, 
                                                   task, vmid_v >>

flush_context(self) == flush_context_(self)
                          \/ flush_context_for_each_cpu(self)
                          \/ flush_context_vmid0_check(self)

check_update_reserved_vmid_(self) == /\ pc[self] = "check_update_reserved_vmid_"
                                     /\ ret_check_update_reserved_vmid' = [ret_check_update_reserved_vmid EXCEPT ![self] = FALSE]
                                     /\ cpus' = [cpus EXCEPT ![self] = CPUS]
                                     /\ pc' = [pc EXCEPT ![self] = "check_update_reserved_vmid_for_each_cpu"]
                                     /\ UNCHANGED << tlb, active_kvm, 
                                                     cpu_vmid_lock, 
                                                     vmid_generation, vmid_map, 
                                                     active_vmids, 
                                                     reserved_vmids, cur_idx, 
                                                     kvm_context_id, 
                                                     ret_new_vmid, stack, 
                                                     vmid_, cpu_, cpus_, vmid, 
                                                     newvmid, cpu, task_, 
                                                     vmid_n, newvmid_, 
                                                     generation, old, task_k, 
                                                     vmid_k, old_active_vmid, 
                                                     task, vmid_v >>

check_update_reserved_vmid_for_each_cpu(self) == /\ pc[self] = "check_update_reserved_vmid_for_each_cpu"
                                                 /\ IF cpus[self] # {}
                                                       THEN /\ cpu' = [cpu EXCEPT ![self] = AnyElem(cpus[self])]
                                                            /\ IF reserved_vmids[cpu'[self]] = vmid[self]
                                                                  THEN /\ ret_check_update_reserved_vmid' = [ret_check_update_reserved_vmid EXCEPT ![self] = TRUE]
                                                                       /\ reserved_vmids' = [reserved_vmids EXCEPT ![cpu'[self]] = newvmid[self]]
                                                                  ELSE /\ TRUE
                                                                       /\ UNCHANGED << reserved_vmids, 
                                                                                       ret_check_update_reserved_vmid >>
                                                            /\ cpus' = [cpus EXCEPT ![self] = cpus[self] \ {cpu'[self]}]
                                                            /\ pc' = [pc EXCEPT ![self] = "check_update_reserved_vmid_for_each_cpu"]
                                                            /\ UNCHANGED << stack, 
                                                                            vmid, 
                                                                            newvmid >>
                                                       ELSE /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                                            /\ cpu' = [cpu EXCEPT ![self] = Head(stack[self]).cpu]
                                                            /\ cpus' = [cpus EXCEPT ![self] = Head(stack[self]).cpus]
                                                            /\ vmid' = [vmid EXCEPT ![self] = Head(stack[self]).vmid]
                                                            /\ newvmid' = [newvmid EXCEPT ![self] = Head(stack[self]).newvmid]
                                                            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                                            /\ UNCHANGED << reserved_vmids, 
                                                                            ret_check_update_reserved_vmid >>
                                                 /\ UNCHANGED << tlb, 
                                                                 active_kvm, 
                                                                 cpu_vmid_lock, 
                                                                 vmid_generation, 
                                                                 vmid_map, 
                                                                 active_vmids, 
                                                                 cur_idx, 
                                                                 kvm_context_id, 
                                                                 ret_new_vmid, 
                                                                 vmid_, cpu_, 
                                                                 cpus_, task_, 
                                                                 vmid_n, 
                                                                 newvmid_, 
                                                                 generation, 
                                                                 old, task_k, 
                                                                 vmid_k, 
                                                                 old_active_vmid, 
                                                                 task, vmid_v >>

check_update_reserved_vmid(self) == check_update_reserved_vmid_(self)
                                       \/ check_update_reserved_vmid_for_each_cpu(self)

new_vmid_(self) == /\ pc[self] = "new_vmid_"
                   /\ vmid_n' = [vmid_n EXCEPT ![self] = kvm_context_id[task_[self]]]
                   /\ generation' = [generation EXCEPT ![self] = vmid_generation]
                   /\ IF vmid_n'[self] # NULL_VMID
                         THEN /\ newvmid_' = [newvmid_ EXCEPT ![self] = MakeVmid(vmid_n'[self].vmid, generation'[self])]
                              /\ /\ newvmid' = [newvmid EXCEPT ![self] = newvmid_'[self]]
                                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "check_update_reserved_vmid",
                                                                          pc        |->  "new_vmid_ret_from_check_update_reserved_vmid",
                                                                          cpu       |->  cpu[self],
                                                                          cpus      |->  cpus[self],
                                                                          vmid      |->  vmid[self],
                                                                          newvmid   |->  newvmid[self] ] >>
                                                                      \o stack[self]]
                                 /\ vmid' = [vmid EXCEPT ![self] = vmid_n'[self]]
                              /\ cpu' = [cpu EXCEPT ![self] = defaultInitValue]
                              /\ cpus' = [cpus EXCEPT ![self] = defaultInitValue]
                              /\ pc' = [pc EXCEPT ![self] = "check_update_reserved_vmid_"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "new_vmid_allocate_free_vmid"]
                              /\ UNCHANGED << stack, vmid, newvmid, cpu, cpus, 
                                              newvmid_ >>
                   /\ UNCHANGED << tlb, active_kvm, cpu_vmid_lock, 
                                   vmid_generation, vmid_map, active_vmids, 
                                   reserved_vmids, cur_idx, kvm_context_id, 
                                   ret_check_update_reserved_vmid, 
                                   ret_new_vmid, vmid_, cpu_, cpus_, task_, 
                                   old, task_k, vmid_k, old_active_vmid, task, 
                                   vmid_v >>

new_vmid_ret_from_check_update_reserved_vmid(self) == /\ pc[self] = "new_vmid_ret_from_check_update_reserved_vmid"
                                                      /\ IF ret_check_update_reserved_vmid[self]
                                                            THEN /\ ret_new_vmid' = [ret_new_vmid EXCEPT ![self] = newvmid_[self]]
                                                                 /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                                                 /\ vmid_n' = [vmid_n EXCEPT ![self] = Head(stack[self]).vmid_n]
                                                                 /\ newvmid_' = [newvmid_ EXCEPT ![self] = Head(stack[self]).newvmid_]
                                                                 /\ generation' = [generation EXCEPT ![self] = Head(stack[self]).generation]
                                                                 /\ old' = [old EXCEPT ![self] = Head(stack[self]).old]
                                                                 /\ task_' = [task_ EXCEPT ![self] = Head(stack[self]).task_]
                                                                 /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                                            ELSE /\ pc' = [pc EXCEPT ![self] = "new_vmid_ret_from_check_update_reserved_vmid_end"]
                                                                 /\ UNCHANGED << ret_new_vmid, 
                                                                                 stack, 
                                                                                 task_, 
                                                                                 vmid_n, 
                                                                                 newvmid_, 
                                                                                 generation, 
                                                                                 old >>
                                                      /\ UNCHANGED << tlb, 
                                                                      active_kvm, 
                                                                      cpu_vmid_lock, 
                                                                      vmid_generation, 
                                                                      vmid_map, 
                                                                      active_vmids, 
                                                                      reserved_vmids, 
                                                                      cur_idx, 
                                                                      kvm_context_id, 
                                                                      ret_check_update_reserved_vmid, 
                                                                      vmid_, 
                                                                      cpu_, 
                                                                      cpus_, 
                                                                      vmid, 
                                                                      newvmid, 
                                                                      cpu, 
                                                                      cpus, 
                                                                      task_k, 
                                                                      vmid_k, 
                                                                      old_active_vmid, 
                                                                      task, 
                                                                      vmid_v >>

new_vmid_ret_from_check_update_reserved_vmid_end(self) == /\ pc[self] = "new_vmid_ret_from_check_update_reserved_vmid_end"
                                                          /\ old' = [old EXCEPT ![self] = vmid_map[vmid_n[self].vmid]]
                                                          /\ vmid_map' = [vmid_map EXCEPT ![vmid_n[self].vmid] = TRUE]
                                                          /\ IF ~old'[self]
                                                                THEN /\ ret_new_vmid' = [ret_new_vmid EXCEPT ![self] = newvmid_[self]]
                                                                     /\ pc' = [pc EXCEPT ![self] = "new_vmid_return"]
                                                                ELSE /\ pc' = [pc EXCEPT ![self] = "new_vmid_allocate_free_vmid"]
                                                                     /\ UNCHANGED ret_new_vmid
                                                          /\ UNCHANGED << tlb, 
                                                                          active_kvm, 
                                                                          cpu_vmid_lock, 
                                                                          vmid_generation, 
                                                                          active_vmids, 
                                                                          reserved_vmids, 
                                                                          cur_idx, 
                                                                          kvm_context_id, 
                                                                          ret_check_update_reserved_vmid, 
                                                                          stack, 
                                                                          vmid_, 
                                                                          cpu_, 
                                                                          cpus_, 
                                                                          vmid, 
                                                                          newvmid, 
                                                                          cpu, 
                                                                          cpus, 
                                                                          task_, 
                                                                          vmid_n, 
                                                                          newvmid_, 
                                                                          generation, 
                                                                          task_k, 
                                                                          vmid_k, 
                                                                          old_active_vmid, 
                                                                          task, 
                                                                          vmid_v >>

new_vmid_return(self) == /\ pc[self] = "new_vmid_return"
                         /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                         /\ vmid_n' = [vmid_n EXCEPT ![self] = Head(stack[self]).vmid_n]
                         /\ newvmid_' = [newvmid_ EXCEPT ![self] = Head(stack[self]).newvmid_]
                         /\ generation' = [generation EXCEPT ![self] = Head(stack[self]).generation]
                         /\ old' = [old EXCEPT ![self] = Head(stack[self]).old]
                         /\ task_' = [task_ EXCEPT ![self] = Head(stack[self]).task_]
                         /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                         /\ UNCHANGED << tlb, active_kvm, cpu_vmid_lock, 
                                         vmid_generation, vmid_map, 
                                         active_vmids, reserved_vmids, cur_idx, 
                                         kvm_context_id, 
                                         ret_check_update_reserved_vmid, 
                                         ret_new_vmid, vmid_, cpu_, cpus_, 
                                         vmid, newvmid, cpu, cpus, task_k, 
                                         vmid_k, old_active_vmid, task, vmid_v >>

new_vmid_allocate_free_vmid(self) == /\ pc[self] = "new_vmid_allocate_free_vmid"
                                     /\ IF EmptySlots(vmid_map, cur_idx)
                                           THEN /\ vmid_n' = [vmid_n EXCEPT ![self].vmid = FindEmptySlot(vmid_map, cur_idx)]
                                                /\ pc' = [pc EXCEPT ![self] = "set_vmid"]
                                           ELSE /\ pc' = [pc EXCEPT ![self] = "new_vmid_out_of_vmids"]
                                                /\ UNCHANGED vmid_n
                                     /\ UNCHANGED << tlb, active_kvm, 
                                                     cpu_vmid_lock, 
                                                     vmid_generation, vmid_map, 
                                                     active_vmids, 
                                                     reserved_vmids, cur_idx, 
                                                     kvm_context_id, 
                                                     ret_check_update_reserved_vmid, 
                                                     ret_new_vmid, stack, 
                                                     vmid_, cpu_, cpus_, vmid, 
                                                     newvmid, cpu, cpus, task_, 
                                                     newvmid_, generation, old, 
                                                     task_k, vmid_k, 
                                                     old_active_vmid, task, 
                                                     vmid_v >>

new_vmid_out_of_vmids(self) == /\ pc[self] = "new_vmid_out_of_vmids"
                               /\ vmid_generation' = vmid_generation + 1
                               /\ generation' = [generation EXCEPT ![self] = vmid_generation']
                               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "flush_context",
                                                                        pc        |->  "new_vmid_ret_flush_context",
                                                                        vmid_     |->  vmid_[self],
                                                                        cpu_      |->  cpu_[self],
                                                                        cpus_     |->  cpus_[self] ] >>
                                                                    \o stack[self]]
                               /\ vmid_' = [vmid_ EXCEPT ![self] = defaultInitValue]
                               /\ cpu_' = [cpu_ EXCEPT ![self] = defaultInitValue]
                               /\ cpus_' = [cpus_ EXCEPT ![self] = defaultInitValue]
                               /\ pc' = [pc EXCEPT ![self] = "flush_context_"]
                               /\ UNCHANGED << tlb, active_kvm, cpu_vmid_lock, 
                                               vmid_map, active_vmids, 
                                               reserved_vmids, cur_idx, 
                                               kvm_context_id, 
                                               ret_check_update_reserved_vmid, 
                                               ret_new_vmid, vmid, newvmid, 
                                               cpu, cpus, task_, vmid_n, 
                                               newvmid_, old, task_k, vmid_k, 
                                               old_active_vmid, task, vmid_v >>

new_vmid_ret_flush_context(self) == /\ pc[self] = "new_vmid_ret_flush_context"
                                    /\ vmid_n' = [vmid_n EXCEPT ![self].vmid = FindEmptySlot(vmid_map, 1)]
                                    /\ pc' = [pc EXCEPT ![self] = "set_vmid"]
                                    /\ UNCHANGED << tlb, active_kvm, 
                                                    cpu_vmid_lock, 
                                                    vmid_generation, vmid_map, 
                                                    active_vmids, 
                                                    reserved_vmids, cur_idx, 
                                                    kvm_context_id, 
                                                    ret_check_update_reserved_vmid, 
                                                    ret_new_vmid, stack, vmid_, 
                                                    cpu_, cpus_, vmid, newvmid, 
                                                    cpu, cpus, task_, newvmid_, 
                                                    generation, old, task_k, 
                                                    vmid_k, old_active_vmid, 
                                                    task, vmid_v >>

set_vmid(self) == /\ pc[self] = "set_vmid"
                  /\ vmid_map' = [vmid_map EXCEPT ![vmid_n[self].vmid] = TRUE]
                  /\ cur_idx' = vmid_n[self].vmid
                  /\ ret_new_vmid' = [ret_new_vmid EXCEPT ![self] = MakeVmid(vmid_n[self].vmid, generation[self])]
                  /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                  /\ vmid_n' = [vmid_n EXCEPT ![self] = Head(stack[self]).vmid_n]
                  /\ newvmid_' = [newvmid_ EXCEPT ![self] = Head(stack[self]).newvmid_]
                  /\ generation' = [generation EXCEPT ![self] = Head(stack[self]).generation]
                  /\ old' = [old EXCEPT ![self] = Head(stack[self]).old]
                  /\ task_' = [task_ EXCEPT ![self] = Head(stack[self]).task_]
                  /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                  /\ UNCHANGED << tlb, active_kvm, cpu_vmid_lock, 
                                  vmid_generation, active_vmids, 
                                  reserved_vmids, kvm_context_id, 
                                  ret_check_update_reserved_vmid, vmid_, cpu_, 
                                  cpus_, vmid, newvmid, cpu, cpus, task_k, 
                                  vmid_k, old_active_vmid, task, vmid_v >>

new_vmid(self) == new_vmid_(self)
                     \/ new_vmid_ret_from_check_update_reserved_vmid(self)
                     \/ new_vmid_ret_from_check_update_reserved_vmid_end(self)
                     \/ new_vmid_return(self)
                     \/ new_vmid_allocate_free_vmid(self)
                     \/ new_vmid_out_of_vmids(self)
                     \/ new_vmid_ret_flush_context(self) \/ set_vmid(self)

kvm_arm_vmid_update_(self) == /\ pc[self] = "kvm_arm_vmid_update_"
                              /\ vmid_k' = [vmid_k EXCEPT ![self] = kvm_context_id[task_k[self]]]
                              /\ old_active_vmid' = [old_active_vmid EXCEPT ![self] = active_vmids[self]]
                              /\ pc' = [pc EXCEPT ![self] = "check_current_generation"]
                              /\ UNCHANGED << tlb, active_kvm, cpu_vmid_lock, 
                                              vmid_generation, vmid_map, 
                                              active_vmids, reserved_vmids, 
                                              cur_idx, kvm_context_id, 
                                              ret_check_update_reserved_vmid, 
                                              ret_new_vmid, stack, vmid_, cpu_, 
                                              cpus_, vmid, newvmid, cpu, cpus, 
                                              task_, vmid_n, newvmid_, 
                                              generation, old, task_k, task, 
                                              vmid_v >>

check_current_generation(self) == /\ pc[self] = "check_current_generation"
                                  /\ IF old_active_vmid[self] # NULL_VMID /\ vmid_k[self].generation = vmid_generation
                                        THEN /\ pc' = [pc EXCEPT ![self] = "cmpxchg_active_vmids"]
                                        ELSE /\ pc' = [pc EXCEPT ![self] = "slow_path"]
                                  /\ UNCHANGED << tlb, active_kvm, 
                                                  cpu_vmid_lock, 
                                                  vmid_generation, vmid_map, 
                                                  active_vmids, reserved_vmids, 
                                                  cur_idx, kvm_context_id, 
                                                  ret_check_update_reserved_vmid, 
                                                  ret_new_vmid, stack, vmid_, 
                                                  cpu_, cpus_, vmid, newvmid, 
                                                  cpu, cpus, task_, vmid_n, 
                                                  newvmid_, generation, old, 
                                                  task_k, vmid_k, 
                                                  old_active_vmid, task, 
                                                  vmid_v >>

cmpxchg_active_vmids(self) == /\ pc[self] = "cmpxchg_active_vmids"
                              /\ IF (active_vmids[self]) = old_active_vmid[self]
                                    THEN /\ active_vmids' = [active_vmids EXCEPT ![self] = vmid_k[self]]
                                         /\ UNCHANGED old_active_vmid
                                    ELSE /\ old_active_vmid' = [old_active_vmid EXCEPT ![self] = active_vmids[self]]
                                         /\ UNCHANGED active_vmids
                              /\ pc' = [pc EXCEPT ![self] = "check_roll_over"]
                              /\ UNCHANGED << tlb, active_kvm, cpu_vmid_lock, 
                                              vmid_generation, vmid_map, 
                                              reserved_vmids, cur_idx, 
                                              kvm_context_id, 
                                              ret_check_update_reserved_vmid, 
                                              ret_new_vmid, stack, vmid_, cpu_, 
                                              cpus_, vmid, newvmid, cpu, cpus, 
                                              task_, vmid_n, newvmid_, 
                                              generation, old, task_k, vmid_k, 
                                              task, vmid_v >>

check_roll_over(self) == /\ pc[self] = "check_roll_over"
                         /\ IF old_active_vmid[self] # NULL_VMID
                               THEN /\ pc' = [pc EXCEPT ![self] = "fast_path"]
                               ELSE /\ pc' = [pc EXCEPT ![self] = "slow_path"]
                         /\ UNCHANGED << tlb, active_kvm, cpu_vmid_lock, 
                                         vmid_generation, vmid_map, 
                                         active_vmids, reserved_vmids, cur_idx, 
                                         kvm_context_id, 
                                         ret_check_update_reserved_vmid, 
                                         ret_new_vmid, stack, vmid_, cpu_, 
                                         cpus_, vmid, newvmid, cpu, cpus, 
                                         task_, vmid_n, newvmid_, generation, 
                                         old, task_k, vmid_k, old_active_vmid, 
                                         task, vmid_v >>

slow_path(self) == /\ pc[self] = "slow_path"
                   /\ ~cpu_vmid_lock
                   /\ cpu_vmid_lock' = TRUE
                   /\ vmid_k' = [vmid_k EXCEPT ![self] = kvm_context_id[task_k[self]]]
                   /\ IF vmid_k'[self].generation # vmid_generation
                         THEN /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "new_vmid",
                                                                          pc        |->  "kvm_arm_vmid_update_ret_new_vmid",
                                                                          vmid_n    |->  vmid_n[self],
                                                                          newvmid_  |->  newvmid_[self],
                                                                          generation |->  generation[self],
                                                                          old       |->  old[self],
                                                                          task_     |->  task_[self] ] >>
                                                                      \o stack[self]]
                                 /\ task_' = [task_ EXCEPT ![self] = task_k[self]]
                              /\ vmid_n' = [vmid_n EXCEPT ![self] = defaultInitValue]
                              /\ newvmid_' = [newvmid_ EXCEPT ![self] = defaultInitValue]
                              /\ generation' = [generation EXCEPT ![self] = defaultInitValue]
                              /\ old' = [old EXCEPT ![self] = defaultInitValue]
                              /\ pc' = [pc EXCEPT ![self] = "new_vmid_"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "set_active_vmids"]
                              /\ UNCHANGED << stack, task_, vmid_n, newvmid_, 
                                              generation, old >>
                   /\ UNCHANGED << tlb, active_kvm, vmid_generation, vmid_map, 
                                   active_vmids, reserved_vmids, cur_idx, 
                                   kvm_context_id, 
                                   ret_check_update_reserved_vmid, 
                                   ret_new_vmid, vmid_, cpu_, cpus_, vmid, 
                                   newvmid, cpu, cpus, task_k, old_active_vmid, 
                                   task, vmid_v >>

kvm_arm_vmid_update_ret_new_vmid(self) == /\ pc[self] = "kvm_arm_vmid_update_ret_new_vmid"
                                          /\ vmid_k' = [vmid_k EXCEPT ![self] = ret_new_vmid[self]]
                                          /\ kvm_context_id' = [kvm_context_id EXCEPT ![task_k[self]] = vmid_k'[self]]
                                          /\ pc' = [pc EXCEPT ![self] = "set_active_vmids"]
                                          /\ UNCHANGED << tlb, active_kvm, 
                                                          cpu_vmid_lock, 
                                                          vmid_generation, 
                                                          vmid_map, 
                                                          active_vmids, 
                                                          reserved_vmids, 
                                                          cur_idx, 
                                                          ret_check_update_reserved_vmid, 
                                                          ret_new_vmid, stack, 
                                                          vmid_, cpu_, cpus_, 
                                                          vmid, newvmid, cpu, 
                                                          cpus, task_, vmid_n, 
                                                          newvmid_, generation, 
                                                          old, task_k, 
                                                          old_active_vmid, 
                                                          task, vmid_v >>

set_active_vmids(self) == /\ pc[self] = "set_active_vmids"
                          /\ active_vmids' = [active_vmids EXCEPT ![self] = vmid_k[self]]
                          /\ cpu_vmid_lock' = FALSE
                          /\ pc' = [pc EXCEPT ![self] = "fast_path"]
                          /\ UNCHANGED << tlb, active_kvm, vmid_generation, 
                                          vmid_map, reserved_vmids, cur_idx, 
                                          kvm_context_id, 
                                          ret_check_update_reserved_vmid, 
                                          ret_new_vmid, stack, vmid_, cpu_, 
                                          cpus_, vmid, newvmid, cpu, cpus, 
                                          task_, vmid_n, newvmid_, generation, 
                                          old, task_k, vmid_k, old_active_vmid, 
                                          task, vmid_v >>

fast_path(self) == /\ pc[self] = "fast_path"
                   /\ active_kvm' = [active_kvm EXCEPT ![self].task = task_k[self],
                                                       ![self].vmid = vmid_k[self].vmid]
                   /\ IF task_k[self] # 0
                         THEN /\ tlb' = (tlb \cup {MakeTlbEntry(task_k[self], kvm_context_id[task_k[self]].vmid, self)})
                         ELSE /\ TRUE
                              /\ tlb' = tlb
                   /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                   /\ vmid_k' = [vmid_k EXCEPT ![self] = Head(stack[self]).vmid_k]
                   /\ old_active_vmid' = [old_active_vmid EXCEPT ![self] = Head(stack[self]).old_active_vmid]
                   /\ task_k' = [task_k EXCEPT ![self] = Head(stack[self]).task_k]
                   /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                   /\ UNCHANGED << cpu_vmid_lock, vmid_generation, vmid_map, 
                                   active_vmids, reserved_vmids, cur_idx, 
                                   kvm_context_id, 
                                   ret_check_update_reserved_vmid, 
                                   ret_new_vmid, vmid_, cpu_, cpus_, vmid, 
                                   newvmid, cpu, cpus, task_, vmid_n, newvmid_, 
                                   generation, old, task, vmid_v >>

kvm_arm_vmid_update(self) == kvm_arm_vmid_update_(self)
                                \/ check_current_generation(self)
                                \/ cmpxchg_active_vmids(self)
                                \/ check_roll_over(self) \/ slow_path(self)
                                \/ kvm_arm_vmid_update_ret_new_vmid(self)
                                \/ set_active_vmids(self)
                                \/ fast_path(self)

clear_active_vmid(self) == /\ pc[self] = "clear_active_vmid"
                           /\ active_kvm' = [active_kvm EXCEPT ![self].task = 0]
                           /\ active_vmids' = [active_vmids EXCEPT ![self] = INVALID_VMID]
                           /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                           /\ vmid_v' = [vmid_v EXCEPT ![self] = Head(stack[self]).vmid_v]
                           /\ task' = [task EXCEPT ![self] = Head(stack[self]).task]
                           /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                           /\ UNCHANGED << tlb, cpu_vmid_lock, vmid_generation, 
                                           vmid_map, reserved_vmids, cur_idx, 
                                           kvm_context_id, 
                                           ret_check_update_reserved_vmid, 
                                           ret_new_vmid, vmid_, cpu_, cpus_, 
                                           vmid, newvmid, cpu, cpus, task_, 
                                           vmid_n, newvmid_, generation, old, 
                                           task_k, vmid_k, old_active_vmid >>

vcpu_sched_out(self) == clear_active_vmid(self)

sched_out_ == /\ pc[SCHED_OUT] = "sched_out_"
              /\ \E t \in TASKS:
                   /\ /\ stack' = [stack EXCEPT ![SCHED_OUT] = << [ procedure |->  "vcpu_sched_out",
                                                                    pc        |->  "sched_out_",
                                                                    vmid_v    |->  vmid_v[SCHED_OUT],
                                                                    task      |->  task[SCHED_OUT] ] >>
                                                                \o stack[SCHED_OUT]]
                      /\ task' = [task EXCEPT ![SCHED_OUT] = t]
                   /\ vmid_v' = [vmid_v EXCEPT ![SCHED_OUT] = defaultInitValue]
                   /\ pc' = [pc EXCEPT ![SCHED_OUT] = "clear_active_vmid"]
              /\ UNCHANGED << tlb, active_kvm, cpu_vmid_lock, vmid_generation, 
                              vmid_map, active_vmids, reserved_vmids, cur_idx, 
                              kvm_context_id, ret_check_update_reserved_vmid, 
                              ret_new_vmid, vmid_, cpu_, cpus_, vmid, newvmid, 
                              cpu, cpus, task_, vmid_n, newvmid_, generation, 
                              old, task_k, vmid_k, old_active_vmid >>

sched_out == sched_out_

sched_loop(self) == /\ pc[self] = "sched_loop"
                    /\ \E t \in TASKS:
                         IF t # ActiveTask(self)
                            THEN /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "kvm_arm_vmid_update",
                                                                             pc        |->  "sched_loop",
                                                                             vmid_k    |->  vmid_k[self],
                                                                             old_active_vmid |->  old_active_vmid[self],
                                                                             task_k    |->  task_k[self] ] >>
                                                                         \o stack[self]]
                                    /\ task_k' = [task_k EXCEPT ![self] = t]
                                 /\ vmid_k' = [vmid_k EXCEPT ![self] = defaultInitValue]
                                 /\ old_active_vmid' = [old_active_vmid EXCEPT ![self] = defaultInitValue]
                                 /\ pc' = [pc EXCEPT ![self] = "kvm_arm_vmid_update_"]
                            ELSE /\ pc' = [pc EXCEPT ![self] = "sched_loop"]
                                 /\ UNCHANGED << stack, task_k, vmid_k, 
                                                 old_active_vmid >>
                    /\ UNCHANGED << tlb, active_kvm, cpu_vmid_lock, 
                                    vmid_generation, vmid_map, active_vmids, 
                                    reserved_vmids, cur_idx, kvm_context_id, 
                                    ret_check_update_reserved_vmid, 
                                    ret_new_vmid, vmid_, cpu_, cpus_, vmid, 
                                    newvmid, cpu, cpus, task_, vmid_n, 
                                    newvmid_, generation, old, task, vmid_v >>

sched(self) == sched_loop(self)

Next == sched_out
           \/ (\E self \in ProcSet:  \/ flush_context(self)
                                     \/ check_update_reserved_vmid(self)
                                     \/ new_vmid(self)
                                     \/ kvm_arm_vmid_update(self)
                                     \/ vcpu_sched_out(self))
           \/ (\E self \in CPUS: sched(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-071a3790d26807e2a4906e2ce2f9bf7a
==============================================================================
