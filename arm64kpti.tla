------------------------------ MODULE arm64kpti -------------------------------
\*
\* Model of the arm64 Linux KPTI support
\*
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS	CPUS,
		THREADS,
		MMS,
		TTBR0_PAN

(* --algorithm kpti {
variables
	\* OS + CPU state
	current		= [c \in CPUS |-> "idle"];
	interrupts	= [c \in CPUS |-> "off"];
	preempt_count	= [c \in CPUS |-> 0];
	mode		= [c \in CPUS |-> "kernel"];
	tlb		= {};
	runqueue	= THREADS;
	pt_regs		= [t \in THREADS \cup {"idle"} |->
				[pc	|-> "start_thread",
				sp	|-> << >>,
				mode	|-> "kernel",
				interrupted |-> FALSE]];

	\* Additional thread state
	thread		= [t \in THREADS \cup {"idle"} |->
				[mm		|-> "init_mm",
				 active_mm	|-> "null",
				 psr_pan_bit	|-> FALSE,
				 ttbr0		|-> defaultInitValue]];

	\* Additional CPU state (other than pc and stack)
	cpu		= [c \in CPUS |-> [ttbr0 |-> [asid |-> << "zero", 0 >>, baddr |-> "reserved"],
					   ttbr1 |-> [asid |-> << "zero", 0 >>, baddr |-> "init_mm"]]];

define {
	\* Helpers
	MakeTTB(asid, baddr) == [asid |-> asid, baddr |-> baddr]
	MakeTLB(b, a, c) == [baddr |-> b, asid |-> a, cpu |-> c]
	\* Set of TLB entries for the currently active TTBRs
	NG(baddr) == IF baddr \in {"trampoline", "idmap"}
			THEN FALSE
			ELSE TRUE
	ASIDTag(c, baddr) == IF NG(baddr) THEN cpu[c].ttbr1.asid ELSE << "all", 0 >>
	ActiveTLBs == {MakeTLB(cpu[c].ttbr0.baddr, ASIDTag(c, cpu[c].ttbr0.baddr), c) :
		        c \in {c1 \in CPUS : cpu[c1].ttbr0.baddr # "reserved"}} \cup
		      {MakeTLB(cpu[c].ttbr1.baddr, ASIDTag(c, cpu[c].ttbr1.baddr), c) :
		        c \in {c1 \in CPUS : cpu[c1].ttbr1.baddr # "reserved"}}

	KernelThread(t) == thread[t].mm = "null"
	KernelMapped(c) == cpu[c].ttbr1.baddr = "init_mm"

	\* Type invariants
	ASIDType	== {<< asid, user >> : asid \in MMS \cup {"all", "zero", "efi_mm"},
					     user \in {0, 1}}
	BADDRType	== MMS \cup {"reserved", "init_mm", "trampoline", "idmap", "efi_mm"}
	TTBRType	== [asid: ASIDType, baddr: BADDRType]
	TLBType		== [baddr: BADDRType \ {"reserved"}, asid: ASIDType, cpu: CPUS]
	ThreadType	== [mm:		MMS \cup {"init_mm", "null"},
			    active_mm:	MMS \cup {"init_mm", "null"},
			    psr_pan_bit: BOOLEAN,
			    ttbr0:	TTBRType \cup {defaultInitValue}]
	TypeInv		== /\ current \in [CPUS -> THREADS \cup {"idle"}]
			   /\ interrupts \in [CPUS -> {"on", "off"}]
			   /\ preempt_count \in [CPUS-> Nat]
			   /\ mode \in [CPUS -> {"user", "kernel"}]
			   /\ cpu \in [CPUS -> [ttbr0: TTBRType, ttbr1: TTBRType]]
			   /\ thread \in [THREADS \cup {"idle"} -> ThreadType]
			   /\ tlb \subseteq TLBType

	\* Algorithm invariants
	SchedInv	== /\ \A c \in CPUS : current[c] \notin runqueue	\* current task not in runqueue
			   /\ \A c \in CPUS : pc[c] = "schedule_done" =>
				/\ current[c] # "idle"
				/\ KernelThread(current[c]) =>
					thread[current[c]].active_mm \in MMS \cup {"init_mm"}
				/\ ~KernelThread(current[c]) =>
					thread[current[c]].active_mm = thread[current[c]].mm

	\* KPTI invariants
	KPTIInv		== /\ \A c \in CPUS :
				mode[c] = "user" => cpu[c].ttbr1.asid[2] = 1
			   /\ \A t \in tlb :
				t.baddr = "init_mm" => t.asid[1] # "all" /\ t.asid[2] = 0
			   /\ \A c \in CPUS :
				cpu[c].ttbr0.baddr \in MMS \cup {"reserved", "efi_mm"}

	\* TLB invariants
	UniqueASID	== \A t1, t2 \in tlb :
				/\ t1.baddr \in MMS \cup {"efi_mm"}
				/\ t2.baddr \in MMS \cup {"efi_mm"}
				/\ t1.baddr # t2.baddr
				=> t1.asid[1] # t2.asid[1]
	SameASID	== \A t1, t2 \in tlb :
				/\ t1.baddr \in MMS \cup {"efi_mm"}
				/\ t2.baddr \in MMS \cup {"efi_mm"}
				/\ t1.baddr = t2.baddr
				=> t1.asid[1] = t2.asid[1]
	BaddrASIDMatch	== \A t \in tlb :
				t.baddr \in MMS \cup {"efi_mm"} => t.asid[1] = t.baddr
	KernelASID	== \A t \in tlb : t.baddr \notin MMS => t.asid[2] = 0
	UserASID	== \A t \in tlb : t.asid[2] = 1 => t.baddr \in MMS
	GlobalEntry	== \A t \in tlb :
				t.asid[1] = "all" <=> t.baddr = "trampoline"

	\* Symmetry optimisations
	Perms		== Permutations(CPUS) \cup Permutations(THREADS) \cup
				Permutations(MMS)
}

macro update_tlbs() {
	tlb := tlb \cup ActiveTLBs;
}

macro local_irq_disable() {
	assert interrupts[self] = "on";
	interrupts[self] := "off";
}

macro local_irq_enable() {
	interrupts[self] := "on";
}

macro preempt_disable() {
	preempt_count[self] := preempt_count[self] + 1;
}

macro preempt_enable() {
	preempt_count[self] := preempt_count[self] - 1;
}

macro cpu_set_reserved_ttbr0() {
	cpu[self].ttbr0 := MakeTTB(<< "zero", 0 >>, "reserved");
}

macro switch_to(next) {
	if (current[self] # "idle")
		runqueue := runqueue \cup {current[self]};
	current[self] := next;
}

macro mm_init(t) {
	if (thread[t].mm = "init_mm")
		with (mm \in MMS \cup {"null"})
			thread[t].mm := mm ||
			thread[t].active_mm := mm;
}

macro update_saved_ttbr0(t, mm) {
	if (TTBR0_PAN) {
		if (mm = "init_mm")
			thread[t].ttbr0 := MakeTTB(<< "zero", 0 >>, "reserved");
		else
			thread[t].ttbr0 := MakeTTB(<< mm, 0 >>, mm);
	}
}

procedure __uaccess_ttbr0_disable()
{
_utd1:	\* set reserved TTBR0 and ASID
	cpu_set_reserved_ttbr0();
_utd2:	\* set reserved ASID
	cpu[self].ttbr1.asid := << "zero", 0 >>;
_utd3:	update_tlbs();
	return;
}

procedure __uaccess_ttbr0_enable()
{
_ute1:	assert /\ cpu[self].ttbr1.asid = << "zero", 0 >>
	       /\ cpu[self].ttbr0.baddr = "reserved";
	\* restore user ASID
	cpu[self].ttbr1.asid := thread[current[self]].ttbr0.asid;
_ute2:	update_tlbs();
	\* restore user page tables
	cpu[self].ttbr0 := thread[current[self]].ttbr0;
_ute3:	update_tlbs();
	return;
}

procedure uaccess_ttbr0_disable()
{
utd1:	if (TTBR0_PAN) {
		local_irq_disable();
		call __uaccess_ttbr0_disable();
utd2:		local_irq_enable();
	};
utd3:	return;
}

procedure uaccess_ttbr0_enable()
{
ute1:	if (TTBR0_PAN) {
		local_irq_disable();
		call __uaccess_ttbr0_enable();
ute2:		local_irq_enable();
	};
ute3:	return;
}

procedure cpu_switch_mm(next_mm)
{
csm1:	assert next_mm # "init_mm";
	cpu_set_reserved_ttbr0();
csm2:	\* cpu_do_switch_mm()
	cpu[self].ttbr1.asid := << next_mm, 0 >>;		\* ASID in TTBR1
csm3:	update_tlbs();
	cpu[self].ttbr0 := MakeTTB(<< "zero", 0 >>, next_mm);
csm4:	update_tlbs();
	return;
}

procedure __switch_mm(__mm)
{
_sm1:	if (__mm = "init_mm") {
		cpu_set_reserved_ttbr0();
		return;
	};
	\* check_and_switch_context() squashed
_sm3:	if (~TTBR0_PAN)
		call cpu_switch_mm(__mm);
_sm4:	return;
}

procedure switch_mm(prev_mm, next)
{
sm1:	if (thread[next].mm # prev_mm)
		call __switch_mm(thread[next].mm);
sm2:	update_saved_ttbr0(next, thread[next].mm);
sm3:	return;
}

procedure use_mm()
	variable active_mm;
{
um1:	preempt_disable();
	with (mm \in MMS) {
		active_mm := thread[current[self]].active_mm;
		thread[current[self]].active_mm := mm ||
		thread[current[self]].mm := mm;
		call switch_mm(active_mm, current[self]);
	};
um2:	preempt_enable();
	return;
}

procedure unuse_mm()
{
unm1:	preempt_disable();
	thread[current[self]].mm := "null";
unm2:	update_saved_ttbr0(current[self], "init_mm");
	preempt_enable();
	return;
}

procedure context_switch(next_thread)
{
cs1:	if (thread[next_thread].mm = "null")
		\* kernel thread, reusing current active_mm
		thread[next_thread].active_mm :=
			thread[current[self]].active_mm;
	else
		call switch_mm(thread[current[self]].active_mm, next_thread);

cs2:	if (thread[current[self]].mm = "null")
		\* restore active_mm of the previous kernel thread
		thread[current[self]].active_mm := "null";

cs3:	switch_to(next_thread);
	return;
}

procedure schedule()
{
do_schedule:
	if (preempt_count[self] > 0)
		return;
s1:	assert interrupts[self] = "off";
	either {
		\* Simulate no pending thread if not idle
		await current[self] # "idle";
		return;
	} or {
		\* Pick a thread in the runqueue
		with (n \in runqueue) {
			runqueue := runqueue \ {n};
			mm_init(n);
			call context_switch(n);
		}
	};
schedule_done:
	return;
}

procedure tramp_map_kernel()
{
tmk1:	cpu[self].ttbr1.baddr := "init_mm" ||
	cpu[self].ttbr1.asid[2] := 0;	\* kernel ASID
tmk2:	update_tlbs();
	return;
}

procedure tramp_unmap_kernel()
{
tuk1:	cpu[self].ttbr1.baddr := "trampoline" ||
	cpu[self].ttbr1.asid[2] := 1;	\* user ASID
tuk2:	update_tlbs();
	return;
}

procedure kernel_entry(entry_el)
{
ken1:	assert interrupts[self] = "off";
	mode[self] := "kernel";
	if (~KernelMapped(self))
		call tramp_map_kernel();
ken2:	if (TTBR0_PAN) {
		if (entry_el = "kernel" /\ cpu[self].ttbr0.asid = << "zero", 0 >>)
			thread[current[self]].psr_pan_bit := TRUE;
		else
			call __uaccess_ttbr0_disable();
	};
ken3:	return;
}

procedure kernel_exit(exit_el)
{
kex1:	assert interrupts[self] = "off";
	if (TTBR0_PAN) {
		if (exit_el = "kernel" /\ thread[current[self]].psr_pan_bit)
			thread[current[self]].psr_pan_bit := FALSE;
		else
			call __uaccess_ttbr0_enable();
	};
kex2:	if (exit_el = "user")
		call tramp_unmap_kernel();
kex3:	mode[self] := exit_el;
	return;
}

procedure interrupt()
{
interrupt_handler:
	call kernel_entry(mode[self]);
i1:	call schedule();		\* (maybe) re-schedule
i2:	\* Only exit the kernel if the thread we are returning to was
	\* previously interrupted (no explicit calls to schedule() from thread
	\* context yet)
	if (pt_regs[current[self]].interrupted) {
		pt_regs[current[self]].interrupted := FALSE;
		call kernel_exit(pt_regs[current[self]].mode);
	};
ret_from_interrupt:
	await FALSE;			\* never pass this point
}

procedure ret_to_user()
{
rtu1:	assert mode[self] = "kernel";
	local_irq_disable();
rtu2:	call kernel_exit("user");
rtu3:	local_irq_enable();
	return;
}

procedure syscall()
{
sys1:	assert mode[self] = "user";
	local_irq_disable();
sys2:	call kernel_entry(mode[self]);
sys3:	local_irq_enable();
	return;
}

procedure uaccess()
{
ua1:	call uaccess_ttbr0_enable();
ua2:	assert /\ cpu[self].ttbr0.baddr \in MMS
	       /\ cpu[self].ttbr0.baddr = thread[current[self]].active_mm;
	\* user access removed
	call uaccess_ttbr0_disable();
ua3:	return;
}

procedure efi_set_pgd(mm_efi)
{
esp1:	call __switch_mm(mm_efi);
esp2:	if (TTBR0_PAN) {
		if (mm_efi # thread[current[self]].active_mm) {
			update_saved_ttbr0(current[self], mm_efi);
			call uaccess_ttbr0_enable();
		} else {
			call uaccess_ttbr0_disable();
esp3:			update_saved_ttbr0(current[self], thread[current[self]].active_mm);
		}
	};
esp4:	return;
}

procedure efi_call_virt()
{
ecv1:	\* efi_virtmap_load()
	preempt_disable();
	call efi_set_pgd("efi_mm");
	\* EFI run-time invokation removed
ecv2:	\* efi_virtmap_unload()
	call efi_set_pgd(thread[current[self]].active_mm);
ecv3:	preempt_enable();
	return;
}

procedure run_kernel()
{
rk1:	assert cpu[self].ttbr1.baddr = "init_mm";
	either {
		await ~KernelThread(current[self]);
		call ret_to_user();
	} or {
		await ~KernelThread(current[self]);
		call uaccess();
	} or {
		await KernelThread(current[self]);
		call use_mm();
rk2:		call uaccess();
rk3:		call unuse_mm();
	} or {
		call efi_call_virt();
	};
rk4:	return;
}

procedure run_user()
{
ru1:	assert /\ cpu[self].ttbr0.baddr \in MMS
	       /\ ~thread[current[self]].psr_pan_bit;
	call syscall();
	return;
}

procedure run_thread()
{
start_thread:
	while (TRUE) {
		assert interrupts[self] = "on";
		either {
			await mode[self] = "kernel";
			call run_kernel();
		} or {
			await mode[self] = "user";
			call run_user();
		} or {
			\* something else
			skip;
		}
	}
}

process (Processor \in CPUS)
{
start_cpu:
	thread["idle"].active_mm := "init_mm";
	update_tlbs();
	local_irq_enable();
idle:
	await FALSE;
}
} *)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES current, interrupts, preempt_count, mode, tlb, runqueue, pt_regs, 
          thread, cpu, pc, stack

(* define statement *)
MakeTTB(asid, baddr) == [asid |-> asid, baddr |-> baddr]
MakeTLB(b, a, c) == [baddr |-> b, asid |-> a, cpu |-> c]

NG(baddr) == IF baddr \in {"trampoline", "idmap"}
                THEN FALSE
                ELSE TRUE
ASIDTag(c, baddr) == IF NG(baddr) THEN cpu[c].ttbr1.asid ELSE << "all", 0 >>
ActiveTLBs == {MakeTLB(cpu[c].ttbr0.baddr, ASIDTag(c, cpu[c].ttbr0.baddr), c) :
                c \in {c1 \in CPUS : cpu[c1].ttbr0.baddr # "reserved"}} \cup
              {MakeTLB(cpu[c].ttbr1.baddr, ASIDTag(c, cpu[c].ttbr1.baddr), c) :
                c \in {c1 \in CPUS : cpu[c1].ttbr1.baddr # "reserved"}}

KernelThread(t) == thread[t].mm = "null"
KernelMapped(c) == cpu[c].ttbr1.baddr = "init_mm"


ASIDType        == {<< asid, user >> : asid \in MMS \cup {"all", "zero", "efi_mm"},
                                     user \in {0, 1}}
BADDRType       == MMS \cup {"reserved", "init_mm", "trampoline", "idmap", "efi_mm"}
TTBRType        == [asid: ASIDType, baddr: BADDRType]
TLBType         == [baddr: BADDRType \ {"reserved"}, asid: ASIDType, cpu: CPUS]
ThreadType      == [mm:         MMS \cup {"init_mm", "null"},
                    active_mm:  MMS \cup {"init_mm", "null"},
                    psr_pan_bit: BOOLEAN,
                    ttbr0:      TTBRType \cup {defaultInitValue}]
TypeInv         == /\ current \in [CPUS -> THREADS \cup {"idle"}]
                   /\ interrupts \in [CPUS -> {"on", "off"}]
                   /\ preempt_count \in [CPUS-> Nat]
                   /\ mode \in [CPUS -> {"user", "kernel"}]
                   /\ cpu \in [CPUS -> [ttbr0: TTBRType, ttbr1: TTBRType]]
                   /\ thread \in [THREADS \cup {"idle"} -> ThreadType]
                   /\ tlb \subseteq TLBType


SchedInv        == /\ \A c \in CPUS : current[c] \notin runqueue
                   /\ \A c \in CPUS : pc[c] = "schedule_done" =>
                        /\ current[c] # "idle"
                        /\ KernelThread(current[c]) =>
                                thread[current[c]].active_mm \in MMS \cup {"init_mm"}
                        /\ ~KernelThread(current[c]) =>
                                thread[current[c]].active_mm = thread[current[c]].mm


KPTIInv         == /\ \A c \in CPUS :
                        mode[c] = "user" => cpu[c].ttbr1.asid[2] = 1
                   /\ \A t \in tlb :
                        t.baddr = "init_mm" => t.asid[1] # "all" /\ t.asid[2] = 0
                   /\ \A c \in CPUS :
                        cpu[c].ttbr0.baddr \in MMS \cup {"reserved", "efi_mm"}


UniqueASID      == \A t1, t2 \in tlb :
                        /\ t1.baddr \in MMS \cup {"efi_mm"}
                        /\ t2.baddr \in MMS \cup {"efi_mm"}
                        /\ t1.baddr # t2.baddr
                        => t1.asid[1] # t2.asid[1]
SameASID        == \A t1, t2 \in tlb :
                        /\ t1.baddr \in MMS \cup {"efi_mm"}
                        /\ t2.baddr \in MMS \cup {"efi_mm"}
                        /\ t1.baddr = t2.baddr
                        => t1.asid[1] = t2.asid[1]
BaddrASIDMatch  == \A t \in tlb :
                        t.baddr \in MMS \cup {"efi_mm"} => t.asid[1] = t.baddr
KernelASID      == \A t \in tlb : t.baddr \notin MMS => t.asid[2] = 0
UserASID        == \A t \in tlb : t.asid[2] = 1 => t.baddr \in MMS
GlobalEntry     == \A t \in tlb :
                        t.asid[1] = "all" <=> t.baddr = "trampoline"


Perms           == Permutations(CPUS) \cup Permutations(THREADS) \cup
                        Permutations(MMS)

VARIABLES next_mm, __mm, prev_mm, next, active_mm, next_thread, entry_el, 
          exit_el, mm_efi

vars == << current, interrupts, preempt_count, mode, tlb, runqueue, pt_regs, 
           thread, cpu, pc, stack, next_mm, __mm, prev_mm, next, active_mm, 
           next_thread, entry_el, exit_el, mm_efi >>

ProcSet == (CPUS)

Init == (* Global variables *)
        /\ current = [c \in CPUS |-> "idle"]
        /\ interrupts = [c \in CPUS |-> "off"]
        /\ preempt_count = [c \in CPUS |-> 0]
        /\ mode = [c \in CPUS |-> "kernel"]
        /\ tlb = {}
        /\ runqueue = THREADS
        /\ pt_regs = [t \in THREADS \cup {"idle"} |->
                           [pc     |-> "start_thread",
                           sp      |-> << >>,
                           mode    |-> "kernel",
                           interrupted |-> FALSE]]
        /\ thread = [t \in THREADS \cup {"idle"} |->
                          [mm             |-> "init_mm",
                           active_mm      |-> "null",
                           psr_pan_bit    |-> FALSE,
                           ttbr0          |-> defaultInitValue]]
        /\ cpu = [c \in CPUS |-> [ttbr0 |-> [asid |-> << "zero", 0 >>, baddr |-> "reserved"],
                                  ttbr1 |-> [asid |-> << "zero", 0 >>, baddr |-> "init_mm"]]]
        (* Procedure cpu_switch_mm *)
        /\ next_mm = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure __switch_mm *)
        /\ __mm = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure switch_mm *)
        /\ prev_mm = [ self \in ProcSet |-> defaultInitValue]
        /\ next = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure use_mm *)
        /\ active_mm = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure context_switch *)
        /\ next_thread = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure kernel_entry *)
        /\ entry_el = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure kernel_exit *)
        /\ exit_el = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure efi_set_pgd *)
        /\ mm_efi = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "start_cpu"]

_utd1(self) == /\ pc[self] = "_utd1"
               /\ cpu' = [cpu EXCEPT ![self].ttbr0 = MakeTTB(<< "zero", 0 >>, "reserved")]
               /\ pc' = [pc EXCEPT ![self] = "_utd2"]
               /\ UNCHANGED << current, interrupts, preempt_count, mode, tlb, 
                               runqueue, pt_regs, thread, stack, next_mm, __mm, 
                               prev_mm, next, active_mm, next_thread, entry_el, 
                               exit_el, mm_efi >>

_utd2(self) == /\ pc[self] = "_utd2"
               /\ cpu' = [cpu EXCEPT ![self].ttbr1.asid = << "zero", 0 >>]
               /\ pc' = [pc EXCEPT ![self] = "_utd3"]
               /\ UNCHANGED << current, interrupts, preempt_count, mode, tlb, 
                               runqueue, pt_regs, thread, stack, next_mm, __mm, 
                               prev_mm, next, active_mm, next_thread, entry_el, 
                               exit_el, mm_efi >>

_utd3(self) == /\ pc[self] = "_utd3"
               /\ tlb' = (tlb \cup ActiveTLBs)
               /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
               /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
               /\ UNCHANGED << current, interrupts, preempt_count, mode, 
                               runqueue, pt_regs, thread, cpu, next_mm, __mm, 
                               prev_mm, next, active_mm, next_thread, entry_el, 
                               exit_el, mm_efi >>

__uaccess_ttbr0_disable(self) == _utd1(self) \/ _utd2(self) \/ _utd3(self)

_ute1(self) == /\ pc[self] = "_ute1"
               /\ Assert(/\ cpu[self].ttbr1.asid = << "zero", 0 >>
                         /\ cpu[self].ttbr0.baddr = "reserved", 
                         "Failure of assertion at line 172, column 9.")
               /\ cpu' = [cpu EXCEPT ![self].ttbr1.asid = thread[current[self]].ttbr0.asid]
               /\ pc' = [pc EXCEPT ![self] = "_ute2"]
               /\ UNCHANGED << current, interrupts, preempt_count, mode, tlb, 
                               runqueue, pt_regs, thread, stack, next_mm, __mm, 
                               prev_mm, next, active_mm, next_thread, entry_el, 
                               exit_el, mm_efi >>

_ute2(self) == /\ pc[self] = "_ute2"
               /\ tlb' = (tlb \cup ActiveTLBs)
               /\ cpu' = [cpu EXCEPT ![self].ttbr0 = thread[current[self]].ttbr0]
               /\ pc' = [pc EXCEPT ![self] = "_ute3"]
               /\ UNCHANGED << current, interrupts, preempt_count, mode, 
                               runqueue, pt_regs, thread, stack, next_mm, __mm, 
                               prev_mm, next, active_mm, next_thread, entry_el, 
                               exit_el, mm_efi >>

_ute3(self) == /\ pc[self] = "_ute3"
               /\ tlb' = (tlb \cup ActiveTLBs)
               /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
               /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
               /\ UNCHANGED << current, interrupts, preempt_count, mode, 
                               runqueue, pt_regs, thread, cpu, next_mm, __mm, 
                               prev_mm, next, active_mm, next_thread, entry_el, 
                               exit_el, mm_efi >>

__uaccess_ttbr0_enable(self) == _ute1(self) \/ _ute2(self) \/ _ute3(self)

utd1(self) == /\ pc[self] = "utd1"
              /\ IF TTBR0_PAN
                    THEN /\ Assert(interrupts[self] = "on", 
                                   "Failure of assertion at line 118, column 9 of macro called at line 186, column 17.")
                         /\ interrupts' = [interrupts EXCEPT ![self] = "off"]
                         /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "__uaccess_ttbr0_disable",
                                                                  pc        |->  "utd2" ] >>
                                                              \o stack[self]]
                         /\ pc' = [pc EXCEPT ![self] = "_utd1"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "utd3"]
                         /\ UNCHANGED << interrupts, stack >>
              /\ UNCHANGED << current, preempt_count, mode, tlb, runqueue, 
                              pt_regs, thread, cpu, next_mm, __mm, prev_mm, 
                              next, active_mm, next_thread, entry_el, exit_el, 
                              mm_efi >>

utd2(self) == /\ pc[self] = "utd2"
              /\ interrupts' = [interrupts EXCEPT ![self] = "on"]
              /\ pc' = [pc EXCEPT ![self] = "utd3"]
              /\ UNCHANGED << current, preempt_count, mode, tlb, runqueue, 
                              pt_regs, thread, cpu, stack, next_mm, __mm, 
                              prev_mm, next, active_mm, next_thread, entry_el, 
                              exit_el, mm_efi >>

utd3(self) == /\ pc[self] = "utd3"
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << current, interrupts, preempt_count, mode, tlb, 
                              runqueue, pt_regs, thread, cpu, next_mm, __mm, 
                              prev_mm, next, active_mm, next_thread, entry_el, 
                              exit_el, mm_efi >>

uaccess_ttbr0_disable(self) == utd1(self) \/ utd2(self) \/ utd3(self)

ute1(self) == /\ pc[self] = "ute1"
              /\ IF TTBR0_PAN
                    THEN /\ Assert(interrupts[self] = "on", 
                                   "Failure of assertion at line 118, column 9 of macro called at line 196, column 17.")
                         /\ interrupts' = [interrupts EXCEPT ![self] = "off"]
                         /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "__uaccess_ttbr0_enable",
                                                                  pc        |->  "ute2" ] >>
                                                              \o stack[self]]
                         /\ pc' = [pc EXCEPT ![self] = "_ute1"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "ute3"]
                         /\ UNCHANGED << interrupts, stack >>
              /\ UNCHANGED << current, preempt_count, mode, tlb, runqueue, 
                              pt_regs, thread, cpu, next_mm, __mm, prev_mm, 
                              next, active_mm, next_thread, entry_el, exit_el, 
                              mm_efi >>

ute2(self) == /\ pc[self] = "ute2"
              /\ interrupts' = [interrupts EXCEPT ![self] = "on"]
              /\ pc' = [pc EXCEPT ![self] = "ute3"]
              /\ UNCHANGED << current, preempt_count, mode, tlb, runqueue, 
                              pt_regs, thread, cpu, stack, next_mm, __mm, 
                              prev_mm, next, active_mm, next_thread, entry_el, 
                              exit_el, mm_efi >>

ute3(self) == /\ pc[self] = "ute3"
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << current, interrupts, preempt_count, mode, tlb, 
                              runqueue, pt_regs, thread, cpu, next_mm, __mm, 
                              prev_mm, next, active_mm, next_thread, entry_el, 
                              exit_el, mm_efi >>

uaccess_ttbr0_enable(self) == ute1(self) \/ ute2(self) \/ ute3(self)

csm1(self) == /\ pc[self] = "csm1"
              /\ Assert(next_mm[self] # "init_mm", 
                        "Failure of assertion at line 205, column 9.")
              /\ cpu' = [cpu EXCEPT ![self].ttbr0 = MakeTTB(<< "zero", 0 >>, "reserved")]
              /\ pc' = [pc EXCEPT ![self] = "csm2"]
              /\ UNCHANGED << current, interrupts, preempt_count, mode, tlb, 
                              runqueue, pt_regs, thread, stack, next_mm, __mm, 
                              prev_mm, next, active_mm, next_thread, entry_el, 
                              exit_el, mm_efi >>

csm2(self) == /\ pc[self] = "csm2"
              /\ cpu' = [cpu EXCEPT ![self].ttbr1.asid = << next_mm[self], 0 >>]
              /\ pc' = [pc EXCEPT ![self] = "csm3"]
              /\ UNCHANGED << current, interrupts, preempt_count, mode, tlb, 
                              runqueue, pt_regs, thread, stack, next_mm, __mm, 
                              prev_mm, next, active_mm, next_thread, entry_el, 
                              exit_el, mm_efi >>

csm3(self) == /\ pc[self] = "csm3"
              /\ tlb' = (tlb \cup ActiveTLBs)
              /\ cpu' = [cpu EXCEPT ![self].ttbr0 = MakeTTB(<< "zero", 0 >>, next_mm[self])]
              /\ pc' = [pc EXCEPT ![self] = "csm4"]
              /\ UNCHANGED << current, interrupts, preempt_count, mode, 
                              runqueue, pt_regs, thread, stack, next_mm, __mm, 
                              prev_mm, next, active_mm, next_thread, entry_el, 
                              exit_el, mm_efi >>

csm4(self) == /\ pc[self] = "csm4"
              /\ tlb' = (tlb \cup ActiveTLBs)
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ next_mm' = [next_mm EXCEPT ![self] = Head(stack[self]).next_mm]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << current, interrupts, preempt_count, mode, 
                              runqueue, pt_regs, thread, cpu, __mm, prev_mm, 
                              next, active_mm, next_thread, entry_el, exit_el, 
                              mm_efi >>

cpu_switch_mm(self) == csm1(self) \/ csm2(self) \/ csm3(self) \/ csm4(self)

_sm1(self) == /\ pc[self] = "_sm1"
              /\ IF __mm[self] = "init_mm"
                    THEN /\ cpu' = [cpu EXCEPT ![self].ttbr0 = MakeTTB(<< "zero", 0 >>, "reserved")]
                         /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                         /\ __mm' = [__mm EXCEPT ![self] = Head(stack[self]).__mm]
                         /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "_sm3"]
                         /\ UNCHANGED << cpu, stack, __mm >>
              /\ UNCHANGED << current, interrupts, preempt_count, mode, tlb, 
                              runqueue, pt_regs, thread, next_mm, prev_mm, 
                              next, active_mm, next_thread, entry_el, exit_el, 
                              mm_efi >>

_sm3(self) == /\ pc[self] = "_sm3"
              /\ IF ~TTBR0_PAN
                    THEN /\ /\ next_mm' = [next_mm EXCEPT ![self] = __mm[self]]
                            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "cpu_switch_mm",
                                                                     pc        |->  "_sm4",
                                                                     next_mm   |->  next_mm[self] ] >>
                                                                 \o stack[self]]
                         /\ pc' = [pc EXCEPT ![self] = "csm1"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "_sm4"]
                         /\ UNCHANGED << stack, next_mm >>
              /\ UNCHANGED << current, interrupts, preempt_count, mode, tlb, 
                              runqueue, pt_regs, thread, cpu, __mm, prev_mm, 
                              next, active_mm, next_thread, entry_el, exit_el, 
                              mm_efi >>

_sm4(self) == /\ pc[self] = "_sm4"
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ __mm' = [__mm EXCEPT ![self] = Head(stack[self]).__mm]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << current, interrupts, preempt_count, mode, tlb, 
                              runqueue, pt_regs, thread, cpu, next_mm, prev_mm, 
                              next, active_mm, next_thread, entry_el, exit_el, 
                              mm_efi >>

__switch_mm(self) == _sm1(self) \/ _sm3(self) \/ _sm4(self)

sm1(self) == /\ pc[self] = "sm1"
             /\ IF thread[next[self]].mm # prev_mm[self]
                   THEN /\ /\ __mm' = [__mm EXCEPT ![self] = thread[next[self]].mm]
                           /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "__switch_mm",
                                                                    pc        |->  "sm2",
                                                                    __mm      |->  __mm[self] ] >>
                                                                \o stack[self]]
                        /\ pc' = [pc EXCEPT ![self] = "_sm1"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "sm2"]
                        /\ UNCHANGED << stack, __mm >>
             /\ UNCHANGED << current, interrupts, preempt_count, mode, tlb, 
                             runqueue, pt_regs, thread, cpu, next_mm, prev_mm, 
                             next, active_mm, next_thread, entry_el, exit_el, 
                             mm_efi >>

sm2(self) == /\ pc[self] = "sm2"
             /\ IF TTBR0_PAN
                   THEN /\ IF (thread[next[self]].mm) = "init_mm"
                              THEN /\ thread' = [thread EXCEPT ![next[self]].ttbr0 = MakeTTB(<< "zero", 0 >>, "reserved")]
                              ELSE /\ thread' = [thread EXCEPT ![next[self]].ttbr0 = MakeTTB(<< (thread[next[self]].mm), 0 >>, (thread[next[self]].mm))]
                   ELSE /\ TRUE
                        /\ UNCHANGED thread
             /\ pc' = [pc EXCEPT ![self] = "sm3"]
             /\ UNCHANGED << current, interrupts, preempt_count, mode, tlb, 
                             runqueue, pt_regs, cpu, stack, next_mm, __mm, 
                             prev_mm, next, active_mm, next_thread, entry_el, 
                             exit_el, mm_efi >>

sm3(self) == /\ pc[self] = "sm3"
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ prev_mm' = [prev_mm EXCEPT ![self] = Head(stack[self]).prev_mm]
             /\ next' = [next EXCEPT ![self] = Head(stack[self]).next]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << current, interrupts, preempt_count, mode, tlb, 
                             runqueue, pt_regs, thread, cpu, next_mm, __mm, 
                             active_mm, next_thread, entry_el, exit_el, mm_efi >>

switch_mm(self) == sm1(self) \/ sm2(self) \/ sm3(self)

um1(self) == /\ pc[self] = "um1"
             /\ preempt_count' = [preempt_count EXCEPT ![self] = preempt_count[self] + 1]
             /\ \E mm \in MMS:
                  /\ active_mm' = [active_mm EXCEPT ![self] = thread[current[self]].active_mm]
                  /\ thread' = [thread EXCEPT ![current[self]].active_mm = mm,
                                              ![current[self]].mm = mm]
                  /\ /\ next' = [next EXCEPT ![self] = current[self]]
                     /\ prev_mm' = [prev_mm EXCEPT ![self] = active_mm'[self]]
                     /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "switch_mm",
                                                              pc        |->  "um2",
                                                              prev_mm   |->  prev_mm[self],
                                                              next      |->  next[self] ] >>
                                                          \o stack[self]]
                  /\ pc' = [pc EXCEPT ![self] = "sm1"]
             /\ UNCHANGED << current, interrupts, mode, tlb, runqueue, pt_regs, 
                             cpu, next_mm, __mm, next_thread, entry_el, 
                             exit_el, mm_efi >>

um2(self) == /\ pc[self] = "um2"
             /\ preempt_count' = [preempt_count EXCEPT ![self] = preempt_count[self] - 1]
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ active_mm' = [active_mm EXCEPT ![self] = Head(stack[self]).active_mm]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << current, interrupts, mode, tlb, runqueue, pt_regs, 
                             thread, cpu, next_mm, __mm, prev_mm, next, 
                             next_thread, entry_el, exit_el, mm_efi >>

use_mm(self) == um1(self) \/ um2(self)

unm1(self) == /\ pc[self] = "unm1"
              /\ preempt_count' = [preempt_count EXCEPT ![self] = preempt_count[self] + 1]
              /\ thread' = [thread EXCEPT ![current[self]].mm = "null"]
              /\ pc' = [pc EXCEPT ![self] = "unm2"]
              /\ UNCHANGED << current, interrupts, mode, tlb, runqueue, 
                              pt_regs, cpu, stack, next_mm, __mm, prev_mm, 
                              next, active_mm, next_thread, entry_el, exit_el, 
                              mm_efi >>

unm2(self) == /\ pc[self] = "unm2"
              /\ IF TTBR0_PAN
                    THEN /\ IF "init_mm" = "init_mm"
                               THEN /\ thread' = [thread EXCEPT ![(current[self])].ttbr0 = MakeTTB(<< "zero", 0 >>, "reserved")]
                               ELSE /\ thread' = [thread EXCEPT ![(current[self])].ttbr0 = MakeTTB(<< "init_mm", 0 >>, "init_mm")]
                    ELSE /\ TRUE
                         /\ UNCHANGED thread
              /\ preempt_count' = [preempt_count EXCEPT ![self] = preempt_count[self] - 1]
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << current, interrupts, mode, tlb, runqueue, 
                              pt_regs, cpu, next_mm, __mm, prev_mm, next, 
                              active_mm, next_thread, entry_el, exit_el, 
                              mm_efi >>

unuse_mm(self) == unm1(self) \/ unm2(self)

cs1(self) == /\ pc[self] = "cs1"
             /\ IF thread[next_thread[self]].mm = "null"
                   THEN /\ thread' = [thread EXCEPT ![next_thread[self]].active_mm = thread[current[self]].active_mm]
                        /\ pc' = [pc EXCEPT ![self] = "cs2"]
                        /\ UNCHANGED << stack, prev_mm, next >>
                   ELSE /\ /\ next' = [next EXCEPT ![self] = next_thread[self]]
                           /\ prev_mm' = [prev_mm EXCEPT ![self] = thread[current[self]].active_mm]
                           /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "switch_mm",
                                                                    pc        |->  "cs2",
                                                                    prev_mm   |->  prev_mm[self],
                                                                    next      |->  next[self] ] >>
                                                                \o stack[self]]
                        /\ pc' = [pc EXCEPT ![self] = "sm1"]
                        /\ UNCHANGED thread
             /\ UNCHANGED << current, interrupts, preempt_count, mode, tlb, 
                             runqueue, pt_regs, cpu, next_mm, __mm, active_mm, 
                             next_thread, entry_el, exit_el, mm_efi >>

cs2(self) == /\ pc[self] = "cs2"
             /\ IF thread[current[self]].mm = "null"
                   THEN /\ thread' = [thread EXCEPT ![current[self]].active_mm = "null"]
                   ELSE /\ TRUE
                        /\ UNCHANGED thread
             /\ pc' = [pc EXCEPT ![self] = "cs3"]
             /\ UNCHANGED << current, interrupts, preempt_count, mode, tlb, 
                             runqueue, pt_regs, cpu, stack, next_mm, __mm, 
                             prev_mm, next, active_mm, next_thread, entry_el, 
                             exit_el, mm_efi >>

cs3(self) == /\ pc[self] = "cs3"
             /\ IF current[self] # "idle"
                   THEN /\ runqueue' = (runqueue \cup {current[self]})
                   ELSE /\ TRUE
                        /\ UNCHANGED runqueue
             /\ current' = [current EXCEPT ![self] = next_thread[self]]
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ next_thread' = [next_thread EXCEPT ![self] = Head(stack[self]).next_thread]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << interrupts, preempt_count, mode, tlb, pt_regs, 
                             thread, cpu, next_mm, __mm, prev_mm, next, 
                             active_mm, entry_el, exit_el, mm_efi >>

context_switch(self) == cs1(self) \/ cs2(self) \/ cs3(self)

do_schedule(self) == /\ pc[self] = "do_schedule"
                     /\ IF preempt_count[self] > 0
                           THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "s1"]
                                /\ stack' = stack
                     /\ UNCHANGED << current, interrupts, preempt_count, mode, 
                                     tlb, runqueue, pt_regs, thread, cpu, 
                                     next_mm, __mm, prev_mm, next, active_mm, 
                                     next_thread, entry_el, exit_el, mm_efi >>

s1(self) == /\ pc[self] = "s1"
            /\ Assert(interrupts[self] = "off", 
                      "Failure of assertion at line 280, column 9.")
            /\ \/ /\ current[self] # "idle"
                  /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                  /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                  /\ UNCHANGED <<runqueue, thread, next_thread>>
               \/ /\ \E n \in runqueue:
                       /\ runqueue' = runqueue \ {n}
                       /\ IF thread[n].mm = "init_mm"
                             THEN /\ \E mm \in MMS \cup {"null"}:
                                       thread' = [thread EXCEPT ![n].mm = mm,
                                                                ![n].active_mm = mm]
                             ELSE /\ TRUE
                                  /\ UNCHANGED thread
                       /\ /\ next_thread' = [next_thread EXCEPT ![self] = n]
                          /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "context_switch",
                                                                   pc        |->  "schedule_done",
                                                                   next_thread |->  next_thread[self] ] >>
                                                               \o stack[self]]
                       /\ pc' = [pc EXCEPT ![self] = "cs1"]
            /\ UNCHANGED << current, interrupts, preempt_count, mode, tlb, 
                            pt_regs, cpu, next_mm, __mm, prev_mm, next, 
                            active_mm, entry_el, exit_el, mm_efi >>

schedule_done(self) == /\ pc[self] = "schedule_done"
                       /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                       /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                       /\ UNCHANGED << current, interrupts, preempt_count, 
                                       mode, tlb, runqueue, pt_regs, thread, 
                                       cpu, next_mm, __mm, prev_mm, next, 
                                       active_mm, next_thread, entry_el, 
                                       exit_el, mm_efi >>

schedule(self) == do_schedule(self) \/ s1(self) \/ schedule_done(self)

tmk1(self) == /\ pc[self] = "tmk1"
              /\ cpu' = [cpu EXCEPT ![self].ttbr1.baddr = "init_mm",
                                    ![self].ttbr1.asid[2] = 0]
              /\ pc' = [pc EXCEPT ![self] = "tmk2"]
              /\ UNCHANGED << current, interrupts, preempt_count, mode, tlb, 
                              runqueue, pt_regs, thread, stack, next_mm, __mm, 
                              prev_mm, next, active_mm, next_thread, entry_el, 
                              exit_el, mm_efi >>

tmk2(self) == /\ pc[self] = "tmk2"
              /\ tlb' = (tlb \cup ActiveTLBs)
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << current, interrupts, preempt_count, mode, 
                              runqueue, pt_regs, thread, cpu, next_mm, __mm, 
                              prev_mm, next, active_mm, next_thread, entry_el, 
                              exit_el, mm_efi >>

tramp_map_kernel(self) == tmk1(self) \/ tmk2(self)

tuk1(self) == /\ pc[self] = "tuk1"
              /\ cpu' = [cpu EXCEPT ![self].ttbr1.baddr = "trampoline",
                                    ![self].ttbr1.asid[2] = 1]
              /\ pc' = [pc EXCEPT ![self] = "tuk2"]
              /\ UNCHANGED << current, interrupts, preempt_count, mode, tlb, 
                              runqueue, pt_regs, thread, stack, next_mm, __mm, 
                              prev_mm, next, active_mm, next_thread, entry_el, 
                              exit_el, mm_efi >>

tuk2(self) == /\ pc[self] = "tuk2"
              /\ tlb' = (tlb \cup ActiveTLBs)
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << current, interrupts, preempt_count, mode, 
                              runqueue, pt_regs, thread, cpu, next_mm, __mm, 
                              prev_mm, next, active_mm, next_thread, entry_el, 
                              exit_el, mm_efi >>

tramp_unmap_kernel(self) == tuk1(self) \/ tuk2(self)

ken1(self) == /\ pc[self] = "ken1"
              /\ Assert(interrupts[self] = "off", 
                        "Failure of assertion at line 315, column 9.")
              /\ mode' = [mode EXCEPT ![self] = "kernel"]
              /\ IF ~KernelMapped(self)
                    THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "tramp_map_kernel",
                                                                  pc        |->  "ken2" ] >>
                                                              \o stack[self]]
                         /\ pc' = [pc EXCEPT ![self] = "tmk1"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "ken2"]
                         /\ stack' = stack
              /\ UNCHANGED << current, interrupts, preempt_count, tlb, 
                              runqueue, pt_regs, thread, cpu, next_mm, __mm, 
                              prev_mm, next, active_mm, next_thread, entry_el, 
                              exit_el, mm_efi >>

ken2(self) == /\ pc[self] = "ken2"
              /\ IF TTBR0_PAN
                    THEN /\ IF entry_el[self] = "kernel" /\ cpu[self].ttbr0.asid = << "zero", 0 >>
                               THEN /\ thread' = [thread EXCEPT ![current[self]].psr_pan_bit = TRUE]
                                    /\ pc' = [pc EXCEPT ![self] = "ken3"]
                                    /\ stack' = stack
                               ELSE /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "__uaccess_ttbr0_disable",
                                                                             pc        |->  "ken3" ] >>
                                                                         \o stack[self]]
                                    /\ pc' = [pc EXCEPT ![self] = "_utd1"]
                                    /\ UNCHANGED thread
                    ELSE /\ pc' = [pc EXCEPT ![self] = "ken3"]
                         /\ UNCHANGED << thread, stack >>
              /\ UNCHANGED << current, interrupts, preempt_count, mode, tlb, 
                              runqueue, pt_regs, cpu, next_mm, __mm, prev_mm, 
                              next, active_mm, next_thread, entry_el, exit_el, 
                              mm_efi >>

ken3(self) == /\ pc[self] = "ken3"
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ entry_el' = [entry_el EXCEPT ![self] = Head(stack[self]).entry_el]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << current, interrupts, preempt_count, mode, tlb, 
                              runqueue, pt_regs, thread, cpu, next_mm, __mm, 
                              prev_mm, next, active_mm, next_thread, exit_el, 
                              mm_efi >>

kernel_entry(self) == ken1(self) \/ ken2(self) \/ ken3(self)

kex1(self) == /\ pc[self] = "kex1"
              /\ Assert(interrupts[self] = "off", 
                        "Failure of assertion at line 330, column 9.")
              /\ IF TTBR0_PAN
                    THEN /\ IF exit_el[self] = "kernel" /\ thread[current[self]].psr_pan_bit
                               THEN /\ thread' = [thread EXCEPT ![current[self]].psr_pan_bit = FALSE]
                                    /\ pc' = [pc EXCEPT ![self] = "kex2"]
                                    /\ stack' = stack
                               ELSE /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "__uaccess_ttbr0_enable",
                                                                             pc        |->  "kex2" ] >>
                                                                         \o stack[self]]
                                    /\ pc' = [pc EXCEPT ![self] = "_ute1"]
                                    /\ UNCHANGED thread
                    ELSE /\ pc' = [pc EXCEPT ![self] = "kex2"]
                         /\ UNCHANGED << thread, stack >>
              /\ UNCHANGED << current, interrupts, preempt_count, mode, tlb, 
                              runqueue, pt_regs, cpu, next_mm, __mm, prev_mm, 
                              next, active_mm, next_thread, entry_el, exit_el, 
                              mm_efi >>

kex2(self) == /\ pc[self] = "kex2"
              /\ IF exit_el[self] = "user"
                    THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "tramp_unmap_kernel",
                                                                  pc        |->  "kex3" ] >>
                                                              \o stack[self]]
                         /\ pc' = [pc EXCEPT ![self] = "tuk1"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "kex3"]
                         /\ stack' = stack
              /\ UNCHANGED << current, interrupts, preempt_count, mode, tlb, 
                              runqueue, pt_regs, thread, cpu, next_mm, __mm, 
                              prev_mm, next, active_mm, next_thread, entry_el, 
                              exit_el, mm_efi >>

kex3(self) == /\ pc[self] = "kex3"
              /\ mode' = [mode EXCEPT ![self] = exit_el[self]]
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ exit_el' = [exit_el EXCEPT ![self] = Head(stack[self]).exit_el]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << current, interrupts, preempt_count, tlb, 
                              runqueue, pt_regs, thread, cpu, next_mm, __mm, 
                              prev_mm, next, active_mm, next_thread, entry_el, 
                              mm_efi >>

kernel_exit(self) == kex1(self) \/ kex2(self) \/ kex3(self)

interrupt_handler(self) == /\ pc[self] = "interrupt_handler"
                           /\ /\ entry_el' = [entry_el EXCEPT ![self] = mode[self]]
                              /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "kernel_entry",
                                                                       pc        |->  "i1",
                                                                       entry_el  |->  entry_el[self] ] >>
                                                                   \o stack[self]]
                           /\ pc' = [pc EXCEPT ![self] = "ken1"]
                           /\ UNCHANGED << current, interrupts, preempt_count, 
                                           mode, tlb, runqueue, pt_regs, 
                                           thread, cpu, next_mm, __mm, prev_mm, 
                                           next, active_mm, next_thread, 
                                           exit_el, mm_efi >>

i1(self) == /\ pc[self] = "i1"
            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "schedule",
                                                     pc        |->  "i2" ] >>
                                                 \o stack[self]]
            /\ pc' = [pc EXCEPT ![self] = "do_schedule"]
            /\ UNCHANGED << current, interrupts, preempt_count, mode, tlb, 
                            runqueue, pt_regs, thread, cpu, next_mm, __mm, 
                            prev_mm, next, active_mm, next_thread, entry_el, 
                            exit_el, mm_efi >>

i2(self) == /\ pc[self] = "i2"
            /\ IF pt_regs[current[self]].interrupted
                  THEN /\ pt_regs' = [pt_regs EXCEPT ![current[self]].interrupted = FALSE]
                       /\ /\ exit_el' = [exit_el EXCEPT ![self] = pt_regs'[current[self]].mode]
                          /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "kernel_exit",
                                                                   pc        |->  "ret_from_interrupt",
                                                                   exit_el   |->  exit_el[self] ] >>
                                                               \o stack[self]]
                       /\ pc' = [pc EXCEPT ![self] = "kex1"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "ret_from_interrupt"]
                       /\ UNCHANGED << pt_regs, stack, exit_el >>
            /\ UNCHANGED << current, interrupts, preempt_count, mode, tlb, 
                            runqueue, thread, cpu, next_mm, __mm, prev_mm, 
                            next, active_mm, next_thread, entry_el, mm_efi >>

ret_from_interrupt(self) == /\ pc[self] = "ret_from_interrupt"
                            /\ FALSE
                            /\ pc' = [pc EXCEPT ![self] = "Error"]
                            /\ UNCHANGED << current, interrupts, preempt_count, 
                                            mode, tlb, runqueue, pt_regs, 
                                            thread, cpu, stack, next_mm, __mm, 
                                            prev_mm, next, active_mm, 
                                            next_thread, entry_el, exit_el, 
                                            mm_efi >>

interrupt(self) == interrupt_handler(self) \/ i1(self) \/ i2(self)
                      \/ ret_from_interrupt(self)

rtu1(self) == /\ pc[self] = "rtu1"
              /\ Assert(mode[self] = "kernel", 
                        "Failure of assertion at line 361, column 9.")
              /\ Assert(interrupts[self] = "on", 
                        "Failure of assertion at line 118, column 9 of macro called at line 362, column 9.")
              /\ interrupts' = [interrupts EXCEPT ![self] = "off"]
              /\ pc' = [pc EXCEPT ![self] = "rtu2"]
              /\ UNCHANGED << current, preempt_count, mode, tlb, runqueue, 
                              pt_regs, thread, cpu, stack, next_mm, __mm, 
                              prev_mm, next, active_mm, next_thread, entry_el, 
                              exit_el, mm_efi >>

rtu2(self) == /\ pc[self] = "rtu2"
              /\ /\ exit_el' = [exit_el EXCEPT ![self] = "user"]
                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "kernel_exit",
                                                          pc        |->  "rtu3",
                                                          exit_el   |->  exit_el[self] ] >>
                                                      \o stack[self]]
              /\ pc' = [pc EXCEPT ![self] = "kex1"]
              /\ UNCHANGED << current, interrupts, preempt_count, mode, tlb, 
                              runqueue, pt_regs, thread, cpu, next_mm, __mm, 
                              prev_mm, next, active_mm, next_thread, entry_el, 
                              mm_efi >>

rtu3(self) == /\ pc[self] = "rtu3"
              /\ interrupts' = [interrupts EXCEPT ![self] = "on"]
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << current, preempt_count, mode, tlb, runqueue, 
                              pt_regs, thread, cpu, next_mm, __mm, prev_mm, 
                              next, active_mm, next_thread, entry_el, exit_el, 
                              mm_efi >>

ret_to_user(self) == rtu1(self) \/ rtu2(self) \/ rtu3(self)

sys1(self) == /\ pc[self] = "sys1"
              /\ Assert(mode[self] = "user", 
                        "Failure of assertion at line 370, column 9.")
              /\ Assert(interrupts[self] = "on", 
                        "Failure of assertion at line 118, column 9 of macro called at line 371, column 9.")
              /\ interrupts' = [interrupts EXCEPT ![self] = "off"]
              /\ pc' = [pc EXCEPT ![self] = "sys2"]
              /\ UNCHANGED << current, preempt_count, mode, tlb, runqueue, 
                              pt_regs, thread, cpu, stack, next_mm, __mm, 
                              prev_mm, next, active_mm, next_thread, entry_el, 
                              exit_el, mm_efi >>

sys2(self) == /\ pc[self] = "sys2"
              /\ /\ entry_el' = [entry_el EXCEPT ![self] = mode[self]]
                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "kernel_entry",
                                                          pc        |->  "sys3",
                                                          entry_el  |->  entry_el[self] ] >>
                                                      \o stack[self]]
              /\ pc' = [pc EXCEPT ![self] = "ken1"]
              /\ UNCHANGED << current, interrupts, preempt_count, mode, tlb, 
                              runqueue, pt_regs, thread, cpu, next_mm, __mm, 
                              prev_mm, next, active_mm, next_thread, exit_el, 
                              mm_efi >>

sys3(self) == /\ pc[self] = "sys3"
              /\ interrupts' = [interrupts EXCEPT ![self] = "on"]
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << current, preempt_count, mode, tlb, runqueue, 
                              pt_regs, thread, cpu, next_mm, __mm, prev_mm, 
                              next, active_mm, next_thread, entry_el, exit_el, 
                              mm_efi >>

syscall(self) == sys1(self) \/ sys2(self) \/ sys3(self)

ua1(self) == /\ pc[self] = "ua1"
             /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "uaccess_ttbr0_enable",
                                                      pc        |->  "ua2" ] >>
                                                  \o stack[self]]
             /\ pc' = [pc EXCEPT ![self] = "ute1"]
             /\ UNCHANGED << current, interrupts, preempt_count, mode, tlb, 
                             runqueue, pt_regs, thread, cpu, next_mm, __mm, 
                             prev_mm, next, active_mm, next_thread, entry_el, 
                             exit_el, mm_efi >>

ua2(self) == /\ pc[self] = "ua2"
             /\ Assert(/\ cpu[self].ttbr0.baddr \in MMS
                       /\ cpu[self].ttbr0.baddr = thread[current[self]].active_mm, 
                       "Failure of assertion at line 380, column 9.")
             /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "uaccess_ttbr0_disable",
                                                      pc        |->  "ua3" ] >>
                                                  \o stack[self]]
             /\ pc' = [pc EXCEPT ![self] = "utd1"]
             /\ UNCHANGED << current, interrupts, preempt_count, mode, tlb, 
                             runqueue, pt_regs, thread, cpu, next_mm, __mm, 
                             prev_mm, next, active_mm, next_thread, entry_el, 
                             exit_el, mm_efi >>

ua3(self) == /\ pc[self] = "ua3"
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << current, interrupts, preempt_count, mode, tlb, 
                             runqueue, pt_regs, thread, cpu, next_mm, __mm, 
                             prev_mm, next, active_mm, next_thread, entry_el, 
                             exit_el, mm_efi >>

uaccess(self) == ua1(self) \/ ua2(self) \/ ua3(self)

esp1(self) == /\ pc[self] = "esp1"
              /\ /\ __mm' = [__mm EXCEPT ![self] = mm_efi[self]]
                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "__switch_mm",
                                                          pc        |->  "esp2",
                                                          __mm      |->  __mm[self] ] >>
                                                      \o stack[self]]
              /\ pc' = [pc EXCEPT ![self] = "_sm1"]
              /\ UNCHANGED << current, interrupts, preempt_count, mode, tlb, 
                              runqueue, pt_regs, thread, cpu, next_mm, prev_mm, 
                              next, active_mm, next_thread, entry_el, exit_el, 
                              mm_efi >>

esp2(self) == /\ pc[self] = "esp2"
              /\ IF TTBR0_PAN
                    THEN /\ IF mm_efi[self] # thread[current[self]].active_mm
                               THEN /\ IF TTBR0_PAN
                                          THEN /\ IF mm_efi[self] = "init_mm"
                                                     THEN /\ thread' = [thread EXCEPT ![(current[self])].ttbr0 = MakeTTB(<< "zero", 0 >>, "reserved")]
                                                     ELSE /\ thread' = [thread EXCEPT ![(current[self])].ttbr0 = MakeTTB(<< mm_efi[self], 0 >>, mm_efi[self])]
                                          ELSE /\ TRUE
                                               /\ UNCHANGED thread
                                    /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "uaccess_ttbr0_enable",
                                                                             pc        |->  "esp4" ] >>
                                                                         \o stack[self]]
                                    /\ pc' = [pc EXCEPT ![self] = "ute1"]
                               ELSE /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "uaccess_ttbr0_disable",
                                                                             pc        |->  "esp3" ] >>
                                                                         \o stack[self]]
                                    /\ pc' = [pc EXCEPT ![self] = "utd1"]
                                    /\ UNCHANGED thread
                    ELSE /\ pc' = [pc EXCEPT ![self] = "esp4"]
                         /\ UNCHANGED << thread, stack >>
              /\ UNCHANGED << current, interrupts, preempt_count, mode, tlb, 
                              runqueue, pt_regs, cpu, next_mm, __mm, prev_mm, 
                              next, active_mm, next_thread, entry_el, exit_el, 
                              mm_efi >>

esp3(self) == /\ pc[self] = "esp3"
              /\ IF TTBR0_PAN
                    THEN /\ IF (thread[current[self]].active_mm) = "init_mm"
                               THEN /\ thread' = [thread EXCEPT ![(current[self])].ttbr0 = MakeTTB(<< "zero", 0 >>, "reserved")]
                               ELSE /\ thread' = [thread EXCEPT ![(current[self])].ttbr0 = MakeTTB(<< (thread[current[self]].active_mm), 0 >>, (thread[current[self]].active_mm))]
                    ELSE /\ TRUE
                         /\ UNCHANGED thread
              /\ pc' = [pc EXCEPT ![self] = "esp4"]
              /\ UNCHANGED << current, interrupts, preempt_count, mode, tlb, 
                              runqueue, pt_regs, cpu, stack, next_mm, __mm, 
                              prev_mm, next, active_mm, next_thread, entry_el, 
                              exit_el, mm_efi >>

esp4(self) == /\ pc[self] = "esp4"
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ mm_efi' = [mm_efi EXCEPT ![self] = Head(stack[self]).mm_efi]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << current, interrupts, preempt_count, mode, tlb, 
                              runqueue, pt_regs, thread, cpu, next_mm, __mm, 
                              prev_mm, next, active_mm, next_thread, entry_el, 
                              exit_el >>

efi_set_pgd(self) == esp1(self) \/ esp2(self) \/ esp3(self) \/ esp4(self)

ecv1(self) == /\ pc[self] = "ecv1"
              /\ preempt_count' = [preempt_count EXCEPT ![self] = preempt_count[self] + 1]
              /\ /\ mm_efi' = [mm_efi EXCEPT ![self] = "efi_mm"]
                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "efi_set_pgd",
                                                          pc        |->  "ecv2",
                                                          mm_efi    |->  mm_efi[self] ] >>
                                                      \o stack[self]]
              /\ pc' = [pc EXCEPT ![self] = "esp1"]
              /\ UNCHANGED << current, interrupts, mode, tlb, runqueue, 
                              pt_regs, thread, cpu, next_mm, __mm, prev_mm, 
                              next, active_mm, next_thread, entry_el, exit_el >>

ecv2(self) == /\ pc[self] = "ecv2"
              /\ /\ mm_efi' = [mm_efi EXCEPT ![self] = thread[current[self]].active_mm]
                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "efi_set_pgd",
                                                          pc        |->  "ecv3",
                                                          mm_efi    |->  mm_efi[self] ] >>
                                                      \o stack[self]]
              /\ pc' = [pc EXCEPT ![self] = "esp1"]
              /\ UNCHANGED << current, interrupts, preempt_count, mode, tlb, 
                              runqueue, pt_regs, thread, cpu, next_mm, __mm, 
                              prev_mm, next, active_mm, next_thread, entry_el, 
                              exit_el >>

ecv3(self) == /\ pc[self] = "ecv3"
              /\ preempt_count' = [preempt_count EXCEPT ![self] = preempt_count[self] - 1]
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << current, interrupts, mode, tlb, runqueue, 
                              pt_regs, thread, cpu, next_mm, __mm, prev_mm, 
                              next, active_mm, next_thread, entry_el, exit_el, 
                              mm_efi >>

efi_call_virt(self) == ecv1(self) \/ ecv2(self) \/ ecv3(self)

rk1(self) == /\ pc[self] = "rk1"
             /\ Assert(cpu[self].ttbr1.baddr = "init_mm", 
                       "Failure of assertion at line 416, column 9.")
             /\ \/ /\ ~KernelThread(current[self])
                   /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "ret_to_user",
                                                            pc        |->  "rk4" ] >>
                                                        \o stack[self]]
                   /\ pc' = [pc EXCEPT ![self] = "rtu1"]
                   /\ UNCHANGED active_mm
                \/ /\ ~KernelThread(current[self])
                   /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "uaccess",
                                                            pc        |->  "rk4" ] >>
                                                        \o stack[self]]
                   /\ pc' = [pc EXCEPT ![self] = "ua1"]
                   /\ UNCHANGED active_mm
                \/ /\ KernelThread(current[self])
                   /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "use_mm",
                                                            pc        |->  "rk2",
                                                            active_mm |->  active_mm[self] ] >>
                                                        \o stack[self]]
                   /\ active_mm' = [active_mm EXCEPT ![self] = defaultInitValue]
                   /\ pc' = [pc EXCEPT ![self] = "um1"]
                \/ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "efi_call_virt",
                                                            pc        |->  "rk4" ] >>
                                                        \o stack[self]]
                   /\ pc' = [pc EXCEPT ![self] = "ecv1"]
                   /\ UNCHANGED active_mm
             /\ UNCHANGED << current, interrupts, preempt_count, mode, tlb, 
                             runqueue, pt_regs, thread, cpu, next_mm, __mm, 
                             prev_mm, next, next_thread, entry_el, exit_el, 
                             mm_efi >>

rk2(self) == /\ pc[self] = "rk2"
             /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "uaccess",
                                                      pc        |->  "rk3" ] >>
                                                  \o stack[self]]
             /\ pc' = [pc EXCEPT ![self] = "ua1"]
             /\ UNCHANGED << current, interrupts, preempt_count, mode, tlb, 
                             runqueue, pt_regs, thread, cpu, next_mm, __mm, 
                             prev_mm, next, active_mm, next_thread, entry_el, 
                             exit_el, mm_efi >>

rk3(self) == /\ pc[self] = "rk3"
             /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "unuse_mm",
                                                      pc        |->  "rk4" ] >>
                                                  \o stack[self]]
             /\ pc' = [pc EXCEPT ![self] = "unm1"]
             /\ UNCHANGED << current, interrupts, preempt_count, mode, tlb, 
                             runqueue, pt_regs, thread, cpu, next_mm, __mm, 
                             prev_mm, next, active_mm, next_thread, entry_el, 
                             exit_el, mm_efi >>

rk4(self) == /\ pc[self] = "rk4"
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << current, interrupts, preempt_count, mode, tlb, 
                             runqueue, pt_regs, thread, cpu, next_mm, __mm, 
                             prev_mm, next, active_mm, next_thread, entry_el, 
                             exit_el, mm_efi >>

run_kernel(self) == rk1(self) \/ rk2(self) \/ rk3(self) \/ rk4(self)

ru1(self) == /\ pc[self] = "ru1"
             /\ Assert(/\ cpu[self].ttbr0.baddr \in MMS
                       /\ ~thread[current[self]].psr_pan_bit, 
                       "Failure of assertion at line 436, column 9.")
             /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "syscall",
                                                      pc        |->  Head(stack[self]).pc ] >>
                                                  \o Tail(stack[self])]
             /\ pc' = [pc EXCEPT ![self] = "sys1"]
             /\ UNCHANGED << current, interrupts, preempt_count, mode, tlb, 
                             runqueue, pt_regs, thread, cpu, next_mm, __mm, 
                             prev_mm, next, active_mm, next_thread, entry_el, 
                             exit_el, mm_efi >>

run_user(self) == ru1(self)

start_thread(self) == /\ pc[self] = "start_thread"
                      /\ Assert(interrupts[self] = "on", 
                                "Failure of assertion at line 446, column 17.")
                      /\ \/ /\ mode[self] = "kernel"
                            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "run_kernel",
                                                                     pc        |->  "start_thread" ] >>
                                                                 \o stack[self]]
                            /\ pc' = [pc EXCEPT ![self] = "rk1"]
                         \/ /\ mode[self] = "user"
                            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "run_user",
                                                                     pc        |->  "start_thread" ] >>
                                                                 \o stack[self]]
                            /\ pc' = [pc EXCEPT ![self] = "ru1"]
                         \/ /\ TRUE
                            /\ pc' = [pc EXCEPT ![self] = "start_thread"]
                            /\ stack' = stack
                      /\ UNCHANGED << current, interrupts, preempt_count, mode, 
                                      tlb, runqueue, pt_regs, thread, cpu, 
                                      next_mm, __mm, prev_mm, next, active_mm, 
                                      next_thread, entry_el, exit_el, mm_efi >>

run_thread(self) == start_thread(self)

start_cpu(self) == /\ pc[self] = "start_cpu"
                   /\ thread' = [thread EXCEPT !["idle"].active_mm = "init_mm"]
                   /\ tlb' = (tlb \cup ActiveTLBs)
                   /\ interrupts' = [interrupts EXCEPT ![self] = "on"]
                   /\ pc' = [pc EXCEPT ![self] = "idle"]
                   /\ UNCHANGED << current, preempt_count, mode, runqueue, 
                                   pt_regs, cpu, stack, next_mm, __mm, prev_mm, 
                                   next, active_mm, next_thread, entry_el, 
                                   exit_el, mm_efi >>

idle(self) == /\ pc[self] = "idle"
              /\ FALSE
              /\ pc' = [pc EXCEPT ![self] = "Done"]
              /\ UNCHANGED << current, interrupts, preempt_count, mode, tlb, 
                              runqueue, pt_regs, thread, cpu, stack, next_mm, 
                              __mm, prev_mm, next, active_mm, next_thread, 
                              entry_el, exit_el, mm_efi >>

Processor(self) == start_cpu(self) \/ idle(self)

Next == (\E self \in ProcSet:  \/ __uaccess_ttbr0_disable(self)
                               \/ __uaccess_ttbr0_enable(self)
                               \/ uaccess_ttbr0_disable(self)
                               \/ uaccess_ttbr0_enable(self)
                               \/ cpu_switch_mm(self) \/ __switch_mm(self)
                               \/ switch_mm(self) \/ use_mm(self)
                               \/ unuse_mm(self) \/ context_switch(self)
                               \/ schedule(self) \/ tramp_map_kernel(self)
                               \/ tramp_unmap_kernel(self)
                               \/ kernel_entry(self) \/ kernel_exit(self)
                               \/ interrupt(self) \/ ret_to_user(self)
                               \/ syscall(self) \/ uaccess(self)
                               \/ efi_set_pgd(self) \/ efi_call_virt(self)
                               \/ run_kernel(self) \/ run_user(self)
                               \/ run_thread(self))
           \/ (\E self \in CPUS: Processor(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

int_vars == <<current, cpu, mode, thread, runqueue, tlb, preempt_count,
	      active_mm, prev_mm, next, next_thread, next_mm, __mm, mm_efi,
	      entry_el, exit_el>>

\* Handle interrupt. Save current thread context and invoke handler
HandleInt(self)	== /\ interrupts[self] = "on"		\* only when interrupts are enabled
		   \* Save current thread's context
		   /\ pt_regs' = [pt_regs EXCEPT ![current[self]].pc = pc[self],
						 ![current[self]].sp = stack[self],
						 ![current[self]].mode = mode[self],
						 ![current[self]].interrupted = TRUE]
		   /\ interrupts' = [interrupts EXCEPT ![self] = "off"]	\* turn interrupts off
		   \* Invoke the interrupt handler
		   /\ pc' = [pc EXCEPT ![self] = "interrupt_handler"]
		   /\ UNCHANGED <<stack>>
		   /\ UNCHANGED int_vars

\* Return from interrupt. Restore current thread context
ReturnInt(self)	== /\ pc[self] = "ret_from_interrupt"
		   \* Restore the current thread's context
		   /\ pc' = [pc EXCEPT ![self] = pt_regs[current[self]].pc]
		   /\ stack' = [stack EXCEPT ![self] = pt_regs[current[self]].sp]
		   /\ interrupts' = [interrupts EXCEPT ![self] = "on"]	\* re-enable interrupts
		   /\ UNCHANGED <<pt_regs>>
		   /\ UNCHANGED int_vars

Interrupt(self)	== HandleInt(self) \/ ReturnInt(self)

PreemptNext == (\E self \in ProcSet : Interrupt(self)) \/ Next

PreemptSpec == Init /\ [][PreemptNext]_vars
==============================================================================
