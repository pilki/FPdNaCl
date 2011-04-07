Require Import Lib.
Require Import BinaryProps.
Require Import List.
Require Import Program.
Require Import LazyList.

Set Implicit Arguments.

(* classification of instructions *)

Inductive instruction_classification (register:Type) : Type :=
  (* an instruction that only modifies register and memory, but does not jump *)
| OK_instr: instruction_classification register
  (* an instruction that masks the value of a register *)
| Mask_instr: register -> word -> instruction_classification register
  (* a (optional) direct jump to a static address *)
| Direct_jump: word -> instruction_classification register
  (* an (optional) indirect jump to the address in a given register *)
| Indirect_jump: register -> instruction_classification register
  (* a dangerous instruction *)
| Invalid_instruction: instruction_classification register.

Implicit Arguments OK_instr [[register]].
Implicit Arguments Direct_jump [[register]].
Implicit Arguments Indirect_jump [[register]].
Implicit Arguments Invalid_instruction [[register]].

Definition memory := N -> option byte.

(* the state of the machine *)

Record state (register:Type) :=
  { state_mem: memory;
    state_regs: register -> word;
    state_pc: N}.
Implicit Arguments state_mem [[register]].
Implicit Arguments state_regs [[register]].
Implicit Arguments state_pc [[register]].

(* the target state of a semantic transformation *)
Inductive instruction_target_state register :=
| Good_state: state register -> instruction_target_state register
| Bad_state: instruction_target_state register.

Implicit Arguments Good_state [[register]].
Implicit Arguments Bad_state [[register]].

Inductive is_good_state {register}: instruction_target_state register -> Prop :=
| Is_Good_State: forall state, is_good_state (Good_state state).



Module Type INSTRUCTION.

  Parameter register: Type.
  Parameter register_eq_dec: forall r1 r2: register, {r1 = r2}+{r1 <> r2}.
  Parameter instruction: Type.

  (* parse an instruction *)
  Parameter parse_instruction: byte_map -> option (instruction * nat).

  Parameter parse_instruction_do_read:
    forall bm instr n, parse_instruction bm = Some (instr, n) ->
    forall n', (n' < n)%nat -> is_some (bm n').

  Parameter parse_instruction_only_read:
    forall bm instr n, parse_instruction bm = Some (instr, n) ->
    forall bm', (forall n', (n' < n)%nat -> bm n' = bm' n') ->
      parse_instruction bm' = Some (instr, n).

  Parameter size_instr_not_0: forall bm instr n,
    parse_instruction bm = Some (instr, n) -> n <> O.

  Parameter classify_instruction: instruction -> instruction_classification register.

  Parameter instruction_semantics: N -> instruction ->
    state register -> instruction_target_state register -> Prop.

End INSTRUCTION.



(*Fixpoint pow2 (n: nat) :=
  match n with
    | O => 1
    | S n' => 2 * pow2 n'
  end.


Definition dividable_by_pow2 (p: nat) (n:N) :=
  exists d:N, n = (pow2 p) * d.

Lemma dividable_by_pow2_dec:
  forall p n, {dividable_by_pow2 p n}+{~dividable_by_pow2 p n}.
Proof.
  unfold dividable_by_pow2.
  intros. destruct' n as [|pos].
  Case "0".
  left. exists 0. zify. omega.
  Case "Npos pos".
  revert p.
  induction' pos as [pos|pos|]; intros.
  SCase "xI pos".
  destruct' p as [|p'].
    SSCase "0%nat".
    left. exists (Npos pos~1). reflexivity.
    SSCase "S p'".
    right. intros [d H]. simpl in H. destruct (pow2 p').
      inv H.
      simpl in H. destruct d; inv H.

   SCase "xO pos".
   destruct' p as [|p'].
   SSCase "0%nat".
     left. exists (Npos pos~0). reflexivity.
   SSCase "S p'".
     destruct' (IHpos p') as [EXISTS|NEXISTS].
     S3Case "left EXISTS".
       left. destruct EXISTS as [d H].
       exists d. simpl. destruct (pow2 p'). inv H.
       simpl. destruct d. inv H. inv H. reflexivity.

     S3Case "right NEXISTS".
       right. intros [d H].
       apply NEXISTS.
       simpl in H. destruct (pow2 p'). inv H.
       exists d. simpl. destruct d; inv H. reflexivity.

  SCase "1%positive".
   destruct' p as [|p'].
   SSCase "0%nat".
     left. exists 1. reflexivity.
   SSCase "S p'".
     right. intros [d H]. simpl in H. destruct (pow2 p'); inv H.
     destruct d; inv H1.
Qed.*)

Definition dividable_by_32 (n:N) :=
  exists d:N, n = 32 * d.

Program Definition dividable_by_32_dec n
  : {dividable_by_32 n} + {~dividable_by_32 n}:=
  match n with
    | N0 => left _
    | Npos p~0~0~0~0~0 => left _
    | Npos _ => right _
  end.
Next Obligation.
  unfold dividable_by_32. exists 0. reflexivity.
Qed.
Next Obligation.
  unfold dividable_by_32. simpl. exists (Npos p). reflexivity.
Qed.
Next Obligation.
  destruct wildcard' as [wildcard'|wildcard'|]; try solve
    [let H0 := fresh "H" in intros [[|?] H0]; simpl in H0; inv H0].
  destruct wildcard' as [wildcard'|wildcard'|]; try solve
    [let H0 := fresh "H" in intros [[|?] H0]; simpl in H0; inv H0].
  destruct wildcard' as [wildcard'|wildcard'|]; try solve
    [let H0 := fresh "H" in intros [[|?] H0]; simpl in H0; inv H0].
  destruct wildcard' as [wildcard'|wildcard'|]; try solve
    [let H0 := fresh "H" in intros [[|?] H0]; simpl in H0; inv H0].
  destruct wildcard' as [wildcard'|wildcard'|]; try solve
    [let H0 := fresh "H" in intros [[|?] H0]; simpl in H0; inv H0].
  intro. apply (H wildcard'). reflexivity.
Qed.



(* Define the semantics of programs, parameterized by those of instruction *)
Module Prog_Semantics (Import I: INSTRUCTION).

  Inductive target_state :=
    (* a regular state *)
  | Normal_state: state register -> target_state
    (* a state that should *never* be reached ! *)
  | DANGER_STATE: target_state.


  Definition read_instr_from_memory (mem: memory) (pc: N): option (instruction * nat) :=
    parse_instruction (fun n => mem ((N_of_nat n) + pc)).





  (* parse an instruction *)
  Definition same_code (code_segment_size: N) (mem1 mem2: memory): Prop:=
    forall n, n < code_segment_size -> mem1 n = mem2 n.

  Definition in_code (header_size code_size: N) (st: state register) :=
    header_size <= st.(state_pc) /\ st.(state_pc) < header_size + code_size.

  Inductive step (header_size code_size: N) (st1: state register): target_state -> Prop :=
  | Step_good: forall instr n st2,
    in_code header_size code_size st1 ->
    read_instr_from_memory st1.(state_mem) st1.(state_pc) = Some (instr, n) ->
    instruction_semantics (header_size + code_size) instr st1 (Good_state st2) ->
    (* we allow any modification of the memory outside of the code
       segment because of multi threading *)
    forall m2', same_code (header_size + code_size) m2' st2.(state_mem) ->
    step header_size code_size st1
      (Normal_state {| state_mem := m2';
                       state_pc := st2.(state_pc);
                       state_regs :=st2.(state_regs) |})
    (* if no instruction can be read, something wrong is hapening *)
  | Step_cannot_read_instr:
    in_code header_size code_size st1 ->
    read_instr_from_memory st1.(state_mem) st1.(state_pc) = None ->
    step header_size  code_size st1 DANGER_STATE
    (* if we can read an instruction, and its execution goes wrong, it is wrong *)
  | Step_bad: forall instr n,
    in_code header_size code_size st1 ->
    read_instr_from_memory st1.(state_mem) st1.(state_pc) = Some (instr, n) ->
    instruction_semantics (header_size + code_size) instr st1 Bad_state ->
    step header_size code_size st1 DANGER_STATE

    (* if we are in the header, it must be at a correct address *)
  | Step_header_bad:
    st1.(state_pc) < header_size -> ~dividable_by_32 st1.(state_pc) ->
    step header_size code_size st1 DANGER_STATE

    (* if the address in the header is correct, we can jump anywhere in the code *)
  | Step_header_good: 
    st1.(state_pc) < header_size -> dividable_by_32 st1.(state_pc) ->
    forall m2 regs2 pc2,
      same_code (header_size + code_size) st1.(state_mem) m2 ->
      dividable_by_32 pc2 ->
      step header_size code_size st1
        (Normal_state {| state_mem := m2;
                         state_pc := pc2;
                         state_regs := regs2 |}).


  Inductive accessible_state (header_size code_size: N)
    (st1: state register): state register -> Prop :=
  | AS0: accessible_state header_size code_size st1 st1
  | ASS: forall st2 st3,
    step header_size code_size st1 (Normal_state st2) ->
    accessible_state header_size code_size st2 st3 ->
    accessible_state header_size code_size st1 st3.

  (* is DANGER_STATE accessible from a state ? *)
  Inductive accessible_danger (header_size code_size: N) (st1: state register) : Prop :=
  | AD_one_step:
    step header_size code_size st1 DANGER_STATE ->
    accessible_danger header_size code_size st1
  | AD_more_steps: forall st2,
    step header_size code_size st1 (Normal_state st2)  ->
    accessible_danger header_size code_size st2 ->
    accessible_danger header_size code_size st1.

End Prog_Semantics.

