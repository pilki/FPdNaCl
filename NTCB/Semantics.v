Require Import Lib.
Require Import BinaryProps.
Require Import List.
Require Import Program.

Set Implicit Arguments.
(* move to lib *)
Notation "[ ]" := (nil).
Notation "[ x , .. , z ]" := (cons x ( .. (cons z []) .. )).

Fixpoint list_take {A} n (l: list A) : list A:=
  match n, l with
    | O, _
    | _, [] => []
    | S n', h::t => h :: (list_take n' t)
  end.

Fixpoint list_drop {A} n (l: list A) : list A:=
  match n, l with
    | O, _ => l
    | _, [] => []
    | S n', h::t => (list_drop n' t)
  end.

CoInductive lazy (X:Type) :=
| Lazy : X -> lazy X.
Implicit Arguments Lazy [[X]].

Unset Elimination Schemes.

Inductive lazy_list (X:Type) :=
| ll_nil: lazy_list X
| ll_cons: forall (x:X) (l: lazy (lazy_list X)), lazy_list X.

Implicit Arguments ll_nil [[X]].
Implicit Arguments ll_cons [[X]].

Notation "x ::: ll" := (ll_cons x (Lazy ll)) (at level 60, right associativity).

Notation "〈 〉" := (ll_nil).

Notation "〈 x ; .. ; z 〉" := (ll_cons x (Lazy ( .. (ll_cons z (Lazy ll_nil)) .. ))).


Set Elimination Schemes.

Fixpoint lazy_list_rect (A:Type) (P : lazy_list A -> Type) (Hnil: P ll_nil)
  (Hcons: forall (a: A) ll, P ll -> P (ll_cons a (Lazy ll))) (l: lazy_list A) : P l :=
  match l as l0 return P l0 with
    | 〈〉 => Hnil
    | x ::: l' => (Hcons x l' (lazy_list_rect P Hnil Hcons l'))
  end.

Implicit Arguments lazy_list_rect [A].

Definition lazy_list_ind (A:Type) (P : lazy_list A -> Prop) (Hnil: P ll_nil)
  (Hcons: forall (a: A) ll, P ll -> P (ll_cons a (Lazy ll))) (l: lazy_list A) : P l :=
  lazy_list_rect P Hnil Hcons l.

Fixpoint to_list {X} (ll: lazy_list X) : list X :=
  match ll with
    | 〈〉 => []
    | x ::: l' => x :: to_list l'
  end.

Fixpoint ll_length {X} (l: lazy_list X) : nat :=
  match l with
    | 〈〉 => O
    | x ::: l' => S (ll_length l')
  end.

Lemma ll_length_correct: forall {X} (ll: lazy_list X),
  ll_length ll = length (to_list ll).
Proof.
  induction ll; simpl; congruence.
Qed.


Fixpoint ll_nth {X} n (ll: lazy_list X) :=
  match n, ll with
    | _ ,〈〉 => None
    | O, x ::: _ => Some x
    | S n', _ ::: ll' => ll_nth n' ll'
  end.

Lemma ll_nth_correct: forall {X} n (ll: lazy_list X),
  ll_nth n ll = nth_error (to_list ll) n.
Proof.
  induction n; simpl; intros; destruct ll as [| x [ll'] ]; simpl; auto.
Qed.


Definition byte_map := nat -> option byte.
Definition eq_byte_map (bm1 bm2: byte_map) := forall n, bm1 n = bm2 n.
Notation "bm1 ≡ bm2" := (eq_byte_map bm1 bm2) (at level 70, no associativity).


Definition start_map_from (start: nat) (bm: byte_map) : byte_map :=
  fun n => bm (start + n)%nat.

Lemma start_map_from_0: forall bm, start_map_from 0 bm ≡ bm.
Proof.
  intros bm n.
  unfold start_map_from. simpl. reflexivity.
Qed.

Lemma start_map_from_right: forall start bm n,
  (start_map_from start bm n) = bm (n + start)%nat.
Proof.
  intros; simpl. unfold start_map_from. f_equal. omega.
Qed.

Definition update_byte_map (bm: byte_map) (loc:nat) (ob: option byte): byte_map :=
  fun n =>
    if eq_nat_dec n loc then ob else bm n.


Definition byte_map_from_ll (ll: lazy_list byte) : byte_map:=
  fun n => ll_nth n ll.



Inductive is_some {X}: option X -> Prop :=
| Is_Some: forall x, is_some (Some x).

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
End INSTRUCTION.


Module Type INSTRUCTION_SEMANTICS(Import I: INSTRUCTION).
  (* the first parameter is to indicate that the n first bytes of the memory
     cannot be written *)
  Parameter instruction_semantics: N -> instruction ->
    state register -> instruction_target_state register -> Prop.


  (* an instruction cannot write in the lower code segment *)
  Parameter sem_no_overwrite: forall code_segment_size instr st1 st2,
    instruction_semantics code_segment_size instr st1 (Good_state st2) ->
    forall n', n' < code_segment_size -> st1.(state_mem) n' = st2.(state_mem) n'.

  (* the "good" instructions can get stuck but neverr lead to a "bad state" *)

  Parameter sem_not_invalid_not_bad: forall instr,
    classify_instruction instr <> Invalid_instruction ->
    forall code_segment_size st tst,
      instruction_semantics code_segment_size instr st tst ->
      is_good_state tst.


  Parameter sem_OK_instr_pc: forall bm instr size,
    parse_instruction bm = Some (instr, size) ->
    classify_instruction instr = OK_instr ->
    forall code_segment_size st1 st2,
    instruction_semantics code_segment_size instr st1 (Good_state st2) ->
    st2.(state_pc) = st1.(state_pc) + (N_of_nat size).

  Parameter sem_Mask_instr_pc: forall bm instr size,
    parse_instruction bm = Some (instr, size) ->
    forall reg w,
    classify_instruction instr = Mask_instr reg w->
    forall code_segment_size st1 st2,
    instruction_semantics code_segment_size instr st1 (Good_state st2) ->
    st2.(state_pc) = st1.(state_pc) + (N_of_nat size).

  Parameter sem_Direct_jump_pc: forall bm instr size,
    parse_instruction bm = Some (instr, size) ->
    forall w,
    classify_instruction instr = Direct_jump w ->
    forall code_segment_size st1 st2,
    instruction_semantics code_segment_size instr st1 (Good_state st2) ->
    st2.(state_pc) = st1.(state_pc) + (N_of_nat size) \/
    st2.(state_pc) = word_to_N w.

  Parameter sem_Indirect_jump_pc: forall bm instr size,
    parse_instruction bm = Some (instr, size) ->
    forall reg,
    classify_instruction instr = Indirect_jump reg ->
    forall code_segment_size st1 st2,
    instruction_semantics code_segment_size instr st1 (Good_state st2) ->
    st2.(state_pc) = st1.(state_pc) + (N_of_nat size) \/
    st2.(state_pc) = word_to_N (st1.(state_regs) reg).

End INSTRUCTION_SEMANTICS.

Fixpoint pow2 (n: nat) :=
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
Qed.

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
Module Prog_Semantics (Import I: INSTRUCTION)(Import IS:INSTRUCTION_SEMANTICS(I)).

  Inductive target_state :=
    (* a regular state *)
  | Normal_state: state register -> target_state
    (* after a jump outside of the code segment *)
  | Non_executable_code: state register -> target_state
    (* a state that should *never* be reached ! *)
  | DANGER_STATE: target_state.


  Definition read_instr_from_memory (mem: memory) (pc: N): option (instruction * nat) :=
    parse_instruction (fun n => mem ((N_of_nat n) + pc)).



  (* parse an instruction *)
  Definition same_code (code_segment_size: N) (mem1 mem2: memory): Prop:=
    forall n, n < code_segment_size -> mem1 n = mem2 n.

  Inductive step (header_size code_size: N) (st1: state register): target_state -> Prop :=
    (* if no instruction can be read, something wrong is hapening *)
  | Step_cannot_read_instr:
    read_instr_from_memory st1.(state_mem) st1.(state_pc) = None ->
    step header_size  code_size st1 DANGER_STATE
    (* if we can read an instruction, and its execution goes wrong, it is wrong *)
  | Step_bad: forall instr n,
    read_instr_from_memory st1.(state_mem) st1.(state_pc) = Some (instr, n) ->
    instruction_semantics (header_size + code_size) instr st1 Bad_state ->
    step header_size code_size st1 DANGER_STATE

    (* if we jump in the header, it must be at a correct address *)
  | Step_header_bad: forall instr n st2,
    read_instr_from_memory st1.(state_mem) st1.(state_pc) = Some (instr, n) ->
    instruction_semantics (header_size + code_size) instr st1 (Good_state st2) ->
    st2.(state_pc) < header_size -> ~dividable_by_32 st2.(state_pc) ->
    step header_size code_size st1 DANGER_STATE

    (* if the address in the header is correct, we can jump anywhere in the code *)

  | Step_header_good: forall instr n st2,
    read_instr_from_memory st1.(state_mem) st1.(state_pc) = Some (instr, n) ->
    instruction_semantics (header_size + code_size) instr st1 (Good_state st2) ->
    st2.(state_pc) < header_size -> dividable_by_32 st2.(state_pc) ->
    forall m2 regs2 pc2,
      same_code (header_size + code_size) st2.(state_mem) m2 ->
      header_size <= pc2 -> pc2 < header_size + code_size ->
      dividable_by_32 pc2 ->
      step header_size code_size st1
        (Normal_state {| state_mem := m2;
                         state_pc := pc2;
                         state_regs := regs2 |})

  | Step_outside: forall instr n st2,
    read_instr_from_memory st1.(state_mem) st1.(state_pc) = Some (instr, n) ->
    instruction_semantics (header_size + code_size) instr st1 (Good_state st2) ->
    st2.(state_pc) >= header_size + code_size ->
    step header_size code_size st1 (Non_executable_code st2)
  | Step_good: forall instr n st2,
    read_instr_from_memory st1.(state_mem) st1.(state_pc) = Some (instr, n) ->
    instruction_semantics (header_size + code_size) instr st1 (Good_state st2) ->
    st2.(state_pc) >= header_size -> st2.(state_pc) < header_size + code_size->
    (* we allow any modification of the memory outside of the code
       segment because of multi threading *)
    forall m2', same_code (header_size + code_size) m2' st2.(state_mem) ->
    step header_size code_size st1
      (Normal_state {| state_mem := m2';
                       state_pc := st2.(state_pc);
                       state_regs :=st2.(state_regs) |}).


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

