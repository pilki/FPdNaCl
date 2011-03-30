Require Import Lib.
Require Import BinaryProps.
Require Import List.

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

Extraction lazy.

Unset Elimination Schemes.

Inductive lazy_list (X:Type) :=
| ll_nil: lazy_list X
| ll_cons: forall (x:X) (l: lazy (lazy_list X)), lazy_list X.

Implicit Arguments ll_nil [[X]].
Implicit Arguments ll_cons [[X]].

Notation "œôû© œôûª" := (ll_nil).
Notation "x ::: ll" := (ll_cons x (Lazy ll)) (at level 60, right associativity).

Notation "œôû© x ; .. ; z œôûª" := (ll_cons x (Lazy ( .. (ll_cons z (Lazy ll_nil)) .. ))).


Set Elimination Schemes.

Fixpoint lazy_list_rect (A:Type) (P : lazy_list A -> Type) (Hnil: P ll_nil)
  (Hcons: forall (a: A) ll, P ll -> P (ll_cons a (Lazy ll))) (l: lazy_list A) : P l :=
  match l as l0 return P l0 with
    | œôû©œôûª => Hnil
    | x ::: l' => (Hcons x l' (lazy_list_rect P Hnil Hcons l'))
  end.

Implicit Arguments lazy_list_rect [A].

Definition lazy_list_ind (A:Type) (P : lazy_list A -> Prop) (Hnil: P ll_nil)
  (Hcons: forall (a: A) ll, P ll -> P (ll_cons a (Lazy ll))) (l: lazy_list A) : P l :=
  lazy_list_rect P Hnil Hcons l.

Fixpoint to_list {X} (ll: lazy_list X) : list X :=
  match ll with
    | œôû©œôûª => []
    | x ::: l' => x :: to_list l'
  end.

Fixpoint ll_length {X} (l: lazy_list X) : nat :=
  match l with
    | œôû©œôûª => O
    | x ::: l' => S (ll_length l')
  end.

Lemma ll_length_correct: forall {X} (ll: lazy_list X),
  ll_length ll = length (to_list ll).
Proof.
  induction ll; simpl; congruence.
Qed.


Fixpoint ll_nth {X} n (ll: lazy_list X) :=
  match n, ll with
    | _ ,œôû©œôûª => None
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
Notation "bm1 œôù¡ bm2":= (eq_byte_map bm1 bm2) (at level 70, no associativity).


Definition start_map_from (start: nat) (bm: byte_map) : byte_map :=
  fun n => bm (start + n)%nat.

Lemma start_map_from_0: forall bm, start_map_from 0 bm œôù¡ bm.
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
  (* a (optional) direct jump to a static address *)
| Direct_jump: word -> instruction_classification register
  (* an (optional) indirect jump to the address in a given register *)
| Indirect_jump: register -> instruction_classification register
  (* a dangerous instruction *)
| Invalid_instruction: instruction_classification register.

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
Inductive target_state register :=
| Good_state: state register -> target_state register
| Bad_state: target_state register.

Implicit Arguments Good_state [[register]].
Implicit Arguments Bad_state [[register]].

Inductive is_good_state {register}: target_state register -> Prop :=
| Is_Good_State: forall state, is_good_state (Good_state state).



Module Type INSTRUCTIONS.

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

  Parameter classify_instruction: instruction -> instruction_classification register.

  (* the first parameter is to indicate that the n first bytes of the memory
     cannot be written *)
  Parameter instruction_semantic: N -> instruction -> state register ->
    target_state register -> Prop.


  Parameter sem_no_overwrite: forall code_size instr st1 st2,
    instruction_semantic code_size instr st1 (Good_state st2) ->
    forall n', n' < code_size -> st1.(state_mem) n' = st2.(state_mem) n'.


  Parameter sem_good_not_bad: forall code_size instr st tst,
    classify_instruction instr = Ok_instr



End INSTRUCTIONS.