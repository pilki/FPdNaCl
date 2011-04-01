Require Import Lib.
Require Import BinaryProps.
Require Import List.
Require Import Semantics.
Require Import NSet.
Require Import BinaryProps.
Require Import Recdef.
Require Import Coqlibext.


Lemma remove_some: forall A (x y: A), Some x = Some y -r> x = y.
Proof.
  split; congruence. 
Qed.

Hint Rewrite remove_some: clean.

Fixpoint ll_safe_drop {X} (n: nat) (ll: lazy_list X) :=
  match n with
    | O => Some ll
    | S n' =>
      match ll with
        | 〈〉 => None
        | x ::: ll' => ll_safe_drop n' ll'
      end
  end.

Lemma ll_safe_drop_size {X} n: forall  (ll ll': lazy_list X),
  ll_safe_drop n ll = Some ll' ->
  ll_length ll = (n + ll_length ll')%nat.
Proof.
  induction' n as [|n]; simpl; intros; clean.
  Case "S n".
  destruct ll as [| ? [ll2]]; clean.
  specialize (IHn _ _ H).
  simpl in *. congruence.
Qed.


Notation "'option_bind' f oa" :=
  (match oa with
    | Some a => f a
    | None => None
  end) (at level 10, f at next level, oa at next level, only parsing).


Notation "'do' '_' '<-' A ; B" :=
  (option_bind (fun _ => B) (A))
   (at level 200, A at level 100, B at level 200, format
   "'[v' 'do'  '_'  <-  A ;  '/' B ']'").

Notation "'do' X '<-' A ; B" :=
  (option_bind (fun X => B) A)
   (at level 200, X ident, A at level 100, B at level 200, format
   "'[v' 'do'  X  '<-'  A ;  '/' B ']'").

Notation "'do' ( X : T ) <- A ; B" :=
  (option_bind (fun (X: T) => B) A)
   (at level 200, X ident, A at level 100,
    T at level 100, B at level 200, only parsing).

Notation "'do' ( '_' : T ) <- A ; B" :=
  (option_bind (fun (_: T) => B) A)
   (at level 200, A at level 100, T at level 100, B at level 200, only parsing).

Notation "'do' ( X , Y ) <- A ; B" :=
  (option_bind (fun _XY_ => let '(X, Y) := _XY_ in  B) A)
   (at level 200, X ident, Y ident, A at level 100, B at level 200, format
   "'[v' 'do'  ( X ,  Y )  '<-'  A ;  '/' B ']'").

Notation "'do' ( '_' , Y ) <- A ; B" :=
  (option_bind (fun _XY_ => let '(_, Y) := _XY_ in  B) A)
   (at level 200, Y ident, A at level 100, B at level 200, format
   "'[v' 'do'  ( '_' ,  Y )  '<-'  A ;  '/' B ']'").
Notation "'do' ( X , '_' ) <- A ; B" :=
  (option_bind (fun _XY_ => let '(X, _) := _XY_ in  B) A)
   (at level 200, X ident, A at level 100, B at level 200, format
   "'[v' 'do'  ( X ,  '_' )  '<-'  A ;  '/' B ']'").



Notation "'do' ( X , Y , Z ) <- A ; B" :=
  (option_bind (fun (_XYZ_: _ * _ *_) =>
    let '(X, Y, Z) := _XYZ_ in B) A)
   (at level 200, X ident, Y ident, Z ident, A at level 100, B at level 200, format
   "'[v' 'do'  ( X ,  Y ,  Z )  '<-'  A ;  '/' B ']'").

Notation "'do' ( '_' , Y , Z ) <- A ; B" :=
  (option_bind (fun (_XYZ_: _ * _ *_) =>
    let '(_, Y, Z) := _XYZ_ in B) A)
   (at level 200,  Y ident, Z ident, A at level 100, B at level 200, format
   "'[v' 'do'  ( '_' ,  Y ,  Z )  '<-'  A ;  '/' B ']'").

Notation "'do' ( X , '_' , Z ) <- A ; B" :=
  (option_bind (fun (_XYZ_: _ * _ *_) =>
    let '(X, _, Z) := _XYZ_ in B) A)
   (at level 200, X ident, Z ident, A at level 100, B at level 200, format
   "'[v' 'do'  ( X ,  '_' ,  Z )  '<-'  A ;  '/' B ']'").


Notation "'do' ( X , Y , '_' ) <- A ; B" :=
  (option_bind (fun (_XYZ_: _ * _ *_) =>
    let '(X, Y, _) := _XYZ_ in B) A)
   (at level 200, X ident, Y ident, A at level 100, B at level 200, format
   "'[v' 'do'  ( X ,  Y ,  '_' )  '<-'  A ;  '/' B ']'").

Notation "'do' ( X , '_' , '_' ) <- A ; B" :=
  (option_bind (fun (_XYZ_: _ * _ *_) =>
    let '(X, _, _) := _XYZ_ in B) A)
   (at level 200, X ident, A at level 100, B at level 200, format
   "'[v' 'do'  ( X ,  '_' ,  '_' )  '<-'  A ;  '/' B ']'").

Notation "'do' ( '_' , Y , '_' ) <- A ; B" :=
  (option_bind (fun (_XYZ_: _ * _ *_) =>
    let '(X, Y, Z) := _XYZ_ in B) A)
   (at level 200, Y ident, A at level 100, B at level 200, format
   "'[v' 'do'  ( '_' ,  Y ,  '_' )  '<-'  A ;  '/' B ']'").

Notation "'do' ( '_' , '_' , Z ) <- A ; B" :=
  (option_bind (fun (_XYZ_: _ * _ *_) =>
    let '(_, _, Z) := _XYZ_ in B) A)
   (at level 200, Z ident, A at level 100, B at level 200, format
   "'[v' 'do'  ( '_' ,  '_' ,  Z )  '<-'  A ;  '/' B ']'").

Fixpoint safe_minus (m n : nat) :=
  match m, n with
    | _, O => Some m
    | O, S _ => None
    | S m', S n' => safe_minus m' n'
  end.

Lemma safe_minus_correct: forall m n p, safe_minus m n = Some p ->
  m  = (n + p)%nat.
Proof.
  induction' m as [|m']; simpl; intros; destruct' n as [|n']; clean; try congruence; eauto.
  simpl. f_equal. eauto.
Qed.

Definition eq_dec (X: Type):= forall (x1 x2:X), {x1 = x2}+{x1 <> x2}.

Lemma half_byte_eq_dec: eq_dec half_byte.
Proof.
  unfold eq_dec. decide equality.
Qed.

Lemma byte_eq_dec: eq_dec byte.
Proof.
  unfold eq_dec; decide equality; apply half_byte_eq_dec.
Qed.

Lemma word_eq_dec: forall (w1 w2: word), {w1 = w2}+{w1 <> w2}.
Proof.
  unfold eq_dec; decide equality; apply byte_eq_dec.
Qed.


Module ValidatorCode (Import I: INSTRUCTION).

  Definition proper_mask := W (HBF, HBF) (HBF, HBF) (HBF, HBF) (HBE, HB0).

  Definition id (n: nat) := n.

  Function validate_n_byte (n: nat) (oreg: option register) (addr: N)
    (valid_addresses to_be_checked_addresses: NSet) (ll: lazy_list byte)
    {measure id n}: option (NSet * NSet * lazy_list byte):=
    match n with
      | O => Some (valid_addresses, to_be_checked_addresses, ll)
      | _ =>
        do (instr, size_instr) <- parse_instruction (byte_map_from_ll ll);
        do ll' <- ll_safe_drop size_instr ll;
        do n' <- safe_minus n size_instr;
        let addr' := N_of_nat n' in
        match classify_instruction instr with
          | OK_instr =>
            validate_n_byte n' None addr'
              (Nadd addr valid_addresses) to_be_checked_addresses ll'
          | Mask_instr reg w =>
            match word_eq_dec w proper_mask with
              | left _ =>
                validate_n_byte n' (Some reg)
                addr' (Nadd addr valid_addresses) to_be_checked_addresses ll'
              | right _ =>
                validate_n_byte n' None
                addr' (Nadd addr valid_addresses) to_be_checked_addresses ll'
            end
          | Direct_jump w =>
            let dest_addr := word_to_N w in
            if dividable_by_32_dec dest_addr then
              validate_n_byte n' None
                addr' (Nadd addr valid_addresses) to_be_checked_addresses ll'
            else if is_Nin dest_addr valid_addresses then
              validate_n_byte n' None
                addr' (Nadd addr valid_addresses) to_be_checked_addresses ll'
            else
              validate_n_byte n' None addr' (Nadd addr valid_addresses)
                (Nadd dest_addr to_be_checked_addresses) ll'
          | Indirect_jump reg2 =>
            do reg1 <- oreg;
            match register_eq_dec reg1 reg2 with
              | left _ =>
                validate_n_byte n' None
                addr' valid_addresses to_be_checked_addresses ll'
              | right _ => None
            end
          | Invalid_instruction => None
        end
    end.
  Proof.

    Ltac solve_case teq0 teq3 := solve [
      intros;
      pose proof (size_instr_not_0 teq0);
      apply safe_minus_correct in teq3; subst;
      unfold id; omega].

    solve_case teq0 teq3.
    solve_case teq0 teq3.
    solve_case teq0 teq3.
    solve_case teq0 teq3.
    solve_case teq0 teq3.
    solve_case teq0 teq3.
    solve_case teq0 teq3.
  Qed.

  Ltac fun_ind_validate_n_byte_with call :=
    functional induction call;
      [ fst_Case_tac "fun_ind_validate_n_byte 1"
      | fst_Case_tac "fun_ind_validate_n_byte 2"
      | fst_Case_tac "fun_ind_validate_n_byte 3"
      | fst_Case_tac "fun_ind_validate_n_byte 4"
      | fst_Case_tac "fun_ind_validate_n_byte 5"
      | fst_Case_tac "fun_ind_validate_n_byte 6"
      | fst_Case_tac "fun_ind_validate_n_byte 7"
      | fst_Case_tac "fun_ind_validate_n_byte 8"
      | fst_Case_tac "fun_ind_validate_n_byte 9"
      | fst_Case_tac "fun_ind_validate_n_byte 10"
      | fst_Case_tac "fun_ind_validate_n_byte 11"
      | fst_Case_tac "fun_ind_validate_n_byte 12"
      | fst_Case_tac "fun_ind_validate_n_byte 13"
      | fst_Case_tac "fun_ind_validate_n_byte 14"].

  Ltac fun_ind_validate_n_byte :=
    match goal with
      | |- context[ validate_n_byte ?n ?or ?a ?va ?tbca ?ll] =>
        fun_ind_validate_n_byte_with
          (validate_n_byte n or a va tbca ll)
    end.

  Lemma validate_n_byte_reduces_size_by_n:
    forall n oreg addr valid_addresses to_be_checked_addresses ll
      valid_addresses' to_be_checked_addresses' ll',
      validate_n_byte n oreg addr valid_addresses to_be_checked_addresses ll =
      Some (valid_addresses', to_be_checked_addresses', ll') ->
      ll_length ll = (n + ll_length ll')%nat.
  Proof.
    intros ? ? ? ? ? ?.
    fun_ind_validate_n_byte;
      intros; clean; specialize (IHo _ _ _ H);
        apply ll_safe_drop_size in  e2;
          apply safe_minus_correct in e3; omega.
  Qed.


  Function validate_ll_list (addr: N)
    (valid_addresses to_be_checked_addresses: NSet) (ll: lazy_list byte)
    {measure ll_length ll}: option (NSet * NSet):=
    do (valid_addresses', to_be_checked_addresses', ll') <-
      validate_n_byte 32 None addr valid_addresses to_be_checked_addresses ll;
    match ll' with
      | 〈〉 => Some (valid_addresses', to_be_checked_addresses')
      | _ =>
        validate_ll_list (addr + 32) valid_addresses' to_be_checked_addresses' ll'
    end.
  Proof.
    intros.
    subst.
    apply validate_n_byte_reduces_size_by_n in teq.
    simpl in *. destruct l. omega.
  Qed.

  Definition header_size := 65536.

  Definition validate_program ll :=
    match validate_ll_list header_size Nempty Nempty ll with
      | None => false
      | Some (valid_addresses, to_be_checked_addresses) =>
        Nincluded to_be_checked_addresses valid_addresses
    end.
End ValidatorCode.
  
