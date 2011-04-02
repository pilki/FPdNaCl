Require Import List.
Require Import Lib.
Require Import Omega.
Open Scope positive_scope.
Open Scope N_scope.


(* Definition of a half byte *)

Inductive half_byte :=
| HB0
| HB1
| HB2
| HB3
| HB4
| HB5
| HB6
| HB7
| HB8
| HB9
| HBA
| HBB
| HBC
| HBD
| HBE
| HBF.

Lemma half_byte_eq_dec: eq_dec half_byte.
Proof.
  unfold eq_dec. decide equality.
Qed.

Definition N_of_half_byte hb : N:=
  match hb with
    | HB0 => 0
    | HB1 => 1
    | HB2 => 2
    | HB3 => 3
    | HB4 => 4
    | HB5 => 5
    | HB6 => 6
    | HB7 => 7
    | HB8 => 8
    | HB9 => 9
    | HBA => 10
    | HBB => 11
    | HBC => 12
    | HBD => 13
    | HBE => 14
    | HBF => 15
  end.

(* add [trans] 0 bits *)

Fixpoint translate_P_by trans (p: positive) :=
  match trans with
    | O => p
    | S t' => translate_P_by t' (p~0)
  end.

Definition translate_N_by trans (n: N) :=
  match n with
    | N0 => N0
    | Npos p => Npos (translate_P_by trans p)
  end.

(* specialisation for efficiency reasons *)
Definition translate_N_by_four n :=
  match n with
    | N0 => N0
    | Npos p => Npos (p~0~0~0~0)
  end.

Definition translate_N_by_eight n :=
  match n with
    | 0 => 0
    | Npos p => Npos (p~0~0~0~0~0~0~0~0)
  end.

Lemma translate_N_by_four_correct: forall n, translate_N_by_four n = translate_N_by 4 n.
Proof.
  intros [|pos]; reflexivity.
Qed.

Lemma translate_N_by_eight_correct: forall n, translate_N_by_eight n = translate_N_by 8 n.
Proof.
  intros [|pos]; reflexivity.
Qed.


Definition concat_half_byte n hb := (translate_N_by_four n) + (N_of_half_byte hb).





(* Bytes *)

Definition byte := (half_byte * half_byte)%type.

Lemma byte_eq_dec: eq_dec byte.
Proof.
  unfold eq_dec; decide equality; apply half_byte_eq_dec.
Qed.

Definition N_of_byte (b: byte) : N:=
  concat_half_byte (N_of_half_byte (fst b)) (snd b).

Definition byte0 : byte := (HB0, HB0).


Definition concat_byte n (b: byte) :=
  translate_N_by_eight n + N_of_byte b.


(* a word is four byte, little endian *)
Inductive word := W : byte -> byte -> byte -> byte -> word.

Lemma word_eq_dec: forall (w1 w2: word), {w1 = w2}+{w1 <> w2}.
Proof.
  unfold eq_dec; decide equality; apply byte_eq_dec.
Qed.

Definition N_of_word w :=
  match w with
    | W b4 b3 b2 b1 =>
      let n4 := N_of_byte b4 in
      let n3 := concat_byte n4 b3 in
      let n2 := concat_byte n3 b2 in
      concat_byte n2 b1
  end.


(* logical and *)

Fixpoint bool_list_of_P p : list bool :=
  match p with
    | xH => true :: nil
    | xO p' => false :: bool_list_of_P p'
    | xI p' => true :: bool_list_of_P p'
  end.

Fixpoint P_of_bool_list l : option positive :=
  match l with
    | nil => None
    | false :: l' =>
      match P_of_bool_list l' with
        | None => None
        | Some p => Some (xO p)
      end
    | true :: l' =>
      match P_of_bool_list l' with
        | None => Some xH
        | Some p => Some (xI p)
      end
  end.

Lemma P_of_bool_list_of_P: forall p, P_of_bool_list (bool_list_of_P p) = Some p.
Proof.
  induction' p; auto; simpl; rewrite IHp; congruence.
Qed.

Definition bool_list_of_N n :=
  match n with
    | N0 => nil
    | Npos pos => bool_list_of_P pos
  end.

Definition N_of_bool_list l :=
  match P_of_bool_list l with
    | None => N0
    | Some pos => Npos pos
  end.

Lemma N_of_bool_list_of_N: forall n, N_of_bool_list (bool_list_of_N n) = n.
Proof.
  destruct n; unfold bool_list_of_N, N_of_bool_list; simpl.
  reflexivity.
  rewrite P_of_bool_list_of_P. reflexivity.
Qed.

Fixpoint list_and l1 l2 : list bool :=
  match l1, l2 with
    | nil, _
    | _, nil => nil
    | b1:: l1', b2::l2' => (b1 && b2)%bool :: list_and l1' l2'
  end.

Definition N_and n1 n2 :=
  N_of_bool_list (list_and (bool_list_of_N n1) (bool_list_of_N n2)).

Lemma list_and_same: forall l, list_and l l = l.
Proof.
  induction' l as [|b l]; simpl; auto.
  Case "cons b l".
  destruct b; f_equal; auto.
Qed.

Lemma N_and_same: forall n, N_and n n = n.
Proof.
  intros.
  unfold N_and. rewrite list_and_same. apply N_of_bool_list_of_N.
Qed.

