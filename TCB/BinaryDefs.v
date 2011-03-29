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



Definition half_byte_to_N hb : N:=
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


Definition concat_half_byte n hb := (translate_N_by_four n) + (half_byte_to_N hb).





(* Bytes *)

Definition byte := (half_byte * half_byte)%type.

Definition byte_to_N (b: byte) : N:=
  concat_half_byte (half_byte_to_N (fst b)) (snd b).

Definition byte0 : byte := (HB0, HB0).


Definition concat_byte n (b: byte) :=
  translate_N_by_eight n + byte_to_N b.


(* a word is four byte, little endian *)
Inductive word := W : byte -> byte -> byte -> byte -> word.

Definition word_to_N w :=
  match w with
    | W b1 b2 b3 b4 =>
      let n4 := byte_to_N b4 in
      let n3 := concat_byte n4 b3 in
      let n2 := concat_byte n3 b2 in
      concat_byte n2 b1
  end.


(* logical and *)

Fixpoint P_to_list p : list bool :=
  match p with
    | xH => true :: nil
    | xO p' => false :: P_to_list p'
    | xI p' => true :: P_to_list p'
  end.

Fixpoint list_to_P l : option positive :=
  match l with
    | nil => None
    | false :: l' =>
      match list_to_P l' with
        | None => None
        | Some p => Some (xO p)
      end
    | true :: l' =>
      match list_to_P l' with
        | None => Some xH
        | Some p => Some (xI p)
      end
  end.

Lemma P_to_list_to_P: forall p, list_to_P (P_to_list p) = Some p.
Proof.
  induction' p; auto; simpl; rewrite IHp; congruence.
Qed.

Definition N_to_list n :=
  match n with
    | N0 => nil
    | Npos pos => P_to_list pos
  end.

Definition list_to_N l :=
  match list_to_P l with
    | None => N0
    | Some pos => Npos pos
  end.

Lemma N_to_list_to_N: forall n, list_to_N (N_to_list n) = n.
Proof.
  destruct n; unfold N_to_list, list_to_N; simpl.
  reflexivity.
  rewrite P_to_list_to_P. reflexivity.
Qed.

Fixpoint list_and l1 l2 : list bool :=
  match l1, l2 with
    | nil, _
    | _, nil => nil
    | b1:: l1', b2::l2' => (b1 && b2)%bool :: list_and l1' l2'
  end.

Definition N_and n1 n2 :=
  list_to_N (list_and (N_to_list n1) (N_to_list n2)).

Lemma list_and_same: forall l, list_and l l = l.
Proof.
  induction' l as [|b l]; simpl; auto.
  Case "cons b l".
  destruct b; f_equal; auto.
Qed.

Lemma N_and_same: forall n, N_and n n = n.
Proof.
  intros.
  unfold N_and. rewrite list_and_same. apply N_to_list_to_N.
Qed.
