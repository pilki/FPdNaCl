Require Import Lib.
Require Import BinaryDefs.
Open Scope positive_scope.
Open Scope N_scope.

Lemma half_byte_eq_dec: forall hb1 hb2: half_byte, {hb1 = hb2} + {hb1 <> hb2}.
Proof. decide equality. Qed.



Definition fst_four_bits n : (half_byte * N) :=
  match n with
    | 0 => (HB0, 0)
    | 1 => (HB1, 0)
    | 2 => (HB2, 0)
    | 3 => (HB3, 0)
    | 4 => (HB4, 0)
    | 5 => (HB5, 0)
    | 6 => (HB6, 0)
    | 7 => (HB7, 0)
    | 8 => (HB8, 0)
    | 9 => (HB9, 0)
    | 10 => (HBA, 0)
    | 11 => (HBB, 0)
    | 12 => (HBC, 0)
    | 13 => (HBD, 0)
    | 14 => (HBE, 0)
    | 15 => (HBF, 0)
    | Npos (p ~0~0~0~0) => (HB0, Npos p)
    | Npos (p ~0~0~0~1) => (HB1, Npos p)
    | Npos (p ~0~0~1~0) => (HB2, Npos p)
    | Npos (p ~0~0~1~1) => (HB3, Npos p)
    | Npos (p ~0~1~0~0) => (HB4, Npos p)
    | Npos (p ~0~1~0~1) => (HB5, Npos p)
    | Npos (p ~0~1~1~0) => (HB6, Npos p)
    | Npos (p ~0~1~1~1) => (HB7, Npos p)
    | Npos (p ~1~0~0~0) => (HB8, Npos p)
    | Npos (p ~1~0~0~1) => (HB9, Npos p)
    | Npos (p ~1~0~1~0) => (HBA, Npos p)
    | Npos (p ~1~0~1~1) => (HBB, Npos p)
    | Npos (p ~1~1~0~0) => (HBC, Npos p)
    | Npos (p ~1~1~0~1) => (HBD, Npos p)
    | Npos (p ~1~1~1~0) => (HBE, Npos p)
    | Npos (p ~1~1~1~1) => (HBF, Npos p)
  end.

Lemma fst_four_bits_of_half_byte: forall hb n,
  fst_four_bits (concat_half_byte n hb) = (hb, n).
Proof.
  intros. destruct hb; destruct n; reflexivity.
Qed.


Definition fst_byte n : (byte * N) :=
  let (hb1, n1) := fst_four_bits n in
  let (hb2, n2) := fst_four_bits n1 in
  ((hb2, hb1), n2).


(* for proof purpose *)
Definition concat_byte_aux n (b: byte) :=
  let (hb2, hb1) := b in
  let n2 := concat_half_byte n hb2 in
  concat_half_byte n2 hb1.


Lemma translate_P_xO: forall t p, translate_P_by t (p~0) = (translate_P_by t p)~0.
Proof.
  induction' t as [|t]; simpl; intros; auto.
Qed.

Lemma translate_P_plus: forall t1 t2 p, translate_P_by t1 (translate_P_by t2 p) = translate_P_by (t1 + t2) p.
Proof.
  induction' t1 as [|t1']; simpl; intros.
  Case "0%nat".
    destruct (translate_P_by t2 p); auto.
  Case "S t1'".
    repeat rewrite translate_P_xO. f_equal.
    auto.
Qed.

Lemma translate_N_plus: forall t1 t2 n, translate_N_by t1 (translate_N_by t2 n) = translate_N_by (t1 + t2) n.
Proof.
  intros. destruct n; simpl; auto.
  f_equal. apply translate_P_plus.
Qed.



Lemma translate_N_assoc: forall t n1 n2, translate_N_by t n1 + translate_N_by t n2 = translate_N_by t (n1 + n2).
Proof.
  intros.
  destruct' n1 as [|pos1]; destruct' n2 as [|pos2]; simpl; auto.
  Case "Npos pos1"; SCase "Npos pos2".
  f_equal.
  revert pos1 pos2.
  induction' t as [|t']; intros; simpl; auto.
  SSCase "S t'".
  rewrite IHt'. reflexivity.
Qed.



Lemma concat_byte_aux_correct: forall n b,
  concat_byte n b = concat_byte_aux n b.
Proof.
  unfold concat_byte, concat_byte_aux.
  destruct b as (hb2, hb1).
  unfold byte_to_N, concat_half_byte. simpl.
  repeat match goal with
    | |- context[translate_N_by_four ?n] =>
      rewrite (translate_N_by_four_correct n)
  end.
  repeat match goal with
    | |- context[translate_N_by_eight ?n] =>
      rewrite (translate_N_by_eight_correct n)
  end.

  destruct' n as [|pos].
  Case "0".
  simpl. reflexivity.
  Case "Npos pos".
  remember (half_byte_to_N hb1) as nhb1. clear Heqnhb1.
  remember (half_byte_to_N hb2) as nhb2. clear Heqnhb2.
  rewrite Nplus_assoc. f_equal.
  rewrite <- (translate_N_plus 4 4).
  rewrite translate_N_assoc. reflexivity.
Qed.


Definition to_word n :=
  let (b1, n1):= fst_byte n in
  let (b2, n2):= fst_byte n1 in
  let (b3, n3):= fst_byte n2 in
  let (b4, n4):= fst_byte n3 in
  W b1 b2 b3 b4.
