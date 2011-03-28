Require Import Lib.

(* Definitions relative to binary representation. See
   TCB/BinaryProofs.v for the related proofs *)


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

Lemma half_byte_eq_dec: forall hb1 hb2: half_byte, {hb1 = hb2} + {hb1 <> hb2}.
Proof. decide equality. Qed.


(* TCB *)

Open Scope N_scope.

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



(* NTCB *)

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


(* TCB *)

Definition concat_half_byte n hb := (translate_N_by_four n) + (half_byte_to_N hb).

Lemma fst_four_bits_of_half_byte: forall hb n,
  fst_four_bits (concat_half_byte n hb) = (hb, n).
Proof.
  intros. destruct hb; destruct n; reflexivity.
Qed.



(* NTCB *)

Definition byte := (half_byte * half_byte)%type.


(* TCB *)
Definition byte_to_N (b: byte) :=
  (translate_N_by_four (half_byte_to_N (fst b))) + (half_byte_to_N (snd b)).

Definition byte0 : byte := (HB0, HB0).
Lemma byte_to_N0: byte_to_N byte0 = 0.
Proof.
  reflexivity.
Qed.

Definition fst_byte n : (byte * N) :=
  let (hb1, n1) := fst_four_bits n in
  let (hb2, n2) := fst_four_bits n1 in
  ((hb2, hb1), n2).

Definition concat_byte n (b: byte) :=
  translate_N_by_eight n + byte_to_N b.


(* a word is four byte, little endian *)
Inductive word := W : byte -> byte -> byte -> byte -> word.

Definition word_to_N w :=
  match w with
    | W b1 b2 b3 b4 =>
      let n4 := byte_to_N b4 in
      let n3 := translate_N_by_eight n4 + byte_to_N b3 in
      let n2 := translate_N_by_eight n3 + byte_to_N b2 in
      translate_N_by_eight n2 + byte_to_N b1
  end.

Definition fst_word n :=
  let (b1, n1):= fst_byte n in
  let (b2, n2):= fst_byte n1 in
  let (b3, n3):= fst_byte n2 in
  let (b4, n4):= fst_byte n3 in
  (W b1 b2 b3 b4, n4).


