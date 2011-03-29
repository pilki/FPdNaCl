Require Import Lib.
Require Import BinaryDefs.
Require Import BinaryAux.
Open Scope positive_scope.
Open Scope N_scope.


Lemma byte_to_N0: byte_to_N byte0 = 0.
Proof.
  reflexivity.
Qed.

Lemma fst_byte_of_byte: forall b n,
  fst_byte (concat_byte n b) = (b, n).
Proof.
  intros.
  rewrite concat_byte_aux_correct.
  destruct b as (hb2, hb1).
  unfold fst_byte.
  simpl.
  repeat rewrite fst_four_bits_of_half_byte. reflexivity.
Qed.

Lemma fst_word_of_word: forall w,
  to_word (word_to_N w) = w.
Proof.
  destruct w as [b1 b2 b3 b4].
  unfold to_word.
  simpl. repeat rewrite fst_byte_of_byte.
  unfold fst_byte, byte_to_N.
  rewrite fst_four_bits_of_half_byte.
  destruct b4. simpl. destruct h; reflexivity.
Qed.