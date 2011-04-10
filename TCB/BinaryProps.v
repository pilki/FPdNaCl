(* FPdNaCl
 * 
 * Copyright (C) 2011 Alexandre Pilkiewicz (@polytechnique.org)
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License as
 * published by the Free Software Foundation; either version 2 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * General Public License for more details. *)

Require Import Lib.
Require Export BinaryAux.
Open Scope positive_scope.
Open Scope N_scope.


Lemma N_of_byte0: N_of_byte byte0 = 0.
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

Lemma word_of_word: forall w,
  word_of_N (N_of_word w) = w.
Proof.
  destruct w as [b4 b3 b2 b1].
  unfold word_of_N.
  simpl. repeat rewrite fst_byte_of_byte.
  unfold fst_byte, N_of_byte.
  rewrite fst_four_bits_of_half_byte.
  destruct b4. simpl. destruct h; reflexivity.
Qed.

Definition word_and w1 w2 :=
  word_of_N (N_and (N_of_word w1) (N_of_word w2)).

Lemma word_and_same w: word_and w w = w.
Proof.
  unfold word_and. rewrite N_and_same. apply word_of_word.
Qed.