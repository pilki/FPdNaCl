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
Require Import BinaryProps.
Require Import List.
Require Import LazyList.
Require Import Semantics.
Require Import SemanticsProg.
Require Import NSet.
Require Import BinaryProps.
Require Import Recdef.
Require Import Validator.
Require Import ValidatorProof.
Require Import Memory.

Module ValProp (Import I : INSTRUCTION).

  Module VP := ValProof I.
  Import VP.
  Import Val.
  Import ProgSem.

  Lemma same_code_refl: forall n m, same_code n m m.
  Proof.
    unfold same_code. intros. eauto.
  Qed.
  Hint Resolve same_code_refl.
  
  Theorem validator_dividable_no_danger:
    forall ll, validate_program ll = true ->
    forall st,
      memory_compat_addr_ll header_size ll st.(state_mem) ->
      dividable_by_32 st.(state_pc) ->
      ~accessible_danger (N_of_nat (ll_length ll)) st. 
  Proof.
    intros. intro.

    assert (exists n, danger_in_n_steps (N_of_nat (ll_length ll)) st n).
    clear - H2.
    induction H2; auto.
      exists O. constructor; auto.
      edestruct IHaccessible_danger; eauto.
      exists (S x). econstructor; eauto.
    destruct H3.

    unfold validate_program in H.
    destruct (validate_ll_list header_size Nempty Nempty ll) as [] _eqn; eauto.
    destruct p as [valid_addresses to_be_checked_addresses].
    apply is_Nincluded_included in H.
    eapply almost_there; eauto. 
    tri_split.
    right. right. repeat split; auto.
    eapply validate_ll_list_correct_addr; eauto.
    unfold NSet_smaller. intros. edestruct Nempty_empty; eauto.
    omega'.
    eapply addresses_multiple_of_32_in_valid_addresses with (2 := Heqo); eauto.
    apply dividable_by_32_header_size.
  Qed.

  Theorem validator_dividable_no_danger_header_size:
    forall ll, validate_program ll = true ->
    forall st,
      memory_compat_addr_ll header_size ll st.(state_mem) ->
      st.(state_pc) = header_size ->
      ~accessible_danger (N_of_nat (ll_length ll)) st.
  Proof.
    intros. apply validator_dividable_no_danger; auto.
    rewrite H1. apply dividable_by_32_header_size.
  Qed.


End ValProp.
