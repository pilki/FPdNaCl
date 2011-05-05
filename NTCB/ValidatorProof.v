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
Require Import Memory.

Module ValProof (Import I : INSTRUCTION).
  Module Val := ValidatorCode(I).
  Module ProgSem := Prog_Semantics(I).
  Export ProgSem.
  Export Val.
  Ltac fun_ind_validate_n_byte :=
    match goal with
      | |- context[ validate_n_byte ?n ?a ?va ?tbca ?ll] =>
        fun_ind_validate_n_byte_with
          (validate_n_byte n a va tbca ll)
      | H : context[ validate_n_byte ?n ?a ?va ?tbca ?ll] |- _ =>
        fun_ind_validate_n_byte_with
          (validate_n_byte n a va tbca ll)
    end.

  Ltac fun_ind_validate_ll_with call :=
    functional induction call;
      [ fst_Case_tac "fun_ind_validate_ll 1"
      | fst_Case_tac "fun_ind_validate_ll 2"
      | fst_Case_tac "fun_ind_validate_ll 3"].

  Ltac fun_ind_validate_ll :=
    match goal with
      | |- context[ validate_ll_list ?a ?va ?tbca ?ll] =>
        fun_ind_validate_ll_with
          (validate_ll_list a va tbca ll)
      | H: context[ validate_ll_list ?a ?va ?tbca ?ll] |- _  =>
        fun_ind_validate_ll_with
          (validate_ll_list a va tbca ll)
    end.

  (* to lib *)
  Inductive _MARK_:Prop := MARK.

  Ltac pose_mark :=
    generalize MARK.

  Ltac intros_until_mark :=
    repeat
      (match goal with
         | H : _MARK_ |- _ => fail 1
         | _ => idtac
       end; intro);
      (match goal with
         | H : _MARK_ |- _ => clear H
         | _ => idtac
       end).

  Ltac clean_post_fun_ind_validate :=
    clean;
    pose_mark;
    repeat
    match goal with
      | H: parse_instruction _ _ = Some _ |- _ =>
        let H' := fresh H "'" in
        pose proof H as H'; revert H';
        apply parse_instruction_drops in H; symmetry in H; apply ll_safe_drop_size in H
    end;
    repeat
    match goal with
      | H: safe_minus _ _ = Some _ |- _ =>
        let H' := fresh H "'" in
        pose proof H as H'; revert H';
          apply safe_minus_correct in H
    end; intros_until_mark; subst
    .


  Lemma validate_n_byte_increase_valid_addresses:
    forall n (addr: N)
    (valid_addresses to_be_checked_addresses: NSet) (ll: lazy_list byte)
    valid_addresses' to_be_checked_addresses' ll',
    validate_n_byte n addr valid_addresses to_be_checked_addresses ll =
    Some (valid_addresses', to_be_checked_addresses', ll') ->
    forall addr', In_NSet addr' valid_addresses ->
      In_NSet addr' valid_addresses'.
  Proof.
    intros * VALIDATE.
    fun_ind_validate_n_byte; clean; eauto with nset.
  Qed.

  Lemma validate_n_byte_increase_to_be_checked_addresses:
    forall n (addr: N)
    (valid_addresses to_be_checked_addresses: NSet) (ll: lazy_list byte)
    valid_addresses' to_be_checked_addresses' ll',
    validate_n_byte n addr valid_addresses to_be_checked_addresses ll =
    Some (valid_addresses', to_be_checked_addresses', ll') ->
    forall addr', In_NSet addr' to_be_checked_addresses ->
      In_NSet addr' to_be_checked_addresses'.
  Proof.
    intros * VALIDATE.
    fun_ind_validate_n_byte; clean; eauto with nset.
  Qed.

  Lemma ll_safe_drop_plus: forall X n1 n2 (ll: lazy_list X),
    ll_safe_drop (n1 + n2) ll =
    do ll' <- ll_safe_drop n1 ll;
    ll_safe_drop n2 ll'.
  Proof.
    induction' n1 as [|n1]; intros; simpl in *; auto.
    Case "S n1".
      destruct' ll as [| x [ll1]]; auto.
  Qed.


  Lemma validate_n_byte_drop_n:
    forall n (addr: N)
    (valid_addresses to_be_checked_addresses: NSet) (ll: lazy_list byte)
    valid_addresses' to_be_checked_addresses' ll',
    validate_n_byte n addr valid_addresses to_be_checked_addresses ll =
    Some (valid_addresses', to_be_checked_addresses', ll') ->
    ll_safe_drop (nat_of_N n) ll = Some ll'.
  Proof.
    intros * VALIDATE.

    fun_ind_validate_n_byte; clean_post_fun_ind_validate; subst;
    rewrite nat_of_Nplus; rewrite ll_safe_drop_plus;
    erewrite <- parse_instruction_drops; eauto.
    Case "fun_ind_validate_n_byte 3".
      simpl. auto.

    Case "fun_ind_validate_n_byte 4".
      rewrite nat_of_Nplus; rewrite ll_safe_drop_plus;
      erewrite <- parse_instruction_drops; eauto.
  Qed.

  (* specialization on 32 *)

  Lemma validate_n_byte_drop_32:
    forall (addr: N)
    (valid_addresses to_be_checked_addresses: NSet) (ll: lazy_list byte)
    valid_addresses' to_be_checked_addresses' ll',
    validate_n_byte 32 addr valid_addresses to_be_checked_addresses ll =
    Some (valid_addresses', to_be_checked_addresses', ll') ->
    ll_safe_drop 32 ll = Some ll'.
  Proof.
    change 32%nat with (nat_of_N 32).
    apply validate_n_byte_drop_n.
  Qed.

  Local Hint Resolve validate_n_byte_drop_n validate_n_byte_increase_to_be_checked_addresses
    validate_n_byte_increase_valid_addresses validate_n_byte_drop_32.

  Lemma validate_ll_list_increase_valid_addresses:
    forall (addr: N)
    (valid_addresses to_be_checked_addresses: NSet) (ll: lazy_list byte)
    valid_addresses' to_be_checked_addresses',
    validate_ll_list addr valid_addresses to_be_checked_addresses ll =
    Some (valid_addresses', to_be_checked_addresses') ->
    forall addr', In_NSet addr' valid_addresses ->
      In_NSet addr' valid_addresses'.
  Proof.
    intros * VALIDATE.
    fun_ind_validate_ll; clean; eauto with nset.
  Qed.

  Lemma validate_ll_list_increase_to_be_checked_addresses:
    forall (addr: N)
    (valid_addresses to_be_checked_addresses: NSet) (ll: lazy_list byte)
    valid_addresses' to_be_checked_addresses',
    validate_ll_list addr valid_addresses to_be_checked_addresses ll =
    Some (valid_addresses', to_be_checked_addresses') ->
    forall addr', In_NSet addr' to_be_checked_addresses ->
      In_NSet addr' to_be_checked_addresses'.
  Proof.
    intros * VALIDATE.
    fun_ind_validate_ll; clean; eauto with nset.
  Qed.

  Local Hint Resolve validate_ll_list_increase_to_be_checked_addresses
    validate_ll_list_increase_valid_addresses.


  Lemma validate_n_byte_add_addr:
    forall (addr: N) p
    (valid_addresses to_be_checked_addresses: NSet) (ll: lazy_list byte)
    valid_addresses' to_be_checked_addresses' ll',
    validate_n_byte (Npos p) addr valid_addresses to_be_checked_addresses ll =
    Some (valid_addresses', to_be_checked_addresses', ll') ->
    In_NSet addr valid_addresses'.
  Proof.
    intros * VALIDATE.
    functional inversion VALIDATE; try (subst;
    subst);
    repeat match goal with
      | x := _ : _ |- _ => subst x
    end;
    (try apply validate_n_byte_increase_valid_addresses in X);
    eauto with nset.
  Qed.

  Local Hint Resolve validate_n_byte_add_addr.


  Lemma validate_n_byte_size:
    forall n (addr: N)
    (valid_addresses to_be_checked_addresses: NSet) (ll: lazy_list byte)
    valid_addresses' to_be_checked_addresses',
    validate_n_byte n addr valid_addresses to_be_checked_addresses ll =
    Some (valid_addresses', to_be_checked_addresses', 〈〉) ->
    ll_length ll = nat_of_N n.
  Proof.
    intros * VALIDATE.

    fun_ind_validate_n_byte; clean_post_fun_ind_validate; rewrite nat_of_Nplus;
      try (specialize (IHo VALIDATE); omega').

    Case "fun_ind_validate_n_byte 3".
    simpl in *. omega'.
  Qed.

  Lemma addresses_multiple_of_32_in_valid_addresses:
    forall addr valid_addresses to_be_checked_addresses ll
      valid_addresses' to_be_checked_addresses',
      dividable_by_32 addr ->
      validate_ll_list addr valid_addresses to_be_checked_addresses ll =
        Some (valid_addresses', to_be_checked_addresses') ->
      forall addr', addr <= addr' -> addr' < addr + (N_of_nat (ll_length ll)) ->
        dividable_by_32 addr' -> In_NSet addr' valid_addresses'.
  Proof.
    intros *.
    fun_ind_validate_ll; intros; clean; eauto.
    Case "fun_ind_validate_ll 1".
      pose proof (validate_n_byte_size _ _ _ _ _ _ _ e).
      apply validate_n_byte_add_addr in e.
      replace addr' with addr. assumption.
      rewrite H0 in H2. simpl in H2.
      destruct H. destruct H3. subst. omega'.

    Case "fun_ind_validate_ll 2".
      assert (dividable_by_32 (addr + 32)) by
        (destruct H; exists (x + 1);omega').
      specialize (IHo H4 H0).
      destruct (N_eq_dec addr addr').
      SCase "addr = addr'".
        subst.
        eapply validate_ll_list_increase_valid_addresses; eauto.
      SCase "addr <> addr'".
        destruct H as [xaddr H].
        destruct H3 as [xaddr' H3]. subst.
        apply IHo. omega'.
        replace 32 with (N_of_nat 32) by reflexivity.
        rewrite <- Nplus_assoc. rewrite <- N_of_plus.
        erewrite <- ll_safe_drop_size; eauto.
        exists xaddr'; eauto.
  Qed.


  Inductive ok_addr next_addr valid_addresses
    to_be_checked_addresses addr : Prop :=
  | OA_Valid:
    In_NSet addr valid_addresses ->
    ok_addr next_addr valid_addresses to_be_checked_addresses addr
  | OK_checked:
    In_NSet addr to_be_checked_addresses ->
    ok_addr next_addr valid_addresses to_be_checked_addresses addr
  | OK_next: addr = next_addr ->
    ok_addr next_addr valid_addresses to_be_checked_addresses addr
  | OK_div:
    dividable_by_32 addr ->
    ok_addr next_addr valid_addresses to_be_checked_addresses addr.

  Local Hint Constructors ok_addr.

  Inductive correct_addr mem next_addr valid_addresses
    to_be_checked_addresses addr : Prop :=
  | CA_intro:
    forall instr size_instr
    (SMALLER: addr + size_instr <= next_addr)
    (READ_FROM_MEM: read_instr_from_memory mem addr = Some (instr, size_instr))
    (NOT_INV: classify_instruction instr <> Invalid_instruction)
    (NOT_IND: forall reg, classify_instruction instr <> Indirect_jump reg)
    (CLASSIFY_OK: classify_instruction instr = OK_instr ->
      ok_addr next_addr valid_addresses to_be_checked_addresses
        (addr + size_instr))
    (CLASSIFY_DIRECT: forall w,
      classify_instruction instr = Direct_jump w ->
      ok_addr next_addr valid_addresses to_be_checked_addresses
        (addr + size_instr) /\
      ok_addr next_addr valid_addresses to_be_checked_addresses
        (N_of_word w))
    (CLASSIFY_MASK: forall reg w,
      classify_instruction instr = Mask_instr reg w ->
      ok_addr next_addr valid_addresses to_be_checked_addresses
        (addr + size_instr) \/
      (exists instr', exists size_instr',
        w = proper_mask /\
        read_instr_from_memory mem (addr + size_instr) =
          Some (instr', size_instr') /\
        addr + size_instr + size_instr' <= next_addr/\
        ok_addr next_addr valid_addresses to_be_checked_addresses
          (addr + size_instr + size_instr') /\
        classify_instruction instr' = Indirect_jump reg)),
    correct_addr mem next_addr valid_addresses
      to_be_checked_addresses addr.



  Lemma correct_addr_same_code mem1 mem2
    next_addr valid_addresses to_be_checked_addresses addr:
    (forall addr, addr < next_addr -> mem1 addr = mem2 addr) ->
    correct_addr mem1 next_addr valid_addresses to_be_checked_addresses addr ->
    correct_addr mem2 next_addr valid_addresses to_be_checked_addresses addr.
  Proof.
    intros SAME CORRECT.
    inv CORRECT.
    eapply' CA_intro; eauto.
    Case "CLASSIFY_MASK".
      intros * OK.
      specialize (CLASSIFY_MASK reg w OK).
      destruct CLASSIFY_MASK as [|[instr' [size_instr' ?]]]; eauto.
      decompose [and] H.
      right. exists instr'; exists size_instr'.
      repeat split; eauto.
  Qed.

  Lemma ok_addr_bigger next_addr next_addr' valid_addresses
    valid_addresses' to_be_checked_addresses to_be_checked_addresses' addr:
    next_addr <= next_addr' ->
    Nincluded to_be_checked_addresses to_be_checked_addresses' ->
    Nincluded valid_addresses valid_addresses' ->
    In_NSet next_addr valid_addresses' ->
    ok_addr next_addr valid_addresses to_be_checked_addresses addr ->
    ok_addr next_addr' valid_addresses' to_be_checked_addresses' addr.
  Proof.
    intros. inv H3; eauto.
  Qed.

  Local Hint Resolve ok_addr_bigger.

  Lemma correct_addr_bigger mem next_addr next_addr' valid_addresses
    valid_addresses' to_be_checked_addresses to_be_checked_addresses' addr:
    next_addr <= next_addr' ->
    Nincluded to_be_checked_addresses to_be_checked_addresses' ->
    Nincluded valid_addresses valid_addresses' ->
    In_NSet next_addr valid_addresses' ->
    correct_addr mem next_addr valid_addresses to_be_checked_addresses addr ->
    correct_addr mem next_addr' valid_addresses' to_be_checked_addresses' addr.
  Proof.
    intros INF INCL_TBC INCL_VAL IN CORRECT.
    inv CORRECT.
    eapply' CA_intro; eauto.
    Case "SMALLER".
      omega'.
    Case "CLASSIFY_DIRECT".
      intros. specialize (CLASSIFY_DIRECT w H).
      destruct CLASSIFY_DIRECT. split; eauto.
    Case "CLASSIFY_MASK".
      intros. specialize (CLASSIFY_MASK reg w H).
      decompose [and or ex] CLASSIFY_MASK; eauto.
      right. eexists; eexists; intuition eauto.
      omega'. omega'.
  Qed.


  (* LIB *)
  Require Import ZArith_dec.
  Lemma N_le_dec: forall n1 n2: N, {n1 <= n2} + {n2 < n1}.
  Proof.
    intros.
    destruct (Z_le_dec (Z_of_N n1) (Z_of_N n2)).
    left. omega'. right; omega'.
  Qed.

  Lemma N_lt_dec: forall n1 n2: N, {n1 < n2} + {n2 <= n1}.
  Proof.
    intros.
    destruct (Z_lt_dec (Z_of_N n1) (Z_of_N n2)).
    left. omega'. right; omega'.
  Qed.


  Ltac clean_safe_minus :=
    repeat match goal with
      | H : safe_minus _ _ = Some _ |- _ =>
        apply safe_minus_correct in H
           end.

  Lemma plus_N_of_nat: forall x n1 n2,
    x + N_of_nat n1 + N_of_nat n2 = x + N_of_nat (n1 + n2).
  Proof.
    intros.
    rewrite N_of_plus. omega'.
  Qed.

  Ltac clean0 :=
    clean;
    try match goal with
          | |- context[ ?x + N_of_nat 0] =>
            replace (x + N_of_nat 0) with x by omega'
          | |- context[ ?x + 0] =>
            replace (x +  0) with x by omega'
        end.

  Definition NSet_smaller nset addr :=
    forall addr', In_NSet addr' nset -> addr' < addr.

  Lemma NSet_smaller_add nset addr n:
    n <> 0 -> NSet_smaller nset addr ->
    NSet_smaller (Nadd addr nset) (addr + n).
  Proof.
    unfold NSet_smaller; intros.
    destruct (Nadd_In_or _ _ _ H1).
    Case "=".
      subst. omega'.
    Case "In".
      specialize (H0 _ H2). omega'.
  Qed.

  Lemma NSet_smaller_plus nset addr n:
    n <> 0 -> NSet_smaller nset addr ->
    NSet_smaller nset (addr + n).
  Proof.
    unfold NSet_smaller; intros.
    specialize (H0 _ H1). omega'.
  Qed.


(*
  Lemma size_instr_not_0_N: forall bm instr n,
    parse_instruction bm = Some (instr, n) -> N_of_nat n <> 0.
  Proof.
    intros.
    pose proof (size_instr_not_0 H). zify. auto.
  Qed.
*)
  Local Hint Unfold NSet_smaller.
  Local Hint Resolve NSet_smaller_add size_instr_not_0 NSet_smaller_plus.

  Lemma In_NSet_dec: forall n nset, {In_NSet n nset} + {~In_NSet n nset}.
  Proof.
    intros.
    destruct (is_Nin n nset) as [] _eqn.
    left. apply is_Nin_NIn; auto.
    right. intro. apply NIn_is_Nin in H. congruence.
  Qed.

  Lemma validate_n_byte_add_valid_addresses_after n init_addr valid_addresses
    to_be_checked_addresses ll valid_addresses' to_be_checked_addresses' ll':
    validate_n_byte n init_addr valid_addresses to_be_checked_addresses ll
      = Some (valid_addresses', to_be_checked_addresses', ll') ->
    NSet_smaller valid_addresses init_addr ->
    forall addr,
      In_NSet addr valid_addresses' ->
      (addr < init_addr /\ In_NSet addr valid_addresses) \/
      (addr >= init_addr /\ addr < init_addr + n).
  Proof.

    fun_ind_validate_n_byte; intros; clean_post_fun_ind_validate; eauto;
    try match type of IHo with
          | ?X -> ?Y -> _ =>
            assert X as HX; auto;
            assert Y as HY; eauto;
            specialize (IHo HX HY _ H1);
            clear HX HY
          end;

(*    assert (a0<>0) by (destruct a0; clean).*)
    try solve [destruct (N_eq_dec addr0 addr);
      [subst; right; split; omega'|];
    destruct IHo as [[INF IN]| [SUP INF]];
      [destruct (Nadd_In_or _ _ _ IN); [contradiction| eauto]|
        right; split; omega']].

    Case "fun_ind_validate_n_byte 3".
      unfold NSet_smaller in *.
      assert (size_instr<>0) by eauto.
      destruct (Nadd_In_or _ _ _ H1); subst; eauto;
      right; split; omega'.
   Qed.



  Lemma HELPER1 n size init_addr valid_addresses
    to_be_checked_addresses ll valid_addresses' to_be_checked_addresses' ll':
    validate_n_byte n (init_addr + size) (Nadd init_addr valid_addresses)
      to_be_checked_addresses ll = Some (valid_addresses', to_be_checked_addresses', ll') ->
    size <> 0 ->
    NSet_smaller valid_addresses init_addr ->
    forall addr, addr >= init_addr -> init_addr <> addr ->
      In_NSet addr valid_addresses' ->
      addr >= init_addr + size.
  Proof.
    intros.
    edestruct validate_n_byte_add_valid_addresses_after; eauto.
    elimtype False.
    destruct H5. unfold NSet_smaller in *.
    destruct (Nadd_In_or _ _ _ H6); subst; eauto. specialize (H1 _ H7).
    omega'.
    destruct H5. eauto.
  Qed.


  Lemma HELPER2 n size1 size2 init_addr valid_addresses
    to_be_checked_addresses ll valid_addresses' to_be_checked_addresses' ll':
    validate_n_byte n (init_addr + size1 + size2) (Nadd init_addr valid_addresses)
      to_be_checked_addresses ll = Some (valid_addresses', to_be_checked_addresses', ll') ->
    size1 <> 0 -> size2 <> 0 ->
    NSet_smaller valid_addresses init_addr ->
    forall addr, addr >= init_addr -> init_addr <> addr ->
      In_NSet addr valid_addresses' ->
      addr >= init_addr + size1 + size2.
  Proof.
    intros.
    rewrite <- Nplus_assoc in *. eapply HELPER1; eauto. omega'.
  Qed.


  Lemma validate_n_byte_ok_addr n init_addr valid_addresses to_be_checked_addresses ll
    valid_addresses' to_be_checked_addresses' ll':
    validate_n_byte n init_addr valid_addresses to_be_checked_addresses ll
      = Some (valid_addresses', to_be_checked_addresses', ll') ->
    ok_addr (init_addr + n) valid_addresses'
      to_be_checked_addresses' init_addr.
  Proof.
    fun_ind_validate_n_byte; intros; clean0; eauto;
      try solve [apply OA_Valid;
        eapply validate_n_byte_increase_valid_addresses; eauto with nset].
    Case "fun_ind_validate_n_byte 3".
      apply OA_Valid. eauto with nset.
  Qed.
  Local Hint Resolve validate_n_byte_ok_addr.


  Local Hint Resolve HELPER1 HELPER2 memory_compat_read_instr.


  Lemma memory_compat_parse_instruction: forall ll instr size_instr rst_ll addr,
    parse_instruction addr ll = Some (instr, size_instr, rst_ll) ->
    forall mem,
    memory_compat_addr_ll addr ll mem ->
    memory_compat_addr_ll (addr + size_instr) rst_ll mem.
  Proof.
    intros.
    replace size_instr with (N_of_nat (nat_of_N size_instr)) by omega'.
    eapply memory_compat_addr_ll_drop; eauto.
    symmetry.
    eapply parse_instruction_drops; eauto.
  Qed.
  Local Hint Resolve memory_compat_parse_instruction.

  Lemma validate_n_byte_correct_addr n init_addr valid_addresses to_be_checked_addresses ll
    valid_addresses' to_be_checked_addresses' ll':
    validate_n_byte n init_addr valid_addresses to_be_checked_addresses ll
      = Some (valid_addresses', to_be_checked_addresses', ll') ->
    NSet_smaller valid_addresses init_addr ->
    forall mem, memory_compat_addr_ll init_addr ll mem ->
    forall addr, addr >= init_addr -> In_NSet addr valid_addresses' ->
      correct_addr mem (init_addr + n) valid_addresses'
        to_be_checked_addresses' addr.
  Proof.
    Ltac clean_classify :=
        match goal with
          | H : classify_instruction ?instr = _ |- _ =>
            match goal with
              | H' : classify_instruction instr = _ |- _ =>
                match H with
                  | H' => fail 1
                  | _ => rewrite H' in H; inv H
                end
            end
        end.

    fun_ind_validate_n_byte; intros; clean_post_fun_ind_validate; eauto;
    try(rewrite Nplus_assoc in *;
        destruct (N_eq_dec addr addr0);
        [ SCase " = "; subst|
          solve [eapply IHo; eauto]];

        eapply' CA_intro; eauto; instantiate; try(try red; intros; congruence);
          solve [try omega'; intros; clean_classify; eauto]).

    Case "fun_ind_validate_n_byte 1".
      specialize (H0 _ H3). contradiction.

    Case "fun_ind_validate_n_byte 3".
    clean0.
    destruct (Nadd_In_or _ _ _ H3).
      SCase "=". subst.
        eapply' CA_intro; eauto; instantiate; try (try red; intros; congruence).
        SSCase "SMALLER".
          omega'.
      SCase "<>".
        specialize (H0 _ H). contradiction.
    Case "fun_ind_validate_n_byte 4".
      repeat (rewrite Nplus_assoc in *).
      destruct (N_eq_dec addr addr0); [SCase "="|SCase "<>"].
      SCase "=".
       subst.
        eapply' CA_intro; eauto; instantiate; try (try red; intros; congruence).
        SSCase "SMALLER".
          omega'.
        SSCase "CLASSIFY_MASK".
          intros. rewrite H4 in e3. inv e3; clean.
          right. exists instr'; exists size_instr'.
          repeat split; eauto; try omega'.

      SCase "<>".
        apply IHo; eauto.

    Case "fun_ind_validate_n_byte 11".
      Focus 1.
      apply is_Nin_NIn in e5.
      destruct (N_eq_dec addr addr0).
      SCase "=".
        subst.
        eapply' CA_intro; eauto; instantiate; try (try red; intros; congruence).
          omega'.
          intros; clean_classify; eauto. repeat rewrite Nplus_assoc in *.
          split; eauto with nset.
      repeat rewrite Nplus_assoc in *.
      solve [eapply IHo; eauto].

    Case "fun_ind_validate_n_byte 12".
      repeat rewrite Nplus_assoc in *.
      destruct (N_eq_dec addr addr0).
      SCase "=".
        subst.

        eapply' CA_intro; eauto; instantiate; try (try red; intros; congruence).
          omega'.
          intros; clean_classify; eauto.
          repeat rewrite Nplus_assoc in *.
          split; eauto with nset.
       SCase "<>".
       eapply IHo; eauto.
  Qed.

  Hint Resolve validate_n_byte_correct_addr.

  Lemma validate_ll_list_add_valid_addresses_after init_addr valid_addresses
    to_be_checked_addresses ll valid_addresses' to_be_checked_addresses':
    validate_ll_list init_addr valid_addresses to_be_checked_addresses ll
      = Some (valid_addresses', to_be_checked_addresses') ->
    NSet_smaller valid_addresses init_addr ->
    forall addr,
      In_NSet addr valid_addresses' ->
      (addr < init_addr /\ In_NSet addr valid_addresses) \/
      (addr >= init_addr /\ addr < init_addr + N_of_nat (ll_length ll)).
  Proof.
    fun_ind_validate_ll; intros; clean; eauto.
    Case "fun_ind_validate_ll 1".
    pose proof (validate_n_byte_size _ _ _ _ _ _ _ e).
    rewrite H in *.
    edestruct validate_n_byte_add_valid_addresses_after as [[? ?]| [? ?]]; eauto.
    Case "fun_ind_validate_ll 2".
    edestruct IHo as [[]|[]]; eauto.
      SCase "premice".
        unfold NSet_smaller; intros.
        edestruct validate_n_byte_add_valid_addresses_after as [[]|[]]; eauto; omega'.
      SCase "left".
        edestruct validate_n_byte_add_valid_addresses_after as [[]|[]]; eauto; try omega'.
        right; split; eauto. eapply validate_n_byte_drop_n in e; eauto.
        apply ll_safe_drop_size in e. omega'.
      SCase "right".
        right; split; try omega'. eapply validate_n_byte_drop_n in e; eauto.
        apply ll_safe_drop_size in e. omega'.
  Qed.

  Lemma validate_ll_list_add_addr:
    forall (addr: N)
    (valid_addresses to_be_checked_addresses: NSet) (ll: lazy_list byte)
    valid_addresses' to_be_checked_addresses',
    validate_ll_list addr valid_addresses to_be_checked_addresses ll =
    Some (valid_addresses', to_be_checked_addresses') ->
    ll <> 〈〉 ->
    In_NSet addr valid_addresses'.
  Proof.
    intros * VALIDATE.
    functional inversion VALIDATE; try (subst;
    subst);
    repeat match goal with
      | x := _ : _ |- _ => subst x
    end;
    (try apply validate_n_byte_increase_valid_addresses in X);
    eauto with nset.
  Qed.


  Lemma validate_ll_list_correct_addr init_addr valid_addresses to_be_checked_addresses ll
    valid_addresses' to_be_checked_addresses':
    validate_ll_list init_addr valid_addresses to_be_checked_addresses ll =
      Some (valid_addresses', to_be_checked_addresses') ->
    NSet_smaller valid_addresses init_addr ->
    forall mem, memory_compat_addr_ll init_addr ll mem ->
    forall addr, addr >= init_addr -> In_NSet addr valid_addresses' ->
      correct_addr mem (init_addr + N_of_nat (ll_length ll)) valid_addresses'
        to_be_checked_addresses' addr.
  Proof.
    fun_ind_validate_ll; intros; clean; eauto.
    Case "fun_ind_validate_ll 1".
      pose proof (validate_n_byte_reduces_size_by_n _ _ _ _ _ _ _ _ e).
      simpl in H. rewrite H. eauto.
    Case "fun_ind_validate_ll 2".
      pose proof (validate_n_byte_reduces_size_by_n _ _ _ _ _ _ _ _ e).
      rewrite H4. rewrite N_of_plus. replace (N_of_nat 32) with 32 by reflexivity.
      rewrite Nplus_assoc.

      edestruct validate_ll_list_add_valid_addresses_after as [[]|[]]; eauto.
      SCase "smaller".
        unfold NSet_smaller; intros;
          edestruct validate_n_byte_add_valid_addresses_after as [[]|[]]; eauto; omega'.
      SCase "left".
        eapply validate_n_byte_correct_addr in e; eauto.
        change (N_of_nat 32) with 32 in *.
        assert (forall addr',
          ok_addr (addr + 32) valid_addresses'0 to_be_checked_addresses'0 addr' ->
          ok_addr (addr + 32 + N_of_nat (ll_length ll')) valid_addresses'
            to_be_checked_addresses' addr').
          SSCase "Prove assert".
            Focus 1.
            intros.
            destruct' H7; eauto.
            S3Case "OK_next".
              subst.
              destruct ll'. simpl. clean0.
              eapply OA_Valid; eauto.
              eapply validate_ll_list_add_addr; eauto. congruence.
        SSCase "Use assert".
        inv e.
        eapply' CA_intro; intros; clean;eauto.
        S3Case "SMALLER".
          omega'.
        S3Case "CLASSIFY_DIRECT".
          edestruct CLASSIFY_DIRECT; eauto.
        S3Case "CLASSIFY_MASK".
          edestruct CLASSIFY_MASK as [|[instr'[size_instr'[?[]]]]]; eauto.
          right. exists instr'; exists size_instr'. intuition (try omega').
          eauto.

      SCase "right".
      eapply IHo; eauto.
        SSCase "NSet smaller".
          unfold NSet_smaller.
          intros.
          edestruct validate_n_byte_add_valid_addresses_after as [[? ?]| [? ?]]; eauto.
            omega'.
        SSCase "memory_compat".
          eapply memory_compat_addr_ll_drop in H1; eauto.
          eauto.
  Qed.


  Inductive danger_in_n_steps code_size st: nat -> Prop :=
  | DINS_O: step code_size st DANGER_STATE -> danger_in_n_steps code_size st O
  | DINS_S: forall n st', step code_size st (Normal_state st') ->
    danger_in_n_steps code_size st' n -> danger_in_n_steps code_size st (S n).

  Lemma dividable_by_32_header_size: dividable_by_32 header_size.
  Proof.
    exists 2048; reflexivity.
  Qed.

  Local Hint Resolve addresses_multiple_of_32_in_valid_addresses dividable_by_32_header_size.
  Ltac clean_state :=
    repeat
    match goal with
      | |-
        context [state_pc
          {| state_mem := ?MEM; state_regs := ?REGS; state_pc := ?PC|}] =>
        change (state_pc
          {| state_mem := MEM; state_regs := REGS; state_pc := PC|})
      with PC in *
      | H :  context [state_pc
        {| state_mem := ?MEM; state_regs := ?REGS; state_pc := ?PC|}]|- _ =>
      change (state_pc
        {| state_mem := MEM; state_regs := REGS; state_pc := PC|})
      with PC in *
      | |-
        context [state_mem
          {| state_mem := ?MEM; state_regs := ?REGS; state_pc := ?PC|}] =>
        change (state_mem
          {| state_mem := MEM; state_regs := REGS; state_pc := PC|})
      with MEM in *
      | H :  context [state_mem
        {| state_mem := ?MEM; state_regs := ?REGS; state_pc := ?PC|}]|- _ =>
      change (state_mem
        {| state_mem := MEM; state_regs := REGS; state_pc := PC|})
      with MEM in *
      | |-
        context [state_regs
          {| state_mem := ?MEM; state_regs := ?REGS; state_pc := ?PC|}] =>
        change (state_regs
          {| state_mem := MEM; state_regs := REGS; state_pc := PC|})
      with REGS in *
      | H :  context [state_regs
        {| state_mem := ?MEM; state_regs := ?REGS; state_pc := ?PC|}]|- _ =>
      change (state_regs
        {| state_mem := MEM; state_regs := REGS; state_pc := PC|})
      with REGS in *
    end.

  Lemma step_same_code: forall code_size st1 st2,
    step code_size st1 (Normal_state st2) ->
    same_code code_size st1.(state_mem) st2.(state_mem).
  Proof.
    intros * STEP.
    inv STEP; clean_state; eauto.
    destruct H0.
    pose proof (sem_no_overwrite H2).
    unfold same_code in *; intros. rewrite H3; eauto.
    eapply H4. omega'.
  Qed.
  Local Hint Resolve same_code_trans step_same_code.


  Lemma tri_split n1 n2 n:
    n < n1 \/
    (n1 <= n /\ n < n2) \/
    n2 <= n.
  Proof.
    destruct (N_lt_dec n n1); auto.
    destruct (N_lt_dec n n2); auto.
  Qed.


  Lemma dividable_by_32_translate_by_5: forall n,
    dividable_by_32 n -> exists n1, n = translate_N_by 5 n1.
  Proof.
    intros n [div MULT].
    exists div.
    destruct n; auto.
  Qed.

  Lemma translate_by_5_dividable_by_32: forall n,
    (exists n1, n = translate_N_by 5 n1 )-> dividable_by_32 n.
  Proof.
    intros n [div MULT].
    exists div.
    destruct n; auto.
  Qed.

  Lemma dividable_by_32_and: forall n1 n2, dividable_by_32 n1 ->
    dividable_by_32 (N_and n1 n2).
  Proof.
    intros.
    apply dividable_by_32_translate_by_5 in H.
    apply translate_by_5_dividable_by_32.
    apply translate_and. auto.
  Qed.

  Lemma le_sym_1: forall n1 n2, n1 <= n2 -> n2 >= n1. intros; omega'. Qed.
  Lemma le_sym_2: forall n1 n2, n1 >= n2 -> n2 <= n1. intros; omega'. Qed.
  Local Hint Resolve le_sym_2 le_sym_1.

    Ltac solve_and_proper :=
      repeat match goal with
               | |-
                 context [match ?EXPR with pair  _ _ => _ end] =>
                 destruct EXPR
             end;
      simpl;
      match goal with
        | |- dividable_by_32 (concat_byte ?EXPR _) =>
          destruct EXPR
      end; compute;
      try solve [exists 0; reflexivity];
      try solve [
        match goal with
          | |-
            exists d:N, ?VAL = _ =>
              remember (dividable_by_32_dec VAL) as foo;
                destruct foo; auto
        end];
      match goal with
        | |-
          (exists d:N,
            Npos ?D~0~0~0~0~0 = _) =>
          exists (Npos D); reflexivity
      end.


  Lemma and_proper_mask_dividable : forall n,
    dividable_by_32
    (N_of_word
      (word_of_N
        (N_and (N_of_word proper_mask) n))).
  Proof with (try solve [solve_and_proper]).


    intro n.
    change (N_of_word proper_mask) with 4294967264.
    assert (dividable_by_32 4294967264).
    exists 134217727; auto.
    pose proof (dividable_by_32_and _ n H).
    destruct H0. rewrite H0.
    destruct x.
      exists 0; reflexivity.
      simpl.
      unfold word_of_N, fst_byte. simpl.
      repeat match goal with
        | |-
          context[match ?p with
                    | _~1 => _
                    | _~0 => _
                    | 1%positive => _
                  end] =>
          destruct p
      end; try solve_and_proper.
  Qed.

  Lemma almost_there: forall ll code_size valid_addresses to_be_checked_addresses,
    validate_ll_list header_size Nempty Nempty ll
      = Some (valid_addresses, to_be_checked_addresses) ->
    Nincluded to_be_checked_addresses valid_addresses ->
    code_size = N_of_nat (ll_length ll) ->
    forall mem, memory_compat_addr_ll header_size ll mem ->
    forall n,
    forall st,
      danger_in_n_steps code_size st n ->
      same_code code_size mem st.(state_mem) ->
      ( (st.(state_pc) < header_size /\ dividable_by_32 st.(state_pc)) \/
        (header_size + code_size) <= st.(state_pc) \/
        (header_size <= st.(state_pc) /\ st.(state_pc) < (header_size + code_size)
          /\ correct_addr st.(state_mem) (header_size + code_size)
               valid_addresses to_be_checked_addresses st.(state_pc))) ->
      False.
  Proof.
    Ltac clean_read :=
      match goal with
        | H : read_instr_from_memory ?M ?A = _ |- _ =>
          match goal with
            | H' : read_instr_from_memory M A = _ |- _ =>
              match H with
                | H' => fail 1
                | _ => rewrite H in H'; clean
              end
          end
      end.
    Ltac tri_split:=
      match goal with
        | |- context[header_size + ?code_size <= ?VAL] =>
          decompose [and or]
            (tri_split header_size (header_size + code_size)
              VAL); eauto
      end.

    intros * VALIDATE INCLUDED CODE_SIZE mem COMPAT n.
    assert (forall addr, In_NSet addr valid_addresses ->
      header_size <= addr) as ADDR_SUP.
    intros.
    edestruct validate_ll_list_add_valid_addresses_after as [[]|[]]; eauto with nset.
      elimtype False; eauto with nset.

    assert (forall addr, In_NSet addr valid_addresses ->
      addr < header_size + code_size) as ADDR_INF.
    intros.
    edestruct validate_ll_list_add_valid_addresses_after as [[]|[]]; eauto with nset.
      elimtype False; eauto with nset. omega'.

    pose proof (addresses_multiple_of_32_in_valid_addresses _ _ _ _ _ _
    dividable_by_32_header_size VALIDATE) as IN_SET.

    assert (forall mem,
      memory_compat_addr_ll header_size ll mem ->
      forall addr : N,
      addr >= header_size ->
      In_NSet addr valid_addresses ->
      correct_addr mem (header_size + N_of_nat (ll_length ll))
        valid_addresses to_be_checked_addresses addr) as IMP_CORRECT.
    eapply validate_ll_list_correct_addr; eauto with nset.

    apply (lt_wf_ind n). clear n.
    intros n IND_HYP st DANGER SAME CORRECT.
    destruct' n as [|n]; inv DANGER.
    Case "O".
      decompose [and or] CORRECT.
      SCase "inf".
        inv H; eauto; inv H0; omega'.
      SCase "sup".
        inv H; eauto; (try solve [inv H0; omega']). omega'.
      SCase "incode".
      inv H3; inv H;
      try clean_read.
      SSCase "to bad".
        destruct' (classify_instruction instr) as [] _eqn; try congruence;
          eapply sem_not_invalid_not_bad; eauto; congruence.
      SSCase "not div".
        omega'.
   Case "S n".
   pose proof (step_same_code _ _ _ H0).
   assert (forall addr n' m regs,
     ok_addr (header_size + N_of_nat (ll_length ll))
       valid_addresses to_be_checked_addresses addr ->
     (n' < S n)%nat ->
     same_code (N_of_nat (ll_length ll)) mem m ->
     danger_in_n_steps (N_of_nat (ll_length ll))
     {| state_mem := m;
        state_regs := regs;
        state_pc := addr |} n' ->
     False) as OK_DANGER.
   Focus 1.
   intros.
   eapply IND_HYP; eauto.
   clean_state.
   destruct' H2.
   SCase "OA_Valid".
     right; right; repeat split; eauto.
   SCase "OK_checked".
     right; right; repeat split; eauto.
     eapply validate_ll_list_correct_addr; eauto with nset.
   SCase "OK_next".
     right; left; omega'.
   SCase "OK_div".
     tri_split; eauto with nset.
     right; right; repeat split; eauto.

   inv H0.
   SCase "normal step".
     inv H3. decompose [and or] CORRECT; try omega'.
     inv H9; clean_read.
     unfold read_instr_from_memory in READ_FROM_MEM.
     match type of READ_FROM_MEM with
       | context[parse_instruction ?ADDR ?LL] =>
         destruct (parse_instruction ADDR LL) as [[[]]|] _eqn; clean
     end.
     destruct' (classify_instruction instr) as [] _eqn; try congruence.
     SSCase "@OK_instr".
       clear CLASSIFY_DIRECT CLASSIFY_MASK.
       eapply sem_OK_instr_pc in H5; eauto.
       destruct st2 as [state2_mem state2_regs state2_pc]; clean_state. subst.
       specialize (CLASSIFY_OK eq_refl). eauto.
     SSCase "Mask_instr".
       Focus 1.
       clear CLASSIFY_OK CLASSIFY_DIRECT.
       pose proof H5.
       eapply sem_Mask_instr_pc in H5; eauto.
       eapply sem_Mask_instr_reg in H4; eauto.
       destruct st2 as [state2_mem state2_regs state2_pc]; clean_state. subst.
       specialize (CLASSIFY_MASK r w eq_refl).
       destruct CLASSIFY_MASK as
         [|[instr'[size_instr' ?]]]. eauto.
       S3Case "Indirect_jump".
         decompose [or and] H5. clear H5. subst.
         assert (read_instr_from_memory m2' (state_pc st +  n0) =
           Some (instr', size_instr')) as READ_M2 by eauto.
(*         unfold read_instr_from_memory in *.
         eapply parse_instruction_only_read; eauto.
         intros. simpl.
         assert (same_code (N_of_nat (ll_length ll)) (state_mem st) m2').
           eauto.
         unfold same_code in H5.
         apply H5. omega'.*)
         destruct' n as [|n].
         S4Case "O".
           inv H1.
           inv H5; clean_state; try clean_read; try omega'.
           eapply sem_not_invalid_not_bad; eauto; congruence.
         S4Case "S n".
           inv H1.
           pose proof H8 as STEP. eapply step_same_code in STEP.
           (*eapply (IND_HYP n); eauto.*)
           inv H8; clean_state; try clean_read; eauto.
           S5Case "normal instr".
             destruct st2 as [state3_mem state3_regs state3_pc]; clean_state.

             unfold read_instr_from_memory in H10.
             match type of H10 with
               | context[parse_instruction ?ADDR ?LL] =>
                 destruct (parse_instruction ADDR LL) as [[[]]|] _eqn; clean
             end.

             edestruct sem_Indirect_jump_pc with (instr:=instr'); eauto; instantiate; clean_state.
             eapply Heqo0.
             subst. eapply OK_DANGER with (n' := n) (m := m2'0); eauto.
             subst. clear H11.
             eapply OK_DANGER with (n' := n) (m := m2'0) (4 := H12); eauto.
             eapply OK_div. simpl. rewrite H4.
             unfold word_and. clear.
             apply and_proper_mask_dividable.

           S5Case "before header".
             eapply (IND_HYP n); eauto.
             tri_split; eauto.
             right. right. repeat split; eauto.
             eapply validate_ll_list_correct_addr; eauto with nset.


     SSCase "Direct_jump".
       clear CLASSIFY_OK CLASSIFY_MASK.
       specialize (CLASSIFY_DIRECT w eq_refl).

       destruct CLASSIFY_DIRECT.
       destruct st2 as [state2_mem state2_regs state2_pc]; clean_state.
       edestruct sem_Direct_jump_pc; eauto; instantiate; clean_state;
         subst; eauto.


   SCase "from header".
     eapply IND_HYP; eauto.
     decompose [and or] (tri_split header_size (header_size + N_of_nat (ll_length ll)) pc2); eauto.
     right. right. repeat split; eauto.
     eapply validate_ll_list_correct_addr; eauto with nset.
  Qed.

(* toutes les addresses multiple de 32 sont dans valid_addresses



 *)

End ValProof.