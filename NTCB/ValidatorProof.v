Require Import Lib.
Require Import BinaryProps.
Require Import List.
Require Import LazyList.
Require Import Semantics.
Require Import SemanticsProp.
Require Import NSet.
Require Import BinaryProps.
Require Import Recdef.
Require Import Validator.


Module ValProof (Import I : INSTRUCTION) (Import ISP: INSTRUCTION_SEMANTICS_PROP(I)).
  Module Val := ValidatorCode(I).
  Module ProgSem := Prog_Semantics(I).
  Import ProgSem.
  Import Val.
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


  Lemma validate_n_byte_increase_valid_addresses:
    forall (n: nat) (addr: N)
    (valid_addresses to_be_checked_addresses: NSet) (ll: lazy_list byte)
    valid_addresses' to_be_checked_addresses' ll',
    validate_n_byte n addr valid_addresses to_be_checked_addresses ll =
    Some (valid_addresses', to_be_checked_addresses', ll') ->
    Nincluded valid_addresses valid_addresses'.
  Proof.
    intros * VALIDATE.
    fun_ind_validate_n_byte; clean; eauto with nset.
  Qed.

  Lemma validate_n_byte_increase_to_be_checked_addresses:
    forall (n: nat) (addr: N)
    (valid_addresses to_be_checked_addresses: NSet) (ll: lazy_list byte)
    valid_addresses' to_be_checked_addresses' ll',
    validate_n_byte n addr valid_addresses to_be_checked_addresses ll =
    Some (valid_addresses', to_be_checked_addresses', ll') ->
    Nincluded to_be_checked_addresses to_be_checked_addresses'.
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
    forall (n: nat) (addr: N)
    (valid_addresses to_be_checked_addresses: NSet) (ll: lazy_list byte)
    valid_addresses' to_be_checked_addresses' ll',
    validate_n_byte n addr valid_addresses to_be_checked_addresses ll =
    Some (valid_addresses', to_be_checked_addresses', ll') ->
    ll_safe_drop n ll = Some ll'.
  Proof.
    intros * VALIDATE.
    fun_ind_validate_n_byte; clean; eauto with nset;
    apply safe_minus_correct in e3; subst;
    rewrite ll_safe_drop_plus; rewrite e2; eauto.
    apply safe_minus_correct in e12.
    subst. rewrite ll_safe_drop_plus; rewrite e11; eauto.
  Qed.
  Local Hint Resolve validate_n_byte_drop_n validate_n_byte_increase_to_be_checked_addresses
    validate_n_byte_increase_valid_addresses.

  Lemma validate_ll_list_increase_valid_addresses:
    forall (addr: N)
    (valid_addresses to_be_checked_addresses: NSet) (ll: lazy_list byte)
    valid_addresses' to_be_checked_addresses',
    validate_ll_list addr valid_addresses to_be_checked_addresses ll =
    Some (valid_addresses', to_be_checked_addresses') ->
    Nincluded valid_addresses valid_addresses'.
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
    Nincluded to_be_checked_addresses to_be_checked_addresses'.
  Proof.
    intros * VALIDATE.
    fun_ind_validate_ll; clean; eauto with nset.
  Qed.

  Local Hint Resolve validate_ll_list_increase_to_be_checked_addresses
    validate_ll_list_increase_valid_addresses.


  Lemma validate_n_byte_add_addr:
    forall (addr: N) n
    (valid_addresses to_be_checked_addresses: NSet) (ll: lazy_list byte)
    valid_addresses' to_be_checked_addresses' ll',
    validate_n_byte (S n) addr valid_addresses to_be_checked_addresses ll =
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
    forall (n: nat) (addr: N)
    (valid_addresses to_be_checked_addresses: NSet) (ll: lazy_list byte)
    valid_addresses' to_be_checked_addresses',
    validate_n_byte n addr valid_addresses to_be_checked_addresses ll =
    Some (valid_addresses', to_be_checked_addresses', 〈〉) ->
    ll_length ll = n.
  Proof.
    intros * VALIDATE.
    fun_ind_validate_n_byte; clean;
    try (specialize (IHo VALIDATE)); subst;
    apply ll_safe_drop_size in e2;
    apply safe_minus_correct in e3; try omega.

    Case "fun_ind_validate_n_byte 3".
    simpl in *. omega.
    Case "fun_ind_validate_n_byte 4".
    apply ll_safe_drop_size in e11.
    apply safe_minus_correct in e12. omega.
  Qed.

  Ltac omega' := zify; omega.

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
      destruct H. destruct H3. omega'.

    Case "fun_ind_validate_ll 2".
      assert (dividable_by_32 (addr + 32)).
        destruct H. exists (x + 1). zify; omega.
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
  

  Inductive correct_addr mem next_addr valid_addresses
    to_be_checked_addresses addr : Prop :=
  | CA_intro:
    forall instr size_instr
    (SMALLER: addr + (N_of_nat size_instr) <= next_addr)
    (READ_FROM_MEM: read_instr_from_memory mem addr = Some (instr, size_instr))
    (NOT_INV: classify_instruction instr <> Invalid_instruction)
    (NOT_IND: forall reg, classify_instruction instr <> Indirect_jump reg)
    (CLASSIFY_OK: classify_instruction instr = OK_instr ->
      ok_addr next_addr valid_addresses to_be_checked_addresses
        (addr + N_of_nat size_instr))
    (CLASSIFY_DIRECT: forall w,
      classify_instruction instr = Direct_jump w ->
      ok_addr next_addr valid_addresses to_be_checked_addresses
        (addr + N_of_nat size_instr) /\
      ok_addr next_addr valid_addresses to_be_checked_addresses
        (N_of_word w))
    (CLASSIFY_MASK: forall reg w,
      classify_instruction instr = Mask_instr reg w ->
      ok_addr next_addr valid_addresses to_be_checked_addresses
        (addr + N_of_nat size_instr) \/
      (exists instr', exists size_instr',
        read_instr_from_memory mem (addr + (N_of_nat size_instr)) =
          Some (instr', size_instr') /\
        addr + (N_of_nat size_instr) + (N_of_nat size_instr') <= next_addr /\
        classify_instruction instr' = Indirect_jump reg)),
    correct_addr mem next_addr valid_addresses
      to_be_checked_addresses addr.
      
  Lemma correct_addr_same_code mem1 mem2
    next_addr valid_addresses to_be_checked_addresses addr:
    same_code next_addr mem1 mem2 ->
    correct_addr mem1 next_addr valid_addresses to_be_checked_addresses addr ->
    correct_addr mem2 next_addr valid_addresses to_be_checked_addresses addr.
  Proof.
    intros SAME CORRECT.
    inv CORRECT.
    eapply' CA_intro; eauto.
    Case "READ_FROM_MEM".
      clear - SAME READ_FROM_MEM SMALLER.
      unfold same_code, read_instr_from_memory in *.
      eapply parse_instruction_only_read; eauto.
      intros. simpl. apply SAME. omega'.
    Case "CLASSIFY_MASK".
      intros * OK.
      specialize (CLASSIFY_MASK reg w OK).
      destruct CLASSIFY_MASK as [|[instr' [size_instr' [?[? ?]]]]]; eauto.
      right. exists instr'; exists size_instr'.
      repeat split; eauto.
      unfold same_code, read_instr_from_memory in *.
      eapply parse_instruction_only_read; eauto.
      intros. simpl. apply SAME. omega'.
  Qed.


  Definition correct_state_1 valid_addresses to_be_checked_addresses next_address (st: state register) :=
    (  dividable_by_32 st.(state_pc)
    \/ In_NSet st.(state_pc) valid_addresses
    \/ In_NSet st.(state_pc) to_be_checked_addresses
    \/ st.(state_pc) = next_address).

  Definition one_step_correct code_size
    valid_addresses to_be_checked_addresses next_address st1 :=
    (~step header_size code_size st1 DANGER_STATE) /\
    forall st2, step header_size code_size st1 (Normal_state st2) ->
      correct_state_1 valid_addresses to_be_checked_addresses next_address st2.


  Definition two_steps_correct code_size
    valid_addresses to_be_checked_addresses next_address st1 :=
    (~step header_size code_size st1 DANGER_STATE) /\
    forall st2, step header_size code_size st1 (Normal_state st2) ->
    ( correct_state_1 valid_addresses to_be_checked_addresses next_address st2 \/
      one_step_correct code_size valid_addresses
         to_be_checked_addresses next_address st2).

  Lemma one_step_correct_trans:
    forall code_size valid_addresses
      to_be_checked_addresses to_be_checked_addresses' addr addr' st,
      Nincluded to_be_checked_addresses to_be_checked_addresses' ->
      one_step_correct code_size valid_addresses
        to_be_checked_addresses addr st ->
      one_step_correct code_size (Nadd addr valid_addresses)
        to_be_checked_addresses' addr' st.
  Proof.
    unfold one_step_correct, correct_state_1, Nincluded.
    intuition eauto.
    edestruct H2 as [ | [ | [|]]];  eauto with nset.
    subst. eauto with nset.
  Qed.

  Hint Resolve one_step_correct_trans.

  Lemma two_steps_correct_trans:
    forall code_size valid_addresses
      to_be_checked_addresses to_be_checked_addresses' addr addr' st,
      Nincluded to_be_checked_addresses to_be_checked_addresses' ->
      two_steps_correct code_size valid_addresses
        to_be_checked_addresses addr st ->
      two_steps_correct code_size (Nadd addr valid_addresses)
        to_be_checked_addresses' addr' st.
  Proof.
    unfold two_steps_correct, Nincluded, correct_state_1.
    intuition eauto.
    edestruct H2 as [[|[|[|]]]|]; eauto 6 with nset.
    subst. eauto with nset.
  Qed.




  Definition memory_compat_addr_ll addr ll (mem: memory):=
    forall n, (n < ll_length ll)%nat -> ll_nth n ll = mem (addr + N_of_nat n).


  (* to lib *)
  Lemma ll_safe_drop_nth {X}: forall n (ll: lazy_list X) ll',
    ll_safe_drop n ll = Some ll' ->
    forall i, ll_nth i ll' = ll_nth (n + i) ll.
  Proof.
    induction' n as [|n]; auto; simpl; intros; clean.
    Case "S n".
      destruct' ll as [|x [ll]]; clean.
  Qed.




  Lemma memory_compat_addr_ll_drop: forall addr ll mem n ll',
    ll_safe_drop n ll = Some ll' ->
    memory_compat_addr_ll addr ll mem ->
    memory_compat_addr_ll (addr + N_of_nat n) ll' mem.
  Proof.
    unfold memory_compat_addr_ll. intros.
    erewrite ll_safe_drop_nth; eauto.
    rewrite <- Nplus_assoc. rewrite <- N_of_plus. apply H0.
    apply ll_safe_drop_size in H. omega.
  Qed.

  Local Hint Resolve memory_compat_addr_ll_drop.

(*  Lemma parse_instr_impl_read_instr:
    forall ll instr size_instr
  parse_instruction (byte_map_from_ll ll) = Some (instr, size_instr) ->
  memory_compat_addr_ll addr ll mem ->
  same_code (header_size + code_size) mem st.(state_mem) ->
  in_code header_size code_size st ->
  read_instr_from_memory st.(state_mem) st.(state_pc) = Some instr. *)

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
        end.

  Lemma validate_n_byte_two_steps: forall code_size (n: nat) (addr: N)
    (valid_addresses to_be_checked_addresses: NSet) (ll: lazy_list byte)
    valid_addresses' to_be_checked_addresses' ll' oreg,

    validate_n_byte n addr valid_addresses to_be_checked_addresses ll =
      Some (valid_addresses', to_be_checked_addresses', ll') ->
    addr + (N_of_nat n) <= header_size + code_size ->

    forall mem, memory_compat_addr_ll addr ll mem ->

    (forall st, same_code (header_size + code_size) mem st.(state_mem) ->
       In_NSet st.(state_pc) valid_addresses ->
       two_steps_correct code_size
         valid_addresses to_be_checked_addresses addr st) ->

    (forall st, same_code (header_size + code_size) mem st.(state_mem) ->
       In_NSet st.(state_pc) valid_addresses' ->
       two_steps_correct code_size
         valid_addresses' to_be_checked_addresses' (addr + N_of_nat n) st).
  Proof.
    intros *.
    fun_ind_validate_n_byte; intros; clean0; eauto;
    apply safe_minus_correct in e3; subst;
    rewrite plus_N_of_nat in *.
    admit. admit. admit. admit. admit. admit.




    eapply IHo; clear IHo; clean_safe_minus; eauto; try omega';
      intros; clean; eauto;
    (destruct (Nadd_In_or _ _ _ H6));
      [(subst; clear H6)
      | solve [eapply two_steps_correct_trans; eauto with nset]].




    Case "fun_ind_validate_n_byte 2".
      unfold two_steps_correct.
      assert (read_instr_from_memory st0.(state_mem) st0.(state_pc)
                = Some (instr, size_instr)) by admit.
(*        unfold read_instr_from_memory.
        eapply parse_instruction_only_read; eauto.
        unfold byte_map_from_ll. intros. unfold memory_compat_addr_ll, same_code in *.
        rewrite Nplus_comm.*)

      split.
      SCase "NON DANGER".
      match goal with
        | H : classify_instruction ?instr = _ |- _ =>
          let NOT_INV := fresh "NOT_INV" in
          assert (classify_instruction instr <> Invalid_instruction) as NOT_INV by
            (rewrite H; intro __EQ_INVALID__; inv __EQ_INVALID__);
          pose proof (sem_not_invalid_not_bad instr NOT_INV)
      end.
      intro DANGER.
      inv DANGER.
        SSCase "read fail".
          congruence.
        SSCase "bad instr sem".
          rewrite H11 in H7. clean.
          eapply H9; eauto.
        SSCase "outside not div".


*)
   Admitted.



  Lemma validate_ll_list_two_steps: forall code_size (addr: N)
    (valid_addresses to_be_checked_addresses: NSet) (ll: lazy_list byte)
    valid_addresses' to_be_checked_addresses',
    validate_ll_list addr valid_addresses to_be_checked_addresses ll =
      Some (valid_addresses', to_be_checked_addresses') ->
    addr + (N_of_nat (ll_length ll)) <= header_size + code_size ->
    forall mem, memory_compat_addr_ll addr ll mem ->
    (forall addr', In_NSet addr' valid_addresses ->
     forall st, same_code (header_size + code_size) mem st.(state_mem) ->
       In_NSet st.(state_pc) valid_addresses ->
       two_steps_correct code_size
         valid_addresses to_be_checked_addresses st) ->
    (forall addr', In_NSet addr' valid_addresses' ->
     forall st, same_code (header_size + code_size) mem st.(state_mem) ->
       In_NSet st.(state_pc) valid_addresses' ->
       two_steps_correct code_size
         valid_addresses' to_be_checked_addresses' st).
  Proof.
    intros *.
    fun_ind_validate_ll; intros; clean; eauto.
    Case "fun_ind_validate_ll 1".
      eapply validate_n_byte_two_steps; eauto.
      apply validate_n_byte_size in e. rewrite e in H0. auto.
    Case "fun_ind_validate_ll 2".
      eapply IHo; eauto; clear IHo.

      apply validate_n_byte_drop_n in e. apply ll_safe_drop_size in e.
      rewrite e in H0. rewrite N_of_plus in H0. simpl N_of_nat in H0.
      omega'.

      replace 32 with (N_of_nat 32) by reflexivity.
      eapply memory_compat_addr_ll_drop; eauto.

      intros. eapply validate_n_byte_two_steps; eauto.
      apply validate_n_byte_drop_n in e. apply ll_safe_drop_size in e.
      rewrite e in H0. rewrite N_of_plus in H0. simpl N_of_nat in H0.
      omega'.
  Qed.


  Inductive danger_in_n_steps code_size st: nat -> Prop :=
  | DINS_O: step header_size code_size st DANGER_STATE -> danger_in_n_steps code_size st O
  | DINS_S: forall n st', step header_size code_size st (Normal_state st') ->
    danger_in_n_steps code_size st' n -> danger_in_n_steps code_size st (S n).


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


  Definition correct_state_2 code_size valid_addresses (st: state register) :=
    ((  In_NSet st.(state_pc) valid_addresses)
     \/ (st.(state_pc) < header_size /\ dividable_by_32 st.(state_pc))
     \/ ((header_size + code_size) <= st.(state_pc))).

  Lemma correct_state_2_of_1 valid_addresses to_be_checked_addresses code_size st:
    Nincluded to_be_checked_addresses valid_addresses ->
    (forall addr, header_size <= addr -> addr < header_size + code_size ->
       dividable_by_32 addr -> In_NSet addr valid_addresses) ->
    correct_state_1 valid_addresses to_be_checked_addresses st ->
    correct_state_2 code_size valid_addresses st.
  Proof.
    intros * NINCLUDED DIVBY__IN CORRECT1.
    unfold correct_state_2, correct_state_1 in *.
    destruct CORRECT1 as [|[|]]; eauto.
    destruct (N_lt_dec (state_pc st) header_size); eauto.
    destruct (N_le_dec (header_size + code_size) (state_pc st)); auto.
  Qed.

  Lemma dividable_by_32_header_size: dividable_by_32 header_size.
  Proof.
    exists 2048; reflexivity.
  Qed.

  Local Hint Resolve addresses_multiple_of_32_in_valid_addresses correct_state_2_of_1 dividable_by_32_header_size.

  Lemma same_code_trans: forall code_segment_size st1 st2 st3,
    same_code code_segment_size st1 st2 -> same_code code_segment_size st2 st3 ->
    same_code code_segment_size st1 st3.
  Proof.
    unfold same_code; intros.
    rewrite H; eauto.
  Qed.

  Lemma step_same_code: forall header_size code_size st1 st2,
    step header_size code_size st1 (Normal_state st2) ->
    same_code (header_size + code_size) st1.(state_mem) st2.(state_mem).
  Proof.
    intros * STEP.
    inv STEP; simpl in *; eauto.
    destruct H0.
    pose proof (sem_no_overwrite _ _ _ _ H2).
    unfold same_code in *; intros. rewrite H3; eauto.
  Qed.
  Local Hint Resolve same_code_trans step_same_code.




  Theorem roxx: forall ll code_size valid_addresses to_be_checked_addresses,
    validate_ll_list header_size Nempty Nempty ll = Some (valid_addresses, to_be_checked_addresses) ->
    Nincluded to_be_checked_addresses valid_addresses ->
    code_size = N_of_nat (ll_length ll) ->
    forall mem, memory_compat_addr_ll header_size ll mem ->
    forall n,
    forall st, same_code (header_size + code_size) mem st.(state_mem) ->
      correct_state_2 code_size valid_addresses st->
      danger_in_n_steps code_size st n -> False.
  Proof.
    intros * VALIDATE INCLUDED CODE mem COMPAT n.
    apply (lt_wf_ind n). clear n. intros * INDUCTION_PRINCIPLE * SAME PROP_STATE DANGER.
    inv DANGER.
    Case "0%nat".
      destruct PROP_STATE as [IN | [[INF DIV] | SUP]].
      SCase "IN".
        assert (two_steps_correct (N_of_nat (ll_length ll)) valid_addresses to_be_checked_addresses st).
          eapply validate_ll_list_two_steps; eauto.
          omega'.
          intros. apply Nempty_empty in H2. inv H2.
        inv H0. contradiction.
      SCase "INF".
        inv H; try (inv H0; omega'). contradiction.
      SCase "SUP".
        inv H; try (inv H0; omega'). omega'.

    Case "S n".
      unfold correct_state_2 in PROP_STATE.
      destruct PROP_STATE as [IN | [[INF DIV] | SUP]].
      SCase "IN".
        assert (two_steps_correct (N_of_nat (ll_length ll)) valid_addresses to_be_checked_addresses st) as TWO_STEPS.
          eapply validate_ll_list_two_steps; eauto.
          omega'.
          intros. apply Nempty_empty in H3. inv H3.
        destruct TWO_STEPS as [_ ?].
        specialize (H1 _ H).
        destruct H1 as [CORRECT | ONE_STEP].
        SSCase "CORRECT".
          eapply INDUCTION_PRINCIPLE with (st := st'); eauto.
        SSCase "ONE STEP".
          destruct ONE_STEP as [NO_DANGER CORR1].
          inv H0. contradiction.
          specialize (CORR1 _ H1).
          eapply (INDUCTION_PRINCIPLE n) with (st := st'0); eauto.
      SCase "INF".
      inv H.
        destruct H2. omega'.
        eapply (INDUCTION_PRINCIPLE n0).
        Focus 4. eauto. omega. eauto.
        unfold correct_state_2.
        destruct (N_lt_dec pc2 header_size); eauto.
        destruct (N_le_dec (header_size + (N_of_nat (ll_length ll))) pc2); eauto.

      SCase "SUP".
      inv H. destruct H2; omega'. omega'.
  Qed.

(* toutes les addresses multiple de 32 sont dans valid_addresses



 *)



End ValProof.