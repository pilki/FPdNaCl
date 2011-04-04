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
      | |- context[ validate_n_byte ?n ?or ?a ?va ?tbca ?ll] =>
        fun_ind_validate_n_byte_with
          (validate_n_byte n or a va tbca ll)
      | H : context[ validate_n_byte ?n ?or ?a ?va ?tbca ?ll] |- _ =>
        fun_ind_validate_n_byte_with
          (validate_n_byte n or a va tbca ll)
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
    forall (n: nat) (oreg: option register) (addr: N)
    (valid_addresses to_be_checked_addresses: NSet) (ll: lazy_list byte)
    valid_addresses' to_be_checked_addresses' ll',
    validate_n_byte n oreg addr valid_addresses to_be_checked_addresses ll =
    Some (valid_addresses', to_be_checked_addresses', ll') ->
    Nincluded valid_addresses valid_addresses'.
  Proof.
    intros * VALIDATE.
    fun_ind_validate_n_byte; clean; eauto with nset.
  Qed.

  Lemma validate_n_byte_increase_to_be_checked_addresses:
    forall (n: nat) (oreg: option register) (addr: N)
    (valid_addresses to_be_checked_addresses: NSet) (ll: lazy_list byte)
    valid_addresses' to_be_checked_addresses' ll',
    validate_n_byte n oreg addr valid_addresses to_be_checked_addresses ll =
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
    forall (n: nat) (oreg: option register) (addr: N)
    (valid_addresses to_be_checked_addresses: NSet) (ll: lazy_list byte)
    valid_addresses' to_be_checked_addresses' ll',
    validate_n_byte n oreg addr valid_addresses to_be_checked_addresses ll =
    Some (valid_addresses', to_be_checked_addresses', ll') ->
    ll_safe_drop n ll = Some ll'.
  Proof.
    intros * VALIDATE.
    fun_ind_validate_n_byte; clean; eauto with nset;
    apply safe_minus_correct in e3; subst;
    rewrite ll_safe_drop_plus; rewrite e2; eauto.
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
    validate_n_byte (S n) None addr valid_addresses to_be_checked_addresses ll =
    Some (valid_addresses', to_be_checked_addresses', ll') ->
    In_NSet addr valid_addresses'.
  Proof.
    intros * VALIDATE.
    functional inversion VALIDATE; subst;
    subst;
    repeat match goal with
      | x := _ : _ |- _ => subst x
    end;
    apply validate_n_byte_increase_valid_addresses in X;
    eauto with nset.
  Qed.

  Local Hint Resolve validate_n_byte_add_addr.

  Lemma validate_n_byte_size: 
    forall (n: nat) (oreg: option register) (addr: N)
    (valid_addresses to_be_checked_addresses: NSet) (ll: lazy_list byte)
    valid_addresses' to_be_checked_addresses',
    validate_n_byte n oreg addr valid_addresses to_be_checked_addresses ll =
    Some (valid_addresses', to_be_checked_addresses', 〈〉) ->
    ll_length ll = n.
  Proof.
    intros * VALIDATE.
    fun_ind_validate_n_byte; clean;
    specialize (IHo VALIDATE); subst;
    apply ll_safe_drop_size in e2;
    apply safe_minus_correct in e3; omega.
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
      pose proof (validate_n_byte_size _ _ _ _ _ _ _ _ e).
      apply validate_n_byte_add_addr in e.
      replace addr' with addr. assumption.
      rewrite H0 in H2. simpl in H2.
      destruct H. destruct H3. zify. omega.

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


  Definition one_step_correct code_size
    valid_addresses to_be_checked_addresses st1 :=
    (~step header_size code_size st1 DANGER_STATE) /\
    forall st2, step header_size code_size st1 (Normal_state st2) ->
    (  dividable_by_32 st2.(state_pc) 
    \/ In_NSet st2.(state_pc) valid_addresses
    \/ In_NSet st2.(state_pc) to_be_checked_addresses).
    
  Definition two_steps_correct code_size
    valid_addresses to_be_checked_addresses st1 :=
    (~step header_size code_size st1 DANGER_STATE) /\
    forall st2, step header_size code_size st1 (Normal_state st2) ->
    (  dividable_by_32 st2.(state_pc) 
    \/ In_NSet st2.(state_pc) valid_addresses
    \/ In_NSet st2.(state_pc) to_be_checked_addresses
    \/ one_step_correct code_size valid_addresses
         to_be_checked_addresses st2).

  Lemma one_step_correct_trans:
    forall code_size valid_addresses valid_addresses'
      to_be_checked_addresses to_be_checked_addresses' st,
      Nincluded to_be_checked_addresses to_be_checked_addresses' ->
      Nincluded valid_addresses valid_addresses' ->
      one_step_correct code_size valid_addresses
        to_be_checked_addresses st ->
      one_step_correct code_size valid_addresses'
        to_be_checked_addresses' st.
  Proof.
    unfold one_step_correct, Nincluded.
    intuition eauto.
    edestruct H3 as [ | [ |]]; eauto.
  Qed.

  Hint Resolve one_step_correct_trans.

  Lemma two_steps_correct_trans:
    forall code_size valid_addresses valid_addresses'
      to_be_checked_addresses to_be_checked_addresses' st,
      Nincluded to_be_checked_addresses to_be_checked_addresses' ->
      Nincluded valid_addresses valid_addresses' ->
      two_steps_correct code_size valid_addresses
        to_be_checked_addresses st ->
      two_steps_correct code_size valid_addresses'
        to_be_checked_addresses' st.
  Proof.
    unfold two_steps_correct, Nincluded.
    intuition eauto.
    edestruct H3 as [ | [ |[|]]]; eauto.
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

  Lemma validate_n_byte_two_steps: forall code_size (n: nat) (addr: N)
    (valid_addresses to_be_checked_addresses: NSet) (ll: lazy_list byte)
    valid_addresses' to_be_checked_addresses' ll',
    validate_n_byte n None addr valid_addresses to_be_checked_addresses ll =
      Some (valid_addresses', to_be_checked_addresses', ll') ->
    addr + (N_of_nat n) <= header_size + code_size ->
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
    fun_ind_validate_n_byte; intros; clean; eauto;
      eapply IHo0; clear IHo0; clean_safe_minus; eauto; try omega';
        intros; clean; eauto;
      (destruct (Nadd_In_or _ _ _ H8);
        [(subst; clear H7)
        | solve [eapply two_steps_correct_trans; eauto with nset]]).

    Case "fun_ind_validate_n_byte 2".
      unfold two_steps_correct.
      constructor'.
      NSCase "Non danger".
        intro DANGER. 
        inv DANGER.
      assert (read_instr_from_memory st0.(state_mem) st0.(state_pc)
                = Some (instr, size_instr)).
        unfold read_instr_from_memory.
        eapply parse_instruction_only_read; eauto.
        unfold byte_map_from_ll. intros. unfold memory_compat_addr_ll in H0.
        rewrite Nplus_comm. auto.
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
      

  Theorem roxx: forall ll code_size valid_addresses to_be_checked_addresses,
    validate_ll_list header_size Nempty Nempty ll = Some (valid_addresses, to_be_checked_addresses) ->
    Nincluded to_be_checked_addresses valid_addresses ->
    code_size = N_of_nat (ll_length ll) ->
    forall mem, memory_compat_addr_ll header_size ll mem ->
    forall st, same_code (header_size + code_size) mem st.(state_mem) ->
      (In_NSet st.(state_pc) valid_addresses) ->
      ~accessible_danger header_size code_size st.
  Proof.
    intros. intro.
    revert H4 H3.
    induction' H5; intros.
    Case "AD_one_step".
    assert (two_steps_correct code_size valid_addresses to_be_checked_addresses st1).
      eapply validate_ll_list_two_steps; eauto.
      omega'.
      intros. apply Nempty_empty in H8. inv H8.
    inv H6. apply H7. assumption.

   Case "AD_more_steps".
    assert (two_steps_correct code_size valid_addresses to_be_checked_addresses st1).
      eapply validate_ll_list_two_steps; eauto.
      omega'.
      intros. apply Nempty_empty in H9. inv H9.
    inv H7.


(* toutes les addresses multiple de 32 sont dans valid_addresses



 *)



End ValProof.