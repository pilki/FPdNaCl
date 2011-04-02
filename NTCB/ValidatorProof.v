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





End ValProof.