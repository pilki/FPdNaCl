Require Import Lib.
Require Import BinaryProps.
Require Import List.
Require Import LazyList.
Require Import Semantics.
Require Import NSet.
Require Import BinaryProps.
Require Import Recdef.
Require Export DoOption.



Module ValidatorCode (Import I: INSTRUCTION).

  Definition proper_mask := W (HBF, HBF) (HBF, HBF) (HBF, HBF) (HBE, HB0).

  Definition id (n: nat) := n.

  Function validate_n_byte (n: nat) (oreg: option register) (addr: N)
    (valid_addresses to_be_checked_addresses: NSet) (ll: lazy_list byte)
    {measure id n}: option (NSet * NSet * lazy_list byte):=
    match n with
      | O => Some (valid_addresses, to_be_checked_addresses, ll)
      | _ =>
        do (instr, size_instr) <- parse_instruction (byte_map_from_ll ll);
        do ll' <- ll_safe_drop size_instr ll;
        do n' <- safe_minus n size_instr;
        let addr' := addr + (N_of_nat size_instr) in
        match classify_instruction instr with
          | OK_instr =>
            validate_n_byte n' None addr'
              (Nadd addr valid_addresses) to_be_checked_addresses ll'
          | Mask_instr reg w =>
            match word_eq_dec w proper_mask with
              | left _ =>
                validate_n_byte n' (Some reg)
                addr' (Nadd addr valid_addresses) to_be_checked_addresses ll'
              | right _ =>
                validate_n_byte n' None
                addr' (Nadd addr valid_addresses) to_be_checked_addresses ll'
            end
          | Direct_jump w =>
            let dest_addr := N_of_word w in
            if dividable_by_32_dec dest_addr then
              validate_n_byte n' None
                addr' (Nadd addr valid_addresses) to_be_checked_addresses ll'
            else if is_Nin dest_addr valid_addresses then
              validate_n_byte n' None
                addr' (Nadd addr valid_addresses) to_be_checked_addresses ll'
            else
              validate_n_byte n' None addr' (Nadd addr valid_addresses)
                (Nadd dest_addr to_be_checked_addresses) ll'
          | Indirect_jump reg2 =>
            do reg1 <- oreg;
            match register_eq_dec reg1 reg2 with
              | left _ =>
                validate_n_byte n' None
                addr' valid_addresses to_be_checked_addresses ll'
              | right _ => None
            end
          | Invalid_instruction => None
        end
    end.
  Proof.

    Ltac solve_case teq0 teq3 := solve [
      intros;
      pose proof (size_instr_not_0 teq0);
      apply safe_minus_correct in teq3; subst;
      unfold id; omega].

    solve_case teq0 teq3.
    solve_case teq0 teq3.
    solve_case teq0 teq3.
    solve_case teq0 teq3.
    solve_case teq0 teq3.
    solve_case teq0 teq3.
    solve_case teq0 teq3.
  Qed.
 
  Ltac fun_ind_validate_n_byte_with call :=
    functional induction call;
      [ fst_Case_tac "fun_ind_validate_n_byte 1"
      | fst_Case_tac "fun_ind_validate_n_byte 2"
      | fst_Case_tac "fun_ind_validate_n_byte 3"
      | fst_Case_tac "fun_ind_validate_n_byte 4"
      | fst_Case_tac "fun_ind_validate_n_byte 5"
      | fst_Case_tac "fun_ind_validate_n_byte 6"
      | fst_Case_tac "fun_ind_validate_n_byte 7"
      | fst_Case_tac "fun_ind_validate_n_byte 8"
      | fst_Case_tac "fun_ind_validate_n_byte 9"
      | fst_Case_tac "fun_ind_validate_n_byte 10"
      | fst_Case_tac "fun_ind_validate_n_byte 11"
      | fst_Case_tac "fun_ind_validate_n_byte 12"
      | fst_Case_tac "fun_ind_validate_n_byte 13"
      | fst_Case_tac "fun_ind_validate_n_byte 14"].

  Ltac fun_ind_validate_n_byte :=
    match goal with
      | |- context[ validate_n_byte ?n ?or ?a ?va ?tbca ?ll] =>
        fun_ind_validate_n_byte_with
          (validate_n_byte n or a va tbca ll)
    end.

  Lemma validate_n_byte_reduces_size_by_n:
    forall n oreg addr valid_addresses to_be_checked_addresses ll
      valid_addresses' to_be_checked_addresses' ll',
      validate_n_byte n oreg addr valid_addresses to_be_checked_addresses ll =
      Some (valid_addresses', to_be_checked_addresses', ll') ->
      ll_length ll = (n + ll_length ll')%nat.
  Proof.
    intros ? ? ? ? ? ?.
    fun_ind_validate_n_byte;
      intros; clean; specialize (IHo _ _ _ H);
        apply ll_safe_drop_size in  e2;
          apply safe_minus_correct in e3; omega.
  Qed.


  Function validate_ll_list (addr: N)
    (valid_addresses to_be_checked_addresses: NSet) (ll: lazy_list byte)
    {measure ll_length ll}: option (NSet * NSet):=
    do (valid_addresses', to_be_checked_addresses', ll') <-
      validate_n_byte 32 None addr valid_addresses to_be_checked_addresses ll;
    match ll' with
      | 〈〉 => Some (valid_addresses', to_be_checked_addresses')
      | _ =>
        validate_ll_list (addr + 32) valid_addresses' to_be_checked_addresses' ll'
    end.
  Proof.
    intros.
    subst.
    apply validate_n_byte_reduces_size_by_n in teq.
    simpl in *. destruct l. omega.
  Qed.

  Definition header_size := 65536.

  Definition validate_program ll :=
    match validate_ll_list header_size Nempty Nempty ll with
      | None => false
      | Some (valid_addresses, to_be_checked_addresses) =>
        is_Nincluded to_be_checked_addresses valid_addresses
    end.
End ValidatorCode.
  
