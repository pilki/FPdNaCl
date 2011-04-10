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
Require Import NSet.
Require Import BinaryProps.
Require Import Recdef.
Require Export DoOption.
Require Import SemanticsProg.


Module ValidatorCode (Import I: INSTRUCTION).

  Definition proper_mask := W (HBF, HBF) (HBF, HBF) (HBF, HBF) (HBE, HB0).

  Definition id (n: nat) := n.

  Function validate_n_byte (n: nat) (addr: N)
    (valid_addresses to_be_checked_addresses: NSet) (ll: lazy_list byte)
    {measure id n}: option (NSet * NSet * lazy_list byte):=
    match n with
      | O => Some (valid_addresses, to_be_checked_addresses, ll)
      | _ =>
        do (instr, size_instr) <- parse_instruction ll;
        do ll' <- ll_safe_drop size_instr ll;
        do n' <- safe_minus n size_instr;
        let addr' := addr + (N_of_nat size_instr) in
        match classify_instruction instr with
          | OK_instr =>
            validate_n_byte n' addr'
              (Nadd addr valid_addresses) to_be_checked_addresses ll'
          | Mask_instr reg1 w =>
            match word_eq_dec w proper_mask with
              | left _ =>
                (* if we are masking with the right mask, we check the next instruction*)
                match n' with
                  | O => Some (Nadd addr valid_addresses, to_be_checked_addresses, ll')
                  | _ =>
                    do (instr', size_instr') <- parse_instruction ll';
                    match classify_instruction instr' with
                      | Indirect_jump reg2 => (* an indirect jump *)
                        match register_eq_dec reg1 reg2 with
                          | left _ => (* the proper register *)
                            do ll'' <- ll_safe_drop size_instr' ll';
                            do n'' <- safe_minus n' size_instr';
                            let addr'' := addr' + (N_of_nat size_instr') in
                            validate_n_byte n'' addr''
                              (Nadd addr valid_addresses) to_be_checked_addresses ll''
                          | right _ => None
                        end
                      | _ =>
                        validate_n_byte n' addr'
                          (Nadd addr valid_addresses) to_be_checked_addresses ll'
                    end
                end
              | right _ =>
                validate_n_byte n'
                  addr' (Nadd addr valid_addresses) to_be_checked_addresses ll'
            end
          | Direct_jump w =>
            let dest_addr := N_of_word w in
            if dividable_by_32_dec dest_addr then
              validate_n_byte n' addr'
                (Nadd addr valid_addresses) to_be_checked_addresses ll'
            else if is_Nin dest_addr valid_addresses then
              validate_n_byte n' addr'
                (Nadd addr valid_addresses) to_be_checked_addresses ll'
            else
              validate_n_byte n' addr' (Nadd addr valid_addresses)
                (Nadd dest_addr to_be_checked_addresses) ll'
          | Invalid_instruction
          | Indirect_jump _ => None
        end
    end.
  Proof.
    Ltac solve_case :=
    intros;
    repeat
      match goal with
        | H : parse_instruction _ = Some _ |- _ =>
          apply size_instr_not_0 in H
      end;
    repeat
      match goal with
        | H: safe_minus _ _ = _ |- _ =>
          apply safe_minus_correct in H
      end; subst; unfold id; omega.
    solve_case.
    solve_case.
    solve_case.
    solve_case.
    solve_case.
    solve_case.
    solve_case.
    solve_case.
    solve_case.
    solve_case.
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
      | fst_Case_tac "fun_ind_validate_n_byte 14"
      | fst_Case_tac "fun_ind_validate_n_byte 15"
      | fst_Case_tac "fun_ind_validate_n_byte 16"
      | fst_Case_tac "fun_ind_validate_n_byte 17"
      | fst_Case_tac "fun_ind_validate_n_byte 18"].

  Ltac fun_ind_validate_n_byte :=
    match goal with
      | |- context[ validate_n_byte ?n ?a ?va ?tbca ?ll] =>
        fun_ind_validate_n_byte_with
          (validate_n_byte n a va tbca ll)
    end.

  Lemma validate_n_byte_reduces_size_by_n:
    forall n addr valid_addresses to_be_checked_addresses ll
      valid_addresses' to_be_checked_addresses' ll',
      validate_n_byte n addr valid_addresses to_be_checked_addresses ll =
      Some (valid_addresses', to_be_checked_addresses', ll') ->
      ll_length ll = (n + ll_length ll')%nat.
  Proof.
    intros ? ? ? ? ? ?.
    fun_ind_validate_n_byte;
      intros; clean;
        try (specialize (IHo _ _ H));
        apply ll_safe_drop_size in  e2;
          apply safe_minus_correct in e3; try omega.
    apply ll_safe_drop_size in e11. apply safe_minus_correct in e12.
    subst. omega.
  Qed.


  Function validate_ll_list (addr: N)
    (valid_addresses to_be_checked_addresses: NSet) (ll: lazy_list byte)
    {measure ll_length ll}: option (NSet * NSet):=
    do (valid_addresses', to_be_checked_addresses', ll') <-
      validate_n_byte 32 addr valid_addresses to_be_checked_addresses ll;
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

  Definition validate_program ll :=
    match validate_ll_list header_size Nempty Nempty ll with
      | None => false
      | Some (valid_addresses, to_be_checked_addresses) =>
        is_Nincluded to_be_checked_addresses valid_addresses
    end.
End ValidatorCode.

