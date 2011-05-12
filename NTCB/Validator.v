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

  Definition proper_mask := W BFF BFF BFF BE0.

  Definition id (n: nat) := n.

  (* function to validate a 32 bytes block. It takes as an argument
  the current valid_addresses (a set of addresses where we already
  found an instruction), the current to_be_checked_addresses (the set
  of addresses where an instruction might jump) and the list of
  bytes *)

  Function validate_n_byte (n: N) (addr: N)
    (valid_addresses to_be_checked_addresses: NSet) (ll: lazy_list byte)
    {measure nat_of_N n}: res (NSet * NSet * lazy_list byte):=
    match n with
      (* we are done with the validation of this block *)
      | N0 => OK (valid_addresses, to_be_checked_addresses, ll)

      | _ => (* the do notation is defined in DoOption.  *)

        (* we parse the instruction *)
        do (instr, size_instr, ll') <- parse_instruction addr ll;
        (* and the number of byte left to validate *)
        match safe_minus n size_instr with
        | None => Err "Instruction overlaps 32 bytes boundary"
        | Some n' =>

        let addr' := addr + size_instr in
        match classify_instruction instr with

          (* for a normal instruction, we just add the current address
             in the valid addresses *)
          | OK_instr =>
            validate_n_byte n' addr'
              (Nadd addr valid_addresses) to_be_checked_addresses ll'

          (* for a mask instruction: if the mask is not the
             "proper_mask", we treat it as a normal instruction. But
             if it is equal, we look at the next instruction to see if
             it is a indirect jump, to check if we have the pseudo
             instruction of guarded indirect jump*)

          | Mask_instr reg1 w =>
            match word_eq_dec w proper_mask with
              | left _ =>
              (* if we are masking with the right mask,
                 we check the next instruction*)
                match n' with
                  | N0 => OK (Nadd addr valid_addresses, to_be_checked_addresses, ll')
                  | _ =>
                    do (instr', size_instr', ll'') <- parse_instruction addr' ll';
                    match classify_instruction instr' with
                      | Indirect_jump reg2 => (* an indirect jump *)
                        match register_eq_dec reg1 reg2 with
                          | left _ => (* the proper register *)
                            match safe_minus n' size_instr' with
                            | None => Err "Instruction overlaps 32 bytes boundary"
                            | Some n'' =>
                            let addr'' := addr' + size_instr' in
                            validate_n_byte n'' addr''
                              (Nadd addr valid_addresses) to_be_checked_addresses ll''
                            end
                          (* an indirect jump that was not properly masked *)
                          | right _ => Err "The mask used before the jump is incorrect"
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
            (* a direct jump to an address that is dividable by 32 is always ok *)
            if dividable_by_32_dec dest_addr then
              validate_n_byte n' addr'
                (Nadd addr valid_addresses) to_be_checked_addresses ll'
            (* a direct jump to an already valid address is ok *)
            else if is_Nin dest_addr valid_addresses then
              validate_n_byte n' addr'
                (Nadd addr valid_addresses) to_be_checked_addresses ll'
            (* if it is not, we postpone the checking of the validity of this address *)
            else
              validate_n_byte n' addr' (Nadd addr valid_addresses)
                (Nadd dest_addr to_be_checked_addresses) ll'
          | Invalid_instruction => Err "Invalid instruction"
          | Indirect_jump _ => Err "Not masked indirect jump"
        end
        end
    end.
  Proof.
    Ltac solve_case :=
    intros;
    repeat
      match goal with
        | H : parse_instruction _ _ = OK _ |- _ =>
          apply size_instr_not_0 in H
      end;
    repeat
      match goal with
        | H: safe_minus _ _ = _ |- _ =>
          apply safe_minus_correct in H
      end; subst; unfold id; abstract omega'.
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
      | fst_Case_tac "fun_ind_validate_n_byte 16"].

  Ltac fun_ind_validate_n_byte :=
    match goal with
      | |- context[ validate_n_byte ?n ?a ?va ?tbca ?ll] =>
        fun_ind_validate_n_byte_with
          (validate_n_byte n a va tbca ll)
      | H : context[ validate_n_byte ?n ?a ?va ?tbca ?ll] |- _ =>
        fun_ind_validate_n_byte_with
          (validate_n_byte n a va tbca ll)
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
      | H: parse_instruction _ _ = OK _ |- _ =>
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


  Require Import Memory.
  Lemma validate_n_byte_reduces_size_by_n:
    forall n addr valid_addresses to_be_checked_addresses ll
      valid_addresses' to_be_checked_addresses' ll',
      validate_n_byte n addr valid_addresses to_be_checked_addresses ll =
      OK (valid_addresses', to_be_checked_addresses', ll') ->
      ll_length ll = (nat_of_N n + ll_length ll')%nat.
  Proof.
    intros ? ? ? ? ? ?.

    fun_ind_validate_n_byte; intros; clean;
      try (specialize (IHr _ _ H)); clean_post_fun_ind_validate; try omega'.
  Qed.


  Function validate_ll_list (addr: N)
    (valid_addresses to_be_checked_addresses: NSet) (ll: lazy_list byte)
    {measure ll_length ll}: res (NSet * NSet):=
    (* to validate a list, we repeatedly validate 32 byte blocks *)
    do (valid_addresses', to_be_checked_addresses', ll') <-
      validate_n_byte 32 addr valid_addresses to_be_checked_addresses ll;
    match ll' with
      | 〈〉 => OK (valid_addresses', to_be_checked_addresses')
      | _ =>
        validate_ll_list (addr + 32) valid_addresses' to_be_checked_addresses' ll'
    end.
  Proof.
    intros.
    subst.
    apply validate_n_byte_reduces_size_by_n in teq.
    simpl in *. destruct l. omega.
  Qed.

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


  Definition validate_program ll :=
    (* to validate the program, we finally check the addresses left
       (the forward jumps) *)
    do (valid_addresses, to_be_checked_addresses) <-
      validate_ll_list header_size Nempty Nempty ll;
    if is_Nincluded to_be_checked_addresses valid_addresses then
      OK tt
    else
      Err "Direct jump to an invalid address".
End ValidatorCode.

