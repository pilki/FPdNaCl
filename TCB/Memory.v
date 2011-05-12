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
Require Import Program.
Require Import LazyList.
Require Import Semantics.
Require Import DoOption.


(* specifies that the content of the memory, starting at address addr,
   is the content of the list. It basically means that we are executing the code *)

Definition memory_compat_addr_ll addr ll (mem: memory):=
  forall n, (n < ll_length ll)%nat -> ll_nth n ll = mem (addr + N_of_nat n).



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

Lemma memory_compat_addr_ll_cons: forall addr b ll mem,
  memory_compat_addr_ll addr (b:::ll) mem ->
  memory_compat_addr_ll (addr + 1) ll mem.
Proof.
  unfold memory_compat_addr_ll. intros.
  simpl in H.
  specialize (H (S n)). simpl in H.
  rewrite H. f_equal. omega'. omega.
Qed.



Lemma csi_1: forall n1 n2,
  N_of_nat n1 >= N_of_nat n2 -> (n1 >= n2)%nat.
Proof. intros; omega'. Qed.

Lemma csi_2: forall n1 n2,
  N_of_nat n1 <= N_of_nat n2 -> (n1 <= n2)%nat.
Proof. intros; omega'. Qed.


Ltac change_size_instr size_instr :=
  let size_instr' := fresh size_instr "'" in
  rename size_instr into size_instr';
  remember (nat_of_N size_instr') as size_instr;
  replace size_instr' with (N_of_nat size_instr) in * by omega';
  match goal with
    | Heqsize_instr: size_instr = nat_of_N (N_of_nat size_instr) |- _ =>
      clear Heqsize_instr
  end;
  repeat match goal with
           | H : _ |- _ => apply csi_1 in H
         end;
  repeat match goal with
           | H : _ |- _ => apply csi_2 in H
         end;
  clear size_instr'.

Ltac inv_opt' :=
    match goal with
      | H : match ?X with
              | Some _ => _
              | None => _
            end = Some _ |- _ =>
    case_eq X; intros;
      match goal with
        | HEQ : X = _ |- _ =>
          rewrite HEQ in H; simpl in *; inv H; auto
      end
  end.



Hint Resolve memory_compat_addr_ll_drop memory_compat_addr_ll_cons.

Module Mem(Import I : INSTRUCTION).
Ltac destr_parse_instr_only_read :=
    match goal with
      | |- context[parse_instruction ?addr ?ll2] =>
        edestruct parse_instruction_only_read with (pc:= addr) (ll' := ll2) as [? REW]; eauto;[|rewrite REW; auto]
    end.


  (* to read an instruction in memory, we build a list of maximal size
     instr_size_max, and we parse it *)


  Fixpoint build_list_from_memory (n:nat) (addr:N) (mem:memory) : lazy_list byte :=
    match n with
      | O => 〈〉
      | S n' =>
        match mem addr with
          | None => 〈〉
          | Some b => b ::: build_list_from_memory n' (addr + 1) mem
        end
    end.

  Definition read_instr_from_memory (mem: memory) (pc: N): res (instruction * N) :=
    do (instr, size, _) <- parse_instruction pc (build_list_from_memory (nat_of_N instr_max_size) pc mem);
    OK (instr, size).


  (* reading from memory is the same as parsing instruction when the
  memory is compatible with the list *)
  Theorem memory_compat_read_instr addr ll mem:
    memory_compat_addr_ll addr ll mem ->
    forall instr size_instr rst_ll,
      parse_instruction addr ll = OK (instr, size_instr, rst_ll) ->
      read_instr_from_memory mem addr = OK (instr, size_instr).
  Proof.
    intros COMPAT * PARSE.
    unfold read_instr_from_memory.
    remember instr_max_size as ims.
    assert (size_instr <= ims).
      subst. eapply size_instr_inf_max_size; eauto.
    clear Heqims.

    destr_parse_instr_only_read.

    apply parse_instruction_do_read in PARSE.

    change_size_instr size_instr.
    change_size_instr ims.

    assert (is_ok (ll_safe_take size_instr ll)).
    clear - PARSE. revert size_instr PARSE.
    induction' ll as [| b ll']; simpl; intros.
    Case "@ll_nil".
      replace size_instr with O in * by omega'. simpl. constructor.
    Case "ll_cons b ll'".
      destruct size_instr.
      simpl. constructor.
      assert (ll_length ll' >= size_instr)%nat by omega'.
      specialize (IHll' _ H). inv IHll'.
      simpl. rewrite <- H1. constructor.

    revert dependent ims. revert addr mem COMPAT instr size_instr PARSE H0.
    induction' ll as [| b ll']; simpl; intros.
    Case "@ll_nil".
      replace size_instr with O in * by omega.
      reflexivity.
    Case "ll_cons b ll'".
      destruct' size_instr.
      SCase "O".
        reflexivity.
      SCase "S".
        destruct ims; [elimtype False; omega|].
        assert (size_instr <= ims)%nat by omega.
        assert (ll_length ll' >= size_instr)%nat by omega.
        simpl in *. inv H0; clean. inv_res.
        pose proof COMPAT.
        unfold memory_compat_addr_ll in H3.
        specialize (H3 O). replace (addr + N_of_nat 0) with addr in * by omega'.
        rewrite <- H3;simpl;[|omega].
        rewrite IHll'; eauto.
        rewrite H0. reflexivity.
  Qed.

  Hint Resolve memory_compat_read_instr.



  (* two memories with the same code segment *)
  Definition same_code (code_size: N) (mem1 mem2: memory): Prop:=
    forall n, n < header_size + code_size -> mem1 n = mem2 n.

  Lemma same_code_trans: forall code_segment_size st1 st2 st3,
    same_code code_segment_size st1 st2 -> same_code code_segment_size st2 st3 ->
    same_code code_segment_size st1 st3.
  Proof.
    unfold same_code; intros.
    rewrite H; eauto.
  Qed.

  Lemma memory_compat_same_code ll mem1 mem2:
    memory_compat_addr_ll header_size ll mem1 ->
    same_code (N_of_nat (ll_length ll)) mem1 mem2 ->
    memory_compat_addr_ll header_size ll mem2.
  Proof.
    unfold memory_compat_addr_ll, same_code.
    intros.
    rewrite H; auto.
    apply H0. omega'.
  Qed.

  Hint Resolve memory_compat_same_code same_code_trans.


  Lemma same_code_read_instr (mem1 mem2: memory) next_addr addr:
    (forall addr : N, addr < next_addr -> mem1 addr = mem2 addr) ->
    forall instr size_instr,
      addr + size_instr <= next_addr ->
      read_instr_from_memory mem1 addr = OK (instr, size_instr) ->
      read_instr_from_memory mem2 addr = OK (instr, size_instr).
  Proof.
    unfold read_instr_from_memory. intros SAME * INF READ.

    match goal with
      | H : match ?X with
              | OK _ => _
              | Err _ => Err _
            end = OK _ |- _ =>
      destruct X as [[[]]|] _eqn; clean
    end.
    destr_parse_instr_only_read.



(*    pose proof READ.*)
(*    apply parse_instruction_do_read in READ.*)
    remember instr_max_size as ims. clear Heqims. clear Heqr.
    change_size_instr size_instr. change_size_instr ims.

    revert dependent ims. revert dependent addr. clear instr.
    induction' size_instr as [|size_instr]; intros.
    Case "O".
      simpl. reflexivity.
    Case "S size_instr".
      simpl.
      destruct ims; simpl.
      reflexivity.
      replace (mem2 addr) with (mem1 addr) in * by (apply SAME; omega').
      destruct (mem1 addr); auto.
      erewrite IHsize_instr; eauto. omega'.
  Qed.

  Hint Resolve same_code_read_instr.

  Definition in_code (code_size: N) (st: state register) :=
    header_size <= st.(state_pc) /\ st.(state_pc) < header_size + code_size.

End Mem.
