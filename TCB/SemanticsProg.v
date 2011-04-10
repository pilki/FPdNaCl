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
Require Import Memory.

Definition dividable_by_32 (n:N) :=
  exists d:N, n = 32 * d.

Program Definition dividable_by_32_dec n
  : {dividable_by_32 n} + {~dividable_by_32 n}:=
  match n with
    | N0 => left _
    | Npos p~0~0~0~0~0 => left _
    | Npos _ => right _
  end.
Next Obligation.
  unfold dividable_by_32. exists 0. reflexivity.
Qed.
Next Obligation.
  unfold dividable_by_32. simpl. exists (Npos p). reflexivity.
Qed.
Next Obligation.
  destruct wildcard' as [wildcard'|wildcard'|]; try solve
    [let H0 := fresh "H" in intros [[|?] H0]; simpl in H0; inv H0].
  destruct wildcard' as [wildcard'|wildcard'|]; try solve
    [let H0 := fresh "H" in intros [[|?] H0]; simpl in H0; inv H0].
  destruct wildcard' as [wildcard'|wildcard'|]; try solve
    [let H0 := fresh "H" in intros [[|?] H0]; simpl in H0; inv H0].
  destruct wildcard' as [wildcard'|wildcard'|]; try solve
    [let H0 := fresh "H" in intros [[|?] H0]; simpl in H0; inv H0].
  destruct wildcard' as [wildcard'|wildcard'|]; try solve
    [let H0 := fresh "H" in intros [[|?] H0]; simpl in H0; inv H0].
  intro. apply (H wildcard'). reflexivity.
Qed.



(* Define the semantics of programs, parameterized by those of instruction *)
Module Prog_Semantics (Import I: INSTRUCTION).

  Module M := Mem(I).
  Export M.

  Inductive target_state :=
    (* a regular state *)
  | Normal_state: state register -> target_state
    (* a state that should *never* be reached ! *)
  | DANGER_STATE: target_state.


  Inductive step (code_size: N) (st1: state register): target_state -> Prop :=
  | Step_good: forall instr n st2,
    in_code code_size st1 ->
    read_instr_from_memory st1.(state_mem) st1.(state_pc) = Some (instr, n) ->
    instruction_semantics (header_size + code_size) instr st1 (Good_state st2) ->
    (* we allow any modification of the memory outside of the code
       segment because of multi threading *)
    forall m2', same_code code_size m2' st2.(state_mem) ->
    step code_size st1
      (Normal_state {| state_mem := m2';
                       state_pc := st2.(state_pc);
                       state_regs :=st2.(state_regs) |})
    (* if no instruction can be read, something wrong is hapening *)
  | Step_cannot_read_instr:
    in_code code_size st1 ->
    read_instr_from_memory st1.(state_mem) st1.(state_pc) = None ->
    step code_size st1 DANGER_STATE
    (* if we can read an instruction, and its execution goes wrong, it is wrong *)
  | Step_bad: forall instr n,
    in_code code_size st1 ->
    read_instr_from_memory st1.(state_mem) st1.(state_pc) = Some (instr, n) ->
    instruction_semantics code_size instr st1 Bad_state ->
    step code_size st1 DANGER_STATE

    (* if we are in the header, it must be at a correct address *)
  | Step_header_bad:
    st1.(state_pc) < header_size -> ~dividable_by_32 st1.(state_pc) ->
    step code_size st1 DANGER_STATE

    (* if the address in the header is correct, we can jump anywhere in the code *)
  | Step_header_good:
    st1.(state_pc) < header_size -> dividable_by_32 st1.(state_pc) ->
    forall m2 regs2 pc2,
      same_code code_size st1.(state_mem) m2 ->
      dividable_by_32 pc2 ->
      step code_size st1
        (Normal_state {| state_mem := m2;
                         state_pc := pc2;
                         state_regs := regs2 |}).


  Inductive accessible_state (code_size: N)
    (st1: state register): state register -> Prop :=
  | AS0: accessible_state code_size st1 st1
  | ASS: forall st2 st3,
    step code_size st1 (Normal_state st2) ->
    accessible_state code_size st2 st3 ->
    accessible_state code_size st1 st3.

  (* is DANGER_STATE accessible from a state ? *)
  Inductive accessible_danger (code_size: N) (st1: state register) : Prop :=
  | AD_one_step:
    step code_size st1 DANGER_STATE ->
    accessible_danger code_size st1
  | AD_more_steps: forall st2,
    step code_size st1 (Normal_state st2)  ->
    accessible_danger code_size st2 ->
    accessible_danger code_size st1.

End Prog_Semantics.

