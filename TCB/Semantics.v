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

Set Implicit Arguments.

(* a memory is a map from addresses to maybe byte *)
Definition memory := N -> option byte.

(* we fix the size of the header *)
Definition header_size := 65536.

(* classification of instructions *)
Inductive instruction_classification (register:Type) : Type :=
  (* an instruction that only modifies register and memory, but does not jump *)
| OK_instr: instruction_classification register
  (* an instruction that masks the value of a register *)
| Mask_instr: register -> word -> instruction_classification register
  (* a (optional) direct jump to a static address *)
| Direct_jump: word -> instruction_classification register
  (* an (optional) indirect jump to the address in a given register *)
| Indirect_jump: register -> instruction_classification register
  (* a dangerous instruction *)
| Invalid_instruction: instruction_classification register.

Implicit Arguments OK_instr [[register]].
Implicit Arguments Direct_jump [[register]].
Implicit Arguments Indirect_jump [[register]].
Implicit Arguments Invalid_instruction [[register]].


(* the state of the machine *)

Record state (register:Type) :=
  { state_mem: memory;
    state_regs: register -> word; (* the registers are a map from register to words *)
    state_pc: N}.
Implicit Arguments state_mem [[register]].
Implicit Arguments state_regs [[register]].
Implicit Arguments state_pc [[register]].

(* the target state of a semantic transformation *)
Inductive instruction_target_state register :=
| Good_state: state register -> instruction_target_state register
| Bad_state: instruction_target_state register.

Implicit Arguments Good_state [[register]].
Implicit Arguments Bad_state [[register]].

Inductive is_good_state {register}: instruction_target_state register -> Prop :=
| Is_Good_State: forall state, is_good_state (Good_state state).


(* what we expect from an assembly language *)
Module Type INSTRUCTION.

  (* a type of registers *)
  Parameter register: Type.
  Parameter register_eq_dec: forall r1 r2: register, {r1 = r2}+{r1 <> r2}.


  (* a type of instructions *)
  Parameter instruction: Type.

  (* a way to parse an instruction *)
  Parameter parse_instruction: lazy_list byte -> option (instruction * nat).

  Parameter instr_max_size: nat.

  Parameter parse_instruction_do_read:
    forall ll instr n, parse_instruction ll = Some (instr, n) ->
    (ll_length ll >= n)%nat.

  Parameter parse_instruction_only_read:
    forall ll instr n, parse_instruction ll = Some (instr, n) ->
    forall ll',
      ll_safe_take n ll' = ll_safe_take n ll ->
      parse_instruction ll' = Some (instr, n).

  Parameter size_instr_not_0: forall ll instr n,
    parse_instruction ll = Some (instr, n) -> n <> O.

  Parameter size_instr_inf_max_size: forall ll instr n,
    parse_instruction ll = Some (instr, n) -> (n <= instr_max_size)%nat.


  (* a way to classify instructions *)
  Parameter classify_instruction: instruction -> instruction_classification register.



  (* a semantic for instructions *)
  Parameter instruction_semantics: forall code_size:N, instruction ->
    state register -> instruction_target_state register -> Prop.


  (* an instruction cannot write in the lower code segment (this
     simulates the protections by segment on the x86 processor *)
  Parameter sem_no_overwrite: forall code_size instr st1 st2,
    instruction_semantics code_size instr st1 (Good_state st2) ->
    forall n', n' < header_size + code_size -> st1.(state_mem) n' = st2.(state_mem) n'.


  (* the "good" instructions can get stuck but never lead to a "bad state" *)

  Parameter sem_not_invalid_not_bad: forall instr,
    classify_instruction instr <> Invalid_instruction ->
    forall code_size st,
      ~ instruction_semantics code_size instr st Bad_state.


  (* an OK instruction increases the pc by size_instr *)
  Parameter sem_OK_instr_pc: forall bm instr size,
    parse_instruction bm = Some (instr, size) ->
    classify_instruction instr = OK_instr ->
    forall code_size st1 st2,
    instruction_semantics code_size instr st1 (Good_state st2) ->
    st2.(state_pc) = st1.(state_pc) + (N_of_nat size).

  (* a Mask instruction increases the pc by size_instr *)
  Parameter sem_Mask_instr_pc: forall bm instr size,
    parse_instruction bm = Some (instr, size) ->
    forall reg w,
    classify_instruction instr = Mask_instr reg w->
    forall code_size st1 st2,
    instruction_semantics code_size instr st1 (Good_state st2) ->
    st2.(state_pc) = st1.(state_pc) + (N_of_nat size).

  (* a Mask instruction mask the register *)
  Parameter sem_Mask_instr_reg: forall bm instr size,
    parse_instruction bm = Some (instr, size) ->
    forall reg w,
    classify_instruction instr = Mask_instr reg w->
    forall code_size st1 st2,
    instruction_semantics code_size instr st1 (Good_state st2) ->
    st2.(state_regs) reg = word_and w (st1.(state_regs) reg).


  (* a Direct jump instruction increases the pc by size_instr of jump
     to the address (this works for both conditional and unconditional
     jumps )*)

  Parameter sem_Direct_jump_pc: forall bm instr size,
    parse_instruction bm = Some (instr, size) ->
    forall w,
    classify_instruction instr = Direct_jump w ->
    forall code_size st1 st2,
    instruction_semantics code_size instr st1 (Good_state st2) ->
    st2.(state_pc) = st1.(state_pc) + (N_of_nat size) \/
    st2.(state_pc) = N_of_word w.


  (* an indirect jump can jump to the address in the register *)
  Parameter sem_Indirect_jump_pc: forall bm instr size,
    parse_instruction bm = Some (instr, size) ->
    forall reg,
    classify_instruction instr = Indirect_jump reg ->
    forall code_size st1 st2,
    instruction_semantics code_size instr st1 (Good_state st2) ->
    st2.(state_pc) = st1.(state_pc) + (N_of_nat size) \/
    st2.(state_pc) = N_of_word (st1.(state_regs) reg).



End INSTRUCTION.






