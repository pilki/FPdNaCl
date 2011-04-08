Require Import Lib.
Require Import BinaryProps.
Require Import List.
Require Import Program.
Require Import LazyList.
Require Import Semantics.
Require Import Memory.
Require Export DoOption.


(* a toy assembly language *)

Module Instruction : INSTRUCTION.

  Inductive register: Type :=
  | REG1
  | REG2
  | REG3
  | REG4
  | REG5
  | REG6
  | REG7
  | REG8.


  Definition register_eq_dec  (r1 r2: register): {r1 = r2}+{r1 <> r2}.
  Proof.
    decide equality.
  Qed.


  Inductive instruction : Type :=
  | Instr_noop: instruction
  | Instr_and: register -> word -> register -> instruction
  | Instr_direct_jump: word -> instruction
  | Instr_direct_cond_jump: register -> word -> instruction
  | Instr_indirect_jump: register -> instruction
  | Instr_os_call: word -> instruction.


  Open Scope nat_scope.

  Definition reg_from_byte (b:byte) : option register :=
    match fst b with
      | HB0 =>
        match snd b with
          | HB1 => Some (REG1)
          | HB2 => Some (REG2)
          | HB3 => Some (REG3)
          | HB4 => Some (REG4)
          | HB5 => Some (REG5)
          | HB6 => Some (REG6)
          | HB7 => Some (REG7)
          | HB8 => Some (REG8)
          | _ => None
        end
      | _ => None
    end.



  Function parse_instruction (ll: lazy_list byte) : option (instruction * nat):=
    match ll with
      | 〈〉 => None
        (* No op *)
      | (HB0, HB0) ::: _ => Some (Instr_noop, 1)
      | (HB0, HB1) ::: reg_code1 ::: b1 ::: b2 ::: b3 ::: b4 ::: reg_code2 ::: _ =>
        do reg1 <- reg_from_byte reg_code1;
        do reg2 <- reg_from_byte reg_code2;
          (* we assume a little endian processor *)
        Some (Instr_and reg1 (W b4 b3 b2 b1) reg2, 7)
      | (HB0, HB2) ::: b1 ::: b2 ::: b3 ::: b4 ::: _ =>
        Some (Instr_direct_jump (W b4 b3 b2 b1), 5)
      | (HB0, HB3) ::: reg_code1 ::: b1 ::: b2 ::: b3 ::: b4 ::: _ =>
        do reg1 <- reg_from_byte reg_code1;
          (* we assume a little endian processor *)
        Some (Instr_direct_cond_jump reg1 (W b4 b3 b2 b1), 6)
      | (HB0, HB4) ::: reg_code1 :::  _ =>
        do reg1 <- reg_from_byte reg_code1;
          (* we assume a little endian processor *)
        Some (Instr_indirect_jump reg1, 2)
      | (HB0, HB5) ::: _ =>
        Some (Instr_os_call (W byte0 byte0 byte0 byte0), 1)
      | _ => None
    end.

  Definition instr_max_size: nat := 7.

  Ltac fun_ind_parse_instr_with call :=
    functional induction call;
      [ fst_Case_tac "fun_ind_parse_instr 1"
      |  fst_Case_tac "fun_ind_parse_instr 2"
      |  fst_Case_tac "fun_ind_parse_instr 3"
      |  fst_Case_tac "fun_ind_parse_instr 4"
      |  fst_Case_tac "fun_ind_parse_instr 5"
      |  fst_Case_tac "fun_ind_parse_instr 6"
      |  fst_Case_tac "fun_ind_parse_instr 7"
      |  fst_Case_tac "fun_ind_parse_instr 8"
      |  fst_Case_tac "fun_ind_parse_instr 9"
      |  fst_Case_tac "fun_ind_parse_instr 10"
      |  fst_Case_tac "fun_ind_parse_instr 11"
      |  fst_Case_tac "fun_ind_parse_instr 12"].


  Ltac fun_ind_parse_instr :=
    match goal with
      | H: context[ parse_instruction ?ll] |- _ =>
        fun_ind_parse_instr_with (parse_instruction ll)
      | |- context[ parse_instruction ?ll] =>
        fun_ind_parse_instr_with (parse_instruction ll)
    end.


  Lemma parse_instruction_do_read:
    forall ll instr n, parse_instruction ll = Some (instr, n) ->
    (ll_length ll >= n)%nat.
  Proof.
    intros.
    fun_ind_parse_instr; simpl; clean; try omega.
  Qed.


  Lemma parse_instruction_only_read:
    forall ll instr n, parse_instruction ll = Some (instr, n) ->
    forall ll',
      ll_safe_take n ll' = ll_safe_take n ll ->
      parse_instruction ll' = Some (instr, n).
  Proof.
    intros.
    fun_ind_parse_instr; simpl in *; clean.
    Case "fun_ind_parse_instr 2".
    

  Lemma size_instr_not_0: forall ll instr n,
    parse_instruction ll = Some (instr, n) -> n <> O.

  Lemma size_instr_inf_max_size: forall ll instr n,
    parse_instruction ll = Some (instr, n) -> (n < instr_max_size)%nat.


  Lemma classify_instruction: instruction -> instruction_classification register.


  Lemma instruction_semantics: forall code_size:N, instruction ->
    state register -> instruction_target_state register -> Prop.


  (* the first parameter is to indicate that the n first bytes of the memory
     cannot be written *)


  (* an instruction cannot write in the lower code segment *)
  Lemma sem_no_overwrite: forall code_size instr st1 st2,
    instruction_semantics code_size instr st1 (Good_state st2) ->
    forall n', n' < header_size + code_size -> st1.(state_mem) n' = st2.(state_mem) n'.

  (* the "good" instructions can get stuck but neverr lead to a "bad state" *)

  Lemma sem_not_invalid_not_bad: forall instr,
    classify_instruction instr <> Invalid_instruction ->
    forall code_size st,
      ~ instruction_semantics code_size instr st Bad_state.


  Lemma sem_OK_instr_pc: forall bm instr size,
    parse_instruction bm = Some (instr, size) ->
    classify_instruction instr = OK_instr ->
    forall code_size st1 st2,
    instruction_semantics code_size instr st1 (Good_state st2) ->
    st2.(state_pc) = st1.(state_pc) + (N_of_nat size).

  Lemma sem_Mask_instr_pc: forall bm instr size,
    parse_instruction bm = Some (instr, size) ->
    forall reg w,
    classify_instruction instr = Mask_instr reg w->
    forall code_size st1 st2,
    instruction_semantics code_size instr st1 (Good_state st2) ->
    st2.(state_pc) = st1.(state_pc) + (N_of_nat size).

  Lemma sem_Mask_instr_reg: forall bm instr size,
    parse_instruction bm = Some (instr, size) ->
    forall reg w,
    classify_instruction instr = Mask_instr reg w->
    forall code_size st1 st2,
    instruction_semantics code_size instr st1 (Good_state st2) ->
    st2.(state_regs) reg = word_and w (st1.(state_regs) reg).


  Lemma sem_Direct_jump_pc: forall bm instr size,
    parse_instruction bm = Some (instr, size) ->
    forall w,
    classify_instruction instr = Direct_jump w ->
    forall code_size st1 st2,
    instruction_semantics code_size instr st1 (Good_state st2) ->
    st2.(state_pc) = st1.(state_pc) + (N_of_nat size) \/
    st2.(state_pc) = N_of_word w.

  Lemma sem_Indirect_jump_pc: forall bm instr size,
    parse_instruction bm = Some (instr, size) ->
    forall reg,
    classify_instruction instr = Indirect_jump reg ->
    forall code_size st1 st2,
    instruction_semantics code_size instr st1 (Good_state st2) ->
    st2.(state_pc) = st1.(state_pc) + (N_of_nat size) \/
    st2.(state_pc) = N_of_word (st1.(state_regs) reg).


