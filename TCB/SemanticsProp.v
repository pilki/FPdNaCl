Require Import Lib.
Require Import BinaryProps.
Require Import Semantics.

Module Type INSTRUCTION_SEMANTICS_PROP(Import I: INSTRUCTION).
  (* the first parameter is to indicate that the n first bytes of the memory
     cannot be written *)


  (* an instruction cannot write in the lower code segment *)
  Parameter sem_no_overwrite: forall code_segment_size instr st1 st2,
    instruction_semantics code_segment_size instr st1 (Good_state st2) ->
    forall n', n' < code_segment_size -> st1.(state_mem) n' = st2.(state_mem) n'.

  (* the "good" instructions can get stuck but neverr lead to a "bad state" *)

  Parameter sem_not_invalid_not_bad: forall instr,
    classify_instruction instr <> Invalid_instruction ->
    forall code_segment_size st,
      ~ instruction_semantics code_segment_size instr st Bad_state.


  Parameter sem_OK_instr_pc: forall bm instr size,
    parse_instruction bm = Some (instr, size) ->
    classify_instruction instr = OK_instr ->
    forall code_segment_size st1 st2,
    instruction_semantics code_segment_size instr st1 (Good_state st2) ->
    st2.(state_pc) = st1.(state_pc) + (N_of_nat size).

  Parameter sem_Mask_instr_pc: forall bm instr size,
    parse_instruction bm = Some (instr, size) ->
    forall reg w,
    classify_instruction instr = Mask_instr reg w->
    forall code_segment_size st1 st2,
    instruction_semantics code_segment_size instr st1 (Good_state st2) ->
    st2.(state_pc) = st1.(state_pc) + (N_of_nat size).

  Parameter sem_Mask_instr_reg: forall bm instr size,
    parse_instruction bm = Some (instr, size) ->
    forall reg w,
    classify_instruction instr = Mask_instr reg w->
    forall code_segment_size st1 st2,
    instruction_semantics code_segment_size instr st1 (Good_state st2) ->
    st2.(state_regs) reg = word_and w (st1.(state_regs) reg).


  Parameter sem_Direct_jump_pc: forall bm instr size,
    parse_instruction bm = Some (instr, size) ->
    forall w,
    classify_instruction instr = Direct_jump w ->
    forall code_segment_size st1 st2,
    instruction_semantics code_segment_size instr st1 (Good_state st2) ->
    st2.(state_pc) = st1.(state_pc) + (N_of_nat size) \/
    st2.(state_pc) = N_of_word w.

  Parameter sem_Indirect_jump_pc: forall bm instr size,
    parse_instruction bm = Some (instr, size) ->
    forall reg,
    classify_instruction instr = Indirect_jump reg ->
    forall code_segment_size st1 st2,
    instruction_semantics code_segment_size instr st1 (Good_state st2) ->
    st2.(state_pc) = st1.(state_pc) + (N_of_nat size) \/
    st2.(state_pc) = N_of_word (st1.(state_regs) reg).

End INSTRUCTION_SEMANTICS_PROP.
