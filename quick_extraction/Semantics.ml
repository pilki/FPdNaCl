open BinNat
open BinPos
open BinaryDefs
open Byte
open DoOption
open LazyList

type memory = coq_N -> byte option

(** val header_size : coq_N **)

let header_size =
  Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
    (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
    Coq_xH))))))))))))))))

type 'register instruction_classification =
  | OK_instr
  | Mask_instr of 'register * word
  | Direct_jump of word
  | Indirect_jump of 'register
  | Invalid_instruction

(** val instruction_classification_rect :
    'a2 -> ('a1 -> word -> 'a2) -> (word -> 'a2) -> ('a1 -> 'a2) -> 'a2 ->
    'a1 instruction_classification -> 'a2 **)

let instruction_classification_rect f f0 f1 f2 f3 = function
  | OK_instr -> f
  | Mask_instr (x, x0) -> f0 x x0
  | Direct_jump x -> f1 x
  | Indirect_jump x -> f2 x
  | Invalid_instruction -> f3

(** val instruction_classification_rec :
    'a2 -> ('a1 -> word -> 'a2) -> (word -> 'a2) -> ('a1 -> 'a2) -> 'a2 ->
    'a1 instruction_classification -> 'a2 **)

let instruction_classification_rec f f0 f1 f2 f3 = function
  | OK_instr -> f
  | Mask_instr (x, x0) -> f0 x x0
  | Direct_jump x -> f1 x
  | Indirect_jump x -> f2 x
  | Invalid_instruction -> f3

type 'register state = { state_mem : memory;
                         state_regs : ('register -> word); state_pc : 
                         coq_N }

(** val state_rect :
    (memory -> ('a1 -> word) -> coq_N -> 'a2) -> 'a1 state -> 'a2 **)

let state_rect f s =
  let { state_mem = x; state_regs = x0; state_pc = x1 } = s in f x x0 x1

(** val state_rec :
    (memory -> ('a1 -> word) -> coq_N -> 'a2) -> 'a1 state -> 'a2 **)

let state_rec f s =
  let { state_mem = x; state_regs = x0; state_pc = x1 } = s in f x x0 x1

(** val state_mem : 'a1 state -> memory **)

let state_mem x = x.state_mem

(** val state_regs : 'a1 state -> 'a1 -> word **)

let state_regs x = x.state_regs

(** val state_pc : 'a1 state -> coq_N **)

let state_pc x = x.state_pc

type 'register instruction_target_state =
  | Good_state of 'register state
  | Bad_state

(** val instruction_target_state_rect :
    ('a1 state -> 'a2) -> 'a2 -> 'a1 instruction_target_state -> 'a2 **)

let instruction_target_state_rect f f0 = function
  | Good_state x -> f x
  | Bad_state -> f0

(** val instruction_target_state_rec :
    ('a1 state -> 'a2) -> 'a2 -> 'a1 instruction_target_state -> 'a2 **)

let instruction_target_state_rec f f0 = function
  | Good_state x -> f x
  | Bad_state -> f0

module type INSTRUCTION = 
 sig 
  type register 
  
  val register_eq_dec : register -> register -> bool
  
  type instruction 
  
  val parse_instruction :
    coq_N -> byte lazy_list -> ((instruction * coq_N) * byte lazy_list) res
  
  val instr_max_size : coq_N
  
  val classify_instruction :
    instruction -> register instruction_classification
 end

