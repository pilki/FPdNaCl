open BinNat
open BinPos
open Byte
open Datatypes
open DoOption
open LazyList
open Memory
open Semantics

val dividable_by_32_dec : coq_N -> bool

module Prog_Semantics : 
 functor (I:INSTRUCTION) ->
 sig 
  module M : 
   sig 
    val build_list_from_memory : nat -> coq_N -> memory -> byte lazy_list
    
    val read_instr_from_memory :
      memory -> coq_N -> (I.instruction * coq_N) res
   end
  
  type target_state =
    | Normal_state of I.register state
    | DANGER_STATE
  
  val target_state_rect :
    (I.register state -> 'a1) -> 'a1 -> target_state -> 'a1
  
  val target_state_rec :
    (I.register state -> 'a1) -> 'a1 -> target_state -> 'a1
 end

