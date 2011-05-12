open BinNat
open BinPos
open Byte
open Datatypes
open DoOption
open LazyList
open Nnat
open Semantics

module Mem : 
 functor (I:INSTRUCTION) ->
 sig 
  val build_list_from_memory : nat -> coq_N -> memory -> byte lazy_list
  
  val read_instr_from_memory : memory -> coq_N -> (I.instruction * coq_N) res
 end

