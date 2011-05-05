open BinNat
open BinPos
open Byte
open Datatypes
open LazyList
open Nnat
open Semantics

module Mem = 
 functor (I:INSTRUCTION) ->
 struct 
  (** val build_list_from_memory :
      nat -> coq_N -> memory -> byte lazy_list **)
  
  let rec build_list_from_memory n addr mem =
    match n with
      | O -> Coq_ll_nil
      | S n' ->
          (match mem addr with
             | Some b -> Coq_ll_cons (b, (lazy (Lazy
                 (build_list_from_memory n' (coq_Nplus addr (Npos Coq_xH))
                   mem))))
             | None -> Coq_ll_nil)
  
  (** val read_instr_from_memory :
      memory -> coq_N -> (I.instruction * coq_N) option **)
  
  let read_instr_from_memory mem pc =
    match I.parse_instruction pc
            (build_list_from_memory (nat_of_N I.instr_max_size) pc mem) with
      | Some a -> let (p, y) = a in Some p
      | None -> None
 end

