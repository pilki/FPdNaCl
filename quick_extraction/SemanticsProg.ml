open BinNat
open BinPos
open Byte
open Datatypes
open DoOption
open LazyList
open Memory
open Semantics

let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val dividable_by_32_dec : coq_N -> bool **)

let dividable_by_32_dec n =
  let branch_0 = fun _ -> true in
  let branch_1 = fun p -> true in
  let branch_2 = fun wildcard' -> false in
  (match n with
     | N0 -> branch_0 __
     | Npos wildcard' ->
         (match wildcard' with
            | Coq_xO p0 ->
                (match p0 with
                   | Coq_xO p1 ->
                       (match p1 with
                          | Coq_xO p2 ->
                              (match p2 with
                                 | Coq_xO p3 ->
                                     (match p3 with
                                        | Coq_xO p -> branch_1 p
                                        | x ->
                                            let wildcard'0 = Coq_xO (Coq_xO
                                              (Coq_xO (Coq_xO x)))
                                            in
                                            branch_2 wildcard'0)
                                 | x ->
                                     let wildcard'0 = Coq_xO (Coq_xO (Coq_xO
                                       x))
                                     in
                                     branch_2 wildcard'0)
                          | x ->
                              let wildcard'0 = Coq_xO (Coq_xO x) in
                              branch_2 wildcard'0)
                   | x -> let wildcard'0 = Coq_xO x in branch_2 wildcard'0)
            | x -> let wildcard'0 = x in branch_2 wildcard'0))

module Prog_Semantics = 
 functor (I:INSTRUCTION) ->
 struct 
  module M = Mem(I)
  
  type target_state =
    | Normal_state of I.register state
    | DANGER_STATE
  
  (** val target_state_rect :
      (I.register state -> 'a1) -> 'a1 -> target_state -> 'a1 **)
  
  let target_state_rect f f0 = function
    | Normal_state x -> f x
    | DANGER_STATE -> f0
  
  (** val target_state_rec :
      (I.register state -> 'a1) -> 'a1 -> target_state -> 'a1 **)
  
  let target_state_rec f f0 = function
    | Normal_state x -> f x
    | DANGER_STATE -> f0
 end

