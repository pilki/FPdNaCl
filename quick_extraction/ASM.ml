open Ascii
open BinNat
open BinPos
open BinaryDefs
open Byte
open Datatypes
open DoOption
open LazyList
open NSet
open Semantics
open String0
open Validator

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

module Instruction = 
 struct 
  type register' =
    | REG1
    | REG2
    | REG3
    | REG4
    | REG5
    | REG6
    | REG7
    | REG8
  
  (** val register'_rect :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> register' ->
      'a1 **)
  
  let register'_rect f f0 f1 f2 f3 f4 f5 f6 = function
    | REG1 -> f
    | REG2 -> f0
    | REG3 -> f1
    | REG4 -> f2
    | REG5 -> f3
    | REG6 -> f4
    | REG7 -> f5
    | REG8 -> f6
  
  (** val register'_rec :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> register' ->
      'a1 **)
  
  let register'_rec f f0 f1 f2 f3 f4 f5 f6 = function
    | REG1 -> f
    | REG2 -> f0
    | REG3 -> f1
    | REG4 -> f2
    | REG5 -> f3
    | REG6 -> f4
    | REG7 -> f5
    | REG8 -> f6
  
  type register = register'
  
  (** val register_eq_dec : register -> register -> bool **)
  
  let register_eq_dec r1 r2 =
    match r1 with
      | REG1 -> (match r2 with
                   | REG1 -> true
                   | _ -> false)
      | REG2 -> (match r2 with
                   | REG2 -> true
                   | _ -> false)
      | REG3 -> (match r2 with
                   | REG3 -> true
                   | _ -> false)
      | REG4 -> (match r2 with
                   | REG4 -> true
                   | _ -> false)
      | REG5 -> (match r2 with
                   | REG5 -> true
                   | _ -> false)
      | REG6 -> (match r2 with
                   | REG6 -> true
                   | _ -> false)
      | REG7 -> (match r2 with
                   | REG7 -> true
                   | _ -> false)
      | REG8 -> (match r2 with
                   | REG8 -> true
                   | _ -> false)
  
  type instruction' =
    | Instr_noop
    | Instr_and of register * word * register
    | Instr_read of register * register
    | Instr_write of register * register
    | Instr_direct_jump of word
    | Instr_direct_cond_jump of register * word
    | Instr_indirect_jump of register
    | Instr_os_call of word
  
  (** val instruction'_rect :
      'a1 -> (register -> word -> register -> 'a1) -> (register -> register
      -> 'a1) -> (register -> register -> 'a1) -> (word -> 'a1) -> (register
      -> word -> 'a1) -> (register -> 'a1) -> (word -> 'a1) -> instruction'
      -> 'a1 **)
  
  let instruction'_rect f f0 f1 f2 f3 f4 f5 f6 = function
    | Instr_noop -> f
    | Instr_and (x, x0, x1) -> f0 x x0 x1
    | Instr_read (x, x0) -> f1 x x0
    | Instr_write (x, x0) -> f2 x x0
    | Instr_direct_jump x -> f3 x
    | Instr_direct_cond_jump (x, x0) -> f4 x x0
    | Instr_indirect_jump x -> f5 x
    | Instr_os_call x -> f6 x
  
  (** val instruction'_rec :
      'a1 -> (register -> word -> register -> 'a1) -> (register -> register
      -> 'a1) -> (register -> register -> 'a1) -> (word -> 'a1) -> (register
      -> word -> 'a1) -> (register -> 'a1) -> (word -> 'a1) -> instruction'
      -> 'a1 **)
  
  let instruction'_rec f f0 f1 f2 f3 f4 f5 f6 = function
    | Instr_noop -> f
    | Instr_and (x, x0, x1) -> f0 x x0 x1
    | Instr_read (x, x0) -> f1 x x0
    | Instr_write (x, x0) -> f2 x x0
    | Instr_direct_jump x -> f3 x
    | Instr_direct_cond_jump (x, x0) -> f4 x x0
    | Instr_indirect_jump x -> f5 x
    | Instr_os_call x -> f6 x
  
  type instruction = instruction'
  
  (** val reg_from_byte : byte -> register res **)
  
  let reg_from_byte = function
    | B01 -> OK REG1
    | B02 -> OK REG2
    | B03 -> OK REG3
    | B04 -> OK REG4
    | B05 -> OK REG5
    | B06 -> OK REG6
    | B07 -> OK REG7
    | B08 -> OK REG8
    | _ -> Err (String ((Ascii (false, true, false, false, true, false, true,
        false)), (String ((Ascii (true, false, true, false, false, true,
        true, false)), (String ((Ascii (true, true, true, false, false, true,
        true, false)), (String ((Ascii (true, false, false, true, false,
        true, true, false)), (String ((Ascii (true, true, false, false, true,
        true, true, false)), (String ((Ascii (false, false, true, false,
        true, true, true, false)), (String ((Ascii (true, false, true, false,
        false, true, true, false)), (String ((Ascii (false, true, false,
        false, true, true, true, false)), (String ((Ascii (false, false,
        false, false, false, true, false, false)), (String ((Ascii (false,
        true, true, true, false, true, true, false)), (String ((Ascii (true,
        false, true, false, true, true, true, false)), (String ((Ascii (true,
        false, true, true, false, true, true, false)), (String ((Ascii
        (false, true, false, false, false, true, true, false)), (String
        ((Ascii (true, false, true, false, false, true, true, false)),
        (String ((Ascii (false, true, false, false, true, true, true,
        false)), (String ((Ascii (false, false, false, false, false, true,
        false, false)), (String ((Ascii (true, false, true, true, false,
        true, true, false)), (String ((Ascii (true, false, true, false, true,
        true, true, false)), (String ((Ascii (true, true, false, false, true,
        true, true, false)), (String ((Ascii (false, false, true, false,
        true, true, true, false)), (String ((Ascii (false, false, false,
        false, false, true, false, false)), (String ((Ascii (false, true,
        false, false, false, true, true, false)), (String ((Ascii (true,
        false, true, false, false, true, true, false)), (String ((Ascii
        (false, false, false, false, false, true, false, false)), (String
        ((Ascii (false, true, false, false, false, true, true, false)),
        (String ((Ascii (true, false, true, false, false, true, true,
        false)), (String ((Ascii (false, false, true, false, true, true,
        true, false)), (String ((Ascii (true, true, true, false, true, true,
        true, false)), (String ((Ascii (true, false, true, false, false,
        true, true, false)), (String ((Ascii (true, false, true, false,
        false, true, true, false)), (String ((Ascii (false, true, true, true,
        false, true, true, false)), (String ((Ascii (false, false, false,
        false, false, true, false, false)), (String ((Ascii (true, false,
        false, false, true, true, false, false)), (String ((Ascii (false,
        false, false, false, false, true, false, false)), (String ((Ascii
        (true, false, false, false, false, true, true, false)), (String
        ((Ascii (false, true, true, true, false, true, true, false)), (String
        ((Ascii (false, false, true, false, false, true, true, false)),
        (String ((Ascii (false, false, false, false, false, true, false,
        false)), (String ((Ascii (false, false, false, true, true, true,
        false, false)),
        EmptyString))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  
  (** val parse_instruction :
      coq_N -> byte lazy_list -> ((instruction * coq_N) * byte lazy_list) res **)
  
  let parse_instruction addr = function
    | Coq_ll_nil -> Err (String ((Ascii (true, false, true, false, true,
        false, true, false)), (String ((Ascii (false, true, true, true,
        false, true, true, false)), (String ((Ascii (true, true, false, true,
        false, true, true, false)), (String ((Ascii (false, true, true, true,
        false, true, true, false)), (String ((Ascii (true, true, true, true,
        false, true, true, false)), (String ((Ascii (true, true, true, false,
        true, true, true, false)), (String ((Ascii (false, true, true, true,
        false, true, true, false)), (String ((Ascii (false, false, false,
        false, false, true, false, false)), (String ((Ascii (true, false,
        false, true, false, true, true, false)), (String ((Ascii (false,
        true, true, true, false, true, true, false)), (String ((Ascii (true,
        true, false, false, true, true, true, false)), (String ((Ascii
        (false, false, true, false, true, true, true, false)), (String
        ((Ascii (false, true, false, false, true, true, true, false)),
        (String ((Ascii (true, false, true, false, true, true, true, false)),
        (String ((Ascii (true, true, false, false, false, true, true,
        false)), (String ((Ascii (false, false, true, false, true, true,
        true, false)), (String ((Ascii (true, false, false, true, false,
        true, true, false)), (String ((Ascii (true, true, true, true, false,
        true, true, false)), (String ((Ascii (false, true, true, true, false,
        true, true, false)),
        EmptyString))))))))))))))))))))))))))))))))))))))
    | Coq_ll_cons (x, l) ->
        (match x with
           | B00 ->
               let Lazy rst_ll = Lazy.force l in
               OK ((Instr_noop, (Npos Coq_xH)), rst_ll)
           | B01 ->
               let Lazy l0 = Lazy.force l in
               (match l0 with
                  | Coq_ll_nil -> Err (String ((Ascii (true, false, true,
                      false, true, false, true, false)), (String ((Ascii
                      (false, true, true, true, false, true, true, false)),
                      (String ((Ascii (true, true, false, true, false, true,
                      true, false)), (String ((Ascii (false, true, true,
                      true, false, true, true, false)), (String ((Ascii
                      (true, true, true, true, false, true, true, false)),
                      (String ((Ascii (true, true, true, false, true, true,
                      true, false)), (String ((Ascii (false, true, true,
                      true, false, true, true, false)), (String ((Ascii
                      (false, false, false, false, false, true, false,
                      false)), (String ((Ascii (true, false, false, true,
                      false, true, true, false)), (String ((Ascii (false,
                      true, true, true, false, true, true, false)), (String
                      ((Ascii (true, true, false, false, true, true, true,
                      false)), (String ((Ascii (false, false, true, false,
                      true, true, true, false)), (String ((Ascii (false,
                      true, false, false, true, true, true, false)), (String
                      ((Ascii (true, false, true, false, true, true, true,
                      false)), (String ((Ascii (true, true, false, false,
                      false, true, true, false)), (String ((Ascii (false,
                      false, true, false, true, true, true, false)), (String
                      ((Ascii (true, false, false, true, false, true, true,
                      false)), (String ((Ascii (true, true, true, true,
                      false, true, true, false)), (String ((Ascii (false,
                      true, true, true, false, true, true, false)),
                      EmptyString))))))))))))))))))))))))))))))))))))))
                  | Coq_ll_cons (reg_code1, l1) ->
                      let Lazy l2 = Lazy.force l1 in
                      (match l2 with
                         | Coq_ll_nil -> Err (String ((Ascii (true, false,
                             true, false, true, false, true, false)), (String
                             ((Ascii (false, true, true, true, false, true,
                             true, false)), (String ((Ascii (true, true,
                             false, true, false, true, true, false)), (String
                             ((Ascii (false, true, true, true, false, true,
                             true, false)), (String ((Ascii (true, true,
                             true, true, false, true, true, false)), (String
                             ((Ascii (true, true, true, false, true, true,
                             true, false)), (String ((Ascii (false, true,
                             true, true, false, true, true, false)), (String
                             ((Ascii (false, false, false, false, false,
                             true, false, false)), (String ((Ascii (true,
                             false, false, true, false, true, true, false)),
                             (String ((Ascii (false, true, true, true, false,
                             true, true, false)), (String ((Ascii (true,
                             true, false, false, true, true, true, false)),
                             (String ((Ascii (false, false, true, false,
                             true, true, true, false)), (String ((Ascii
                             (false, true, false, false, true, true, true,
                             false)), (String ((Ascii (true, false, true,
                             false, true, true, true, false)), (String
                             ((Ascii (true, true, false, false, false, true,
                             true, false)), (String ((Ascii (false, false,
                             true, false, true, true, true, false)), (String
                             ((Ascii (true, false, false, true, false, true,
                             true, false)), (String ((Ascii (true, true,
                             true, true, false, true, true, false)), (String
                             ((Ascii (false, true, true, true, false, true,
                             true, false)),
                             EmptyString))))))))))))))))))))))))))))))))))))))
                         | Coq_ll_cons (b1, l3) ->
                             let Lazy l4 = Lazy.force l3 in
                             (match l4 with
                                | Coq_ll_nil -> Err (String ((Ascii (true,
                                    false, true, false, true, false, true,
                                    false)), (String ((Ascii (false, true,
                                    true, true, false, true, true, false)),
                                    (String ((Ascii (true, true, false, true,
                                    false, true, true, false)), (String
                                    ((Ascii (false, true, true, true, false,
                                    true, true, false)), (String ((Ascii
                                    (true, true, true, true, false, true,
                                    true, false)), (String ((Ascii (true,
                                    true, true, false, true, true, true,
                                    false)), (String ((Ascii (false, true,
                                    true, true, false, true, true, false)),
                                    (String ((Ascii (false, false, false,
                                    false, false, true, false, false)),
                                    (String ((Ascii (true, false, false,
                                    true, false, true, true, false)), (String
                                    ((Ascii (false, true, true, true, false,
                                    true, true, false)), (String ((Ascii
                                    (true, true, false, false, true, true,
                                    true, false)), (String ((Ascii (false,
                                    false, true, false, true, true, true,
                                    false)), (String ((Ascii (false, true,
                                    false, false, true, true, true, false)),
                                    (String ((Ascii (true, false, true,
                                    false, true, true, true, false)), (String
                                    ((Ascii (true, true, false, false, false,
                                    true, true, false)), (String ((Ascii
                                    (false, false, true, false, true, true,
                                    true, false)), (String ((Ascii (true,
                                    false, false, true, false, true, true,
                                    false)), (String ((Ascii (true, true,
                                    true, true, false, true, true, false)),
                                    (String ((Ascii (false, true, true, true,
                                    false, true, true, false)),
                                    EmptyString))))))))))))))))))))))))))))))))))))))
                                | Coq_ll_cons (b2, l5) ->
                                    let Lazy l6 = Lazy.force l5 in
                                    (match l6 with
                                       | Coq_ll_nil -> Err (String ((Ascii
                                           (true, false, true, false, true,
                                           false, true, false)), (String
                                           ((Ascii (false, true, true, true,
                                           false, true, true, false)),
                                           (String ((Ascii (true, true,
                                           false, true, false, true, true,
                                           false)), (String ((Ascii (false,
                                           true, true, true, false, true,
                                           true, false)), (String ((Ascii
                                           (true, true, true, true, false,
                                           true, true, false)), (String
                                           ((Ascii (true, true, true, false,
                                           true, true, true, false)), (String
                                           ((Ascii (false, true, true, true,
                                           false, true, true, false)),
                                           (String ((Ascii (false, false,
                                           false, false, false, true, false,
                                           false)), (String ((Ascii (true,
                                           false, false, true, false, true,
                                           true, false)), (String ((Ascii
                                           (false, true, true, true, false,
                                           true, true, false)), (String
                                           ((Ascii (true, true, false, false,
                                           true, true, true, false)), (String
                                           ((Ascii (false, false, true,
                                           false, true, true, true, false)),
                                           (String ((Ascii (false, true,
                                           false, false, true, true, true,
                                           false)), (String ((Ascii (true,
                                           false, true, false, true, true,
                                           true, false)), (String ((Ascii
                                           (true, true, false, false, false,
                                           true, true, false)), (String
                                           ((Ascii (false, false, true,
                                           false, true, true, true, false)),
                                           (String ((Ascii (true, false,
                                           false, true, false, true, true,
                                           false)), (String ((Ascii (true,
                                           true, true, true, false, true,
                                           true, false)), (String ((Ascii
                                           (false, true, true, true, false,
                                           true, true, false)),
                                           EmptyString))))))))))))))))))))))))))))))))))))))
                                       | Coq_ll_cons (
                                           b3, l7) ->
                                           let Lazy l8 = Lazy.force l7 in
                                           (match l8 with
                                              | Coq_ll_nil -> Err (String
                                                  ((Ascii (true, false, true,
                                                  false, true, false, true,
                                                  false)), (String ((Ascii
                                                  (false, true, true, true,
                                                  false, true, true, false)),
                                                  (String ((Ascii (true,
                                                  true, false, true, false,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  true, true, true, false,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  true, true, true, false,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  true, true, false, true,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  true, true, true, false,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  false, false, false, false,
                                                  true, false, false)),
                                                  (String ((Ascii (true,
                                                  false, false, true, false,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  true, true, true, false,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  true, false, false, true,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  false, true, false, true,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  true, false, false, true,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  false, true, false, true,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  true, false, false, false,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  false, true, false, true,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  false, false, true, false,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  true, true, true, false,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  true, true, true, false,
                                                  true, true, false)),
                                                  EmptyString))))))))))))))))))))))))))))))))))))))
                                              | Coq_ll_cons (
                                                  b4, l9) ->
                                                  let Lazy l10 = Lazy.force
                                                  l9
                                                  in
                                                  (
                                                  match l10 with
                                                    | 
                                                  Coq_ll_nil -> Err (String
                                                  ((Ascii (true, false, true,
                                                  false, true, false, true,
                                                  false)), (String ((Ascii
                                                  (false, true, true, true,
                                                  false, true, true, false)),
                                                  (String ((Ascii (true,
                                                  true, false, true, false,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  true, true, true, false,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  true, true, true, false,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  true, true, false, true,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  true, true, true, false,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  false, false, false, false,
                                                  true, false, false)),
                                                  (String ((Ascii (true,
                                                  false, false, true, false,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  true, true, true, false,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  true, false, false, true,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  false, true, false, true,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  true, false, false, true,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  false, true, false, true,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  true, false, false, false,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  false, true, false, true,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  false, false, true, false,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  true, true, true, false,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  true, true, true, false,
                                                  true, true, false)),
                                                  EmptyString))))))))))))))))))))))))))))))))))))))
                                                    | 
                                                  Coq_ll_cons
                                                  (reg_code2, l11) ->
                                                  let Lazy rst_ll =
                                                  Lazy.force l11
                                                  in
                                                  (
                                                  match 
                                                  reg_from_byte reg_code1 with
                                                    | 
                                                  OK a ->
                                                  (match 
                                                  reg_from_byte reg_code2 with
                                                    | 
                                                  OK a0 -> OK (((Instr_and
                                                  (a, (W (b4, b3, b2, b1)),
                                                  a0)), (Npos (Coq_xI (Coq_xI
                                                  Coq_xH)))), rst_ll)
                                                    | 
                                                  Err e -> Err e)
                                                    | 
                                                  Err e -> Err e)))))))
           | B02 ->
               let Lazy l0 = Lazy.force l in
               (match l0 with
                  | Coq_ll_nil -> Err (String ((Ascii (true, false, true,
                      false, true, false, true, false)), (String ((Ascii
                      (false, true, true, true, false, true, true, false)),
                      (String ((Ascii (true, true, false, true, false, true,
                      true, false)), (String ((Ascii (false, true, true,
                      true, false, true, true, false)), (String ((Ascii
                      (true, true, true, true, false, true, true, false)),
                      (String ((Ascii (true, true, true, false, true, true,
                      true, false)), (String ((Ascii (false, true, true,
                      true, false, true, true, false)), (String ((Ascii
                      (false, false, false, false, false, true, false,
                      false)), (String ((Ascii (true, false, false, true,
                      false, true, true, false)), (String ((Ascii (false,
                      true, true, true, false, true, true, false)), (String
                      ((Ascii (true, true, false, false, true, true, true,
                      false)), (String ((Ascii (false, false, true, false,
                      true, true, true, false)), (String ((Ascii (false,
                      true, false, false, true, true, true, false)), (String
                      ((Ascii (true, false, true, false, true, true, true,
                      false)), (String ((Ascii (true, true, false, false,
                      false, true, true, false)), (String ((Ascii (false,
                      false, true, false, true, true, true, false)), (String
                      ((Ascii (true, false, false, true, false, true, true,
                      false)), (String ((Ascii (true, true, true, true,
                      false, true, true, false)), (String ((Ascii (false,
                      true, true, true, false, true, true, false)),
                      EmptyString))))))))))))))))))))))))))))))))))))))
                  | Coq_ll_cons (reg_code1, l1) ->
                      let Lazy l2 = Lazy.force l1 in
                      (match l2 with
                         | Coq_ll_nil -> Err (String ((Ascii (true, false,
                             true, false, true, false, true, false)), (String
                             ((Ascii (false, true, true, true, false, true,
                             true, false)), (String ((Ascii (true, true,
                             false, true, false, true, true, false)), (String
                             ((Ascii (false, true, true, true, false, true,
                             true, false)), (String ((Ascii (true, true,
                             true, true, false, true, true, false)), (String
                             ((Ascii (true, true, true, false, true, true,
                             true, false)), (String ((Ascii (false, true,
                             true, true, false, true, true, false)), (String
                             ((Ascii (false, false, false, false, false,
                             true, false, false)), (String ((Ascii (true,
                             false, false, true, false, true, true, false)),
                             (String ((Ascii (false, true, true, true, false,
                             true, true, false)), (String ((Ascii (true,
                             true, false, false, true, true, true, false)),
                             (String ((Ascii (false, false, true, false,
                             true, true, true, false)), (String ((Ascii
                             (false, true, false, false, true, true, true,
                             false)), (String ((Ascii (true, false, true,
                             false, true, true, true, false)), (String
                             ((Ascii (true, true, false, false, false, true,
                             true, false)), (String ((Ascii (false, false,
                             true, false, true, true, true, false)), (String
                             ((Ascii (true, false, false, true, false, true,
                             true, false)), (String ((Ascii (true, true,
                             true, true, false, true, true, false)), (String
                             ((Ascii (false, true, true, true, false, true,
                             true, false)),
                             EmptyString))))))))))))))))))))))))))))))))))))))
                         | Coq_ll_cons (reg_code2, l3) ->
                             let Lazy rst_ll = Lazy.force l3 in
                             (match reg_from_byte reg_code1 with
                                | OK a ->
                                    (match reg_from_byte reg_code2 with
                                       | OK a0 -> OK (((Instr_read (a, a0)),
                                           (Npos (Coq_xI Coq_xH))), rst_ll)
                                       | Err e -> Err e)
                                | Err e -> Err e)))
           | B03 ->
               let Lazy l0 = Lazy.force l in
               (match l0 with
                  | Coq_ll_nil -> Err (String ((Ascii (true, false, true,
                      false, true, false, true, false)), (String ((Ascii
                      (false, true, true, true, false, true, true, false)),
                      (String ((Ascii (true, true, false, true, false, true,
                      true, false)), (String ((Ascii (false, true, true,
                      true, false, true, true, false)), (String ((Ascii
                      (true, true, true, true, false, true, true, false)),
                      (String ((Ascii (true, true, true, false, true, true,
                      true, false)), (String ((Ascii (false, true, true,
                      true, false, true, true, false)), (String ((Ascii
                      (false, false, false, false, false, true, false,
                      false)), (String ((Ascii (true, false, false, true,
                      false, true, true, false)), (String ((Ascii (false,
                      true, true, true, false, true, true, false)), (String
                      ((Ascii (true, true, false, false, true, true, true,
                      false)), (String ((Ascii (false, false, true, false,
                      true, true, true, false)), (String ((Ascii (false,
                      true, false, false, true, true, true, false)), (String
                      ((Ascii (true, false, true, false, true, true, true,
                      false)), (String ((Ascii (true, true, false, false,
                      false, true, true, false)), (String ((Ascii (false,
                      false, true, false, true, true, true, false)), (String
                      ((Ascii (true, false, false, true, false, true, true,
                      false)), (String ((Ascii (true, true, true, true,
                      false, true, true, false)), (String ((Ascii (false,
                      true, true, true, false, true, true, false)),
                      EmptyString))))))))))))))))))))))))))))))))))))))
                  | Coq_ll_cons (reg_code1, l1) ->
                      let Lazy l2 = Lazy.force l1 in
                      (match l2 with
                         | Coq_ll_nil -> Err (String ((Ascii (true, false,
                             true, false, true, false, true, false)), (String
                             ((Ascii (false, true, true, true, false, true,
                             true, false)), (String ((Ascii (true, true,
                             false, true, false, true, true, false)), (String
                             ((Ascii (false, true, true, true, false, true,
                             true, false)), (String ((Ascii (true, true,
                             true, true, false, true, true, false)), (String
                             ((Ascii (true, true, true, false, true, true,
                             true, false)), (String ((Ascii (false, true,
                             true, true, false, true, true, false)), (String
                             ((Ascii (false, false, false, false, false,
                             true, false, false)), (String ((Ascii (true,
                             false, false, true, false, true, true, false)),
                             (String ((Ascii (false, true, true, true, false,
                             true, true, false)), (String ((Ascii (true,
                             true, false, false, true, true, true, false)),
                             (String ((Ascii (false, false, true, false,
                             true, true, true, false)), (String ((Ascii
                             (false, true, false, false, true, true, true,
                             false)), (String ((Ascii (true, false, true,
                             false, true, true, true, false)), (String
                             ((Ascii (true, true, false, false, false, true,
                             true, false)), (String ((Ascii (false, false,
                             true, false, true, true, true, false)), (String
                             ((Ascii (true, false, false, true, false, true,
                             true, false)), (String ((Ascii (true, true,
                             true, true, false, true, true, false)), (String
                             ((Ascii (false, true, true, true, false, true,
                             true, false)),
                             EmptyString))))))))))))))))))))))))))))))))))))))
                         | Coq_ll_cons (reg_code2, l3) ->
                             let Lazy rst_ll = Lazy.force l3 in
                             (match reg_from_byte reg_code1 with
                                | OK a ->
                                    (match reg_from_byte reg_code2 with
                                       | OK a0 -> OK (((Instr_write (a, a0)),
                                           (Npos (Coq_xI Coq_xH))), rst_ll)
                                       | Err e -> Err e)
                                | Err e -> Err e)))
           | B04 ->
               let Lazy l0 = Lazy.force l in
               (match l0 with
                  | Coq_ll_nil -> Err (String ((Ascii (true, false, true,
                      false, true, false, true, false)), (String ((Ascii
                      (false, true, true, true, false, true, true, false)),
                      (String ((Ascii (true, true, false, true, false, true,
                      true, false)), (String ((Ascii (false, true, true,
                      true, false, true, true, false)), (String ((Ascii
                      (true, true, true, true, false, true, true, false)),
                      (String ((Ascii (true, true, true, false, true, true,
                      true, false)), (String ((Ascii (false, true, true,
                      true, false, true, true, false)), (String ((Ascii
                      (false, false, false, false, false, true, false,
                      false)), (String ((Ascii (true, false, false, true,
                      false, true, true, false)), (String ((Ascii (false,
                      true, true, true, false, true, true, false)), (String
                      ((Ascii (true, true, false, false, true, true, true,
                      false)), (String ((Ascii (false, false, true, false,
                      true, true, true, false)), (String ((Ascii (false,
                      true, false, false, true, true, true, false)), (String
                      ((Ascii (true, false, true, false, true, true, true,
                      false)), (String ((Ascii (true, true, false, false,
                      false, true, true, false)), (String ((Ascii (false,
                      false, true, false, true, true, true, false)), (String
                      ((Ascii (true, false, false, true, false, true, true,
                      false)), (String ((Ascii (true, true, true, true,
                      false, true, true, false)), (String ((Ascii (false,
                      true, true, true, false, true, true, false)),
                      EmptyString))))))))))))))))))))))))))))))))))))))
                  | Coq_ll_cons (b1, l1) ->
                      let Lazy l2 = Lazy.force l1 in
                      (match l2 with
                         | Coq_ll_nil -> Err (String ((Ascii (true, false,
                             true, false, true, false, true, false)), (String
                             ((Ascii (false, true, true, true, false, true,
                             true, false)), (String ((Ascii (true, true,
                             false, true, false, true, true, false)), (String
                             ((Ascii (false, true, true, true, false, true,
                             true, false)), (String ((Ascii (true, true,
                             true, true, false, true, true, false)), (String
                             ((Ascii (true, true, true, false, true, true,
                             true, false)), (String ((Ascii (false, true,
                             true, true, false, true, true, false)), (String
                             ((Ascii (false, false, false, false, false,
                             true, false, false)), (String ((Ascii (true,
                             false, false, true, false, true, true, false)),
                             (String ((Ascii (false, true, true, true, false,
                             true, true, false)), (String ((Ascii (true,
                             true, false, false, true, true, true, false)),
                             (String ((Ascii (false, false, true, false,
                             true, true, true, false)), (String ((Ascii
                             (false, true, false, false, true, true, true,
                             false)), (String ((Ascii (true, false, true,
                             false, true, true, true, false)), (String
                             ((Ascii (true, true, false, false, false, true,
                             true, false)), (String ((Ascii (false, false,
                             true, false, true, true, true, false)), (String
                             ((Ascii (true, false, false, true, false, true,
                             true, false)), (String ((Ascii (true, true,
                             true, true, false, true, true, false)), (String
                             ((Ascii (false, true, true, true, false, true,
                             true, false)),
                             EmptyString))))))))))))))))))))))))))))))))))))))
                         | Coq_ll_cons (b2, l3) ->
                             let Lazy l4 = Lazy.force l3 in
                             (match l4 with
                                | Coq_ll_nil -> Err (String ((Ascii (true,
                                    false, true, false, true, false, true,
                                    false)), (String ((Ascii (false, true,
                                    true, true, false, true, true, false)),
                                    (String ((Ascii (true, true, false, true,
                                    false, true, true, false)), (String
                                    ((Ascii (false, true, true, true, false,
                                    true, true, false)), (String ((Ascii
                                    (true, true, true, true, false, true,
                                    true, false)), (String ((Ascii (true,
                                    true, true, false, true, true, true,
                                    false)), (String ((Ascii (false, true,
                                    true, true, false, true, true, false)),
                                    (String ((Ascii (false, false, false,
                                    false, false, true, false, false)),
                                    (String ((Ascii (true, false, false,
                                    true, false, true, true, false)), (String
                                    ((Ascii (false, true, true, true, false,
                                    true, true, false)), (String ((Ascii
                                    (true, true, false, false, true, true,
                                    true, false)), (String ((Ascii (false,
                                    false, true, false, true, true, true,
                                    false)), (String ((Ascii (false, true,
                                    false, false, true, true, true, false)),
                                    (String ((Ascii (true, false, true,
                                    false, true, true, true, false)), (String
                                    ((Ascii (true, true, false, false, false,
                                    true, true, false)), (String ((Ascii
                                    (false, false, true, false, true, true,
                                    true, false)), (String ((Ascii (true,
                                    false, false, true, false, true, true,
                                    false)), (String ((Ascii (true, true,
                                    true, true, false, true, true, false)),
                                    (String ((Ascii (false, true, true, true,
                                    false, true, true, false)),
                                    EmptyString))))))))))))))))))))))))))))))))))))))
                                | Coq_ll_cons (b3, l5) ->
                                    let Lazy l6 = Lazy.force l5 in
                                    (match l6 with
                                       | Coq_ll_nil -> Err (String ((Ascii
                                           (true, false, true, false, true,
                                           false, true, false)), (String
                                           ((Ascii (false, true, true, true,
                                           false, true, true, false)),
                                           (String ((Ascii (true, true,
                                           false, true, false, true, true,
                                           false)), (String ((Ascii (false,
                                           true, true, true, false, true,
                                           true, false)), (String ((Ascii
                                           (true, true, true, true, false,
                                           true, true, false)), (String
                                           ((Ascii (true, true, true, false,
                                           true, true, true, false)), (String
                                           ((Ascii (false, true, true, true,
                                           false, true, true, false)),
                                           (String ((Ascii (false, false,
                                           false, false, false, true, false,
                                           false)), (String ((Ascii (true,
                                           false, false, true, false, true,
                                           true, false)), (String ((Ascii
                                           (false, true, true, true, false,
                                           true, true, false)), (String
                                           ((Ascii (true, true, false, false,
                                           true, true, true, false)), (String
                                           ((Ascii (false, false, true,
                                           false, true, true, true, false)),
                                           (String ((Ascii (false, true,
                                           false, false, true, true, true,
                                           false)), (String ((Ascii (true,
                                           false, true, false, true, true,
                                           true, false)), (String ((Ascii
                                           (true, true, false, false, false,
                                           true, true, false)), (String
                                           ((Ascii (false, false, true,
                                           false, true, true, true, false)),
                                           (String ((Ascii (true, false,
                                           false, true, false, true, true,
                                           false)), (String ((Ascii (true,
                                           true, true, true, false, true,
                                           true, false)), (String ((Ascii
                                           (false, true, true, true, false,
                                           true, true, false)),
                                           EmptyString))))))))))))))))))))))))))))))))))))))
                                       | Coq_ll_cons (
                                           b4, l7) ->
                                           let Lazy rst_ll = Lazy.force l7 in
                                           OK (((Instr_direct_jump (W (b4,
                                           b3, b2, b1))), (Npos (Coq_xI
                                           (Coq_xO Coq_xH)))), rst_ll)))))
           | B05 ->
               let Lazy l0 = Lazy.force l in
               (match l0 with
                  | Coq_ll_nil -> Err (String ((Ascii (true, false, true,
                      false, true, false, true, false)), (String ((Ascii
                      (false, true, true, true, false, true, true, false)),
                      (String ((Ascii (true, true, false, true, false, true,
                      true, false)), (String ((Ascii (false, true, true,
                      true, false, true, true, false)), (String ((Ascii
                      (true, true, true, true, false, true, true, false)),
                      (String ((Ascii (true, true, true, false, true, true,
                      true, false)), (String ((Ascii (false, true, true,
                      true, false, true, true, false)), (String ((Ascii
                      (false, false, false, false, false, true, false,
                      false)), (String ((Ascii (true, false, false, true,
                      false, true, true, false)), (String ((Ascii (false,
                      true, true, true, false, true, true, false)), (String
                      ((Ascii (true, true, false, false, true, true, true,
                      false)), (String ((Ascii (false, false, true, false,
                      true, true, true, false)), (String ((Ascii (false,
                      true, false, false, true, true, true, false)), (String
                      ((Ascii (true, false, true, false, true, true, true,
                      false)), (String ((Ascii (true, true, false, false,
                      false, true, true, false)), (String ((Ascii (false,
                      false, true, false, true, true, true, false)), (String
                      ((Ascii (true, false, false, true, false, true, true,
                      false)), (String ((Ascii (true, true, true, true,
                      false, true, true, false)), (String ((Ascii (false,
                      true, true, true, false, true, true, false)),
                      EmptyString))))))))))))))))))))))))))))))))))))))
                  | Coq_ll_cons (reg_code1, l1) ->
                      let Lazy l2 = Lazy.force l1 in
                      (match l2 with
                         | Coq_ll_nil -> Err (String ((Ascii (true, false,
                             true, false, true, false, true, false)), (String
                             ((Ascii (false, true, true, true, false, true,
                             true, false)), (String ((Ascii (true, true,
                             false, true, false, true, true, false)), (String
                             ((Ascii (false, true, true, true, false, true,
                             true, false)), (String ((Ascii (true, true,
                             true, true, false, true, true, false)), (String
                             ((Ascii (true, true, true, false, true, true,
                             true, false)), (String ((Ascii (false, true,
                             true, true, false, true, true, false)), (String
                             ((Ascii (false, false, false, false, false,
                             true, false, false)), (String ((Ascii (true,
                             false, false, true, false, true, true, false)),
                             (String ((Ascii (false, true, true, true, false,
                             true, true, false)), (String ((Ascii (true,
                             true, false, false, true, true, true, false)),
                             (String ((Ascii (false, false, true, false,
                             true, true, true, false)), (String ((Ascii
                             (false, true, false, false, true, true, true,
                             false)), (String ((Ascii (true, false, true,
                             false, true, true, true, false)), (String
                             ((Ascii (true, true, false, false, false, true,
                             true, false)), (String ((Ascii (false, false,
                             true, false, true, true, true, false)), (String
                             ((Ascii (true, false, false, true, false, true,
                             true, false)), (String ((Ascii (true, true,
                             true, true, false, true, true, false)), (String
                             ((Ascii (false, true, true, true, false, true,
                             true, false)),
                             EmptyString))))))))))))))))))))))))))))))))))))))
                         | Coq_ll_cons (b1, l3) ->
                             let Lazy l4 = Lazy.force l3 in
                             (match l4 with
                                | Coq_ll_nil -> Err (String ((Ascii (true,
                                    false, true, false, true, false, true,
                                    false)), (String ((Ascii (false, true,
                                    true, true, false, true, true, false)),
                                    (String ((Ascii (true, true, false, true,
                                    false, true, true, false)), (String
                                    ((Ascii (false, true, true, true, false,
                                    true, true, false)), (String ((Ascii
                                    (true, true, true, true, false, true,
                                    true, false)), (String ((Ascii (true,
                                    true, true, false, true, true, true,
                                    false)), (String ((Ascii (false, true,
                                    true, true, false, true, true, false)),
                                    (String ((Ascii (false, false, false,
                                    false, false, true, false, false)),
                                    (String ((Ascii (true, false, false,
                                    true, false, true, true, false)), (String
                                    ((Ascii (false, true, true, true, false,
                                    true, true, false)), (String ((Ascii
                                    (true, true, false, false, true, true,
                                    true, false)), (String ((Ascii (false,
                                    false, true, false, true, true, true,
                                    false)), (String ((Ascii (false, true,
                                    false, false, true, true, true, false)),
                                    (String ((Ascii (true, false, true,
                                    false, true, true, true, false)), (String
                                    ((Ascii (true, true, false, false, false,
                                    true, true, false)), (String ((Ascii
                                    (false, false, true, false, true, true,
                                    true, false)), (String ((Ascii (true,
                                    false, false, true, false, true, true,
                                    false)), (String ((Ascii (true, true,
                                    true, true, false, true, true, false)),
                                    (String ((Ascii (false, true, true, true,
                                    false, true, true, false)),
                                    EmptyString))))))))))))))))))))))))))))))))))))))
                                | Coq_ll_cons (b2, l5) ->
                                    let Lazy l6 = Lazy.force l5 in
                                    (match l6 with
                                       | Coq_ll_nil -> Err (String ((Ascii
                                           (true, false, true, false, true,
                                           false, true, false)), (String
                                           ((Ascii (false, true, true, true,
                                           false, true, true, false)),
                                           (String ((Ascii (true, true,
                                           false, true, false, true, true,
                                           false)), (String ((Ascii (false,
                                           true, true, true, false, true,
                                           true, false)), (String ((Ascii
                                           (true, true, true, true, false,
                                           true, true, false)), (String
                                           ((Ascii (true, true, true, false,
                                           true, true, true, false)), (String
                                           ((Ascii (false, true, true, true,
                                           false, true, true, false)),
                                           (String ((Ascii (false, false,
                                           false, false, false, true, false,
                                           false)), (String ((Ascii (true,
                                           false, false, true, false, true,
                                           true, false)), (String ((Ascii
                                           (false, true, true, true, false,
                                           true, true, false)), (String
                                           ((Ascii (true, true, false, false,
                                           true, true, true, false)), (String
                                           ((Ascii (false, false, true,
                                           false, true, true, true, false)),
                                           (String ((Ascii (false, true,
                                           false, false, true, true, true,
                                           false)), (String ((Ascii (true,
                                           false, true, false, true, true,
                                           true, false)), (String ((Ascii
                                           (true, true, false, false, false,
                                           true, true, false)), (String
                                           ((Ascii (false, false, true,
                                           false, true, true, true, false)),
                                           (String ((Ascii (true, false,
                                           false, true, false, true, true,
                                           false)), (String ((Ascii (true,
                                           true, true, true, false, true,
                                           true, false)), (String ((Ascii
                                           (false, true, true, true, false,
                                           true, true, false)),
                                           EmptyString))))))))))))))))))))))))))))))))))))))
                                       | Coq_ll_cons (
                                           b3, l7) ->
                                           let Lazy l8 = Lazy.force l7 in
                                           (match l8 with
                                              | Coq_ll_nil -> Err (String
                                                  ((Ascii (true, false, true,
                                                  false, true, false, true,
                                                  false)), (String ((Ascii
                                                  (false, true, true, true,
                                                  false, true, true, false)),
                                                  (String ((Ascii (true,
                                                  true, false, true, false,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  true, true, true, false,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  true, true, true, false,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  true, true, false, true,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  true, true, true, false,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  false, false, false, false,
                                                  true, false, false)),
                                                  (String ((Ascii (true,
                                                  false, false, true, false,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  true, true, true, false,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  true, false, false, true,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  false, true, false, true,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  true, false, false, true,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  false, true, false, true,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  true, false, false, false,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  false, true, false, true,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  false, false, true, false,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  true, true, true, false,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  true, true, true, false,
                                                  true, true, false)),
                                                  EmptyString))))))))))))))))))))))))))))))))))))))
                                              | Coq_ll_cons (
                                                  b4, l9) ->
                                                  let Lazy rst_ll =
                                                  Lazy.force l9
                                                  in
                                                  (
                                                  match 
                                                  reg_from_byte reg_code1 with
                                                    | 
                                                  OK a -> OK
                                                  (((Instr_direct_cond_jump
                                                  (a, (W (b4, b3, b2, b1)))),
                                                  (Npos (Coq_xO (Coq_xI
                                                  Coq_xH)))), rst_ll)
                                                    | 
                                                  Err e -> Err e))))))
           | B06 ->
               let Lazy l0 = Lazy.force l in
               (match l0 with
                  | Coq_ll_nil -> Err (String ((Ascii (true, false, true,
                      false, true, false, true, false)), (String ((Ascii
                      (false, true, true, true, false, true, true, false)),
                      (String ((Ascii (true, true, false, true, false, true,
                      true, false)), (String ((Ascii (false, true, true,
                      true, false, true, true, false)), (String ((Ascii
                      (true, true, true, true, false, true, true, false)),
                      (String ((Ascii (true, true, true, false, true, true,
                      true, false)), (String ((Ascii (false, true, true,
                      true, false, true, true, false)), (String ((Ascii
                      (false, false, false, false, false, true, false,
                      false)), (String ((Ascii (true, false, false, true,
                      false, true, true, false)), (String ((Ascii (false,
                      true, true, true, false, true, true, false)), (String
                      ((Ascii (true, true, false, false, true, true, true,
                      false)), (String ((Ascii (false, false, true, false,
                      true, true, true, false)), (String ((Ascii (false,
                      true, false, false, true, true, true, false)), (String
                      ((Ascii (true, false, true, false, true, true, true,
                      false)), (String ((Ascii (true, true, false, false,
                      false, true, true, false)), (String ((Ascii (false,
                      false, true, false, true, true, true, false)), (String
                      ((Ascii (true, false, false, true, false, true, true,
                      false)), (String ((Ascii (true, true, true, true,
                      false, true, true, false)), (String ((Ascii (false,
                      true, true, true, false, true, true, false)),
                      EmptyString))))))))))))))))))))))))))))))))))))))
                  | Coq_ll_cons (reg_code1, l1) ->
                      let Lazy rst_ll = Lazy.force l1 in
                      (match reg_from_byte reg_code1 with
                         | OK a -> OK (((Instr_indirect_jump a), (Npos
                             (Coq_xO Coq_xH))), rst_ll)
                         | Err e -> Err e))
           | B07 ->
               let Lazy rst_ll = Lazy.force l in
               OK (((Instr_os_call (W (byte0, byte0, byte0, byte0))), (Npos
               Coq_xH)), rst_ll)
           | _ -> Err (String ((Ascii (true, false, true, false, true, false,
               true, false)), (String ((Ascii (false, true, true, true,
               false, true, true, false)), (String ((Ascii (true, true,
               false, true, false, true, true, false)), (String ((Ascii
               (false, true, true, true, false, true, true, false)), (String
               ((Ascii (true, true, true, true, false, true, true, false)),
               (String ((Ascii (true, true, true, false, true, true, true,
               false)), (String ((Ascii (false, true, true, true, false,
               true, true, false)), (String ((Ascii (false, false, false,
               false, false, true, false, false)), (String ((Ascii (true,
               false, false, true, false, true, true, false)), (String
               ((Ascii (false, true, true, true, false, true, true, false)),
               (String ((Ascii (true, true, false, false, true, true, true,
               false)), (String ((Ascii (false, false, true, false, true,
               true, true, false)), (String ((Ascii (false, true, false,
               false, true, true, true, false)), (String ((Ascii (true,
               false, true, false, true, true, true, false)), (String ((Ascii
               (true, true, false, false, false, true, true, false)), (String
               ((Ascii (false, false, true, false, true, true, true, false)),
               (String ((Ascii (true, false, false, true, false, true, true,
               false)), (String ((Ascii (true, true, true, true, false, true,
               true, false)), (String ((Ascii (false, true, true, true,
               false, true, true, false)),
               EmptyString)))))))))))))))))))))))))))))))))))))))
  
  type coq_R_parse_instruction =
    | R_parse_instruction_0 of byte lazy_list
    | R_parse_instruction_1 of byte lazy_list * byte lazy_list
    | R_parse_instruction_2 of byte lazy_list * byte * 
       byte * byte * byte * byte * byte * byte lazy_list * 
       register * register
    | R_parse_instruction_3 of byte lazy_list * byte * 
       byte * byte * byte * byte * byte * byte lazy_list * 
       register * string
    | R_parse_instruction_4 of byte lazy_list * byte * 
       byte * byte * byte * byte * byte * byte lazy_list * 
       string
    | R_parse_instruction_5 of byte lazy_list * byte * 
       byte * byte lazy_list * register * register
    | R_parse_instruction_6 of byte lazy_list * byte * 
       byte * byte lazy_list * register * string
    | R_parse_instruction_7 of byte lazy_list * byte * 
       byte * byte lazy_list * string
    | R_parse_instruction_8 of byte lazy_list * byte * 
       byte * byte lazy_list * register * register
    | R_parse_instruction_9 of byte lazy_list * byte * 
       byte * byte lazy_list * register * string
    | R_parse_instruction_10 of byte lazy_list * byte * 
       byte * byte lazy_list * string
    | R_parse_instruction_11 of byte lazy_list * byte * 
       byte * byte * byte * byte lazy_list
    | R_parse_instruction_12 of byte lazy_list * byte * 
       byte * byte * byte * byte * byte lazy_list * 
       register
    | R_parse_instruction_13 of byte lazy_list * byte * 
       byte * byte * byte * byte * byte lazy_list * 
       string
    | R_parse_instruction_14 of byte lazy_list * byte * 
       byte lazy_list * register
    | R_parse_instruction_15 of byte lazy_list * byte * 
       byte lazy_list * string
    | R_parse_instruction_16 of byte lazy_list * byte lazy_list
    | R_parse_instruction_17 of byte lazy_list * byte lazy_list
  
  (** val coq_R_parse_instruction_rect :
      coq_N -> (byte lazy_list -> __ -> 'a1) -> (byte lazy_list -> byte
      lazy_list -> __ -> 'a1) -> (byte lazy_list -> byte -> byte -> byte ->
      byte -> byte -> byte -> byte lazy_list -> __ -> register -> __ ->
      register -> __ -> 'a1) -> (byte lazy_list -> byte -> byte -> byte ->
      byte -> byte -> byte -> byte lazy_list -> __ -> register -> __ ->
      string -> __ -> 'a1) -> (byte lazy_list -> byte -> byte -> byte -> byte
      -> byte -> byte -> byte lazy_list -> __ -> string -> __ -> 'a1) ->
      (byte lazy_list -> byte -> byte -> byte lazy_list -> __ -> register ->
      __ -> register -> __ -> 'a1) -> (byte lazy_list -> byte -> byte -> byte
      lazy_list -> __ -> register -> __ -> string -> __ -> 'a1) -> (byte
      lazy_list -> byte -> byte -> byte lazy_list -> __ -> string -> __ ->
      'a1) -> (byte lazy_list -> byte -> byte -> byte lazy_list -> __ ->
      register -> __ -> register -> __ -> 'a1) -> (byte lazy_list -> byte ->
      byte -> byte lazy_list -> __ -> register -> __ -> string -> __ -> 'a1)
      -> (byte lazy_list -> byte -> byte -> byte lazy_list -> __ -> string ->
      __ -> 'a1) -> (byte lazy_list -> byte -> byte -> byte -> byte -> byte
      lazy_list -> __ -> 'a1) -> (byte lazy_list -> byte -> byte -> byte ->
      byte -> byte -> byte lazy_list -> __ -> register -> __ -> 'a1) -> (byte
      lazy_list -> byte -> byte -> byte -> byte -> byte -> byte lazy_list ->
      __ -> string -> __ -> 'a1) -> (byte lazy_list -> byte -> byte lazy_list
      -> __ -> register -> __ -> 'a1) -> (byte lazy_list -> byte -> byte
      lazy_list -> __ -> string -> __ -> 'a1) -> (byte lazy_list -> byte
      lazy_list -> __ -> 'a1) -> (byte lazy_list -> byte lazy_list -> __ ->
      __ -> 'a1) -> byte lazy_list -> ((instruction * coq_N) * byte
      lazy_list) res -> coq_R_parse_instruction -> 'a1 **)
  
  let coq_R_parse_instruction_rect addr f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 ll r = function
    | R_parse_instruction_0 x -> f x __
    | R_parse_instruction_1 (x, x0) -> f0 x x0 __
    | R_parse_instruction_2 (x, x0, x1, x2, x3, x4, x5, x6, x7, x8) ->
        f1 x x0 x1 x2 x3 x4 x5 x6 __ x7 __ x8 __
    | R_parse_instruction_3 (x, x0, x1, x2, x3, x4, x5, x6, x7, x8) ->
        f2 x x0 x1 x2 x3 x4 x5 x6 __ x7 __ x8 __
    | R_parse_instruction_4 (x, x0, x1, x2, x3, x4, x5, x6, x7) ->
        f3 x x0 x1 x2 x3 x4 x5 x6 __ x7 __
    | R_parse_instruction_5 (x, x0, x1, x2, x3, x4) ->
        f4 x x0 x1 x2 __ x3 __ x4 __
    | R_parse_instruction_6 (x, x0, x1, x2, x3, x4) ->
        f5 x x0 x1 x2 __ x3 __ x4 __
    | R_parse_instruction_7 (x, x0, x1, x2, x3) -> f6 x x0 x1 x2 __ x3 __
    | R_parse_instruction_8 (x, x0, x1, x2, x3, x4) ->
        f7 x x0 x1 x2 __ x3 __ x4 __
    | R_parse_instruction_9 (x, x0, x1, x2, x3, x4) ->
        f8 x x0 x1 x2 __ x3 __ x4 __
    | R_parse_instruction_10 (x, x0, x1, x2, x3) -> f9 x x0 x1 x2 __ x3 __
    | R_parse_instruction_11 (x, x0, x1, x2, x3, x4) ->
        f10 x x0 x1 x2 x3 x4 __
    | R_parse_instruction_12 (x, x0, x1, x2, x3, x4, x5, x6) ->
        f11 x x0 x1 x2 x3 x4 x5 __ x6 __
    | R_parse_instruction_13 (x, x0, x1, x2, x3, x4, x5, x6) ->
        f12 x x0 x1 x2 x3 x4 x5 __ x6 __
    | R_parse_instruction_14 (x, x0, x1, x2) -> f13 x x0 x1 __ x2 __
    | R_parse_instruction_15 (x, x0, x1, x2) -> f14 x x0 x1 __ x2 __
    | R_parse_instruction_16 (x, x0) -> f15 x x0 __
    | R_parse_instruction_17 (x, x0) -> f16 x x0 __ __
  
  (** val coq_R_parse_instruction_rec :
      coq_N -> (byte lazy_list -> __ -> 'a1) -> (byte lazy_list -> byte
      lazy_list -> __ -> 'a1) -> (byte lazy_list -> byte -> byte -> byte ->
      byte -> byte -> byte -> byte lazy_list -> __ -> register -> __ ->
      register -> __ -> 'a1) -> (byte lazy_list -> byte -> byte -> byte ->
      byte -> byte -> byte -> byte lazy_list -> __ -> register -> __ ->
      string -> __ -> 'a1) -> (byte lazy_list -> byte -> byte -> byte -> byte
      -> byte -> byte -> byte lazy_list -> __ -> string -> __ -> 'a1) ->
      (byte lazy_list -> byte -> byte -> byte lazy_list -> __ -> register ->
      __ -> register -> __ -> 'a1) -> (byte lazy_list -> byte -> byte -> byte
      lazy_list -> __ -> register -> __ -> string -> __ -> 'a1) -> (byte
      lazy_list -> byte -> byte -> byte lazy_list -> __ -> string -> __ ->
      'a1) -> (byte lazy_list -> byte -> byte -> byte lazy_list -> __ ->
      register -> __ -> register -> __ -> 'a1) -> (byte lazy_list -> byte ->
      byte -> byte lazy_list -> __ -> register -> __ -> string -> __ -> 'a1)
      -> (byte lazy_list -> byte -> byte -> byte lazy_list -> __ -> string ->
      __ -> 'a1) -> (byte lazy_list -> byte -> byte -> byte -> byte -> byte
      lazy_list -> __ -> 'a1) -> (byte lazy_list -> byte -> byte -> byte ->
      byte -> byte -> byte lazy_list -> __ -> register -> __ -> 'a1) -> (byte
      lazy_list -> byte -> byte -> byte -> byte -> byte -> byte lazy_list ->
      __ -> string -> __ -> 'a1) -> (byte lazy_list -> byte -> byte lazy_list
      -> __ -> register -> __ -> 'a1) -> (byte lazy_list -> byte -> byte
      lazy_list -> __ -> string -> __ -> 'a1) -> (byte lazy_list -> byte
      lazy_list -> __ -> 'a1) -> (byte lazy_list -> byte lazy_list -> __ ->
      __ -> 'a1) -> byte lazy_list -> ((instruction * coq_N) * byte
      lazy_list) res -> coq_R_parse_instruction -> 'a1 **)
  
  let coq_R_parse_instruction_rec addr f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 ll r = function
    | R_parse_instruction_0 x -> f x __
    | R_parse_instruction_1 (x, x0) -> f0 x x0 __
    | R_parse_instruction_2 (x, x0, x1, x2, x3, x4, x5, x6, x7, x8) ->
        f1 x x0 x1 x2 x3 x4 x5 x6 __ x7 __ x8 __
    | R_parse_instruction_3 (x, x0, x1, x2, x3, x4, x5, x6, x7, x8) ->
        f2 x x0 x1 x2 x3 x4 x5 x6 __ x7 __ x8 __
    | R_parse_instruction_4 (x, x0, x1, x2, x3, x4, x5, x6, x7) ->
        f3 x x0 x1 x2 x3 x4 x5 x6 __ x7 __
    | R_parse_instruction_5 (x, x0, x1, x2, x3, x4) ->
        f4 x x0 x1 x2 __ x3 __ x4 __
    | R_parse_instruction_6 (x, x0, x1, x2, x3, x4) ->
        f5 x x0 x1 x2 __ x3 __ x4 __
    | R_parse_instruction_7 (x, x0, x1, x2, x3) -> f6 x x0 x1 x2 __ x3 __
    | R_parse_instruction_8 (x, x0, x1, x2, x3, x4) ->
        f7 x x0 x1 x2 __ x3 __ x4 __
    | R_parse_instruction_9 (x, x0, x1, x2, x3, x4) ->
        f8 x x0 x1 x2 __ x3 __ x4 __
    | R_parse_instruction_10 (x, x0, x1, x2, x3) -> f9 x x0 x1 x2 __ x3 __
    | R_parse_instruction_11 (x, x0, x1, x2, x3, x4) ->
        f10 x x0 x1 x2 x3 x4 __
    | R_parse_instruction_12 (x, x0, x1, x2, x3, x4, x5, x6) ->
        f11 x x0 x1 x2 x3 x4 x5 __ x6 __
    | R_parse_instruction_13 (x, x0, x1, x2, x3, x4, x5, x6) ->
        f12 x x0 x1 x2 x3 x4 x5 __ x6 __
    | R_parse_instruction_14 (x, x0, x1, x2) -> f13 x x0 x1 __ x2 __
    | R_parse_instruction_15 (x, x0, x1, x2) -> f14 x x0 x1 __ x2 __
    | R_parse_instruction_16 (x, x0) -> f15 x x0 __
    | R_parse_instruction_17 (x, x0) -> f16 x x0 __ __
  
  (** val parse_instruction_rect :
      coq_N -> (byte lazy_list -> __ -> 'a1) -> (byte lazy_list -> byte
      lazy_list -> __ -> 'a1) -> (byte lazy_list -> byte -> byte -> byte ->
      byte -> byte -> byte -> byte lazy_list -> __ -> register -> __ ->
      register -> __ -> 'a1) -> (byte lazy_list -> byte -> byte -> byte ->
      byte -> byte -> byte -> byte lazy_list -> __ -> register -> __ ->
      string -> __ -> 'a1) -> (byte lazy_list -> byte -> byte -> byte -> byte
      -> byte -> byte -> byte lazy_list -> __ -> string -> __ -> 'a1) ->
      (byte lazy_list -> byte -> byte -> byte lazy_list -> __ -> register ->
      __ -> register -> __ -> 'a1) -> (byte lazy_list -> byte -> byte -> byte
      lazy_list -> __ -> register -> __ -> string -> __ -> 'a1) -> (byte
      lazy_list -> byte -> byte -> byte lazy_list -> __ -> string -> __ ->
      'a1) -> (byte lazy_list -> byte -> byte -> byte lazy_list -> __ ->
      register -> __ -> register -> __ -> 'a1) -> (byte lazy_list -> byte ->
      byte -> byte lazy_list -> __ -> register -> __ -> string -> __ -> 'a1)
      -> (byte lazy_list -> byte -> byte -> byte lazy_list -> __ -> string ->
      __ -> 'a1) -> (byte lazy_list -> byte -> byte -> byte -> byte -> byte
      lazy_list -> __ -> 'a1) -> (byte lazy_list -> byte -> byte -> byte ->
      byte -> byte -> byte lazy_list -> __ -> register -> __ -> 'a1) -> (byte
      lazy_list -> byte -> byte -> byte -> byte -> byte -> byte lazy_list ->
      __ -> string -> __ -> 'a1) -> (byte lazy_list -> byte -> byte lazy_list
      -> __ -> register -> __ -> 'a1) -> (byte lazy_list -> byte -> byte
      lazy_list -> __ -> string -> __ -> 'a1) -> (byte lazy_list -> byte
      lazy_list -> __ -> 'a1) -> (byte lazy_list -> byte lazy_list -> __ ->
      __ -> 'a1) -> byte lazy_list -> 'a1 **)
  
  let parse_instruction_rect addr f16 f15 f14 f13 f12 f11 f10 f9 f8 f7 f6 f5 f4 f3 f2 f1 f0 f ll =
    let f17 = f16 ll in
    let f18 = f15 ll in
    let f19 = f14 ll in
    let f20 = f13 ll in
    let f21 = f12 ll in
    let f22 = f11 ll in
    let f23 = f10 ll in
    let f24 = f9 ll in
    let f25 = f8 ll in
    let f26 = f7 ll in
    let f27 = f6 ll in
    let f28 = f5 ll in
    let f29 = f4 ll in
    let f30 = f3 ll in
    let f31 = f2 ll in
    let f32 = f1 ll in
    let f33 = f0 ll in
    let f34 = f ll in
    let f35 = f34 ll __ in
    (match ll with
       | Coq_ll_nil -> f17 __
       | Coq_ll_cons (x, l) ->
           (match x with
              | B00 -> let Lazy l0 = Lazy.force l in f18 l0 __
              | B01 ->
                  let Lazy l0 = Lazy.force l in
                  (match l0 with
                     | Coq_ll_nil -> f35 __
                     | Coq_ll_cons (x0, l1) ->
                         let Lazy l2 = Lazy.force l1 in
                         (match l2 with
                            | Coq_ll_nil -> f35 __
                            | Coq_ll_cons (x1, l3) ->
                                let Lazy l4 = Lazy.force l3 in
                                (match l4 with
                                   | Coq_ll_nil -> f35 __
                                   | Coq_ll_cons (x2, l5) ->
                                       let Lazy l6 = Lazy.force l5 in
                                       (match l6 with
                                          | Coq_ll_nil -> f35 __
                                          | Coq_ll_cons (
                                              x3, l7) ->
                                              let Lazy l8 = Lazy.force l7 in
                                              (match l8 with
                                                 | 
                                               Coq_ll_nil -> f35 __
                                                 | 
                                               Coq_ll_cons (
                                                 x4, l9) ->
                                                 let Lazy l10 = Lazy.force l9
                                                 in
                                                 (match l10 with
                                                    | 
                                                  Coq_ll_nil -> f35 __
                                                    | 
                                                  Coq_ll_cons (
                                                  x5, l11) ->
                                                  let Lazy l12 = Lazy.force
                                                  l11
                                                  in
                                                  let f36 =
                                                  f19 x0 x1 x2 x3 x4 x5 l12
                                                  __
                                                  in
                                                  let f37 =
                                                  f20 x0 x1 x2 x3 x4 x5 l12
                                                  __
                                                  in
                                                  let f38 =
                                                  f21 x0 x1 x2 x3 x4 x5 l12
                                                  __
                                                  in
                                                  (
                                                  match 
                                                  reg_from_byte x0 with
                                                    | 
                                                  OK r ->
                                                  let f39 = f37 r __ in
                                                  let f40 = f36 r __ in
                                                  (
                                                  match 
                                                  reg_from_byte x5 with
                                                    | 
                                                  OK r0 -> f40 r0 __
                                                    | 
                                                  Err s -> f39 s __)
                                                    | 
                                                  Err s -> f38 s __)))))))
              | B02 ->
                  let Lazy l0 = Lazy.force l in
                  (match l0 with
                     | Coq_ll_nil -> f35 __
                     | Coq_ll_cons (x0, l1) ->
                         let Lazy l2 = Lazy.force l1 in
                         (match l2 with
                            | Coq_ll_nil -> f35 __
                            | Coq_ll_cons (x1, l3) ->
                                let Lazy l4 = Lazy.force l3 in
                                let f36 = f22 x0 x1 l4 __ in
                                let f37 = f23 x0 x1 l4 __ in
                                let f38 = f24 x0 x1 l4 __ in
                                (match reg_from_byte x0 with
                                   | OK r ->
                                       let f39 = f37 r __ in
                                       let f40 = f36 r __ in
                                       (match reg_from_byte x1 with
                                          | OK r0 -> f40 r0 __
                                          | Err s -> f39 s __)
                                   | Err s -> f38 s __)))
              | B03 ->
                  let Lazy l0 = Lazy.force l in
                  (match l0 with
                     | Coq_ll_nil -> f35 __
                     | Coq_ll_cons (x0, l1) ->
                         let Lazy l2 = Lazy.force l1 in
                         (match l2 with
                            | Coq_ll_nil -> f35 __
                            | Coq_ll_cons (x1, l3) ->
                                let Lazy l4 = Lazy.force l3 in
                                let f36 = f25 x0 x1 l4 __ in
                                let f37 = f26 x0 x1 l4 __ in
                                let f38 = f27 x0 x1 l4 __ in
                                (match reg_from_byte x0 with
                                   | OK r ->
                                       let f39 = f37 r __ in
                                       let f40 = f36 r __ in
                                       (match reg_from_byte x1 with
                                          | OK r0 -> f40 r0 __
                                          | Err s -> f39 s __)
                                   | Err s -> f38 s __)))
              | B04 ->
                  let Lazy l0 = Lazy.force l in
                  (match l0 with
                     | Coq_ll_nil -> f35 __
                     | Coq_ll_cons (x0, l1) ->
                         let Lazy l2 = Lazy.force l1 in
                         (match l2 with
                            | Coq_ll_nil -> f35 __
                            | Coq_ll_cons (x1, l3) ->
                                let Lazy l4 = Lazy.force l3 in
                                (match l4 with
                                   | Coq_ll_nil -> f35 __
                                   | Coq_ll_cons (x2, l5) ->
                                       let Lazy l6 = Lazy.force l5 in
                                       (match l6 with
                                          | Coq_ll_nil -> f35 __
                                          | Coq_ll_cons (
                                              x3, l7) ->
                                              let Lazy l8 = Lazy.force l7 in
                                              f28 x0 x1 x2 x3 l8 __))))
              | B05 ->
                  let Lazy l0 = Lazy.force l in
                  (match l0 with
                     | Coq_ll_nil -> f35 __
                     | Coq_ll_cons (x0, l1) ->
                         let Lazy l2 = Lazy.force l1 in
                         (match l2 with
                            | Coq_ll_nil -> f35 __
                            | Coq_ll_cons (x1, l3) ->
                                let Lazy l4 = Lazy.force l3 in
                                (match l4 with
                                   | Coq_ll_nil -> f35 __
                                   | Coq_ll_cons (x2, l5) ->
                                       let Lazy l6 = Lazy.force l5 in
                                       (match l6 with
                                          | Coq_ll_nil -> f35 __
                                          | Coq_ll_cons (
                                              x3, l7) ->
                                              let Lazy l8 = Lazy.force l7 in
                                              (match l8 with
                                                 | 
                                               Coq_ll_nil -> f35 __
                                                 | 
                                               Coq_ll_cons (
                                                 x4, l9) ->
                                                 let Lazy l10 = Lazy.force l9
                                                 in
                                                 let f36 =
                                                  f29 x0 x1 x2 x3 x4 l10 __
                                                 in
                                                 let f37 =
                                                  f30 x0 x1 x2 x3 x4 l10 __
                                                 in
                                                 (match 
                                                  reg_from_byte x0 with
                                                    | 
                                                  OK r -> f36 r __
                                                    | 
                                                  Err s -> f37 s __))))))
              | B06 ->
                  let Lazy l0 = Lazy.force l in
                  (match l0 with
                     | Coq_ll_nil -> f35 __
                     | Coq_ll_cons (x0, l1) ->
                         let Lazy l2 = Lazy.force l1 in
                         let f36 = f31 x0 l2 __ in
                         let f37 = f32 x0 l2 __ in
                         (match reg_from_byte x0 with
                            | OK r -> f36 r __
                            | Err s -> f37 s __))
              | B07 -> let Lazy l0 = Lazy.force l in f33 l0 __
              | _ -> f35 __))
  
  (** val parse_instruction_rec :
      coq_N -> (byte lazy_list -> __ -> 'a1) -> (byte lazy_list -> byte
      lazy_list -> __ -> 'a1) -> (byte lazy_list -> byte -> byte -> byte ->
      byte -> byte -> byte -> byte lazy_list -> __ -> register -> __ ->
      register -> __ -> 'a1) -> (byte lazy_list -> byte -> byte -> byte ->
      byte -> byte -> byte -> byte lazy_list -> __ -> register -> __ ->
      string -> __ -> 'a1) -> (byte lazy_list -> byte -> byte -> byte -> byte
      -> byte -> byte -> byte lazy_list -> __ -> string -> __ -> 'a1) ->
      (byte lazy_list -> byte -> byte -> byte lazy_list -> __ -> register ->
      __ -> register -> __ -> 'a1) -> (byte lazy_list -> byte -> byte -> byte
      lazy_list -> __ -> register -> __ -> string -> __ -> 'a1) -> (byte
      lazy_list -> byte -> byte -> byte lazy_list -> __ -> string -> __ ->
      'a1) -> (byte lazy_list -> byte -> byte -> byte lazy_list -> __ ->
      register -> __ -> register -> __ -> 'a1) -> (byte lazy_list -> byte ->
      byte -> byte lazy_list -> __ -> register -> __ -> string -> __ -> 'a1)
      -> (byte lazy_list -> byte -> byte -> byte lazy_list -> __ -> string ->
      __ -> 'a1) -> (byte lazy_list -> byte -> byte -> byte -> byte -> byte
      lazy_list -> __ -> 'a1) -> (byte lazy_list -> byte -> byte -> byte ->
      byte -> byte -> byte lazy_list -> __ -> register -> __ -> 'a1) -> (byte
      lazy_list -> byte -> byte -> byte -> byte -> byte -> byte lazy_list ->
      __ -> string -> __ -> 'a1) -> (byte lazy_list -> byte -> byte lazy_list
      -> __ -> register -> __ -> 'a1) -> (byte lazy_list -> byte -> byte
      lazy_list -> __ -> string -> __ -> 'a1) -> (byte lazy_list -> byte
      lazy_list -> __ -> 'a1) -> (byte lazy_list -> byte lazy_list -> __ ->
      __ -> 'a1) -> byte lazy_list -> 'a1 **)
  
  let parse_instruction_rec addr =
    parse_instruction_rect addr
  
  (** val coq_R_parse_instruction_correct :
      coq_N -> byte lazy_list -> ((instruction * coq_N) * byte lazy_list) res
      -> coq_R_parse_instruction **)
  
  let coq_R_parse_instruction_correct x x0 res0 =
    parse_instruction_rect x (fun y _ z _ -> R_parse_instruction_0 y)
      (fun y y0 _ z _ -> R_parse_instruction_1 (y, y0))
      (fun y y0 y1 y2 y3 y4 y5 y6 _ y8 _ y10 _ z _ -> R_parse_instruction_2
      (y, y0, y1, y2, y3, y4, y5, y6, y8, y10))
      (fun y y0 y1 y2 y3 y4 y5 y6 _ y8 _ y10 _ z _ -> R_parse_instruction_3
      (y, y0, y1, y2, y3, y4, y5, y6, y8, y10))
      (fun y y0 y1 y2 y3 y4 y5 y6 _ y8 _ z _ -> R_parse_instruction_4 (y, y0,
      y1, y2, y3, y4, y5, y6, y8)) (fun y y0 y1 y2 _ y4 _ y6 _ z _ ->
      R_parse_instruction_5 (y, y0, y1, y2, y4, y6))
      (fun y y0 y1 y2 _ y4 _ y6 _ z _ -> R_parse_instruction_6 (y, y0, y1,
      y2, y4, y6)) (fun y y0 y1 y2 _ y4 _ z _ -> R_parse_instruction_7 (y,
      y0, y1, y2, y4)) (fun y y0 y1 y2 _ y4 _ y6 _ z _ ->
      R_parse_instruction_8 (y, y0, y1, y2, y4, y6))
      (fun y y0 y1 y2 _ y4 _ y6 _ z _ -> R_parse_instruction_9 (y, y0, y1,
      y2, y4, y6)) (fun y y0 y1 y2 _ y4 _ z _ -> R_parse_instruction_10 (y,
      y0, y1, y2, y4)) (fun y y0 y1 y2 y3 y4 _ z _ -> R_parse_instruction_11
      (y, y0, y1, y2, y3, y4)) (fun y y0 y1 y2 y3 y4 y5 _ y7 _ z _ ->
      R_parse_instruction_12 (y, y0, y1, y2, y3, y4, y5, y7))
      (fun y y0 y1 y2 y3 y4 y5 _ y7 _ z _ -> R_parse_instruction_13 (y, y0,
      y1, y2, y3, y4, y5, y7)) (fun y y0 y1 _ y3 _ z _ ->
      R_parse_instruction_14 (y, y0, y1, y3)) (fun y y0 y1 _ y3 _ z _ ->
      R_parse_instruction_15 (y, y0, y1, y3)) (fun y y0 _ z _ ->
      R_parse_instruction_16 (y, y0)) (fun y y0 _ _ z _ ->
      R_parse_instruction_17 (y, y0)) x0 res0 __
  
  (** val instr_max_size : coq_N **)
  
  let instr_max_size =
    Npos (Coq_xI (Coq_xI Coq_xH))
  
  (** val classify_instruction :
      instruction' -> register instruction_classification **)
  
  let classify_instruction = function
    | Instr_and (reg1, w, reg2) ->
        if register_eq_dec reg1 reg2 then Mask_instr (reg1, w) else OK_instr
    | Instr_direct_jump w -> Direct_jump w
    | Instr_direct_cond_jump (reg, w) -> Direct_jump w
    | Instr_indirect_jump reg -> Indirect_jump reg
    | Instr_os_call w -> Invalid_instruction
    | _ -> OK_instr
  
  (** val read_word : memory -> coq_N -> word option **)
  
  let read_word mem addr =
    match mem addr with
      | Some a ->
          (match mem (coq_Nplus addr (Npos Coq_xH)) with
             | Some a0 ->
                 (match mem (coq_Nplus addr (Npos (Coq_xO Coq_xH))) with
                    | Some a1 ->
                        (match mem (coq_Nplus addr (Npos (Coq_xI Coq_xH))) with
                           | Some a2 -> Some (W (a2, a1, a0, a))
                           | None -> None)
                    | None -> None)
             | None -> None)
      | None -> None
  
  (** val write_byte : memory -> coq_N -> byte -> memory **)
  
  let write_byte mem addr byte1 n =
    if coq_N_eq_dec n addr then Some byte1 else mem n
  
  (** val write_word : memory -> coq_N -> word -> memory **)
  
  let write_word mem addr = function
    | W (b4, b3, b2, b1) ->
        write_byte
          (write_byte
            (write_byte (write_byte mem addr b1)
              (coq_Nplus addr (Npos Coq_xH)) b2)
            (coq_Nplus addr (Npos (Coq_xO Coq_xH))) b3)
          (coq_Nplus addr (Npos (Coq_xI Coq_xH))) b4
  
  (** val update_reg :
      (register -> word) -> register -> word -> register -> word **)
  
  let update_reg regs reg w r =
    if register_eq_dec r reg then w else regs r
 end

module Val = ValidatorCode(Instruction)

(** val validate_program : byte lazy_list -> unit res **)

let validate_program =
  Val.validate_program

