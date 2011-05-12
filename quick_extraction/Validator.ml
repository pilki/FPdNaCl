open Ascii
open BinNat
open BinPos
open BinaryDefs
open Byte
open Datatypes
open DoOption
open LazyList
open Lib
open NSet
open Semantics
open SemanticsProg
open String0

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

module ValidatorCode = 
 functor (I:INSTRUCTION) ->
 struct 
  (** val proper_mask : word **)
  
  let proper_mask =
    W (BFF, BFF, BFF, BE0)
  
  (** val id : nat -> nat **)
  
  let id n =
    n
  
  (** val validate_n_byte_F :
      (coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte lazy_list ->
      ((coq_NSet * coq_NSet) * byte lazy_list) res) -> coq_N -> coq_N ->
      coq_NSet -> coq_NSet -> byte lazy_list -> ((coq_NSet * coq_NSet) * byte
      lazy_list) res **)
  
  let validate_n_byte_F validate_n_byte0 n addr valid_addresses to_be_checked_addresses ll =
    match n with
      | N0 -> OK ((valid_addresses, to_be_checked_addresses), ll)
      | Npos p ->
          (match I.parse_instruction addr ll with
             | OK a ->
                 let (p0, ll') = a in
                 let (instr, size_instr) = p0 in
                 (match safe_minus n size_instr with
                    | Some n' ->
                        (match I.classify_instruction instr with
                           | OK_instr ->
                               validate_n_byte0 n'
                                 (coq_Nplus addr size_instr)
                                 (coq_Nadd addr valid_addresses)
                                 to_be_checked_addresses ll'
                           | Mask_instr (reg1, w) ->
                               if word_eq_dec w proper_mask
                               then (match n' with
                                       | N0 -> OK
                                           (((coq_Nadd addr valid_addresses),
                                           to_be_checked_addresses), ll')
                                       | Npos p1 ->
                                           (match I.parse_instruction
                                                  (coq_Nplus addr size_instr)
                                                  ll' with
                                              | OK a0 ->
                                                  let (p2, ll'') = a0 in
                                                  let (
                                                  instr', size_instr') = p2
                                                  in
                                                  (
                                                  match 
                                                  I.classify_instruction
                                                  instr' with
                                                    | 
                                                  Indirect_jump reg2 ->
                                                  if 
                                                  I.register_eq_dec reg1 reg2
                                                  then 
                                                  (match 
                                                  safe_minus n' size_instr' with
                                                    | 
                                                  Some n'' ->
                                                  validate_n_byte0 n''
                                                  (coq_Nplus
                                                  (coq_Nplus addr size_instr)
                                                  size_instr')
                                                  (coq_Nadd addr
                                                  valid_addresses)
                                                  to_be_checked_addresses
                                                  ll''
                                                    | 
                                                  None -> Err (String ((Ascii
                                                  (true, false, false, true,
                                                  false, false, true,
                                                  false)), (String ((Ascii
                                                  (false, true, true, true,
                                                  false, true, true, false)),
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
                                                  (String ((Ascii (false,
                                                  false, false, false, false,
                                                  true, false, false)),
                                                  (String ((Ascii (true,
                                                  true, true, true, false,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  true, true, false, true,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  false, true, false, false,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  true, false, false, true,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  false, true, true, false,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  false, false, false, false,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  false, false, false, true,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  true, false, false, true,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  false, false, false, false,
                                                  true, false, false)),
                                                  (String ((Ascii (true,
                                                  true, false, false, true,
                                                  true, false, false)),
                                                  (String ((Ascii (false,
                                                  true, false, false, true,
                                                  true, false, false)),
                                                  (String ((Ascii (false,
                                                  false, false, false, false,
                                                  true, false, false)),
                                                  (String ((Ascii (false,
                                                  true, false, false, false,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  false, false, true, true,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  false, true, false, true,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  false, true, false, false,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  true, false, false, true,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  false, false, false, false,
                                                  true, false, false)),
                                                  (String ((Ascii (false,
                                                  true, false, false, false,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  true, true, true, false,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  false, true, false, true,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  true, true, true, false,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  false, true, false, false,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  false, false, false, false,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  true, false, false, true,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  false, false, true, true,
                                                  true, true, false)),
                                                  EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                  else 
                                                  Err (String ((Ascii (false,
                                                  false, true, false, true,
                                                  false, true, false)),
                                                  (String ((Ascii (false,
                                                  false, false, true, false,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  false, true, false, false,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  false, false, false, false,
                                                  true, false, false)),
                                                  (String ((Ascii (true,
                                                  false, true, true, false,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  false, false, false, false,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  true, false, false, true,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  true, false, true, false,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  false, false, false, false,
                                                  true, false, false)),
                                                  (String ((Ascii (true,
                                                  false, true, false, true,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  true, false, false, true,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  false, true, false, false,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  false, true, false, false,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  false, false, false, false,
                                                  true, false, false)),
                                                  (String ((Ascii (false,
                                                  true, false, false, false,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  false, true, false, false,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  true, true, false, false,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  true, true, true, false,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  true, false, false, true,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  false, true, false, false,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  false, false, false, false,
                                                  true, false, false)),
                                                  (String ((Ascii (false,
                                                  false, true, false, true,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  false, false, true, false,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  false, true, false, false,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  false, false, false, false,
                                                  true, false, false)),
                                                  (String ((Ascii (false,
                                                  true, false, true, false,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  false, true, false, true,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  false, true, true, false,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  false, false, false, true,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  false, false, false, false,
                                                  true, false, false)),
                                                  (String ((Ascii (true,
                                                  false, false, true, false,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  true, false, false, true,
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
                                                  true, false, false, false,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  true, true, true, false,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  true, false, false, true,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  true, false, false, true,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  false, true, false, false,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  true, false, false, false,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  false, true, false, true,
                                                  true, true, false)),
                                                  EmptyString))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                    | 
                                                  _ ->
                                                  validate_n_byte0 n'
                                                  (coq_Nplus addr size_instr)
                                                  (coq_Nadd addr
                                                  valid_addresses)
                                                  to_be_checked_addresses ll')
                                              | Err e -> Err e))
                               else validate_n_byte0 n'
                                      (coq_Nplus addr size_instr)
                                      (coq_Nadd addr valid_addresses)
                                      to_be_checked_addresses ll'
                           | Direct_jump w ->
                               if dividable_by_32_dec (coq_N_of_word w)
                               then validate_n_byte0 n'
                                      (coq_Nplus addr size_instr)
                                      (coq_Nadd addr valid_addresses)
                                      to_be_checked_addresses ll'
                               else if is_Nin (coq_N_of_word w)
                                         valid_addresses
                                    then validate_n_byte0 n'
                                           (coq_Nplus addr size_instr)
                                           (coq_Nadd addr valid_addresses)
                                           to_be_checked_addresses ll'
                                    else validate_n_byte0 n'
                                           (coq_Nplus addr size_instr)
                                           (coq_Nadd addr valid_addresses)
                                           (coq_Nadd 
                                             (coq_N_of_word w)
                                             to_be_checked_addresses) ll'
                           | Indirect_jump r -> Err (String ((Ascii (false,
                               true, true, true, false, false, true, false)),
                               (String ((Ascii (true, true, true, true,
                               false, true, true, false)), (String ((Ascii
                               (false, false, true, false, true, true, true,
                               false)), (String ((Ascii (false, false, false,
                               false, false, true, false, false)), (String
                               ((Ascii (true, false, true, true, false, true,
                               true, false)), (String ((Ascii (true, false,
                               false, false, false, true, true, false)),
                               (String ((Ascii (true, true, false, false,
                               true, true, true, false)), (String ((Ascii
                               (true, true, false, true, false, true, true,
                               false)), (String ((Ascii (true, false, true,
                               false, false, true, true, false)), (String
                               ((Ascii (false, false, true, false, false,
                               true, true, false)), (String ((Ascii (false,
                               false, false, false, false, true, false,
                               false)), (String ((Ascii (true, false, false,
                               true, false, true, true, false)), (String
                               ((Ascii (false, true, true, true, false, true,
                               true, false)), (String ((Ascii (false, false,
                               true, false, false, true, true, false)),
                               (String ((Ascii (true, false, false, true,
                               false, true, true, false)), (String ((Ascii
                               (false, true, false, false, true, true, true,
                               false)), (String ((Ascii (true, false, true,
                               false, false, true, true, false)), (String
                               ((Ascii (true, true, false, false, false,
                               true, true, false)), (String ((Ascii (false,
                               false, true, false, true, true, true, false)),
                               (String ((Ascii (false, false, false, false,
                               false, true, false, false)), (String ((Ascii
                               (false, true, false, true, false, true, true,
                               false)), (String ((Ascii (true, false, true,
                               false, true, true, true, false)), (String
                               ((Ascii (true, false, true, true, false, true,
                               true, false)), (String ((Ascii (false, false,
                               false, false, true, true, true, false)),
                               EmptyString))))))))))))))))))))))))))))))))))))))))))))))))
                           | Invalid_instruction -> Err (String ((Ascii
                               (true, false, false, true, false, false, true,
                               false)), (String ((Ascii (false, true, true,
                               true, false, true, true, false)), (String
                               ((Ascii (false, true, true, false, true, true,
                               true, false)), (String ((Ascii (true, false,
                               false, false, false, true, true, false)),
                               (String ((Ascii (false, false, true, true,
                               false, true, true, false)), (String ((Ascii
                               (true, false, false, true, false, true, true,
                               false)), (String ((Ascii (false, false, true,
                               false, false, true, true, false)), (String
                               ((Ascii (false, false, false, false, false,
                               true, false, false)), (String ((Ascii (true,
                               false, false, true, false, true, true,
                               false)), (String ((Ascii (false, true, true,
                               true, false, true, true, false)), (String
                               ((Ascii (true, true, false, false, true, true,
                               true, false)), (String ((Ascii (false, false,
                               true, false, true, true, true, false)),
                               (String ((Ascii (false, true, false, false,
                               true, true, true, false)), (String ((Ascii
                               (true, false, true, false, true, true, true,
                               false)), (String ((Ascii (true, true, false,
                               false, false, true, true, false)), (String
                               ((Ascii (false, false, true, false, true,
                               true, true, false)), (String ((Ascii (true,
                               false, false, true, false, true, true,
                               false)), (String ((Ascii (true, true, true,
                               true, false, true, true, false)), (String
                               ((Ascii (false, true, true, true, false, true,
                               true, false)),
                               EmptyString)))))))))))))))))))))))))))))))))))))))
                    | None -> Err (String ((Ascii (true, false, false, true,
                        false, false, true, false)), (String ((Ascii (false,
                        true, true, true, false, true, true, false)), (String
                        ((Ascii (true, true, false, false, true, true, true,
                        false)), (String ((Ascii (false, false, true, false,
                        true, true, true, false)), (String ((Ascii (false,
                        true, false, false, true, true, true, false)),
                        (String ((Ascii (true, false, true, false, true,
                        true, true, false)), (String ((Ascii (true, true,
                        false, false, false, true, true, false)), (String
                        ((Ascii (false, false, true, false, true, true, true,
                        false)), (String ((Ascii (true, false, false, true,
                        false, true, true, false)), (String ((Ascii (true,
                        true, true, true, false, true, true, false)), (String
                        ((Ascii (false, true, true, true, false, true, true,
                        false)), (String ((Ascii (false, false, false, false,
                        false, true, false, false)), (String ((Ascii (true,
                        true, true, true, false, true, true, false)), (String
                        ((Ascii (false, true, true, false, true, true, true,
                        false)), (String ((Ascii (true, false, true, false,
                        false, true, true, false)), (String ((Ascii (false,
                        true, false, false, true, true, true, false)),
                        (String ((Ascii (false, false, true, true, false,
                        true, true, false)), (String ((Ascii (true, false,
                        false, false, false, true, true, false)), (String
                        ((Ascii (false, false, false, false, true, true,
                        true, false)), (String ((Ascii (true, true, false,
                        false, true, true, true, false)), (String ((Ascii
                        (false, false, false, false, false, true, false,
                        false)), (String ((Ascii (true, true, false, false,
                        true, true, false, false)), (String ((Ascii (false,
                        true, false, false, true, true, false, false)),
                        (String ((Ascii (false, false, false, false, false,
                        true, false, false)), (String ((Ascii (false, true,
                        false, false, false, true, true, false)), (String
                        ((Ascii (true, false, false, true, true, true, true,
                        false)), (String ((Ascii (false, false, true, false,
                        true, true, true, false)), (String ((Ascii (true,
                        false, true, false, false, true, true, false)),
                        (String ((Ascii (true, true, false, false, true,
                        true, true, false)), (String ((Ascii (false, false,
                        false, false, false, true, false, false)), (String
                        ((Ascii (false, true, false, false, false, true,
                        true, false)), (String ((Ascii (true, true, true,
                        true, false, true, true, false)), (String ((Ascii
                        (true, false, true, false, true, true, true, false)),
                        (String ((Ascii (false, true, true, true, false,
                        true, true, false)), (String ((Ascii (false, false,
                        true, false, false, true, true, false)), (String
                        ((Ascii (true, false, false, false, false, true,
                        true, false)), (String ((Ascii (false, true, false,
                        false, true, true, true, false)), (String ((Ascii
                        (true, false, false, true, true, true, true, false)),
                        EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
             | Err e -> Err e)
  
  (** val eq_rew_r_dep : 'a1 -> 'a1 -> 'a2 -> 'a2 **)
  
  let eq_rew_r_dep x y hC =
    hC
  
  (** val validate_n_byte_terminate :
      coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte lazy_list ->
      ((coq_NSet * coq_NSet) * byte lazy_list) res **)
  
  let rec validate_n_byte_terminate n addr valid_addresses to_be_checked_addresses ll =
    match n with
      | N0 -> OK ((valid_addresses, to_be_checked_addresses), ll)
      | Npos p ->
          (match I.parse_instruction addr ll with
             | OK a ->
                 let (p0, ll') = a in
                 let (instr, size_instr) = p0 in
                 (match safe_minus (Npos p) size_instr with
                    | Some n' ->
                        (match I.classify_instruction instr with
                           | OK_instr ->
                               Obj.magic
                                 (fun n0 addr0 valid_addresses0 to_be_checked_addresses0 ll0 _ ->
                                 validate_n_byte_terminate n0 addr0
                                   valid_addresses0 to_be_checked_addresses0
                                   ll0) n' (coq_Nplus addr size_instr)
                                 (coq_Nadd addr valid_addresses)
                                 to_be_checked_addresses ll' __
                           | Mask_instr (reg1, w) ->
                               if word_eq_dec w proper_mask
                               then (match n' with
                                       | N0 -> OK
                                           (((coq_Nadd addr valid_addresses),
                                           (Obj.magic
                                             to_be_checked_addresses)), ll')
                                       | Npos p1 ->
                                           (match I.parse_instruction
                                                  (coq_Nplus addr size_instr)
                                                  ll' with
                                              | OK a0 ->
                                                  let (p2, ll'') = a0 in
                                                  let (
                                                  instr', size_instr') = p2
                                                  in
                                                  (
                                                  match 
                                                  I.classify_instruction
                                                  instr' with
                                                    | 
                                                  Indirect_jump reg2 ->
                                                  if 
                                                  I.register_eq_dec reg1 reg2
                                                  then 
                                                  (match 
                                                  safe_minus (Npos p1)
                                                  size_instr' with
                                                    | 
                                                  Some n'' ->
                                                  Obj.magic
                                                  (fun n0 addr0 valid_addresses0 to_be_checked_addresses0 ll0 _ ->
                                                  validate_n_byte_terminate
                                                  n0 addr0 valid_addresses0
                                                  to_be_checked_addresses0
                                                  ll0) n''
                                                  (coq_Nplus
                                                  (coq_Nplus addr size_instr)
                                                  size_instr')
                                                  (coq_Nadd addr
                                                  valid_addresses)
                                                  to_be_checked_addresses
                                                  ll'' __
                                                    | 
                                                  None -> Err (String ((Ascii
                                                  (true, false, false, true,
                                                  false, false, true,
                                                  false)), (String ((Ascii
                                                  (false, true, true, true,
                                                  false, true, true, false)),
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
                                                  (String ((Ascii (false,
                                                  false, false, false, false,
                                                  true, false, false)),
                                                  (String ((Ascii (true,
                                                  true, true, true, false,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  true, true, false, true,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  false, true, false, false,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  true, false, false, true,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  false, true, true, false,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  false, false, false, false,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  false, false, false, true,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  true, false, false, true,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  false, false, false, false,
                                                  true, false, false)),
                                                  (String ((Ascii (true,
                                                  true, false, false, true,
                                                  true, false, false)),
                                                  (String ((Ascii (false,
                                                  true, false, false, true,
                                                  true, false, false)),
                                                  (String ((Ascii (false,
                                                  false, false, false, false,
                                                  true, false, false)),
                                                  (String ((Ascii (false,
                                                  true, false, false, false,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  false, false, true, true,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  false, true, false, true,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  false, true, false, false,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  true, false, false, true,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  false, false, false, false,
                                                  true, false, false)),
                                                  (String ((Ascii (false,
                                                  true, false, false, false,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  true, true, true, false,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  false, true, false, true,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  true, true, true, false,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  false, true, false, false,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  false, false, false, false,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  true, false, false, true,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  false, false, true, true,
                                                  true, true, false)),
                                                  EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                  else 
                                                  Err (String ((Ascii (false,
                                                  false, true, false, true,
                                                  false, true, false)),
                                                  (String ((Ascii (false,
                                                  false, false, true, false,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  false, true, false, false,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  false, false, false, false,
                                                  true, false, false)),
                                                  (String ((Ascii (true,
                                                  false, true, true, false,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  false, false, false, false,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  true, false, false, true,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  true, false, true, false,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  false, false, false, false,
                                                  true, false, false)),
                                                  (String ((Ascii (true,
                                                  false, true, false, true,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  true, false, false, true,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  false, true, false, false,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  false, true, false, false,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  false, false, false, false,
                                                  true, false, false)),
                                                  (String ((Ascii (false,
                                                  true, false, false, false,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  false, true, false, false,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  true, true, false, false,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  true, true, true, false,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  true, false, false, true,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  false, true, false, false,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  false, false, false, false,
                                                  true, false, false)),
                                                  (String ((Ascii (false,
                                                  false, true, false, true,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  false, false, true, false,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  false, true, false, false,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  false, false, false, false,
                                                  true, false, false)),
                                                  (String ((Ascii (false,
                                                  true, false, true, false,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  false, true, false, true,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  false, true, true, false,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  false, false, false, true,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  false, false, false, false,
                                                  true, false, false)),
                                                  (String ((Ascii (true,
                                                  false, false, true, false,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  true, false, false, true,
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
                                                  true, false, false, false,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  true, true, true, false,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  true, false, false, true,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  true, false, false, true,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  false, true, false, false,
                                                  true, true, false)),
                                                  (String ((Ascii (true,
                                                  true, false, false, false,
                                                  true, true, false)),
                                                  (String ((Ascii (false,
                                                  false, true, false, true,
                                                  true, true, false)),
                                                  EmptyString))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                    | 
                                                  _ ->
                                                  Obj.magic
                                                  (fun n0 addr0 valid_addresses0 to_be_checked_addresses0 ll0 _ ->
                                                  validate_n_byte_terminate
                                                  n0 addr0 valid_addresses0
                                                  to_be_checked_addresses0
                                                  ll0) (Npos p1)
                                                  (coq_Nplus addr size_instr)
                                                  (coq_Nadd addr
                                                  valid_addresses)
                                                  to_be_checked_addresses ll'
                                                  __)
                                              | Err e0 -> Err e0))
                               else Obj.magic
                                      (fun n0 addr0 valid_addresses0 to_be_checked_addresses0 ll0 _ ->
                                      validate_n_byte_terminate n0 addr0
                                        valid_addresses0
                                        to_be_checked_addresses0 ll0) n'
                                      (coq_Nplus addr size_instr)
                                      (coq_Nadd addr valid_addresses)
                                      to_be_checked_addresses ll' __
                           | Direct_jump w ->
                               if dividable_by_32_dec (coq_N_of_word w)
                               then Obj.magic
                                      (fun n0 addr0 valid_addresses0 to_be_checked_addresses0 ll0 _ ->
                                      validate_n_byte_terminate n0 addr0
                                        valid_addresses0
                                        to_be_checked_addresses0 ll0) n'
                                      (coq_Nplus addr size_instr)
                                      (coq_Nadd addr valid_addresses)
                                      to_be_checked_addresses ll' __
                               else if is_Nin (coq_N_of_word w)
                                         valid_addresses
                                    then Obj.magic
                                           (fun n0 addr0 valid_addresses0 to_be_checked_addresses0 ll0 _ ->
                                           validate_n_byte_terminate n0 addr0
                                             valid_addresses0
                                             to_be_checked_addresses0 ll0) n'
                                           (coq_Nplus addr size_instr)
                                           (coq_Nadd addr valid_addresses)
                                           to_be_checked_addresses ll' __
                                    else validate_n_byte_terminate n'
                                           (coq_Nplus addr size_instr)
                                           (coq_Nadd addr valid_addresses)
                                           (coq_Nadd 
                                             (coq_N_of_word w)
                                             to_be_checked_addresses) ll'
                           | Indirect_jump r -> Err (String ((Ascii (false,
                               true, true, true, false, false, true, false)),
                               (String ((Ascii (true, true, true, true,
                               false, true, true, false)), (String ((Ascii
                               (false, false, true, false, true, true, true,
                               false)), (String ((Ascii (false, false, false,
                               false, false, true, false, false)), (String
                               ((Ascii (true, false, true, true, false, true,
                               true, false)), (String ((Ascii (true, false,
                               false, false, false, true, true, false)),
                               (String ((Ascii (true, true, false, false,
                               true, true, true, false)), (String ((Ascii
                               (true, true, false, true, false, true, true,
                               false)), (String ((Ascii (true, false, true,
                               false, false, true, true, false)), (String
                               ((Ascii (false, false, true, false, false,
                               true, true, false)), (String ((Ascii (false,
                               false, false, false, false, true, false,
                               false)), (String ((Ascii (true, false, false,
                               true, false, true, true, false)), (String
                               ((Ascii (false, true, true, true, false, true,
                               true, false)), (String ((Ascii (false, false,
                               true, false, false, true, true, false)),
                               (String ((Ascii (true, false, false, true,
                               false, true, true, false)), (String ((Ascii
                               (false, true, false, false, true, true, true,
                               false)), (String ((Ascii (true, false, true,
                               false, false, true, true, false)), (String
                               ((Ascii (true, true, false, false, false,
                               true, true, false)), (String ((Ascii (false,
                               false, true, false, true, true, true, false)),
                               (String ((Ascii (false, false, false, false,
                               false, true, false, false)), (String ((Ascii
                               (false, true, false, true, false, true, true,
                               false)), (String ((Ascii (true, false, true,
                               false, true, true, true, false)), (String
                               ((Ascii (true, false, true, true, false, true,
                               true, false)), (String ((Ascii (false, false,
                               false, false, true, true, true, false)),
                               EmptyString))))))))))))))))))))))))))))))))))))))))))))))))
                           | Invalid_instruction -> Err (String ((Ascii
                               (true, false, false, true, false, false, true,
                               false)), (String ((Ascii (false, true, true,
                               true, false, true, true, false)), (String
                               ((Ascii (false, true, true, false, true, true,
                               true, false)), (String ((Ascii (true, false,
                               false, false, false, true, true, false)),
                               (String ((Ascii (false, false, true, true,
                               false, true, true, false)), (String ((Ascii
                               (true, false, false, true, false, true, true,
                               false)), (String ((Ascii (false, false, true,
                               false, false, true, true, false)), (String
                               ((Ascii (false, false, false, false, false,
                               true, false, false)), (String ((Ascii (true,
                               false, false, true, false, true, true,
                               false)), (String ((Ascii (false, true, true,
                               true, false, true, true, false)), (String
                               ((Ascii (true, true, false, false, true, true,
                               true, false)), (String ((Ascii (false, false,
                               true, false, true, true, true, false)),
                               (String ((Ascii (false, true, false, false,
                               true, true, true, false)), (String ((Ascii
                               (true, false, true, false, true, true, true,
                               false)), (String ((Ascii (true, true, false,
                               false, false, true, true, false)), (String
                               ((Ascii (false, false, true, false, true,
                               true, true, false)), (String ((Ascii (true,
                               false, false, true, false, true, true,
                               false)), (String ((Ascii (true, true, true,
                               true, false, true, true, false)), (String
                               ((Ascii (false, true, true, true, false, true,
                               true, false)),
                               EmptyString)))))))))))))))))))))))))))))))))))))))
                    | None -> Err (String ((Ascii (true, false, false, true,
                        false, false, true, false)), (String ((Ascii (false,
                        true, true, true, false, true, true, false)), (String
                        ((Ascii (true, true, false, false, true, true, true,
                        false)), (String ((Ascii (false, false, true, false,
                        true, true, true, false)), (String ((Ascii (false,
                        true, false, false, true, true, true, false)),
                        (String ((Ascii (true, false, true, false, true,
                        true, true, false)), (String ((Ascii (true, true,
                        false, false, false, true, true, false)), (String
                        ((Ascii (false, false, true, false, true, true, true,
                        false)), (String ((Ascii (true, false, false, true,
                        false, true, true, false)), (String ((Ascii (true,
                        true, true, true, false, true, true, false)), (String
                        ((Ascii (false, true, true, true, false, true, true,
                        false)), (String ((Ascii (false, false, false, false,
                        false, true, false, false)), (String ((Ascii (true,
                        true, true, true, false, true, true, false)), (String
                        ((Ascii (false, true, true, false, true, true, true,
                        false)), (String ((Ascii (true, false, true, false,
                        false, true, true, false)), (String ((Ascii (false,
                        true, false, false, true, true, true, false)),
                        (String ((Ascii (false, false, true, true, false,
                        true, true, false)), (String ((Ascii (true, false,
                        false, false, false, true, true, false)), (String
                        ((Ascii (false, false, false, false, true, true,
                        true, false)), (String ((Ascii (true, true, false,
                        false, true, true, true, false)), (String ((Ascii
                        (false, false, false, false, false, true, false,
                        false)), (String ((Ascii (true, true, false, false,
                        true, true, false, false)), (String ((Ascii (false,
                        true, false, false, true, true, false, false)),
                        (String ((Ascii (false, false, false, false, false,
                        true, false, false)), (String ((Ascii (false, true,
                        false, false, false, true, true, false)), (String
                        ((Ascii (true, false, false, true, true, true, true,
                        false)), (String ((Ascii (false, false, true, false,
                        true, true, true, false)), (String ((Ascii (true,
                        false, true, false, false, true, true, false)),
                        (String ((Ascii (true, true, false, false, true,
                        true, true, false)), (String ((Ascii (false, false,
                        false, false, false, true, false, false)), (String
                        ((Ascii (false, true, false, false, false, true,
                        true, false)), (String ((Ascii (true, true, true,
                        true, false, true, true, false)), (String ((Ascii
                        (true, false, true, false, true, true, true, false)),
                        (String ((Ascii (false, true, true, true, false,
                        true, true, false)), (String ((Ascii (false, false,
                        true, false, false, true, true, false)), (String
                        ((Ascii (true, false, false, false, false, true,
                        true, false)), (String ((Ascii (false, true, false,
                        false, true, true, true, false)), (String ((Ascii
                        (true, false, false, true, true, true, true, false)),
                        EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
             | Err e -> Err e)
  
  (** val validate_n_byte :
      coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte lazy_list ->
      ((coq_NSet * coq_NSet) * byte lazy_list) res **)
  
  let validate_n_byte x x0 x1 x2 x3 =
    validate_n_byte_terminate x x0 x1 x2 x3
  
  type coq_R_validate_n_byte =
    | R_validate_n_byte_0 of coq_N * coq_N * coq_NSet * 
       coq_NSet * byte lazy_list
    | R_validate_n_byte_1 of coq_N * coq_N * coq_NSet * 
       coq_NSet * byte lazy_list * coq_N
       * ((I.instruction * coq_N) * byte lazy_list) * 
       I.instruction * coq_N * byte lazy_list
    | R_validate_n_byte_2 of coq_N * coq_N * coq_NSet * 
       coq_NSet * byte lazy_list * coq_N
       * ((I.instruction * coq_N) * byte lazy_list) * 
       I.instruction * coq_N * byte lazy_list * coq_N
       * ((coq_NSet * coq_NSet) * byte lazy_list) res * 
       coq_R_validate_n_byte
    | R_validate_n_byte_3 of coq_N * coq_N * coq_NSet * 
       coq_NSet * byte lazy_list * coq_N
       * ((I.instruction * coq_N) * byte lazy_list) * 
       I.instruction * coq_N * byte lazy_list * coq_N * 
       I.register * word
    | R_validate_n_byte_4 of coq_N * coq_N * coq_NSet * 
       coq_NSet * byte lazy_list * coq_N
       * ((I.instruction * coq_N) * byte lazy_list) * 
       I.instruction * coq_N * byte lazy_list * coq_N * 
       I.register * word * coq_N * ((I.instruction * coq_N) * byte lazy_list)
       * I.instruction * coq_N * byte lazy_list * I.register
    | R_validate_n_byte_5 of coq_N * coq_N * coq_NSet * 
       coq_NSet * byte lazy_list * coq_N
       * ((I.instruction * coq_N) * byte lazy_list) * 
       I.instruction * coq_N * byte lazy_list * coq_N * 
       I.register * word * coq_N * ((I.instruction * coq_N) * byte lazy_list)
       * I.instruction * coq_N * byte lazy_list * I.register * 
       coq_N * ((coq_NSet * coq_NSet) * byte lazy_list) res
       * coq_R_validate_n_byte
    | R_validate_n_byte_6 of coq_N * coq_N * coq_NSet * 
       coq_NSet * byte lazy_list * coq_N
       * ((I.instruction * coq_N) * byte lazy_list) * 
       I.instruction * coq_N * byte lazy_list * coq_N * 
       I.register * word * coq_N * ((I.instruction * coq_N) * byte lazy_list)
       * I.instruction * coq_N * byte lazy_list * I.register
    | R_validate_n_byte_7 of coq_N * coq_N * coq_NSet * 
       coq_NSet * byte lazy_list * coq_N
       * ((I.instruction * coq_N) * byte lazy_list) * 
       I.instruction * coq_N * byte lazy_list * coq_N * 
       I.register * word * coq_N * ((I.instruction * coq_N) * byte lazy_list)
       * I.instruction * coq_N * byte lazy_list
       * I.register instruction_classification
       * ((coq_NSet * coq_NSet) * byte lazy_list) res * 
       coq_R_validate_n_byte
    | R_validate_n_byte_8 of coq_N * coq_N * coq_NSet * 
       coq_NSet * byte lazy_list * coq_N
       * ((I.instruction * coq_N) * byte lazy_list) * 
       I.instruction * coq_N * byte lazy_list * coq_N * 
       I.register * word * coq_N * string
    | R_validate_n_byte_9 of coq_N * coq_N * coq_NSet * 
       coq_NSet * byte lazy_list * coq_N
       * ((I.instruction * coq_N) * byte lazy_list) * 
       I.instruction * coq_N * byte lazy_list * coq_N * 
       I.register * word * ((coq_NSet * coq_NSet) * byte lazy_list) res
       * coq_R_validate_n_byte
    | R_validate_n_byte_10 of coq_N * coq_N * coq_NSet * 
       coq_NSet * byte lazy_list * coq_N
       * ((I.instruction * coq_N) * byte lazy_list) * 
       I.instruction * coq_N * byte lazy_list * coq_N * 
       word * ((coq_NSet * coq_NSet) * byte lazy_list) res
       * coq_R_validate_n_byte
    | R_validate_n_byte_11 of coq_N * coq_N * coq_NSet * 
       coq_NSet * byte lazy_list * coq_N
       * ((I.instruction * coq_N) * byte lazy_list) * 
       I.instruction * coq_N * byte lazy_list * coq_N * 
       word * ((coq_NSet * coq_NSet) * byte lazy_list) res
       * coq_R_validate_n_byte
    | R_validate_n_byte_12 of coq_N * coq_N * coq_NSet * 
       coq_NSet * byte lazy_list * coq_N
       * ((I.instruction * coq_N) * byte lazy_list) * 
       I.instruction * coq_N * byte lazy_list * coq_N * 
       word * ((coq_NSet * coq_NSet) * byte lazy_list) res
       * coq_R_validate_n_byte
    | R_validate_n_byte_13 of coq_N * coq_N * coq_NSet * 
       coq_NSet * byte lazy_list * coq_N
       * ((I.instruction * coq_N) * byte lazy_list) * 
       I.instruction * coq_N * byte lazy_list * coq_N
    | R_validate_n_byte_14 of coq_N * coq_N * coq_NSet * 
       coq_NSet * byte lazy_list * coq_N
       * ((I.instruction * coq_N) * byte lazy_list) * 
       I.instruction * coq_N * byte lazy_list * coq_N * 
       I.register
    | R_validate_n_byte_15 of coq_N * coq_N * coq_NSet * 
       coq_NSet * byte lazy_list * coq_N * string
  
  (** val coq_R_validate_n_byte_rect :
      (coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte lazy_list -> __ -> 'a1)
      -> (coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte lazy_list -> coq_N
      -> __ -> __ -> ((I.instruction * coq_N) * byte lazy_list) -> __ ->
      I.instruction -> coq_N -> byte lazy_list -> __ -> __ -> 'a1) -> (coq_N
      -> coq_N -> coq_NSet -> coq_NSet -> byte lazy_list -> coq_N -> __ -> __
      -> ((I.instruction * coq_N) * byte lazy_list) -> __ -> I.instruction ->
      coq_N -> byte lazy_list -> __ -> coq_N -> __ -> __ ->
      ((coq_NSet * coq_NSet) * byte lazy_list) res -> coq_R_validate_n_byte
      -> 'a1 -> 'a1) -> (coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte
      lazy_list -> coq_N -> __ -> __ -> ((I.instruction * coq_N) * byte
      lazy_list) -> __ -> I.instruction -> coq_N -> byte lazy_list -> __ ->
      coq_N -> __ -> I.register -> word -> __ -> __ -> __ -> __ -> 'a1) ->
      (coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte lazy_list -> coq_N ->
      __ -> __ -> ((I.instruction * coq_N) * byte lazy_list) -> __ ->
      I.instruction -> coq_N -> byte lazy_list -> __ -> coq_N -> __ ->
      I.register -> word -> __ -> __ -> __ -> coq_N -> __ -> __ ->
      ((I.instruction * coq_N) * byte lazy_list) -> __ -> I.instruction ->
      coq_N -> byte lazy_list -> __ -> I.register -> __ -> __ -> __ -> __ ->
      'a1) -> (coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte lazy_list ->
      coq_N -> __ -> __ -> ((I.instruction * coq_N) * byte lazy_list) -> __
      -> I.instruction -> coq_N -> byte lazy_list -> __ -> coq_N -> __ ->
      I.register -> word -> __ -> __ -> __ -> coq_N -> __ -> __ ->
      ((I.instruction * coq_N) * byte lazy_list) -> __ -> I.instruction ->
      coq_N -> byte lazy_list -> __ -> I.register -> __ -> __ -> __ -> coq_N
      -> __ -> ((coq_NSet * coq_NSet) * byte lazy_list) res ->
      coq_R_validate_n_byte -> 'a1 -> 'a1) -> (coq_N -> coq_N -> coq_NSet ->
      coq_NSet -> byte lazy_list -> coq_N -> __ -> __ ->
      ((I.instruction * coq_N) * byte lazy_list) -> __ -> I.instruction ->
      coq_N -> byte lazy_list -> __ -> coq_N -> __ -> I.register -> word ->
      __ -> __ -> __ -> coq_N -> __ -> __ -> ((I.instruction * coq_N) * byte
      lazy_list) -> __ -> I.instruction -> coq_N -> byte lazy_list -> __ ->
      I.register -> __ -> __ -> __ -> 'a1) -> (coq_N -> coq_N -> coq_NSet ->
      coq_NSet -> byte lazy_list -> coq_N -> __ -> __ ->
      ((I.instruction * coq_N) * byte lazy_list) -> __ -> I.instruction ->
      coq_N -> byte lazy_list -> __ -> coq_N -> __ -> I.register -> word ->
      __ -> __ -> __ -> coq_N -> __ -> __ -> ((I.instruction * coq_N) * byte
      lazy_list) -> __ -> I.instruction -> coq_N -> byte lazy_list -> __ ->
      I.register instruction_classification -> __ -> __ ->
      ((coq_NSet * coq_NSet) * byte lazy_list) res -> coq_R_validate_n_byte
      -> 'a1 -> 'a1) -> (coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte
      lazy_list -> coq_N -> __ -> __ -> ((I.instruction * coq_N) * byte
      lazy_list) -> __ -> I.instruction -> coq_N -> byte lazy_list -> __ ->
      coq_N -> __ -> I.register -> word -> __ -> __ -> __ -> coq_N -> __ ->
      __ -> string -> __ -> 'a1) -> (coq_N -> coq_N -> coq_NSet -> coq_NSet
      -> byte lazy_list -> coq_N -> __ -> __ ->
      ((I.instruction * coq_N) * byte lazy_list) -> __ -> I.instruction ->
      coq_N -> byte lazy_list -> __ -> coq_N -> __ -> I.register -> word ->
      __ -> __ -> __ -> ((coq_NSet * coq_NSet) * byte lazy_list) res ->
      coq_R_validate_n_byte -> 'a1 -> 'a1) -> (coq_N -> coq_N -> coq_NSet ->
      coq_NSet -> byte lazy_list -> coq_N -> __ -> __ ->
      ((I.instruction * coq_N) * byte lazy_list) -> __ -> I.instruction ->
      coq_N -> byte lazy_list -> __ -> coq_N -> __ -> word -> __ -> __ -> __
      -> ((coq_NSet * coq_NSet) * byte lazy_list) res ->
      coq_R_validate_n_byte -> 'a1 -> 'a1) -> (coq_N -> coq_N -> coq_NSet ->
      coq_NSet -> byte lazy_list -> coq_N -> __ -> __ ->
      ((I.instruction * coq_N) * byte lazy_list) -> __ -> I.instruction ->
      coq_N -> byte lazy_list -> __ -> coq_N -> __ -> word -> __ -> __ -> __
      -> __ -> ((coq_NSet * coq_NSet) * byte lazy_list) res ->
      coq_R_validate_n_byte -> 'a1 -> 'a1) -> (coq_N -> coq_N -> coq_NSet ->
      coq_NSet -> byte lazy_list -> coq_N -> __ -> __ ->
      ((I.instruction * coq_N) * byte lazy_list) -> __ -> I.instruction ->
      coq_N -> byte lazy_list -> __ -> coq_N -> __ -> word -> __ -> __ -> __
      -> __ -> ((coq_NSet * coq_NSet) * byte lazy_list) res ->
      coq_R_validate_n_byte -> 'a1 -> 'a1) -> (coq_N -> coq_N -> coq_NSet ->
      coq_NSet -> byte lazy_list -> coq_N -> __ -> __ ->
      ((I.instruction * coq_N) * byte lazy_list) -> __ -> I.instruction ->
      coq_N -> byte lazy_list -> __ -> coq_N -> __ -> __ -> 'a1) -> (coq_N ->
      coq_N -> coq_NSet -> coq_NSet -> byte lazy_list -> coq_N -> __ -> __ ->
      ((I.instruction * coq_N) * byte lazy_list) -> __ -> I.instruction ->
      coq_N -> byte lazy_list -> __ -> coq_N -> __ -> I.register -> __ ->
      'a1) -> (coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte lazy_list ->
      coq_N -> __ -> __ -> string -> __ -> 'a1) -> coq_N -> coq_N -> coq_NSet
      -> coq_NSet -> byte lazy_list -> ((coq_NSet * coq_NSet) * byte
      lazy_list) res -> coq_R_validate_n_byte -> 'a1 **)
  
  let rec coq_R_validate_n_byte_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 n addr valid_addresses to_be_checked_addresses ll r = function
    | R_validate_n_byte_0
        (n0, addr0, valid_addresses0, to_be_checked_addresses0, ll0) ->
        f n0 addr0 valid_addresses0 to_be_checked_addresses0 ll0 __
    | R_validate_n_byte_1
        (n0, addr0, valid_addresses0, to_be_checked_addresses0, ll0, _x, a,
         x, x0, x1) ->
        f0 n0 addr0 valid_addresses0 to_be_checked_addresses0 ll0 _x __ __ a
          __ x x0 x1 __ __
    | R_validate_n_byte_2
        (n0, addr0, valid_addresses0, to_be_checked_addresses0, ll0, _x, a,
         x, x0, x1, x2, x3, x4) ->
        let addr' = coq_Nplus addr0 x0 in
        f1 n0 addr0 valid_addresses0 to_be_checked_addresses0 ll0 _x __ __ a
          __ x x0 x1 __ x2 __ __ x3 x4
          (coq_R_validate_n_byte_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11
            f12 f13 f14 x2 addr' (coq_Nadd addr0 valid_addresses0)
            to_be_checked_addresses0 x1 x3 x4)
    | R_validate_n_byte_3
        (n0, addr0, valid_addresses0, to_be_checked_addresses0, ll0, _x, a,
         x, x0, x1, x2, x3, x4) ->
        f2 n0 addr0 valid_addresses0 to_be_checked_addresses0 ll0 _x __ __ a
          __ x x0 x1 __ x2 __ x3 x4 __ __ __ __
    | R_validate_n_byte_4
        (n0, addr0, valid_addresses0, to_be_checked_addresses0, ll0, _x, a,
         x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10) ->
        f3 n0 addr0 valid_addresses0 to_be_checked_addresses0 ll0 _x __ __ a
          __ x x0 x1 __ x2 __ x3 x4 __ __ __ x5 __ __ x6 __ x7 x8 x9 __ x10
          __ __ __ __
    | R_validate_n_byte_5
        (n0, addr0, valid_addresses0, to_be_checked_addresses0, ll0, _x, a,
         x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13) ->
        let addr' = coq_Nplus addr0 x0 in
        let addr'' = coq_Nplus addr' x8 in
        f4 n0 addr0 valid_addresses0 to_be_checked_addresses0 ll0 _x __ __ a
          __ x x0 x1 __ x2 __ x3 x4 __ __ __ x5 __ __ x6 __ x7 x8 x9 __ x10
          __ __ __ x11 __ x12 x13
          (coq_R_validate_n_byte_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11
            f12 f13 f14 x11 addr'' (coq_Nadd addr0 valid_addresses0)
            to_be_checked_addresses0 x9 x12 x13)
    | R_validate_n_byte_6
        (n0, addr0, valid_addresses0, to_be_checked_addresses0, ll0, _x, a,
         x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10) ->
        f5 n0 addr0 valid_addresses0 to_be_checked_addresses0 ll0 _x __ __ a
          __ x x0 x1 __ x2 __ x3 x4 __ __ __ x5 __ __ x6 __ x7 x8 x9 __ x10
          __ __ __
    | R_validate_n_byte_7
        (n0, addr0, valid_addresses0, to_be_checked_addresses0, ll0, _x, a,
         x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12) ->
        let addr' = coq_Nplus addr0 x0 in
        f6 n0 addr0 valid_addresses0 to_be_checked_addresses0 ll0 _x __ __ a
          __ x x0 x1 __ x2 __ x3 x4 __ __ __ x5 __ __ x6 __ x7 x8 x9 __ x10
          __ __ x11 x12
          (coq_R_validate_n_byte_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11
            f12 f13 f14 x2 addr' (coq_Nadd addr0 valid_addresses0)
            to_be_checked_addresses0 x1 x11 x12)
    | R_validate_n_byte_8
        (n0, addr0, valid_addresses0, to_be_checked_addresses0, ll0, _x, a,
         x, x0, x1, x2, x3, x4, x5, x6) ->
        f7 n0 addr0 valid_addresses0 to_be_checked_addresses0 ll0 _x __ __ a
          __ x x0 x1 __ x2 __ x3 x4 __ __ __ x5 __ __ x6 __
    | R_validate_n_byte_9
        (n0, addr0, valid_addresses0, to_be_checked_addresses0, ll0, _x, a,
         x, x0, x1, x2, x3, x4, x5, x6) ->
        let addr' = coq_Nplus addr0 x0 in
        f8 n0 addr0 valid_addresses0 to_be_checked_addresses0 ll0 _x __ __ a
          __ x x0 x1 __ x2 __ x3 x4 __ __ __ x5 x6
          (coq_R_validate_n_byte_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11
            f12 f13 f14 x2 addr' (coq_Nadd addr0 valid_addresses0)
            to_be_checked_addresses0 x1 x5 x6)
    | R_validate_n_byte_10
        (n0, addr0, valid_addresses0, to_be_checked_addresses0, ll0, _x, a,
         x, x0, x1, x2, x3, x4, x5) ->
        let addr' = coq_Nplus addr0 x0 in
        f9 n0 addr0 valid_addresses0 to_be_checked_addresses0 ll0 _x __ __ a
          __ x x0 x1 __ x2 __ x3 __ __ __ x4 x5
          (coq_R_validate_n_byte_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11
            f12 f13 f14 x2 addr' (coq_Nadd addr0 valid_addresses0)
            to_be_checked_addresses0 x1 x4 x5)
    | R_validate_n_byte_11
        (n0, addr0, valid_addresses0, to_be_checked_addresses0, ll0, _x, a,
         x, x0, x1, x2, x3, x4, x5) ->
        let addr' = coq_Nplus addr0 x0 in
        f10 n0 addr0 valid_addresses0 to_be_checked_addresses0 ll0 _x __ __ a
          __ x x0 x1 __ x2 __ x3 __ __ __ __ x4 x5
          (coq_R_validate_n_byte_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11
            f12 f13 f14 x2 addr' (coq_Nadd addr0 valid_addresses0)
            to_be_checked_addresses0 x1 x4 x5)
    | R_validate_n_byte_12
        (n0, addr0, valid_addresses0, to_be_checked_addresses0, ll0, _x, a,
         x, x0, x1, x2, x3, x4, x5) ->
        let addr' = coq_Nplus addr0 x0 in
        let dest_addr = coq_N_of_word x3 in
        f11 n0 addr0 valid_addresses0 to_be_checked_addresses0 ll0 _x __ __ a
          __ x x0 x1 __ x2 __ x3 __ __ __ __ x4 x5
          (coq_R_validate_n_byte_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11
            f12 f13 f14 x2 addr' (coq_Nadd addr0 valid_addresses0)
            (coq_Nadd dest_addr to_be_checked_addresses0) x1 x4 x5)
    | R_validate_n_byte_13
        (n0, addr0, valid_addresses0, to_be_checked_addresses0, ll0, _x, a,
         x, x0, x1, x2) ->
        f12 n0 addr0 valid_addresses0 to_be_checked_addresses0 ll0 _x __ __ a
          __ x x0 x1 __ x2 __ __
    | R_validate_n_byte_14
        (n0, addr0, valid_addresses0, to_be_checked_addresses0, ll0, _x, a,
         x, x0, x1, x2, x3) ->
        f13 n0 addr0 valid_addresses0 to_be_checked_addresses0 ll0 _x __ __ a
          __ x x0 x1 __ x2 __ x3 __
    | R_validate_n_byte_15
        (n0, addr0, valid_addresses0, to_be_checked_addresses0, ll0, _x, e) ->
        f14 n0 addr0 valid_addresses0 to_be_checked_addresses0 ll0 _x __ __ e
          __
  
  (** val coq_R_validate_n_byte_rec :
      (coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte lazy_list -> __ -> 'a1)
      -> (coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte lazy_list -> coq_N
      -> __ -> __ -> ((I.instruction * coq_N) * byte lazy_list) -> __ ->
      I.instruction -> coq_N -> byte lazy_list -> __ -> __ -> 'a1) -> (coq_N
      -> coq_N -> coq_NSet -> coq_NSet -> byte lazy_list -> coq_N -> __ -> __
      -> ((I.instruction * coq_N) * byte lazy_list) -> __ -> I.instruction ->
      coq_N -> byte lazy_list -> __ -> coq_N -> __ -> __ ->
      ((coq_NSet * coq_NSet) * byte lazy_list) res -> coq_R_validate_n_byte
      -> 'a1 -> 'a1) -> (coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte
      lazy_list -> coq_N -> __ -> __ -> ((I.instruction * coq_N) * byte
      lazy_list) -> __ -> I.instruction -> coq_N -> byte lazy_list -> __ ->
      coq_N -> __ -> I.register -> word -> __ -> __ -> __ -> __ -> 'a1) ->
      (coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte lazy_list -> coq_N ->
      __ -> __ -> ((I.instruction * coq_N) * byte lazy_list) -> __ ->
      I.instruction -> coq_N -> byte lazy_list -> __ -> coq_N -> __ ->
      I.register -> word -> __ -> __ -> __ -> coq_N -> __ -> __ ->
      ((I.instruction * coq_N) * byte lazy_list) -> __ -> I.instruction ->
      coq_N -> byte lazy_list -> __ -> I.register -> __ -> __ -> __ -> __ ->
      'a1) -> (coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte lazy_list ->
      coq_N -> __ -> __ -> ((I.instruction * coq_N) * byte lazy_list) -> __
      -> I.instruction -> coq_N -> byte lazy_list -> __ -> coq_N -> __ ->
      I.register -> word -> __ -> __ -> __ -> coq_N -> __ -> __ ->
      ((I.instruction * coq_N) * byte lazy_list) -> __ -> I.instruction ->
      coq_N -> byte lazy_list -> __ -> I.register -> __ -> __ -> __ -> coq_N
      -> __ -> ((coq_NSet * coq_NSet) * byte lazy_list) res ->
      coq_R_validate_n_byte -> 'a1 -> 'a1) -> (coq_N -> coq_N -> coq_NSet ->
      coq_NSet -> byte lazy_list -> coq_N -> __ -> __ ->
      ((I.instruction * coq_N) * byte lazy_list) -> __ -> I.instruction ->
      coq_N -> byte lazy_list -> __ -> coq_N -> __ -> I.register -> word ->
      __ -> __ -> __ -> coq_N -> __ -> __ -> ((I.instruction * coq_N) * byte
      lazy_list) -> __ -> I.instruction -> coq_N -> byte lazy_list -> __ ->
      I.register -> __ -> __ -> __ -> 'a1) -> (coq_N -> coq_N -> coq_NSet ->
      coq_NSet -> byte lazy_list -> coq_N -> __ -> __ ->
      ((I.instruction * coq_N) * byte lazy_list) -> __ -> I.instruction ->
      coq_N -> byte lazy_list -> __ -> coq_N -> __ -> I.register -> word ->
      __ -> __ -> __ -> coq_N -> __ -> __ -> ((I.instruction * coq_N) * byte
      lazy_list) -> __ -> I.instruction -> coq_N -> byte lazy_list -> __ ->
      I.register instruction_classification -> __ -> __ ->
      ((coq_NSet * coq_NSet) * byte lazy_list) res -> coq_R_validate_n_byte
      -> 'a1 -> 'a1) -> (coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte
      lazy_list -> coq_N -> __ -> __ -> ((I.instruction * coq_N) * byte
      lazy_list) -> __ -> I.instruction -> coq_N -> byte lazy_list -> __ ->
      coq_N -> __ -> I.register -> word -> __ -> __ -> __ -> coq_N -> __ ->
      __ -> string -> __ -> 'a1) -> (coq_N -> coq_N -> coq_NSet -> coq_NSet
      -> byte lazy_list -> coq_N -> __ -> __ ->
      ((I.instruction * coq_N) * byte lazy_list) -> __ -> I.instruction ->
      coq_N -> byte lazy_list -> __ -> coq_N -> __ -> I.register -> word ->
      __ -> __ -> __ -> ((coq_NSet * coq_NSet) * byte lazy_list) res ->
      coq_R_validate_n_byte -> 'a1 -> 'a1) -> (coq_N -> coq_N -> coq_NSet ->
      coq_NSet -> byte lazy_list -> coq_N -> __ -> __ ->
      ((I.instruction * coq_N) * byte lazy_list) -> __ -> I.instruction ->
      coq_N -> byte lazy_list -> __ -> coq_N -> __ -> word -> __ -> __ -> __
      -> ((coq_NSet * coq_NSet) * byte lazy_list) res ->
      coq_R_validate_n_byte -> 'a1 -> 'a1) -> (coq_N -> coq_N -> coq_NSet ->
      coq_NSet -> byte lazy_list -> coq_N -> __ -> __ ->
      ((I.instruction * coq_N) * byte lazy_list) -> __ -> I.instruction ->
      coq_N -> byte lazy_list -> __ -> coq_N -> __ -> word -> __ -> __ -> __
      -> __ -> ((coq_NSet * coq_NSet) * byte lazy_list) res ->
      coq_R_validate_n_byte -> 'a1 -> 'a1) -> (coq_N -> coq_N -> coq_NSet ->
      coq_NSet -> byte lazy_list -> coq_N -> __ -> __ ->
      ((I.instruction * coq_N) * byte lazy_list) -> __ -> I.instruction ->
      coq_N -> byte lazy_list -> __ -> coq_N -> __ -> word -> __ -> __ -> __
      -> __ -> ((coq_NSet * coq_NSet) * byte lazy_list) res ->
      coq_R_validate_n_byte -> 'a1 -> 'a1) -> (coq_N -> coq_N -> coq_NSet ->
      coq_NSet -> byte lazy_list -> coq_N -> __ -> __ ->
      ((I.instruction * coq_N) * byte lazy_list) -> __ -> I.instruction ->
      coq_N -> byte lazy_list -> __ -> coq_N -> __ -> __ -> 'a1) -> (coq_N ->
      coq_N -> coq_NSet -> coq_NSet -> byte lazy_list -> coq_N -> __ -> __ ->
      ((I.instruction * coq_N) * byte lazy_list) -> __ -> I.instruction ->
      coq_N -> byte lazy_list -> __ -> coq_N -> __ -> I.register -> __ ->
      'a1) -> (coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte lazy_list ->
      coq_N -> __ -> __ -> string -> __ -> 'a1) -> coq_N -> coq_N -> coq_NSet
      -> coq_NSet -> byte lazy_list -> ((coq_NSet * coq_NSet) * byte
      lazy_list) res -> coq_R_validate_n_byte -> 'a1 **)
  
  let rec coq_R_validate_n_byte_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 n addr valid_addresses to_be_checked_addresses ll r = function
    | R_validate_n_byte_0
        (n0, addr0, valid_addresses0, to_be_checked_addresses0, ll0) ->
        f n0 addr0 valid_addresses0 to_be_checked_addresses0 ll0 __
    | R_validate_n_byte_1
        (n0, addr0, valid_addresses0, to_be_checked_addresses0, ll0, _x, a,
         x, x0, x1) ->
        f0 n0 addr0 valid_addresses0 to_be_checked_addresses0 ll0 _x __ __ a
          __ x x0 x1 __ __
    | R_validate_n_byte_2
        (n0, addr0, valid_addresses0, to_be_checked_addresses0, ll0, _x, a,
         x, x0, x1, x2, x3, x4) ->
        let addr' = coq_Nplus addr0 x0 in
        f1 n0 addr0 valid_addresses0 to_be_checked_addresses0 ll0 _x __ __ a
          __ x x0 x1 __ x2 __ __ x3 x4
          (coq_R_validate_n_byte_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11
            f12 f13 f14 x2 addr' (coq_Nadd addr0 valid_addresses0)
            to_be_checked_addresses0 x1 x3 x4)
    | R_validate_n_byte_3
        (n0, addr0, valid_addresses0, to_be_checked_addresses0, ll0, _x, a,
         x, x0, x1, x2, x3, x4) ->
        f2 n0 addr0 valid_addresses0 to_be_checked_addresses0 ll0 _x __ __ a
          __ x x0 x1 __ x2 __ x3 x4 __ __ __ __
    | R_validate_n_byte_4
        (n0, addr0, valid_addresses0, to_be_checked_addresses0, ll0, _x, a,
         x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10) ->
        f3 n0 addr0 valid_addresses0 to_be_checked_addresses0 ll0 _x __ __ a
          __ x x0 x1 __ x2 __ x3 x4 __ __ __ x5 __ __ x6 __ x7 x8 x9 __ x10
          __ __ __ __
    | R_validate_n_byte_5
        (n0, addr0, valid_addresses0, to_be_checked_addresses0, ll0, _x, a,
         x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13) ->
        let addr' = coq_Nplus addr0 x0 in
        let addr'' = coq_Nplus addr' x8 in
        f4 n0 addr0 valid_addresses0 to_be_checked_addresses0 ll0 _x __ __ a
          __ x x0 x1 __ x2 __ x3 x4 __ __ __ x5 __ __ x6 __ x7 x8 x9 __ x10
          __ __ __ x11 __ x12 x13
          (coq_R_validate_n_byte_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11
            f12 f13 f14 x11 addr'' (coq_Nadd addr0 valid_addresses0)
            to_be_checked_addresses0 x9 x12 x13)
    | R_validate_n_byte_6
        (n0, addr0, valid_addresses0, to_be_checked_addresses0, ll0, _x, a,
         x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10) ->
        f5 n0 addr0 valid_addresses0 to_be_checked_addresses0 ll0 _x __ __ a
          __ x x0 x1 __ x2 __ x3 x4 __ __ __ x5 __ __ x6 __ x7 x8 x9 __ x10
          __ __ __
    | R_validate_n_byte_7
        (n0, addr0, valid_addresses0, to_be_checked_addresses0, ll0, _x, a,
         x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12) ->
        let addr' = coq_Nplus addr0 x0 in
        f6 n0 addr0 valid_addresses0 to_be_checked_addresses0 ll0 _x __ __ a
          __ x x0 x1 __ x2 __ x3 x4 __ __ __ x5 __ __ x6 __ x7 x8 x9 __ x10
          __ __ x11 x12
          (coq_R_validate_n_byte_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11
            f12 f13 f14 x2 addr' (coq_Nadd addr0 valid_addresses0)
            to_be_checked_addresses0 x1 x11 x12)
    | R_validate_n_byte_8
        (n0, addr0, valid_addresses0, to_be_checked_addresses0, ll0, _x, a,
         x, x0, x1, x2, x3, x4, x5, x6) ->
        f7 n0 addr0 valid_addresses0 to_be_checked_addresses0 ll0 _x __ __ a
          __ x x0 x1 __ x2 __ x3 x4 __ __ __ x5 __ __ x6 __
    | R_validate_n_byte_9
        (n0, addr0, valid_addresses0, to_be_checked_addresses0, ll0, _x, a,
         x, x0, x1, x2, x3, x4, x5, x6) ->
        let addr' = coq_Nplus addr0 x0 in
        f8 n0 addr0 valid_addresses0 to_be_checked_addresses0 ll0 _x __ __ a
          __ x x0 x1 __ x2 __ x3 x4 __ __ __ x5 x6
          (coq_R_validate_n_byte_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11
            f12 f13 f14 x2 addr' (coq_Nadd addr0 valid_addresses0)
            to_be_checked_addresses0 x1 x5 x6)
    | R_validate_n_byte_10
        (n0, addr0, valid_addresses0, to_be_checked_addresses0, ll0, _x, a,
         x, x0, x1, x2, x3, x4, x5) ->
        let addr' = coq_Nplus addr0 x0 in
        f9 n0 addr0 valid_addresses0 to_be_checked_addresses0 ll0 _x __ __ a
          __ x x0 x1 __ x2 __ x3 __ __ __ x4 x5
          (coq_R_validate_n_byte_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11
            f12 f13 f14 x2 addr' (coq_Nadd addr0 valid_addresses0)
            to_be_checked_addresses0 x1 x4 x5)
    | R_validate_n_byte_11
        (n0, addr0, valid_addresses0, to_be_checked_addresses0, ll0, _x, a,
         x, x0, x1, x2, x3, x4, x5) ->
        let addr' = coq_Nplus addr0 x0 in
        f10 n0 addr0 valid_addresses0 to_be_checked_addresses0 ll0 _x __ __ a
          __ x x0 x1 __ x2 __ x3 __ __ __ __ x4 x5
          (coq_R_validate_n_byte_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11
            f12 f13 f14 x2 addr' (coq_Nadd addr0 valid_addresses0)
            to_be_checked_addresses0 x1 x4 x5)
    | R_validate_n_byte_12
        (n0, addr0, valid_addresses0, to_be_checked_addresses0, ll0, _x, a,
         x, x0, x1, x2, x3, x4, x5) ->
        let addr' = coq_Nplus addr0 x0 in
        let dest_addr = coq_N_of_word x3 in
        f11 n0 addr0 valid_addresses0 to_be_checked_addresses0 ll0 _x __ __ a
          __ x x0 x1 __ x2 __ x3 __ __ __ __ x4 x5
          (coq_R_validate_n_byte_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11
            f12 f13 f14 x2 addr' (coq_Nadd addr0 valid_addresses0)
            (coq_Nadd dest_addr to_be_checked_addresses0) x1 x4 x5)
    | R_validate_n_byte_13
        (n0, addr0, valid_addresses0, to_be_checked_addresses0, ll0, _x, a,
         x, x0, x1, x2) ->
        f12 n0 addr0 valid_addresses0 to_be_checked_addresses0 ll0 _x __ __ a
          __ x x0 x1 __ x2 __ __
    | R_validate_n_byte_14
        (n0, addr0, valid_addresses0, to_be_checked_addresses0, ll0, _x, a,
         x, x0, x1, x2, x3) ->
        f13 n0 addr0 valid_addresses0 to_be_checked_addresses0 ll0 _x __ __ a
          __ x x0 x1 __ x2 __ x3 __
    | R_validate_n_byte_15
        (n0, addr0, valid_addresses0, to_be_checked_addresses0, ll0, _x, e) ->
        f14 n0 addr0 valid_addresses0 to_be_checked_addresses0 ll0 _x __ __ e
          __
  
  (** val validate_n_byte_rect :
      (coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte lazy_list -> __ -> 'a1)
      -> (coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte lazy_list -> coq_N
      -> __ -> __ -> ((I.instruction * coq_N) * byte lazy_list) -> __ ->
      I.instruction -> coq_N -> byte lazy_list -> __ -> __ -> 'a1) -> (coq_N
      -> coq_N -> coq_NSet -> coq_NSet -> byte lazy_list -> coq_N -> __ -> __
      -> ((I.instruction * coq_N) * byte lazy_list) -> __ -> I.instruction ->
      coq_N -> byte lazy_list -> __ -> coq_N -> __ -> __ -> 'a1 -> 'a1) ->
      (coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte lazy_list -> coq_N ->
      __ -> __ -> ((I.instruction * coq_N) * byte lazy_list) -> __ ->
      I.instruction -> coq_N -> byte lazy_list -> __ -> coq_N -> __ ->
      I.register -> word -> __ -> __ -> __ -> __ -> 'a1) -> (coq_N -> coq_N
      -> coq_NSet -> coq_NSet -> byte lazy_list -> coq_N -> __ -> __ ->
      ((I.instruction * coq_N) * byte lazy_list) -> __ -> I.instruction ->
      coq_N -> byte lazy_list -> __ -> coq_N -> __ -> I.register -> word ->
      __ -> __ -> __ -> coq_N -> __ -> __ -> ((I.instruction * coq_N) * byte
      lazy_list) -> __ -> I.instruction -> coq_N -> byte lazy_list -> __ ->
      I.register -> __ -> __ -> __ -> __ -> 'a1) -> (coq_N -> coq_N ->
      coq_NSet -> coq_NSet -> byte lazy_list -> coq_N -> __ -> __ ->
      ((I.instruction * coq_N) * byte lazy_list) -> __ -> I.instruction ->
      coq_N -> byte lazy_list -> __ -> coq_N -> __ -> I.register -> word ->
      __ -> __ -> __ -> coq_N -> __ -> __ -> ((I.instruction * coq_N) * byte
      lazy_list) -> __ -> I.instruction -> coq_N -> byte lazy_list -> __ ->
      I.register -> __ -> __ -> __ -> coq_N -> __ -> 'a1 -> 'a1) -> (coq_N ->
      coq_N -> coq_NSet -> coq_NSet -> byte lazy_list -> coq_N -> __ -> __ ->
      ((I.instruction * coq_N) * byte lazy_list) -> __ -> I.instruction ->
      coq_N -> byte lazy_list -> __ -> coq_N -> __ -> I.register -> word ->
      __ -> __ -> __ -> coq_N -> __ -> __ -> ((I.instruction * coq_N) * byte
      lazy_list) -> __ -> I.instruction -> coq_N -> byte lazy_list -> __ ->
      I.register -> __ -> __ -> __ -> 'a1) -> (coq_N -> coq_N -> coq_NSet ->
      coq_NSet -> byte lazy_list -> coq_N -> __ -> __ ->
      ((I.instruction * coq_N) * byte lazy_list) -> __ -> I.instruction ->
      coq_N -> byte lazy_list -> __ -> coq_N -> __ -> I.register -> word ->
      __ -> __ -> __ -> coq_N -> __ -> __ -> ((I.instruction * coq_N) * byte
      lazy_list) -> __ -> I.instruction -> coq_N -> byte lazy_list -> __ ->
      I.register instruction_classification -> __ -> __ -> 'a1 -> 'a1) ->
      (coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte lazy_list -> coq_N ->
      __ -> __ -> ((I.instruction * coq_N) * byte lazy_list) -> __ ->
      I.instruction -> coq_N -> byte lazy_list -> __ -> coq_N -> __ ->
      I.register -> word -> __ -> __ -> __ -> coq_N -> __ -> __ -> string ->
      __ -> 'a1) -> (coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte lazy_list
      -> coq_N -> __ -> __ -> ((I.instruction * coq_N) * byte lazy_list) ->
      __ -> I.instruction -> coq_N -> byte lazy_list -> __ -> coq_N -> __ ->
      I.register -> word -> __ -> __ -> __ -> 'a1 -> 'a1) -> (coq_N -> coq_N
      -> coq_NSet -> coq_NSet -> byte lazy_list -> coq_N -> __ -> __ ->
      ((I.instruction * coq_N) * byte lazy_list) -> __ -> I.instruction ->
      coq_N -> byte lazy_list -> __ -> coq_N -> __ -> word -> __ -> __ -> __
      -> 'a1 -> 'a1) -> (coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte
      lazy_list -> coq_N -> __ -> __ -> ((I.instruction * coq_N) * byte
      lazy_list) -> __ -> I.instruction -> coq_N -> byte lazy_list -> __ ->
      coq_N -> __ -> word -> __ -> __ -> __ -> __ -> 'a1 -> 'a1) -> (coq_N ->
      coq_N -> coq_NSet -> coq_NSet -> byte lazy_list -> coq_N -> __ -> __ ->
      ((I.instruction * coq_N) * byte lazy_list) -> __ -> I.instruction ->
      coq_N -> byte lazy_list -> __ -> coq_N -> __ -> word -> __ -> __ -> __
      -> __ -> 'a1 -> 'a1) -> (coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte
      lazy_list -> coq_N -> __ -> __ -> ((I.instruction * coq_N) * byte
      lazy_list) -> __ -> I.instruction -> coq_N -> byte lazy_list -> __ ->
      coq_N -> __ -> __ -> 'a1) -> (coq_N -> coq_N -> coq_NSet -> coq_NSet ->
      byte lazy_list -> coq_N -> __ -> __ -> ((I.instruction * coq_N) * byte
      lazy_list) -> __ -> I.instruction -> coq_N -> byte lazy_list -> __ ->
      coq_N -> __ -> I.register -> __ -> 'a1) -> (coq_N -> coq_N -> coq_NSet
      -> coq_NSet -> byte lazy_list -> coq_N -> __ -> __ -> string -> __ ->
      'a1) -> coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte lazy_list -> 'a1 **)
  
  let rec validate_n_byte_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 n addr valid_addresses to_be_checked_addresses ll =
    let f15 = f14 n addr valid_addresses to_be_checked_addresses ll in
    let f16 = f13 n addr valid_addresses to_be_checked_addresses ll in
    let f17 = f12 n addr valid_addresses to_be_checked_addresses ll in
    let f18 = f11 n addr valid_addresses to_be_checked_addresses ll in
    let f19 = f10 n addr valid_addresses to_be_checked_addresses ll in
    let f20 = f9 n addr valid_addresses to_be_checked_addresses ll in
    let f21 = f8 n addr valid_addresses to_be_checked_addresses ll in
    let f22 = f7 n addr valid_addresses to_be_checked_addresses ll in
    let f23 = f6 n addr valid_addresses to_be_checked_addresses ll in
    let f24 = f5 n addr valid_addresses to_be_checked_addresses ll in
    let f25 = f4 n addr valid_addresses to_be_checked_addresses ll in
    let f26 = f3 n addr valid_addresses to_be_checked_addresses ll in
    let f27 = f2 n addr valid_addresses to_be_checked_addresses ll in
    let f28 = f1 n addr valid_addresses to_be_checked_addresses ll in
    let f29 = f0 n addr valid_addresses to_be_checked_addresses ll in
    let f30 = f n addr valid_addresses to_be_checked_addresses ll in
    (match n with
       | N0 -> f30 __
       | Npos p ->
           let f31 = let _x = Npos p in f29 _x __ in
           let f32 = f31 __ in
           let f33 = let _x = Npos p in f28 _x __ in
           let f34 = f33 __ in
           let f35 = let _x = Npos p in f27 _x __ in
           let f36 = f35 __ in
           let f37 = let _x = Npos p in f26 _x __ in
           let f38 = f37 __ in
           let f39 = let _x = Npos p in f25 _x __ in
           let f40 = f39 __ in
           let f41 = let _x = Npos p in f24 _x __ in
           let f42 = f41 __ in
           let f43 = let _x = Npos p in f23 _x __ in
           let f44 = f43 __ in
           let f45 = let _x = Npos p in f22 _x __ in
           let f46 = f45 __ in
           let f47 = let _x = Npos p in f21 _x __ in
           let f48 = f47 __ in
           let f49 = let _x = Npos p in f20 _x __ in
           let f50 = f49 __ in
           let f51 = let _x = Npos p in f19 _x __ in
           let f52 = f51 __ in
           let f53 = let _x = Npos p in f18 _x __ in
           let f54 = f53 __ in
           let f55 = let _x = Npos p in f17 _x __ in
           let f56 = f55 __ in
           let f57 = let _x = Npos p in f16 _x __ in
           let f58 = f57 __ in
           let f59 = let _x = Npos p in f15 _x __ in
           let f60 = f59 __ in
           (match I.parse_instruction addr ll with
              | OK p0 ->
                  let f61 = f58 p0 __ in
                  let f62 = f56 p0 __ in
                  let f63 = f54 p0 __ in
                  let f64 = f52 p0 __ in
                  let f65 = f50 p0 __ in
                  let f66 = f48 p0 __ in
                  let f67 = f46 p0 __ in
                  let f68 = f44 p0 __ in
                  let f69 = f42 p0 __ in
                  let f70 = f40 p0 __ in
                  let f71 = f38 p0 __ in
                  let f72 = f36 p0 __ in
                  let f73 = f34 p0 __ in
                  let f74 = f32 p0 __ in
                  let (p1, l) = p0 in
                  let (i, n0) = p1 in
                  let f75 = f61 i n0 l __ in
                  let f76 = f62 i n0 l __ in
                  let f77 = f63 i n0 l __ in
                  let f78 = f64 i n0 l __ in
                  let f79 = f65 i n0 l __ in
                  let f80 = f66 i n0 l __ in
                  let f81 = f67 i n0 l __ in
                  let f82 = f68 i n0 l __ in
                  let f83 = f69 i n0 l __ in
                  let f84 = f70 i n0 l __ in
                  let f85 = f71 i n0 l __ in
                  let f86 = f72 i n0 l __ in
                  let f87 = f73 i n0 l __ in
                  let f88 = f74 i n0 l __ in
                  (match safe_minus (Npos p) n0 with
                     | Some n1 ->
                         let f89 = f87 n1 __ in
                         let f90 = f86 n1 __ in
                         let f91 = f85 n1 __ in
                         let f92 = fun reg1 w -> f91 reg1 w __ __ __ n1 __ in
                         let f93 = f84 n1 __ in
                         let f94 = fun reg1 w -> f93 reg1 w __ __ __ n1 __ in
                         let f95 = f83 n1 __ in
                         let f96 = fun reg1 w -> f95 reg1 w __ __ __ n1 __ in
                         let f97 = f82 n1 __ in
                         let f98 = fun reg1 w -> f97 reg1 w __ __ __ n1 __ in
                         let f99 = f81 n1 __ in
                         let f100 = fun reg1 w -> f99 reg1 w __ __ __ n1 __
                         in
                         let f101 = f80 n1 __ in
                         let f102 = f79 n1 __ in
                         let f103 = f78 n1 __ in
                         let f104 = f77 n1 __ in
                         let f105 = f76 n1 __ in
                         let f106 = f75 n1 __ in
                         (match I.classify_instruction i with
                            | OK_instr ->
                                let f107 = f89 __ in
                                let hrec =
                                  validate_n_byte_rect f f0 f1 f2 f3 f4 f5 f6
                                    f7 f8 f9 f10 f11 f12 f13 f14 n1
                                    (coq_Nplus addr n0)
                                    (coq_Nadd addr valid_addresses)
                                    to_be_checked_addresses l
                                in
                                f107 hrec
                            | Mask_instr (r, w) ->
                                let f107 = f101 r w __ in
                                let f108 = fun _ _ -> f100 r w in
                                let f109 = fun _ _ -> f98 r w in
                                let f110 = fun _ _ -> f96 r w in
                                let f111 = fun _ _ -> f94 r w in
                                let f112 = fun _ _ -> f92 r w in
                                let f113 = f90 r w __ in
                                if word_eq_dec w proper_mask
                                then let f114 = f113 __ __ in
                                     let f115 = f112 __ __ in
                                     let f116 = f111 __ __ in
                                     let f117 = f110 __ __ in
                                     let f118 = f109 __ __ in
                                     let f119 = f108 __ __ in
                                     (match n1 with
                                        | N0 -> f114 __
                                        | Npos p2 ->
                                            let f120 = f119 __ in
                                            let f121 = f118 __ in
                                            let f122 = f117 __ in
                                            let f123 = f116 __ in
                                            let f124 = f115 __ in
                                            (match 
                                             I.parse_instruction
                                               (coq_Nplus addr n0) l with
                                               | OK p3 ->
                                                  let f125 = f124 p3 __ in
                                                  let f126 = f123 p3 __ in
                                                  let f127 = f122 p3 __ in
                                                  let f128 = f121 p3 __ in
                                                  let (p4, l0) = p3 in
                                                  let (i0, n2) = p4 in
                                                  let f129 = f125 i0 n2 l0 __
                                                  in
                                                  let f130 = f126 i0 n2 l0 __
                                                  in
                                                  let f131 = f127 i0 n2 l0 __
                                                  in
                                                  let f132 = f128 i0 n2 l0 __
                                                  in
                                                  let f133 =
                                                  let _x2 =
                                                  I.classify_instruction i0
                                                  in
                                                  f132 _x2 __
                                                  in
                                                  (
                                                  match 
                                                  I.classify_instruction i0 with
                                                    | 
                                                  Indirect_jump r0 ->
                                                  let f134 = f131 r0 __ in
                                                  let f135 = f130 r0 __ in
                                                  let f136 = f129 r0 __ in
                                                  if I.register_eq_dec r r0
                                                  then 
                                                  let f137 = f136 __ __ in
                                                  let f138 = f135 __ __ in
                                                  (
                                                  match 
                                                  safe_minus (Npos p2) n2 with
                                                    | 
                                                  Some n3 ->
                                                  let f139 = f138 n3 __ in
                                                  let hrec =
                                                  validate_n_byte_rect f f0
                                                  f1 f2 f3 f4 f5 f6 f7 f8 f9
                                                  f10 f11 f12 f13 f14 n3
                                                  (coq_Nplus
                                                  (coq_Nplus addr n0) n2)
                                                  (coq_Nadd addr
                                                  valid_addresses)
                                                  to_be_checked_addresses l0
                                                  in
                                                  f139 hrec
                                                    | 
                                                  None -> f137 __)
                                                  else f134 __ __
                                                    | 
                                                  _ ->
                                                  let f134 = f133 __ in
                                                  let hrec =
                                                  validate_n_byte_rect f f0
                                                  f1 f2 f3 f4 f5 f6 f7 f8 f9
                                                  f10 f11 f12 f13 f14 (Npos
                                                  p2) 
                                                  (coq_Nplus addr n0)
                                                  (coq_Nadd addr
                                                  valid_addresses)
                                                  to_be_checked_addresses l
                                                  in
                                                  f134 hrec)
                                               | Err s -> f120 s __))
                                else let f114 = f107 __ __ in
                                     let hrec =
                                       validate_n_byte_rect f f0 f1 f2 f3 f4
                                         f5 f6 f7 f8 f9 f10 f11 f12 f13 f14
                                         n1 (coq_Nplus addr n0)
                                         (coq_Nadd addr valid_addresses)
                                         to_be_checked_addresses l
                                     in
                                     f114 hrec
                            | Direct_jump w ->
                                let f107 = f104 w __ in
                                let f108 = f103 w __ in
                                let f109 = f102 w __ in
                                if dividable_by_32_dec (coq_N_of_word w)
                                then let f110 = f109 __ __ in
                                     let hrec =
                                       validate_n_byte_rect f f0 f1 f2 f3 f4
                                         f5 f6 f7 f8 f9 f10 f11 f12 f13 f14
                                         n1 (coq_Nplus addr n0)
                                         (coq_Nadd addr valid_addresses)
                                         to_be_checked_addresses l
                                     in
                                     f110 hrec
                                else let f110 = f108 __ __ in
                                     let f111 = f107 __ __ in
                                     if is_Nin (coq_N_of_word w)
                                          valid_addresses
                                     then let f112 = f110 __ in
                                          let hrec =
                                            validate_n_byte_rect f f0 f1 f2
                                              f3 f4 f5 f6 f7 f8 f9 f10 f11
                                              f12 f13 f14 n1
                                              (coq_Nplus addr n0)
                                              (coq_Nadd addr valid_addresses)
                                              to_be_checked_addresses l
                                          in
                                          f112 hrec
                                     else let f112 = f111 __ in
                                          let hrec =
                                            validate_n_byte_rect f f0 f1 f2
                                              f3 f4 f5 f6 f7 f8 f9 f10 f11
                                              f12 f13 f14 n1
                                              (coq_Nplus addr n0)
                                              (coq_Nadd addr valid_addresses)
                                              (coq_Nadd 
                                                (coq_N_of_word w)
                                                to_be_checked_addresses) l
                                          in
                                          f112 hrec
                            | Indirect_jump r -> f106 r __
                            | Invalid_instruction -> f105 __)
                     | None -> f88 __)
              | Err s -> f60 s __))
  
  (** val validate_n_byte_rec :
      (coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte lazy_list -> __ -> 'a1)
      -> (coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte lazy_list -> coq_N
      -> __ -> __ -> ((I.instruction * coq_N) * byte lazy_list) -> __ ->
      I.instruction -> coq_N -> byte lazy_list -> __ -> __ -> 'a1) -> (coq_N
      -> coq_N -> coq_NSet -> coq_NSet -> byte lazy_list -> coq_N -> __ -> __
      -> ((I.instruction * coq_N) * byte lazy_list) -> __ -> I.instruction ->
      coq_N -> byte lazy_list -> __ -> coq_N -> __ -> __ -> 'a1 -> 'a1) ->
      (coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte lazy_list -> coq_N ->
      __ -> __ -> ((I.instruction * coq_N) * byte lazy_list) -> __ ->
      I.instruction -> coq_N -> byte lazy_list -> __ -> coq_N -> __ ->
      I.register -> word -> __ -> __ -> __ -> __ -> 'a1) -> (coq_N -> coq_N
      -> coq_NSet -> coq_NSet -> byte lazy_list -> coq_N -> __ -> __ ->
      ((I.instruction * coq_N) * byte lazy_list) -> __ -> I.instruction ->
      coq_N -> byte lazy_list -> __ -> coq_N -> __ -> I.register -> word ->
      __ -> __ -> __ -> coq_N -> __ -> __ -> ((I.instruction * coq_N) * byte
      lazy_list) -> __ -> I.instruction -> coq_N -> byte lazy_list -> __ ->
      I.register -> __ -> __ -> __ -> __ -> 'a1) -> (coq_N -> coq_N ->
      coq_NSet -> coq_NSet -> byte lazy_list -> coq_N -> __ -> __ ->
      ((I.instruction * coq_N) * byte lazy_list) -> __ -> I.instruction ->
      coq_N -> byte lazy_list -> __ -> coq_N -> __ -> I.register -> word ->
      __ -> __ -> __ -> coq_N -> __ -> __ -> ((I.instruction * coq_N) * byte
      lazy_list) -> __ -> I.instruction -> coq_N -> byte lazy_list -> __ ->
      I.register -> __ -> __ -> __ -> coq_N -> __ -> 'a1 -> 'a1) -> (coq_N ->
      coq_N -> coq_NSet -> coq_NSet -> byte lazy_list -> coq_N -> __ -> __ ->
      ((I.instruction * coq_N) * byte lazy_list) -> __ -> I.instruction ->
      coq_N -> byte lazy_list -> __ -> coq_N -> __ -> I.register -> word ->
      __ -> __ -> __ -> coq_N -> __ -> __ -> ((I.instruction * coq_N) * byte
      lazy_list) -> __ -> I.instruction -> coq_N -> byte lazy_list -> __ ->
      I.register -> __ -> __ -> __ -> 'a1) -> (coq_N -> coq_N -> coq_NSet ->
      coq_NSet -> byte lazy_list -> coq_N -> __ -> __ ->
      ((I.instruction * coq_N) * byte lazy_list) -> __ -> I.instruction ->
      coq_N -> byte lazy_list -> __ -> coq_N -> __ -> I.register -> word ->
      __ -> __ -> __ -> coq_N -> __ -> __ -> ((I.instruction * coq_N) * byte
      lazy_list) -> __ -> I.instruction -> coq_N -> byte lazy_list -> __ ->
      I.register instruction_classification -> __ -> __ -> 'a1 -> 'a1) ->
      (coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte lazy_list -> coq_N ->
      __ -> __ -> ((I.instruction * coq_N) * byte lazy_list) -> __ ->
      I.instruction -> coq_N -> byte lazy_list -> __ -> coq_N -> __ ->
      I.register -> word -> __ -> __ -> __ -> coq_N -> __ -> __ -> string ->
      __ -> 'a1) -> (coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte lazy_list
      -> coq_N -> __ -> __ -> ((I.instruction * coq_N) * byte lazy_list) ->
      __ -> I.instruction -> coq_N -> byte lazy_list -> __ -> coq_N -> __ ->
      I.register -> word -> __ -> __ -> __ -> 'a1 -> 'a1) -> (coq_N -> coq_N
      -> coq_NSet -> coq_NSet -> byte lazy_list -> coq_N -> __ -> __ ->
      ((I.instruction * coq_N) * byte lazy_list) -> __ -> I.instruction ->
      coq_N -> byte lazy_list -> __ -> coq_N -> __ -> word -> __ -> __ -> __
      -> 'a1 -> 'a1) -> (coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte
      lazy_list -> coq_N -> __ -> __ -> ((I.instruction * coq_N) * byte
      lazy_list) -> __ -> I.instruction -> coq_N -> byte lazy_list -> __ ->
      coq_N -> __ -> word -> __ -> __ -> __ -> __ -> 'a1 -> 'a1) -> (coq_N ->
      coq_N -> coq_NSet -> coq_NSet -> byte lazy_list -> coq_N -> __ -> __ ->
      ((I.instruction * coq_N) * byte lazy_list) -> __ -> I.instruction ->
      coq_N -> byte lazy_list -> __ -> coq_N -> __ -> word -> __ -> __ -> __
      -> __ -> 'a1 -> 'a1) -> (coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte
      lazy_list -> coq_N -> __ -> __ -> ((I.instruction * coq_N) * byte
      lazy_list) -> __ -> I.instruction -> coq_N -> byte lazy_list -> __ ->
      coq_N -> __ -> __ -> 'a1) -> (coq_N -> coq_N -> coq_NSet -> coq_NSet ->
      byte lazy_list -> coq_N -> __ -> __ -> ((I.instruction * coq_N) * byte
      lazy_list) -> __ -> I.instruction -> coq_N -> byte lazy_list -> __ ->
      coq_N -> __ -> I.register -> __ -> 'a1) -> (coq_N -> coq_N -> coq_NSet
      -> coq_NSet -> byte lazy_list -> coq_N -> __ -> __ -> string -> __ ->
      'a1) -> coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte lazy_list -> 'a1 **)
  
  let validate_n_byte_rec =
    validate_n_byte_rect
  
  (** val coq_R_validate_n_byte_correct :
      coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte lazy_list ->
      ((coq_NSet * coq_NSet) * byte lazy_list) res -> coq_R_validate_n_byte **)
  
  let coq_R_validate_n_byte_correct x x0 x1 x2 x3 res0 =
    validate_n_byte_rect (fun y y0 y1 y2 y3 _ z _ -> R_validate_n_byte_0 (y,
      y0, y1, y2, y3)) (fun y y0 y1 y2 y3 y4 _ _ y7 _ y9 y10 y11 _ _ z _ ->
      R_validate_n_byte_1 (y, y0, y1, y2, y3, y4, y7, y9, y10, y11))
      (fun y y0 y1 y2 y3 y4 _ _ y7 _ y9 y10 y11 _ y13 _ _ y16 z _ ->
      R_validate_n_byte_2 (y, y0, y1, y2, y3, y4, y7, y9, y10, y11, y13,
      (validate_n_byte y13 (coq_Nplus y0 y10) (coq_Nadd y0 y1) y2 y11),
      (y16 (validate_n_byte y13 (coq_Nplus y0 y10) (coq_Nadd y0 y1) y2 y11)
        __)))
      (fun y y0 y1 y2 y3 y4 _ _ y7 _ y9 y10 y11 _ y13 _ y15 y16 _ _ _ _ z _ ->
      R_validate_n_byte_3 (y, y0, y1, y2, y3, y4, y7, y9, y10, y11, y13, y15,
      y16))
      (fun y y0 y1 y2 y3 y4 _ _ y7 _ y9 y10 y11 _ y13 _ y15 y16 _ _ _ y20 _ _ y23 _ y25 y26 y27 _ y29 _ _ _ _ z _ ->
      R_validate_n_byte_4 (y, y0, y1, y2, y3, y4, y7, y9, y10, y11, y13, y15,
      y16, y20, y23, y25, y26, y27, y29))
      (fun y y0 y1 y2 y3 y4 _ _ y7 _ y9 y10 y11 _ y13 _ y15 y16 _ _ _ y20 _ _ y23 _ y25 y26 y27 _ y29 _ _ _ y33 _ y35 z _ ->
      R_validate_n_byte_5 (y, y0, y1, y2, y3, y4, y7, y9, y10, y11, y13, y15,
      y16, y20, y23, y25, y26, y27, y29, y33,
      (validate_n_byte y33 (coq_Nplus (coq_Nplus y0 y10) y26)
        (coq_Nadd y0 y1) y2 y27),
      (y35
        (validate_n_byte y33 (coq_Nplus (coq_Nplus y0 y10) y26)
          (coq_Nadd y0 y1) y2 y27) __)))
      (fun y y0 y1 y2 y3 y4 _ _ y7 _ y9 y10 y11 _ y13 _ y15 y16 _ _ _ y20 _ _ y23 _ y25 y26 y27 _ y29 _ _ _ z _ ->
      R_validate_n_byte_6 (y, y0, y1, y2, y3, y4, y7, y9, y10, y11, y13, y15,
      y16, y20, y23, y25, y26, y27, y29))
      (fun y y0 y1 y2 y3 y4 _ _ y7 _ y9 y10 y11 _ y13 _ y15 y16 _ _ _ y20 _ _ y23 _ y25 y26 y27 _ y29 _ _ y32 z _ ->
      R_validate_n_byte_7 (y, y0, y1, y2, y3, y4, y7, y9, y10, y11, y13, y15,
      y16, y20, y23, y25, y26, y27, y29,
      (validate_n_byte y13 (coq_Nplus y0 y10) (coq_Nadd y0 y1) y2 y11),
      (y32 (validate_n_byte y13 (coq_Nplus y0 y10) (coq_Nadd y0 y1) y2 y11)
        __)))
      (fun y y0 y1 y2 y3 y4 _ _ y7 _ y9 y10 y11 _ y13 _ y15 y16 _ _ _ y20 _ _ y23 _ z _ ->
      R_validate_n_byte_8 (y, y0, y1, y2, y3, y4, y7, y9, y10, y11, y13, y15,
      y16, y20, y23))
      (fun y y0 y1 y2 y3 y4 _ _ y7 _ y9 y10 y11 _ y13 _ y15 y16 _ _ _ y20 z _ ->
      R_validate_n_byte_9 (y, y0, y1, y2, y3, y4, y7, y9, y10, y11, y13, y15,
      y16, (validate_n_byte y13 (coq_Nplus y0 y10) (coq_Nadd y0 y1) y2 y11),
      (y20 (validate_n_byte y13 (coq_Nplus y0 y10) (coq_Nadd y0 y1) y2 y11)
        __)))
      (fun y y0 y1 y2 y3 y4 _ _ y7 _ y9 y10 y11 _ y13 _ y15 _ _ _ y19 z _ ->
      R_validate_n_byte_10 (y, y0, y1, y2, y3, y4, y7, y9, y10, y11, y13,
      y15, (validate_n_byte y13 (coq_Nplus y0 y10) (coq_Nadd y0 y1) y2 y11),
      (y19 (validate_n_byte y13 (coq_Nplus y0 y10) (coq_Nadd y0 y1) y2 y11)
        __)))
      (fun y y0 y1 y2 y3 y4 _ _ y7 _ y9 y10 y11 _ y13 _ y15 _ _ _ _ y20 z _ ->
      R_validate_n_byte_11 (y, y0, y1, y2, y3, y4, y7, y9, y10, y11, y13,
      y15, (validate_n_byte y13 (coq_Nplus y0 y10) (coq_Nadd y0 y1) y2 y11),
      (y20 (validate_n_byte y13 (coq_Nplus y0 y10) (coq_Nadd y0 y1) y2 y11)
        __)))
      (fun y y0 y1 y2 y3 y4 _ _ y7 _ y9 y10 y11 _ y13 _ y15 _ _ _ _ y20 z _ ->
      R_validate_n_byte_12 (y, y0, y1, y2, y3, y4, y7, y9, y10, y11, y13,
      y15,
      (validate_n_byte y13 (coq_Nplus y0 y10) (coq_Nadd y0 y1)
        (coq_Nadd (coq_N_of_word y15) y2) y11),
      (y20
        (validate_n_byte y13 (coq_Nplus y0 y10) (coq_Nadd y0 y1)
          (coq_Nadd (coq_N_of_word y15) y2) y11) __)))
      (fun y y0 y1 y2 y3 y4 _ _ y7 _ y9 y10 y11 _ y13 _ _ z _ ->
      R_validate_n_byte_13 (y, y0, y1, y2, y3, y4, y7, y9, y10, y11, y13))
      (fun y y0 y1 y2 y3 y4 _ _ y7 _ y9 y10 y11 _ y13 _ y15 _ z _ ->
      R_validate_n_byte_14 (y, y0, y1, y2, y3, y4, y7, y9, y10, y11, y13,
      y15)) (fun y y0 y1 y2 y3 y4 _ _ y7 _ z _ -> R_validate_n_byte_15 (y,
      y0, y1, y2, y3, y4, y7)) x x0 x1 x2 x3 res0 __
  
  (** val _MARK__rect : 'a1 -> 'a1 **)
  
  let _MARK__rect f =
    f
  
  (** val _MARK__rec : 'a1 -> 'a1 **)
  
  let _MARK__rec f =
    f
  
  (** val eq_rew_dep : 'a1 -> 'a2 -> 'a1 -> 'a2 **)
  
  let eq_rew_dep x f y =
    f
  
  (** val validate_ll_list_F :
      (coq_N -> coq_NSet -> coq_NSet -> byte lazy_list ->
      (coq_NSet * coq_NSet) res) -> coq_N -> coq_NSet -> coq_NSet -> byte
      lazy_list -> (coq_NSet * coq_NSet) res **)
  
  let validate_ll_list_F validate_ll_list0 addr valid_addresses to_be_checked_addresses ll =
    match validate_n_byte (Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
            Coq_xH)))))) addr valid_addresses to_be_checked_addresses ll with
      | OK a ->
          let (p, ll') = a in
          let (valid_addresses', to_be_checked_addresses') = p in
          (match ll' with
             | Coq_ll_nil -> OK (valid_addresses', to_be_checked_addresses')
             | Coq_ll_cons (x, l) ->
                 validate_ll_list0
                   (coq_Nplus addr (Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO
                     (Coq_xO Coq_xH))))))) valid_addresses'
                   to_be_checked_addresses' ll')
      | Err e -> Err e
  
  (** val validate_ll_list_terminate :
      coq_N -> coq_NSet -> coq_NSet -> byte lazy_list ->
      (coq_NSet * coq_NSet) res **)
  
  let rec validate_ll_list_terminate addr valid_addresses to_be_checked_addresses ll =
    match validate_n_byte (Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
            Coq_xH)))))) addr valid_addresses to_be_checked_addresses ll with
      | OK a ->
          let (p, ll') = a in
          let (valid_addresses', to_be_checked_addresses') = p in
          (match ll' with
             | Coq_ll_nil -> OK (valid_addresses', to_be_checked_addresses')
             | Coq_ll_cons (x, l) ->
                 validate_ll_list_terminate
                   (coq_Nplus addr (Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO
                     (Coq_xO Coq_xH))))))) valid_addresses'
                   to_be_checked_addresses' (Coq_ll_cons (x, l)))
      | Err e -> Err e
  
  (** val validate_ll_list :
      coq_N -> coq_NSet -> coq_NSet -> byte lazy_list ->
      (coq_NSet * coq_NSet) res **)
  
  let validate_ll_list x x0 x1 x2 =
    validate_ll_list_terminate x x0 x1 x2
  
  type coq_R_validate_ll_list =
    | R_validate_ll_list_0 of coq_N * coq_NSet * coq_NSet * 
       byte lazy_list * ((coq_NSet * coq_NSet) * byte lazy_list) * 
       coq_NSet * coq_NSet * byte lazy_list
    | R_validate_ll_list_1 of coq_N * coq_NSet * coq_NSet * 
       byte lazy_list * ((coq_NSet * coq_NSet) * byte lazy_list) * 
       coq_NSet * coq_NSet * byte lazy_list * byte lazy_list
       * (coq_NSet * coq_NSet) res * coq_R_validate_ll_list
    | R_validate_ll_list_2 of coq_N * coq_NSet * coq_NSet * 
       byte lazy_list * string
  
  (** val coq_R_validate_ll_list_rect :
      (coq_N -> coq_NSet -> coq_NSet -> byte lazy_list ->
      ((coq_NSet * coq_NSet) * byte lazy_list) -> __ -> coq_NSet -> coq_NSet
      -> byte lazy_list -> __ -> __ -> 'a1) -> (coq_N -> coq_NSet -> coq_NSet
      -> byte lazy_list -> ((coq_NSet * coq_NSet) * byte lazy_list) -> __ ->
      coq_NSet -> coq_NSet -> byte lazy_list -> __ -> byte lazy_list -> __ ->
      __ -> (coq_NSet * coq_NSet) res -> coq_R_validate_ll_list -> 'a1 ->
      'a1) -> (coq_N -> coq_NSet -> coq_NSet -> byte lazy_list -> string ->
      __ -> 'a1) -> coq_N -> coq_NSet -> coq_NSet -> byte lazy_list ->
      (coq_NSet * coq_NSet) res -> coq_R_validate_ll_list -> 'a1 **)
  
  let rec coq_R_validate_ll_list_rect f f0 f1 addr valid_addresses to_be_checked_addresses ll r = function
    | R_validate_ll_list_0
        (addr0, valid_addresses0, to_be_checked_addresses0, ll0, a, x, x0, x1) ->
        f addr0 valid_addresses0 to_be_checked_addresses0 ll0 a __ x x0 x1 __
          __
    | R_validate_ll_list_1
        (addr0, valid_addresses0, to_be_checked_addresses0, ll0, a, x, x0,
         x1, x2, x3, x4) ->
        f0 addr0 valid_addresses0 to_be_checked_addresses0 ll0 a __ x x0 x1
          __ x2 __ __ x3 x4
          (coq_R_validate_ll_list_rect f f0 f1
            (coq_Nplus addr0 (Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
              Coq_xH))))))) x x0 x1 x3 x4)
    | R_validate_ll_list_2
        (addr0, valid_addresses0, to_be_checked_addresses0, ll0, e) ->
        f1 addr0 valid_addresses0 to_be_checked_addresses0 ll0 e __
  
  (** val coq_R_validate_ll_list_rec :
      (coq_N -> coq_NSet -> coq_NSet -> byte lazy_list ->
      ((coq_NSet * coq_NSet) * byte lazy_list) -> __ -> coq_NSet -> coq_NSet
      -> byte lazy_list -> __ -> __ -> 'a1) -> (coq_N -> coq_NSet -> coq_NSet
      -> byte lazy_list -> ((coq_NSet * coq_NSet) * byte lazy_list) -> __ ->
      coq_NSet -> coq_NSet -> byte lazy_list -> __ -> byte lazy_list -> __ ->
      __ -> (coq_NSet * coq_NSet) res -> coq_R_validate_ll_list -> 'a1 ->
      'a1) -> (coq_N -> coq_NSet -> coq_NSet -> byte lazy_list -> string ->
      __ -> 'a1) -> coq_N -> coq_NSet -> coq_NSet -> byte lazy_list ->
      (coq_NSet * coq_NSet) res -> coq_R_validate_ll_list -> 'a1 **)
  
  let rec coq_R_validate_ll_list_rec f f0 f1 addr valid_addresses to_be_checked_addresses ll r = function
    | R_validate_ll_list_0
        (addr0, valid_addresses0, to_be_checked_addresses0, ll0, a, x, x0, x1) ->
        f addr0 valid_addresses0 to_be_checked_addresses0 ll0 a __ x x0 x1 __
          __
    | R_validate_ll_list_1
        (addr0, valid_addresses0, to_be_checked_addresses0, ll0, a, x, x0,
         x1, x2, x3, x4) ->
        f0 addr0 valid_addresses0 to_be_checked_addresses0 ll0 a __ x x0 x1
          __ x2 __ __ x3 x4
          (coq_R_validate_ll_list_rec f f0 f1
            (coq_Nplus addr0 (Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
              Coq_xH))))))) x x0 x1 x3 x4)
    | R_validate_ll_list_2
        (addr0, valid_addresses0, to_be_checked_addresses0, ll0, e) ->
        f1 addr0 valid_addresses0 to_be_checked_addresses0 ll0 e __
  
  (** val validate_ll_list_rect :
      (coq_N -> coq_NSet -> coq_NSet -> byte lazy_list ->
      ((coq_NSet * coq_NSet) * byte lazy_list) -> __ -> coq_NSet -> coq_NSet
      -> byte lazy_list -> __ -> __ -> 'a1) -> (coq_N -> coq_NSet -> coq_NSet
      -> byte lazy_list -> ((coq_NSet * coq_NSet) * byte lazy_list) -> __ ->
      coq_NSet -> coq_NSet -> byte lazy_list -> __ -> byte lazy_list -> __ ->
      __ -> 'a1 -> 'a1) -> (coq_N -> coq_NSet -> coq_NSet -> byte lazy_list
      -> string -> __ -> 'a1) -> coq_N -> coq_NSet -> coq_NSet -> byte
      lazy_list -> 'a1 **)
  
  let rec validate_ll_list_rect f f0 f1 addr valid_addresses to_be_checked_addresses ll =
    let f2 = f1 addr valid_addresses to_be_checked_addresses ll in
    let f3 = f0 addr valid_addresses to_be_checked_addresses ll in
    let f4 = f addr valid_addresses to_be_checked_addresses ll in
    (match validate_n_byte (Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
             Coq_xH)))))) addr valid_addresses to_be_checked_addresses ll with
       | OK p ->
           let f5 = f4 p __ in
           let f6 = f3 p __ in
           let (p0, l) = p in
           let (n, n0) = p0 in
           let f7 = f5 n n0 l __ in
           let f8 = f6 n n0 l __ in
           let f9 = f8 l __ in
           (match l with
              | Coq_ll_nil -> f7 __
              | Coq_ll_cons (x, l0) ->
                  let f10 = f9 __ in
                  let hrec =
                    validate_ll_list_rect f f0 f1
                      (coq_Nplus addr (Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO
                        (Coq_xO Coq_xH))))))) n n0 (Coq_ll_cons (x, l0))
                  in
                  f10 hrec)
       | Err s -> f2 s __)
  
  (** val validate_ll_list_rec :
      (coq_N -> coq_NSet -> coq_NSet -> byte lazy_list ->
      ((coq_NSet * coq_NSet) * byte lazy_list) -> __ -> coq_NSet -> coq_NSet
      -> byte lazy_list -> __ -> __ -> 'a1) -> (coq_N -> coq_NSet -> coq_NSet
      -> byte lazy_list -> ((coq_NSet * coq_NSet) * byte lazy_list) -> __ ->
      coq_NSet -> coq_NSet -> byte lazy_list -> __ -> byte lazy_list -> __ ->
      __ -> 'a1 -> 'a1) -> (coq_N -> coq_NSet -> coq_NSet -> byte lazy_list
      -> string -> __ -> 'a1) -> coq_N -> coq_NSet -> coq_NSet -> byte
      lazy_list -> 'a1 **)
  
  let validate_ll_list_rec =
    validate_ll_list_rect
  
  (** val coq_R_validate_ll_list_correct :
      coq_N -> coq_NSet -> coq_NSet -> byte lazy_list ->
      (coq_NSet * coq_NSet) res -> coq_R_validate_ll_list **)
  
  let coq_R_validate_ll_list_correct x x0 x1 x2 res0 =
    validate_ll_list_rect (fun y y0 y1 y2 y3 _ y5 y6 y7 _ _ z _ ->
      R_validate_ll_list_0 (y, y0, y1, y2, y3, y5, y6, y7))
      (fun y y0 y1 y2 y3 _ y5 y6 y7 _ y9 _ _ y12 z _ -> R_validate_ll_list_1
      (y, y0, y1, y2, y3, y5, y6, y7, y9,
      (validate_ll_list
        (coq_Nplus y (Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH))))))) y5 y6 y7),
      (y12
        (validate_ll_list
          (coq_Nplus y (Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
            Coq_xH))))))) y5 y6 y7) __))) (fun y y0 y1 y2 y3 _ z _ ->
      R_validate_ll_list_2 (y, y0, y1, y2, y3)) x x0 x1 x2 res0 __
  
  (** val validate_program : byte lazy_list -> unit res **)
  
  let validate_program ll =
    match validate_ll_list header_size coq_Nempty coq_Nempty ll with
      | OK a ->
          let (valid_addresses, to_be_checked_addresses) = a in
          if is_Nincluded to_be_checked_addresses valid_addresses
          then OK ()
          else Err (String ((Ascii (false, false, true, false, false, false,
                 true, false)), (String ((Ascii (true, false, false, true,
                 false, true, true, false)), (String ((Ascii (false, true,
                 false, false, true, true, true, false)), (String ((Ascii
                 (true, false, true, false, false, true, true, false)),
                 (String ((Ascii (true, true, false, false, false, true,
                 true, false)), (String ((Ascii (false, false, true, false,
                 true, true, true, false)), (String ((Ascii (false, false,
                 false, false, false, true, false, false)), (String ((Ascii
                 (false, true, false, true, false, true, true, false)),
                 (String ((Ascii (true, false, true, false, true, true, true,
                 false)), (String ((Ascii (true, false, true, true, false,
                 true, true, false)), (String ((Ascii (false, false, false,
                 false, true, true, true, false)), (String ((Ascii (false,
                 false, false, false, false, true, false, false)), (String
                 ((Ascii (false, false, true, false, true, true, true,
                 false)), (String ((Ascii (true, true, true, true, false,
                 true, true, false)), (String ((Ascii (false, false, false,
                 false, false, true, false, false)), (String ((Ascii (true,
                 false, false, false, false, true, true, false)), (String
                 ((Ascii (false, true, true, true, false, true, true,
                 false)), (String ((Ascii (false, false, false, false, false,
                 true, false, false)), (String ((Ascii (true, false, false,
                 true, false, true, true, false)), (String ((Ascii (false,
                 true, true, true, false, true, true, false)), (String
                 ((Ascii (false, true, true, false, true, true, true,
                 false)), (String ((Ascii (true, false, false, false, false,
                 true, true, false)), (String ((Ascii (false, false, true,
                 true, false, true, true, false)), (String ((Ascii (true,
                 false, false, true, false, true, true, false)), (String
                 ((Ascii (false, false, true, false, false, true, true,
                 false)), (String ((Ascii (false, false, false, false, false,
                 true, false, false)), (String ((Ascii (true, false, false,
                 false, false, true, true, false)), (String ((Ascii (false,
                 false, true, false, false, true, true, false)), (String
                 ((Ascii (false, false, true, false, false, true, true,
                 false)), (String ((Ascii (false, true, false, false, true,
                 true, true, false)), (String ((Ascii (true, false, true,
                 false, false, true, true, false)), (String ((Ascii (true,
                 true, false, false, true, true, true, false)), (String
                 ((Ascii (true, true, false, false, true, true, true,
                 false)),
                 EmptyString))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      | Err e -> Err e
 end

