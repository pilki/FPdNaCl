open BinNat
open BinPos
open BinaryDefs
open Byte
open Datatypes
open LazyList
open Lib
open NSet
open Semantics
open SemanticsProg

type __ = Obj.t

module ValidatorCode : 
 functor (I:INSTRUCTION) ->
 sig 
  val proper_mask : word
  
  val id : nat -> nat
  
  val validate_n_byte_F :
    (coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte lazy_list ->
    ((coq_NSet * coq_NSet) * byte lazy_list) option) -> coq_N -> coq_N ->
    coq_NSet -> coq_NSet -> byte lazy_list -> ((coq_NSet * coq_NSet) * byte
    lazy_list) option
  
  val eq_rew_r_dep : 'a1 -> 'a1 -> 'a2 -> 'a2
  
  val validate_n_byte_terminate :
    coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte lazy_list ->
    ((coq_NSet * coq_NSet) * byte lazy_list) option
  
  val validate_n_byte :
    coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte lazy_list ->
    ((coq_NSet * coq_NSet) * byte lazy_list) option
  
  type coq_R_validate_n_byte =
    | R_validate_n_byte_0 of coq_N * coq_N * coq_NSet * 
       coq_NSet * byte lazy_list
    | R_validate_n_byte_1 of coq_N * coq_N * coq_NSet * 
       coq_NSet * byte lazy_list * coq_N
       * ((I.instruction * coq_N) * byte lazy_list) * 
       I.instruction * coq_N * byte lazy_list * coq_N
       * ((coq_NSet * coq_NSet) * byte lazy_list) option
       * coq_R_validate_n_byte
    | R_validate_n_byte_2 of coq_N * coq_N * coq_NSet * 
       coq_NSet * byte lazy_list * coq_N
       * ((I.instruction * coq_N) * byte lazy_list) * 
       I.instruction * coq_N * byte lazy_list * coq_N * 
       I.register * word
    | R_validate_n_byte_3 of coq_N * coq_N * coq_NSet * 
       coq_NSet * byte lazy_list * coq_N
       * ((I.instruction * coq_N) * byte lazy_list) * 
       I.instruction * coq_N * byte lazy_list * coq_N * 
       I.register * word * coq_N * ((I.instruction * coq_N) * byte lazy_list)
       * I.instruction * coq_N * byte lazy_list * I.register * 
       coq_N * ((coq_NSet * coq_NSet) * byte lazy_list) option
       * coq_R_validate_n_byte
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
       * I.instruction * coq_N * byte lazy_list * I.register
    | R_validate_n_byte_6 of coq_N * coq_N * coq_NSet * 
       coq_NSet * byte lazy_list * coq_N
       * ((I.instruction * coq_N) * byte lazy_list) * 
       I.instruction * coq_N * byte lazy_list * coq_N * 
       I.register * word * coq_N * ((I.instruction * coq_N) * byte lazy_list)
       * I.instruction * coq_N * byte lazy_list
       * I.register instruction_classification
       * ((coq_NSet * coq_NSet) * byte lazy_list) option
       * coq_R_validate_n_byte
    | R_validate_n_byte_7 of coq_N * coq_N * coq_NSet * 
       coq_NSet * byte lazy_list * coq_N
       * ((I.instruction * coq_N) * byte lazy_list) * 
       I.instruction * coq_N * byte lazy_list * coq_N * 
       I.register * word * coq_N
    | R_validate_n_byte_8 of coq_N * coq_N * coq_NSet * 
       coq_NSet * byte lazy_list * coq_N
       * ((I.instruction * coq_N) * byte lazy_list) * 
       I.instruction * coq_N * byte lazy_list * coq_N * 
       I.register * word * ((coq_NSet * coq_NSet) * byte lazy_list) option
       * coq_R_validate_n_byte
    | R_validate_n_byte_9 of coq_N * coq_N * coq_NSet * 
       coq_NSet * byte lazy_list * coq_N
       * ((I.instruction * coq_N) * byte lazy_list) * 
       I.instruction * coq_N * byte lazy_list * coq_N * 
       word * ((coq_NSet * coq_NSet) * byte lazy_list) option
       * coq_R_validate_n_byte
    | R_validate_n_byte_10 of coq_N * coq_N * coq_NSet * 
       coq_NSet * byte lazy_list * coq_N
       * ((I.instruction * coq_N) * byte lazy_list) * 
       I.instruction * coq_N * byte lazy_list * coq_N * 
       word * ((coq_NSet * coq_NSet) * byte lazy_list) option
       * coq_R_validate_n_byte
    | R_validate_n_byte_11 of coq_N * coq_N * coq_NSet * 
       coq_NSet * byte lazy_list * coq_N
       * ((I.instruction * coq_N) * byte lazy_list) * 
       I.instruction * coq_N * byte lazy_list * coq_N * 
       word * ((coq_NSet * coq_NSet) * byte lazy_list) option
       * coq_R_validate_n_byte
    | R_validate_n_byte_12 of coq_N * coq_N * coq_NSet * 
       coq_NSet * byte lazy_list * coq_N
       * ((I.instruction * coq_N) * byte lazy_list) * 
       I.instruction * coq_N * byte lazy_list * coq_N
    | R_validate_n_byte_13 of coq_N * coq_N * coq_NSet * 
       coq_NSet * byte lazy_list * coq_N
       * ((I.instruction * coq_N) * byte lazy_list) * 
       I.instruction * coq_N * byte lazy_list * coq_N * 
       I.register
    | R_validate_n_byte_14 of coq_N * coq_N * coq_NSet * 
       coq_NSet * byte lazy_list * coq_N
       * ((I.instruction * coq_N) * byte lazy_list) * 
       I.instruction * coq_N * byte lazy_list
    | R_validate_n_byte_15 of coq_N * coq_N * coq_NSet * 
       coq_NSet * byte lazy_list * coq_N
  
  val coq_R_validate_n_byte_rect :
    (coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte lazy_list -> __ -> 'a1)
    -> (coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte lazy_list -> coq_N ->
    __ -> __ -> ((I.instruction * coq_N) * byte lazy_list) -> __ ->
    I.instruction -> coq_N -> byte lazy_list -> __ -> coq_N -> __ -> __ ->
    ((coq_NSet * coq_NSet) * byte lazy_list) option -> coq_R_validate_n_byte
    -> 'a1 -> 'a1) -> (coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte
    lazy_list -> coq_N -> __ -> __ -> ((I.instruction * coq_N) * byte
    lazy_list) -> __ -> I.instruction -> coq_N -> byte lazy_list -> __ ->
    coq_N -> __ -> I.register -> word -> __ -> __ -> __ -> __ -> 'a1) ->
    (coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte lazy_list -> coq_N -> __
    -> __ -> ((I.instruction * coq_N) * byte lazy_list) -> __ ->
    I.instruction -> coq_N -> byte lazy_list -> __ -> coq_N -> __ ->
    I.register -> word -> __ -> __ -> __ -> coq_N -> __ -> __ ->
    ((I.instruction * coq_N) * byte lazy_list) -> __ -> I.instruction ->
    coq_N -> byte lazy_list -> __ -> I.register -> __ -> __ -> __ -> coq_N ->
    __ -> ((coq_NSet * coq_NSet) * byte lazy_list) option ->
    coq_R_validate_n_byte -> 'a1 -> 'a1) -> (coq_N -> coq_N -> coq_NSet ->
    coq_NSet -> byte lazy_list -> coq_N -> __ -> __ ->
    ((I.instruction * coq_N) * byte lazy_list) -> __ -> I.instruction ->
    coq_N -> byte lazy_list -> __ -> coq_N -> __ -> I.register -> word -> __
    -> __ -> __ -> coq_N -> __ -> __ -> ((I.instruction * coq_N) * byte
    lazy_list) -> __ -> I.instruction -> coq_N -> byte lazy_list -> __ ->
    I.register -> __ -> __ -> __ -> __ -> 'a1) -> (coq_N -> coq_N -> coq_NSet
    -> coq_NSet -> byte lazy_list -> coq_N -> __ -> __ ->
    ((I.instruction * coq_N) * byte lazy_list) -> __ -> I.instruction ->
    coq_N -> byte lazy_list -> __ -> coq_N -> __ -> I.register -> word -> __
    -> __ -> __ -> coq_N -> __ -> __ -> ((I.instruction * coq_N) * byte
    lazy_list) -> __ -> I.instruction -> coq_N -> byte lazy_list -> __ ->
    I.register -> __ -> __ -> __ -> 'a1) -> (coq_N -> coq_N -> coq_NSet ->
    coq_NSet -> byte lazy_list -> coq_N -> __ -> __ ->
    ((I.instruction * coq_N) * byte lazy_list) -> __ -> I.instruction ->
    coq_N -> byte lazy_list -> __ -> coq_N -> __ -> I.register -> word -> __
    -> __ -> __ -> coq_N -> __ -> __ -> ((I.instruction * coq_N) * byte
    lazy_list) -> __ -> I.instruction -> coq_N -> byte lazy_list -> __ ->
    I.register instruction_classification -> __ -> __ ->
    ((coq_NSet * coq_NSet) * byte lazy_list) option -> coq_R_validate_n_byte
    -> 'a1 -> 'a1) -> (coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte
    lazy_list -> coq_N -> __ -> __ -> ((I.instruction * coq_N) * byte
    lazy_list) -> __ -> I.instruction -> coq_N -> byte lazy_list -> __ ->
    coq_N -> __ -> I.register -> word -> __ -> __ -> __ -> coq_N -> __ -> __
    -> __ -> 'a1) -> (coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte
    lazy_list -> coq_N -> __ -> __ -> ((I.instruction * coq_N) * byte
    lazy_list) -> __ -> I.instruction -> coq_N -> byte lazy_list -> __ ->
    coq_N -> __ -> I.register -> word -> __ -> __ -> __ ->
    ((coq_NSet * coq_NSet) * byte lazy_list) option -> coq_R_validate_n_byte
    -> 'a1 -> 'a1) -> (coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte
    lazy_list -> coq_N -> __ -> __ -> ((I.instruction * coq_N) * byte
    lazy_list) -> __ -> I.instruction -> coq_N -> byte lazy_list -> __ ->
    coq_N -> __ -> word -> __ -> __ -> __ -> ((coq_NSet * coq_NSet) * byte
    lazy_list) option -> coq_R_validate_n_byte -> 'a1 -> 'a1) -> (coq_N ->
    coq_N -> coq_NSet -> coq_NSet -> byte lazy_list -> coq_N -> __ -> __ ->
    ((I.instruction * coq_N) * byte lazy_list) -> __ -> I.instruction ->
    coq_N -> byte lazy_list -> __ -> coq_N -> __ -> word -> __ -> __ -> __ ->
    __ -> ((coq_NSet * coq_NSet) * byte lazy_list) option ->
    coq_R_validate_n_byte -> 'a1 -> 'a1) -> (coq_N -> coq_N -> coq_NSet ->
    coq_NSet -> byte lazy_list -> coq_N -> __ -> __ ->
    ((I.instruction * coq_N) * byte lazy_list) -> __ -> I.instruction ->
    coq_N -> byte lazy_list -> __ -> coq_N -> __ -> word -> __ -> __ -> __ ->
    __ -> ((coq_NSet * coq_NSet) * byte lazy_list) option ->
    coq_R_validate_n_byte -> 'a1 -> 'a1) -> (coq_N -> coq_N -> coq_NSet ->
    coq_NSet -> byte lazy_list -> coq_N -> __ -> __ ->
    ((I.instruction * coq_N) * byte lazy_list) -> __ -> I.instruction ->
    coq_N -> byte lazy_list -> __ -> coq_N -> __ -> __ -> 'a1) -> (coq_N ->
    coq_N -> coq_NSet -> coq_NSet -> byte lazy_list -> coq_N -> __ -> __ ->
    ((I.instruction * coq_N) * byte lazy_list) -> __ -> I.instruction ->
    coq_N -> byte lazy_list -> __ -> coq_N -> __ -> I.register -> __ -> 'a1)
    -> (coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte lazy_list -> coq_N ->
    __ -> __ -> ((I.instruction * coq_N) * byte lazy_list) -> __ ->
    I.instruction -> coq_N -> byte lazy_list -> __ -> __ -> 'a1) -> (coq_N ->
    coq_N -> coq_NSet -> coq_NSet -> byte lazy_list -> coq_N -> __ -> __ ->
    __ -> 'a1) -> coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte lazy_list ->
    ((coq_NSet * coq_NSet) * byte lazy_list) option -> coq_R_validate_n_byte
    -> 'a1
  
  val coq_R_validate_n_byte_rec :
    (coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte lazy_list -> __ -> 'a1)
    -> (coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte lazy_list -> coq_N ->
    __ -> __ -> ((I.instruction * coq_N) * byte lazy_list) -> __ ->
    I.instruction -> coq_N -> byte lazy_list -> __ -> coq_N -> __ -> __ ->
    ((coq_NSet * coq_NSet) * byte lazy_list) option -> coq_R_validate_n_byte
    -> 'a1 -> 'a1) -> (coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte
    lazy_list -> coq_N -> __ -> __ -> ((I.instruction * coq_N) * byte
    lazy_list) -> __ -> I.instruction -> coq_N -> byte lazy_list -> __ ->
    coq_N -> __ -> I.register -> word -> __ -> __ -> __ -> __ -> 'a1) ->
    (coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte lazy_list -> coq_N -> __
    -> __ -> ((I.instruction * coq_N) * byte lazy_list) -> __ ->
    I.instruction -> coq_N -> byte lazy_list -> __ -> coq_N -> __ ->
    I.register -> word -> __ -> __ -> __ -> coq_N -> __ -> __ ->
    ((I.instruction * coq_N) * byte lazy_list) -> __ -> I.instruction ->
    coq_N -> byte lazy_list -> __ -> I.register -> __ -> __ -> __ -> coq_N ->
    __ -> ((coq_NSet * coq_NSet) * byte lazy_list) option ->
    coq_R_validate_n_byte -> 'a1 -> 'a1) -> (coq_N -> coq_N -> coq_NSet ->
    coq_NSet -> byte lazy_list -> coq_N -> __ -> __ ->
    ((I.instruction * coq_N) * byte lazy_list) -> __ -> I.instruction ->
    coq_N -> byte lazy_list -> __ -> coq_N -> __ -> I.register -> word -> __
    -> __ -> __ -> coq_N -> __ -> __ -> ((I.instruction * coq_N) * byte
    lazy_list) -> __ -> I.instruction -> coq_N -> byte lazy_list -> __ ->
    I.register -> __ -> __ -> __ -> __ -> 'a1) -> (coq_N -> coq_N -> coq_NSet
    -> coq_NSet -> byte lazy_list -> coq_N -> __ -> __ ->
    ((I.instruction * coq_N) * byte lazy_list) -> __ -> I.instruction ->
    coq_N -> byte lazy_list -> __ -> coq_N -> __ -> I.register -> word -> __
    -> __ -> __ -> coq_N -> __ -> __ -> ((I.instruction * coq_N) * byte
    lazy_list) -> __ -> I.instruction -> coq_N -> byte lazy_list -> __ ->
    I.register -> __ -> __ -> __ -> 'a1) -> (coq_N -> coq_N -> coq_NSet ->
    coq_NSet -> byte lazy_list -> coq_N -> __ -> __ ->
    ((I.instruction * coq_N) * byte lazy_list) -> __ -> I.instruction ->
    coq_N -> byte lazy_list -> __ -> coq_N -> __ -> I.register -> word -> __
    -> __ -> __ -> coq_N -> __ -> __ -> ((I.instruction * coq_N) * byte
    lazy_list) -> __ -> I.instruction -> coq_N -> byte lazy_list -> __ ->
    I.register instruction_classification -> __ -> __ ->
    ((coq_NSet * coq_NSet) * byte lazy_list) option -> coq_R_validate_n_byte
    -> 'a1 -> 'a1) -> (coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte
    lazy_list -> coq_N -> __ -> __ -> ((I.instruction * coq_N) * byte
    lazy_list) -> __ -> I.instruction -> coq_N -> byte lazy_list -> __ ->
    coq_N -> __ -> I.register -> word -> __ -> __ -> __ -> coq_N -> __ -> __
    -> __ -> 'a1) -> (coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte
    lazy_list -> coq_N -> __ -> __ -> ((I.instruction * coq_N) * byte
    lazy_list) -> __ -> I.instruction -> coq_N -> byte lazy_list -> __ ->
    coq_N -> __ -> I.register -> word -> __ -> __ -> __ ->
    ((coq_NSet * coq_NSet) * byte lazy_list) option -> coq_R_validate_n_byte
    -> 'a1 -> 'a1) -> (coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte
    lazy_list -> coq_N -> __ -> __ -> ((I.instruction * coq_N) * byte
    lazy_list) -> __ -> I.instruction -> coq_N -> byte lazy_list -> __ ->
    coq_N -> __ -> word -> __ -> __ -> __ -> ((coq_NSet * coq_NSet) * byte
    lazy_list) option -> coq_R_validate_n_byte -> 'a1 -> 'a1) -> (coq_N ->
    coq_N -> coq_NSet -> coq_NSet -> byte lazy_list -> coq_N -> __ -> __ ->
    ((I.instruction * coq_N) * byte lazy_list) -> __ -> I.instruction ->
    coq_N -> byte lazy_list -> __ -> coq_N -> __ -> word -> __ -> __ -> __ ->
    __ -> ((coq_NSet * coq_NSet) * byte lazy_list) option ->
    coq_R_validate_n_byte -> 'a1 -> 'a1) -> (coq_N -> coq_N -> coq_NSet ->
    coq_NSet -> byte lazy_list -> coq_N -> __ -> __ ->
    ((I.instruction * coq_N) * byte lazy_list) -> __ -> I.instruction ->
    coq_N -> byte lazy_list -> __ -> coq_N -> __ -> word -> __ -> __ -> __ ->
    __ -> ((coq_NSet * coq_NSet) * byte lazy_list) option ->
    coq_R_validate_n_byte -> 'a1 -> 'a1) -> (coq_N -> coq_N -> coq_NSet ->
    coq_NSet -> byte lazy_list -> coq_N -> __ -> __ ->
    ((I.instruction * coq_N) * byte lazy_list) -> __ -> I.instruction ->
    coq_N -> byte lazy_list -> __ -> coq_N -> __ -> __ -> 'a1) -> (coq_N ->
    coq_N -> coq_NSet -> coq_NSet -> byte lazy_list -> coq_N -> __ -> __ ->
    ((I.instruction * coq_N) * byte lazy_list) -> __ -> I.instruction ->
    coq_N -> byte lazy_list -> __ -> coq_N -> __ -> I.register -> __ -> 'a1)
    -> (coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte lazy_list -> coq_N ->
    __ -> __ -> ((I.instruction * coq_N) * byte lazy_list) -> __ ->
    I.instruction -> coq_N -> byte lazy_list -> __ -> __ -> 'a1) -> (coq_N ->
    coq_N -> coq_NSet -> coq_NSet -> byte lazy_list -> coq_N -> __ -> __ ->
    __ -> 'a1) -> coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte lazy_list ->
    ((coq_NSet * coq_NSet) * byte lazy_list) option -> coq_R_validate_n_byte
    -> 'a1
  
  val validate_n_byte_rect :
    (coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte lazy_list -> __ -> 'a1)
    -> (coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte lazy_list -> coq_N ->
    __ -> __ -> ((I.instruction * coq_N) * byte lazy_list) -> __ ->
    I.instruction -> coq_N -> byte lazy_list -> __ -> coq_N -> __ -> __ ->
    'a1 -> 'a1) -> (coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte lazy_list
    -> coq_N -> __ -> __ -> ((I.instruction * coq_N) * byte lazy_list) -> __
    -> I.instruction -> coq_N -> byte lazy_list -> __ -> coq_N -> __ ->
    I.register -> word -> __ -> __ -> __ -> __ -> 'a1) -> (coq_N -> coq_N ->
    coq_NSet -> coq_NSet -> byte lazy_list -> coq_N -> __ -> __ ->
    ((I.instruction * coq_N) * byte lazy_list) -> __ -> I.instruction ->
    coq_N -> byte lazy_list -> __ -> coq_N -> __ -> I.register -> word -> __
    -> __ -> __ -> coq_N -> __ -> __ -> ((I.instruction * coq_N) * byte
    lazy_list) -> __ -> I.instruction -> coq_N -> byte lazy_list -> __ ->
    I.register -> __ -> __ -> __ -> coq_N -> __ -> 'a1 -> 'a1) -> (coq_N ->
    coq_N -> coq_NSet -> coq_NSet -> byte lazy_list -> coq_N -> __ -> __ ->
    ((I.instruction * coq_N) * byte lazy_list) -> __ -> I.instruction ->
    coq_N -> byte lazy_list -> __ -> coq_N -> __ -> I.register -> word -> __
    -> __ -> __ -> coq_N -> __ -> __ -> ((I.instruction * coq_N) * byte
    lazy_list) -> __ -> I.instruction -> coq_N -> byte lazy_list -> __ ->
    I.register -> __ -> __ -> __ -> __ -> 'a1) -> (coq_N -> coq_N -> coq_NSet
    -> coq_NSet -> byte lazy_list -> coq_N -> __ -> __ ->
    ((I.instruction * coq_N) * byte lazy_list) -> __ -> I.instruction ->
    coq_N -> byte lazy_list -> __ -> coq_N -> __ -> I.register -> word -> __
    -> __ -> __ -> coq_N -> __ -> __ -> ((I.instruction * coq_N) * byte
    lazy_list) -> __ -> I.instruction -> coq_N -> byte lazy_list -> __ ->
    I.register -> __ -> __ -> __ -> 'a1) -> (coq_N -> coq_N -> coq_NSet ->
    coq_NSet -> byte lazy_list -> coq_N -> __ -> __ ->
    ((I.instruction * coq_N) * byte lazy_list) -> __ -> I.instruction ->
    coq_N -> byte lazy_list -> __ -> coq_N -> __ -> I.register -> word -> __
    -> __ -> __ -> coq_N -> __ -> __ -> ((I.instruction * coq_N) * byte
    lazy_list) -> __ -> I.instruction -> coq_N -> byte lazy_list -> __ ->
    I.register instruction_classification -> __ -> __ -> 'a1 -> 'a1) ->
    (coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte lazy_list -> coq_N -> __
    -> __ -> ((I.instruction * coq_N) * byte lazy_list) -> __ ->
    I.instruction -> coq_N -> byte lazy_list -> __ -> coq_N -> __ ->
    I.register -> word -> __ -> __ -> __ -> coq_N -> __ -> __ -> __ -> 'a1)
    -> (coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte lazy_list -> coq_N ->
    __ -> __ -> ((I.instruction * coq_N) * byte lazy_list) -> __ ->
    I.instruction -> coq_N -> byte lazy_list -> __ -> coq_N -> __ ->
    I.register -> word -> __ -> __ -> __ -> 'a1 -> 'a1) -> (coq_N -> coq_N ->
    coq_NSet -> coq_NSet -> byte lazy_list -> coq_N -> __ -> __ ->
    ((I.instruction * coq_N) * byte lazy_list) -> __ -> I.instruction ->
    coq_N -> byte lazy_list -> __ -> coq_N -> __ -> word -> __ -> __ -> __ ->
    'a1 -> 'a1) -> (coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte lazy_list
    -> coq_N -> __ -> __ -> ((I.instruction * coq_N) * byte lazy_list) -> __
    -> I.instruction -> coq_N -> byte lazy_list -> __ -> coq_N -> __ -> word
    -> __ -> __ -> __ -> __ -> 'a1 -> 'a1) -> (coq_N -> coq_N -> coq_NSet ->
    coq_NSet -> byte lazy_list -> coq_N -> __ -> __ ->
    ((I.instruction * coq_N) * byte lazy_list) -> __ -> I.instruction ->
    coq_N -> byte lazy_list -> __ -> coq_N -> __ -> word -> __ -> __ -> __ ->
    __ -> 'a1 -> 'a1) -> (coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte
    lazy_list -> coq_N -> __ -> __ -> ((I.instruction * coq_N) * byte
    lazy_list) -> __ -> I.instruction -> coq_N -> byte lazy_list -> __ ->
    coq_N -> __ -> __ -> 'a1) -> (coq_N -> coq_N -> coq_NSet -> coq_NSet ->
    byte lazy_list -> coq_N -> __ -> __ -> ((I.instruction * coq_N) * byte
    lazy_list) -> __ -> I.instruction -> coq_N -> byte lazy_list -> __ ->
    coq_N -> __ -> I.register -> __ -> 'a1) -> (coq_N -> coq_N -> coq_NSet ->
    coq_NSet -> byte lazy_list -> coq_N -> __ -> __ ->
    ((I.instruction * coq_N) * byte lazy_list) -> __ -> I.instruction ->
    coq_N -> byte lazy_list -> __ -> __ -> 'a1) -> (coq_N -> coq_N ->
    coq_NSet -> coq_NSet -> byte lazy_list -> coq_N -> __ -> __ -> __ -> 'a1)
    -> coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte lazy_list -> 'a1
  
  val validate_n_byte_rec :
    (coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte lazy_list -> __ -> 'a1)
    -> (coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte lazy_list -> coq_N ->
    __ -> __ -> ((I.instruction * coq_N) * byte lazy_list) -> __ ->
    I.instruction -> coq_N -> byte lazy_list -> __ -> coq_N -> __ -> __ ->
    'a1 -> 'a1) -> (coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte lazy_list
    -> coq_N -> __ -> __ -> ((I.instruction * coq_N) * byte lazy_list) -> __
    -> I.instruction -> coq_N -> byte lazy_list -> __ -> coq_N -> __ ->
    I.register -> word -> __ -> __ -> __ -> __ -> 'a1) -> (coq_N -> coq_N ->
    coq_NSet -> coq_NSet -> byte lazy_list -> coq_N -> __ -> __ ->
    ((I.instruction * coq_N) * byte lazy_list) -> __ -> I.instruction ->
    coq_N -> byte lazy_list -> __ -> coq_N -> __ -> I.register -> word -> __
    -> __ -> __ -> coq_N -> __ -> __ -> ((I.instruction * coq_N) * byte
    lazy_list) -> __ -> I.instruction -> coq_N -> byte lazy_list -> __ ->
    I.register -> __ -> __ -> __ -> coq_N -> __ -> 'a1 -> 'a1) -> (coq_N ->
    coq_N -> coq_NSet -> coq_NSet -> byte lazy_list -> coq_N -> __ -> __ ->
    ((I.instruction * coq_N) * byte lazy_list) -> __ -> I.instruction ->
    coq_N -> byte lazy_list -> __ -> coq_N -> __ -> I.register -> word -> __
    -> __ -> __ -> coq_N -> __ -> __ -> ((I.instruction * coq_N) * byte
    lazy_list) -> __ -> I.instruction -> coq_N -> byte lazy_list -> __ ->
    I.register -> __ -> __ -> __ -> __ -> 'a1) -> (coq_N -> coq_N -> coq_NSet
    -> coq_NSet -> byte lazy_list -> coq_N -> __ -> __ ->
    ((I.instruction * coq_N) * byte lazy_list) -> __ -> I.instruction ->
    coq_N -> byte lazy_list -> __ -> coq_N -> __ -> I.register -> word -> __
    -> __ -> __ -> coq_N -> __ -> __ -> ((I.instruction * coq_N) * byte
    lazy_list) -> __ -> I.instruction -> coq_N -> byte lazy_list -> __ ->
    I.register -> __ -> __ -> __ -> 'a1) -> (coq_N -> coq_N -> coq_NSet ->
    coq_NSet -> byte lazy_list -> coq_N -> __ -> __ ->
    ((I.instruction * coq_N) * byte lazy_list) -> __ -> I.instruction ->
    coq_N -> byte lazy_list -> __ -> coq_N -> __ -> I.register -> word -> __
    -> __ -> __ -> coq_N -> __ -> __ -> ((I.instruction * coq_N) * byte
    lazy_list) -> __ -> I.instruction -> coq_N -> byte lazy_list -> __ ->
    I.register instruction_classification -> __ -> __ -> 'a1 -> 'a1) ->
    (coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte lazy_list -> coq_N -> __
    -> __ -> ((I.instruction * coq_N) * byte lazy_list) -> __ ->
    I.instruction -> coq_N -> byte lazy_list -> __ -> coq_N -> __ ->
    I.register -> word -> __ -> __ -> __ -> coq_N -> __ -> __ -> __ -> 'a1)
    -> (coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte lazy_list -> coq_N ->
    __ -> __ -> ((I.instruction * coq_N) * byte lazy_list) -> __ ->
    I.instruction -> coq_N -> byte lazy_list -> __ -> coq_N -> __ ->
    I.register -> word -> __ -> __ -> __ -> 'a1 -> 'a1) -> (coq_N -> coq_N ->
    coq_NSet -> coq_NSet -> byte lazy_list -> coq_N -> __ -> __ ->
    ((I.instruction * coq_N) * byte lazy_list) -> __ -> I.instruction ->
    coq_N -> byte lazy_list -> __ -> coq_N -> __ -> word -> __ -> __ -> __ ->
    'a1 -> 'a1) -> (coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte lazy_list
    -> coq_N -> __ -> __ -> ((I.instruction * coq_N) * byte lazy_list) -> __
    -> I.instruction -> coq_N -> byte lazy_list -> __ -> coq_N -> __ -> word
    -> __ -> __ -> __ -> __ -> 'a1 -> 'a1) -> (coq_N -> coq_N -> coq_NSet ->
    coq_NSet -> byte lazy_list -> coq_N -> __ -> __ ->
    ((I.instruction * coq_N) * byte lazy_list) -> __ -> I.instruction ->
    coq_N -> byte lazy_list -> __ -> coq_N -> __ -> word -> __ -> __ -> __ ->
    __ -> 'a1 -> 'a1) -> (coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte
    lazy_list -> coq_N -> __ -> __ -> ((I.instruction * coq_N) * byte
    lazy_list) -> __ -> I.instruction -> coq_N -> byte lazy_list -> __ ->
    coq_N -> __ -> __ -> 'a1) -> (coq_N -> coq_N -> coq_NSet -> coq_NSet ->
    byte lazy_list -> coq_N -> __ -> __ -> ((I.instruction * coq_N) * byte
    lazy_list) -> __ -> I.instruction -> coq_N -> byte lazy_list -> __ ->
    coq_N -> __ -> I.register -> __ -> 'a1) -> (coq_N -> coq_N -> coq_NSet ->
    coq_NSet -> byte lazy_list -> coq_N -> __ -> __ ->
    ((I.instruction * coq_N) * byte lazy_list) -> __ -> I.instruction ->
    coq_N -> byte lazy_list -> __ -> __ -> 'a1) -> (coq_N -> coq_N ->
    coq_NSet -> coq_NSet -> byte lazy_list -> coq_N -> __ -> __ -> __ -> 'a1)
    -> coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte lazy_list -> 'a1
  
  val coq_R_validate_n_byte_correct :
    coq_N -> coq_N -> coq_NSet -> coq_NSet -> byte lazy_list ->
    ((coq_NSet * coq_NSet) * byte lazy_list) option -> coq_R_validate_n_byte
  
  val eq_rew_dep : 'a1 -> 'a2 -> 'a1 -> 'a2
  
  val validate_ll_list_F :
    (coq_N -> coq_NSet -> coq_NSet -> byte lazy_list -> (coq_NSet * coq_NSet)
    option) -> coq_N -> coq_NSet -> coq_NSet -> byte lazy_list ->
    (coq_NSet * coq_NSet) option
  
  val validate_ll_list_terminate :
    coq_N -> coq_NSet -> coq_NSet -> byte lazy_list -> (coq_NSet * coq_NSet)
    option
  
  val validate_ll_list :
    coq_N -> coq_NSet -> coq_NSet -> byte lazy_list -> (coq_NSet * coq_NSet)
    option
  
  type coq_R_validate_ll_list =
    | R_validate_ll_list_0 of coq_N * coq_NSet * coq_NSet * 
       byte lazy_list * ((coq_NSet * coq_NSet) * byte lazy_list) * 
       coq_NSet * coq_NSet * byte lazy_list
    | R_validate_ll_list_1 of coq_N * coq_NSet * coq_NSet * 
       byte lazy_list * ((coq_NSet * coq_NSet) * byte lazy_list) * 
       coq_NSet * coq_NSet * byte lazy_list * byte lazy_list
       * (coq_NSet * coq_NSet) option * coq_R_validate_ll_list
    | R_validate_ll_list_2 of coq_N * coq_NSet * coq_NSet * byte lazy_list
  
  val coq_R_validate_ll_list_rect :
    (coq_N -> coq_NSet -> coq_NSet -> byte lazy_list ->
    ((coq_NSet * coq_NSet) * byte lazy_list) -> __ -> coq_NSet -> coq_NSet ->
    byte lazy_list -> __ -> __ -> 'a1) -> (coq_N -> coq_NSet -> coq_NSet ->
    byte lazy_list -> ((coq_NSet * coq_NSet) * byte lazy_list) -> __ ->
    coq_NSet -> coq_NSet -> byte lazy_list -> __ -> byte lazy_list -> __ ->
    __ -> (coq_NSet * coq_NSet) option -> coq_R_validate_ll_list -> 'a1 ->
    'a1) -> (coq_N -> coq_NSet -> coq_NSet -> byte lazy_list -> __ -> 'a1) ->
    coq_N -> coq_NSet -> coq_NSet -> byte lazy_list -> (coq_NSet * coq_NSet)
    option -> coq_R_validate_ll_list -> 'a1
  
  val coq_R_validate_ll_list_rec :
    (coq_N -> coq_NSet -> coq_NSet -> byte lazy_list ->
    ((coq_NSet * coq_NSet) * byte lazy_list) -> __ -> coq_NSet -> coq_NSet ->
    byte lazy_list -> __ -> __ -> 'a1) -> (coq_N -> coq_NSet -> coq_NSet ->
    byte lazy_list -> ((coq_NSet * coq_NSet) * byte lazy_list) -> __ ->
    coq_NSet -> coq_NSet -> byte lazy_list -> __ -> byte lazy_list -> __ ->
    __ -> (coq_NSet * coq_NSet) option -> coq_R_validate_ll_list -> 'a1 ->
    'a1) -> (coq_N -> coq_NSet -> coq_NSet -> byte lazy_list -> __ -> 'a1) ->
    coq_N -> coq_NSet -> coq_NSet -> byte lazy_list -> (coq_NSet * coq_NSet)
    option -> coq_R_validate_ll_list -> 'a1
  
  val validate_ll_list_rect :
    (coq_N -> coq_NSet -> coq_NSet -> byte lazy_list ->
    ((coq_NSet * coq_NSet) * byte lazy_list) -> __ -> coq_NSet -> coq_NSet ->
    byte lazy_list -> __ -> __ -> 'a1) -> (coq_N -> coq_NSet -> coq_NSet ->
    byte lazy_list -> ((coq_NSet * coq_NSet) * byte lazy_list) -> __ ->
    coq_NSet -> coq_NSet -> byte lazy_list -> __ -> byte lazy_list -> __ ->
    __ -> 'a1 -> 'a1) -> (coq_N -> coq_NSet -> coq_NSet -> byte lazy_list ->
    __ -> 'a1) -> coq_N -> coq_NSet -> coq_NSet -> byte lazy_list -> 'a1
  
  val validate_ll_list_rec :
    (coq_N -> coq_NSet -> coq_NSet -> byte lazy_list ->
    ((coq_NSet * coq_NSet) * byte lazy_list) -> __ -> coq_NSet -> coq_NSet ->
    byte lazy_list -> __ -> __ -> 'a1) -> (coq_N -> coq_NSet -> coq_NSet ->
    byte lazy_list -> ((coq_NSet * coq_NSet) * byte lazy_list) -> __ ->
    coq_NSet -> coq_NSet -> byte lazy_list -> __ -> byte lazy_list -> __ ->
    __ -> 'a1 -> 'a1) -> (coq_N -> coq_NSet -> coq_NSet -> byte lazy_list ->
    __ -> 'a1) -> coq_N -> coq_NSet -> coq_NSet -> byte lazy_list -> 'a1
  
  val coq_R_validate_ll_list_correct :
    coq_N -> coq_NSet -> coq_NSet -> byte lazy_list -> (coq_NSet * coq_NSet)
    option -> coq_R_validate_ll_list
  
  val validate_program : byte lazy_list -> bool
 end

