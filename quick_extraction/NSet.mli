open BinNat
open BinPos
open Datatypes

type coq_PSet =
  | PLeaf of bool
  | PNode of coq_PSet * bool * coq_PSet

val coq_PSet_rect :
  (bool -> 'a1) -> (coq_PSet -> 'a1 -> bool -> coq_PSet -> 'a1 -> 'a1) ->
  coq_PSet -> 'a1

val coq_PSet_rec :
  (bool -> 'a1) -> (coq_PSet -> 'a1 -> bool -> coq_PSet -> 'a1 -> 'a1) ->
  coq_PSet -> 'a1

val coq_Pempty : coq_PSet

val is_Pin : positive -> coq_PSet -> bool

val coq_Padd : positive -> coq_PSet -> coq_PSet

val imp_bool : bool -> bool -> bool

val is_Pincluded : coq_PSet -> coq_PSet -> bool

type coq_NSet = bool * coq_PSet

val coq_Nempty : coq_NSet

val is_Nin : coq_N -> coq_NSet -> bool

val coq_Nadd : coq_N -> coq_NSet -> bool * coq_PSet

val is_Nincluded : coq_NSet -> coq_NSet -> bool

