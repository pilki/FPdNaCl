open BinNat
open BinPos
open Byte
open Datatypes

val translate_P_by : nat -> positive -> positive

val translate_N_by : nat -> coq_N -> coq_N

val translate_N_by_four : coq_N -> coq_N

val translate_N_by_eight : coq_N -> coq_N

val coq_N_of_byte : byte -> coq_N

val byte0 : byte

val concat_byte : coq_N -> byte -> coq_N

type word =
  | W of byte * byte * byte * byte

val word_rect : (byte -> byte -> byte -> byte -> 'a1) -> word -> 'a1

val word_rec : (byte -> byte -> byte -> byte -> 'a1) -> word -> 'a1

val word_eq_dec : word -> word -> bool

val coq_N_of_word : word -> coq_N

val bool_list_of_P : positive -> bool list

val coq_P_of_bool_list : bool list -> positive option

val bool_list_of_N : coq_N -> bool list

val coq_N_of_bool_list : bool list -> coq_N

val list_and : bool list -> bool list -> bool list

val coq_N_and : coq_N -> coq_N -> coq_N

