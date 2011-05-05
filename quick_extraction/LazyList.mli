open Datatypes

type 'x coq_lazy = 'x __coq_lazy Lazy.t
and 'x __coq_lazy =
  | Lazy of 'x

type 'x lazy_list =
  | Coq_ll_nil
  | Coq_ll_cons of 'x * 'x lazy_list coq_lazy

val lazy_list_rect :
  'a2 -> ('a1 -> 'a1 lazy_list -> 'a2 -> 'a2) -> 'a1 lazy_list -> 'a2

val to_list : 'a1 lazy_list -> 'a1 list

val ll_length : 'a1 lazy_list -> nat

val ll_nth : nat -> 'a1 lazy_list -> 'a1 option

val ll_safe_drop : nat -> 'a1 lazy_list -> 'a1 lazy_list option

val ll_safe_take : nat -> 'a1 lazy_list -> 'a1 lazy_list option

