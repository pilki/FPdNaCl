open Datatypes

type 'x coq_lazy = 'x __coq_lazy Lazy.t
and 'x __coq_lazy =
  | Lazy of 'x

type 'x lazy_list =
  | Coq_ll_nil
  | Coq_ll_cons of 'x * 'x lazy_list coq_lazy

(** val lazy_list_rect :
    'a2 -> ('a1 -> 'a1 lazy_list -> 'a2 -> 'a2) -> 'a1 lazy_list -> 'a2 **)

let rec lazy_list_rect hnil hcons = function
  | Coq_ll_nil -> hnil
  | Coq_ll_cons (x, l0) ->
      let Lazy l' = Lazy.force l0 in
      hcons x l' (lazy_list_rect hnil hcons l')

(** val to_list : 'a1 lazy_list -> 'a1 list **)

let rec to_list = function
  | Coq_ll_nil -> []
  | Coq_ll_cons (x, l) -> let Lazy l' = Lazy.force l in x :: (to_list l')

(** val ll_length : 'a1 lazy_list -> nat **)

let rec ll_length = function
  | Coq_ll_nil -> O
  | Coq_ll_cons (x, l0) -> let Lazy l' = Lazy.force l0 in S (ll_length l')

(** val ll_nth : nat -> 'a1 lazy_list -> 'a1 option **)

let rec ll_nth n ll =
  match n with
    | O ->
        (match ll with
           | Coq_ll_nil -> None
           | Coq_ll_cons (x, l) -> Some x)
    | S n' ->
        (match ll with
           | Coq_ll_nil -> None
           | Coq_ll_cons (x, l) ->
               let Lazy ll' = Lazy.force l in ll_nth n' ll')

(** val ll_safe_drop : nat -> 'a1 lazy_list -> 'a1 lazy_list option **)

let rec ll_safe_drop n ll =
  match n with
    | O -> Some ll
    | S n' ->
        (match ll with
           | Coq_ll_nil -> None
           | Coq_ll_cons (x, l) ->
               let Lazy ll' = Lazy.force l in ll_safe_drop n' ll')

(** val ll_safe_take : nat -> 'a1 lazy_list -> 'a1 lazy_list option **)

let rec ll_safe_take n ll =
  match n with
    | O -> Some Coq_ll_nil
    | S n' ->
        (match ll with
           | Coq_ll_nil -> None
           | Coq_ll_cons (x, l) ->
               let Lazy ll' = Lazy.force l in
               (match ll_safe_take n' ll' with
                  | Some a -> Some (Coq_ll_cons (x, (lazy (Lazy a))))
                  | None -> None))

