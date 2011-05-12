open String0

type 'rES res =
  | OK of 'rES
  | Err of string

(** val res_rect : ('a1 -> 'a2) -> (string -> 'a2) -> 'a1 res -> 'a2 **)

let res_rect f f0 = function
  | OK x -> f x
  | Err x -> f0 x

(** val res_rec : ('a1 -> 'a2) -> (string -> 'a2) -> 'a1 res -> 'a2 **)

let res_rec f f0 = function
  | OK x -> f x
  | Err x -> f0 x

