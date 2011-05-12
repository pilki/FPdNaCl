open String0

type 'rES res =
  | OK of 'rES
  | Err of string

val res_rect : ('a1 -> 'a2) -> (string -> 'a2) -> 'a1 res -> 'a2

val res_rec : ('a1 -> 'a2) -> (string -> 'a2) -> 'a1 res -> 'a2

