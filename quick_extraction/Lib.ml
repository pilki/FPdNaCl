open BinNat
open BinPos
open Datatypes

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type 'x eq_dec = 'x -> 'x -> bool

(** val list_take : nat -> 'a1 list -> 'a1 list **)

let rec list_take n l =
  match n with
    | O -> []
    | S n' -> (match l with
                 | [] -> []
                 | h :: t -> h :: (list_take n' t))

(** val list_drop : nat -> 'a1 list -> 'a1 list **)

let rec list_drop n l =
  match n with
    | O -> l
    | S n' -> (match l with
                 | [] -> []
                 | h :: t -> list_drop n' t)

(** val imp_rew_rect : (__ -> 'a1) -> 'a1 **)

let imp_rew_rect f =
  f __

(** val imp_rew_rec : (__ -> 'a1) -> 'a1 **)

let imp_rew_rec f =
  f __

type ident = positive

(** val coq_TAG_INV : 'a1 -> 'a1 **)

let coq_TAG_INV p =
  p

(** val coq_TAG_INV_MULTI : 'a1 -> 'a1 **)

let coq_TAG_INV_MULTI p =
  p

(** val _MARK__rect : 'a1 -> 'a1 **)

let _MARK__rect f =
  f

(** val _MARK__rec : 'a1 -> 'a1 **)

let _MARK__rec f =
  f

(** val safe_minus : coq_N -> coq_N -> coq_N option **)

let safe_minus n m =
  match n with
    | N0 -> (match m with
               | N0 -> Some N0
               | Npos p -> None)
    | Npos n' ->
        (match m with
           | N0 -> Some n
           | Npos m' ->
               (match coq_Pminus_mask n' m' with
                  | IsNul -> Some N0
                  | IsPos p -> Some (Npos p)
                  | IsNeg -> None))

