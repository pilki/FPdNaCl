open BinNat
open BinPos
open Datatypes

type __ = Obj.t

type 'x eq_dec = 'x -> 'x -> bool

val list_take : nat -> 'a1 list -> 'a1 list

val list_drop : nat -> 'a1 list -> 'a1 list

val imp_rew_rect : (__ -> 'a1) -> 'a1

val imp_rew_rec : (__ -> 'a1) -> 'a1

type ident = positive

val coq_TAG_INV : 'a1 -> 'a1

val coq_TAG_INV_MULTI : 'a1 -> 'a1

val _MARK__rect : 'a1 -> 'a1

val _MARK__rec : 'a1 -> 'a1

val safe_minus : coq_N -> coq_N -> coq_N option

