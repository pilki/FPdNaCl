(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** [Big] : a wrapper around ocaml [Big_int] with nicer names,
    and a few extraction-specific constructions *)

(** To be linked with [nums.(cma|cmxa)] *)



let zero = Int64.zero
        (** The big integer [0]. *)
let one = Int64.one
        (** The big integer [1]. *)
let two = Int64.of_int 2
        (** The big integer [2]. *)

(** {6 Arithmetic operations} *)

let opp = Int64.neg
        (** Unary negation. *)
let abs = Int64.abs
        (** Absolute value. *)
let add = Int64.add
        (** Addition. *)
let succ = Int64.succ
        (** Successor (add 1). *)
let add_int i j = Int64.add i (Int64.of_int j)
        (** Addition of a small integer to a big integer. *)
let sub = Int64.sub
        (** Subtraction. *)
let pred = Int64.pred
        (** Predecessor (subtract 1). *)
let mult = Int64.mul
        (** Multiplication of two big integers. *)
let mult_int i j = mult i (Int64.of_int j)
        (** Multiplication of a big integer by a small integer *)
let square x = mult x x
        (** Return the square of the given big integer *)
let max (x:int64) y =
  if x < y then y else x
let min (x:int64) y =
  if x < y then x else y
(*let sqrt = sqrt_big_int
        (** [sqrt_big_int a] returns the integer square root of [a],
           that is, the largest big integer [r] such that [r * r <= a].
           Raise [Invalid_argument] if [a] is negative. *)*)
(*let quomod = quomod_big_int
        (** Euclidean division of two big integers.
           The first part of the result is the quotient,
           the second part is the remainder.
           Writing [(q,r) = quomod_big_int a b], we have
           [a = q * b + r] and [0 <= r < |b|].
           Raise [Division_by_zero] if the divisor is zero. *)
let div = div_big_int
        (** Euclidean quotient of two big integers.
           This is the first result [q] of [quomod_big_int] (see above). *)
let modulo = mod_big_int
        (** Euclidean modulus of two big integers.
           This is the second result [r] of [quomod_big_int] (see above). *)
let gcd = gcd_big_int
        (** Greatest common divisor of two big integers. *)
let power = power_big_int_positive_big_int
        (** Exponentiation functions.  Return the big integer
           representing the first argument [a] raised to the power [b]
           (the second argument).  Depending
           on the function, [a] and [b] can be either small integers
           or big integers.  Raise [Invalid_argument] if [b] is negative. *)
*)
(** {6 Comparisons and tests} *)

(*let sign = sign_big_int
        (** Return [0] if the given big integer is zero,
           [1] if it is positive, and [-1] if it is negative. *)*)
let compare = Int64.compare
(*        (** [compare_big_int a b] returns [0] if [a] and [b] are equal,
           [1] if [a] is greater than [b], and [-1] if [a] is smaller
           than [b]. *)
let eq = (=)
let le = (<=)
let ge = (=>)
let lt = 
let gt = gt_big_int
        (** Usual boolean comparisons between two big integers. *)
let max = max_big_int
        (** Return the greater of its two arguments. *)
let min = min_big_int
        (** Return the smaller of its two arguments. *)

(** {6 Conversions to and from strings} *)

let to_string = string_of_big_int
        (** Return the string representation of the given big integer,
           in decimal (base 10). *)
let of_string = big_int_of_string
        (** Convert a string to a big integer, in decimal.
           The string consists of an optional [-] or [+] sign,
           followed by one or several decimal digits. *)


(** {6 Conversions to and from other numerical types} *)

let of_int = big_int_of_int
        (** Convert a small integer to a big integer. *)
let is_int = is_int_big_int
        (** Test whether the given big integer is small enough to
           be representable as a small integer (type [int])
           without loss of precision.  On a 32-bit platform,
           [is_int_big_int a] returns [true] if and only if
           [a] is between 2{^30} and 2{^30}-1.  On a 64-bit platform,
           [is_int_big_int a] returns [true] if and only if
           [a] is between -2{^62} and 2{^62}-1. *)
let to_int = int_of_big_int
        (** Convert a big integer to a small integer (type [int]).
           Raises [Failure "int_of_big_int"] if the big integer
           is not representable as a small integer. *)

(** Functions used by extraction *)
*)
let double x = mult x two
let doubleplusone x = succ (double x)


let nat_case fO fS n = assert false

let positive_case f2p1 f2p f1 p = assert false

let n_case fO fp n = if n <= zero then fO () else fp n

let z_case fO fp fn z = assert false

let compare_case e l g (x: int64) (y: int64) =
  let s = compare x y in if s = 0 then e else if s<0 then l else g

(*let nat_rec fO fS =
  let rec loop acc n =
    if sign n <= 0 then acc else loop (fS acc) (pred n)
  in loop fO

let positive_rec f2p1 f2p f1 =
  let rec loop n =
    if le n one then f1
    else
      let (q,r) = quomod n two in
      if eq r zero then f2p (loop q) else f2p1 (loop q)
  in loop

let z_rec fO fp fn = z_case (fun _ -> fO) fp fn
*)

(** added for FPdNaCl *)


let safe_minus (n: int64) (m: int64) =
  if m <= n then Some (sub n m) else None

let int64_32 = Int64.of_int 32
let dividable_by_32_dec n =
  Int64.rem n int64_32 = zero

(*Lemma safe_minus_inf_is_some: forall n m,
  m <= n -> is_some (safe_minus n m).
Proof.

Lemma safe_minus_sup_is_None: forall n m,
  n < m -> safe_minus n m = None.
Proof.

Lemma safe_minus_correct: forall n m p, safe_minus n m = Some p ->
  n  = (m + p).
Proof.
  assert ((n - m) = p).
*)
