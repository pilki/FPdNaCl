(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Extraction of [positive], [N] and [Z] into Ocaml's [int64] *)

Require Import ZArith NArith ZOdiv_def.
Require Import ExtrOcamlBasic.


(** Mapping of [positive], [Z], [N] into [big_int]. The last strings
    emulate the matching, see documentation of [Extract Inductive]. *)

Extract Inductive positive => "int64"
 [ "MyInt64.doubleplusone" "MyInt64.double" "MyInt64.one" ] "MyInt64.positive_case".

Extract Inductive Z => "int64"
 [ "MyInt64.zero" "" "MyInt64.opp" ] "MyInt64.z_case".

Extract Inductive N => "int64"
 [ "MyInt64.zero" "" ] "MyInt64.n_case".

(** Nota: the "" above is used as an identity function "(fun p->p)" *)

(** Efficient (but uncertified) versions for usual functions *)

Extract Constant Pplus => "MyInt64.add".
Extract Constant Psucc => "MyInt64.succ".
Extract Constant Ppred => "fun n -> MyInt64.max MyInt64.one (MyInt64.pred n)".
Extract Constant Pminus => "fun n m -> MyInt64.max MyInt64.one (MyInt64.sub n m)".
Extract Constant Pmult => "MyInt64.mult".
Extract Constant Pmin => "MyInt64.min".
Extract Constant Pmax => "MyInt64.max".
Extract Constant Pcompare =>
 "fun x y c -> MyInt64.compare_case c Lt Gt x y".

Extract Constant Nplus => "MyInt64.add".
Extract Constant Nsucc => "MyInt64.succ".
Extract Constant Npred => "fun n -> MyInt64.max MyInt64.zero (MyInt64.pred n)".
Extract Constant Nminus => "fun n m -> MyInt64.max MyInt64.zero (MyInt64.sub n m)".
Extract Constant Nmult => "MyInt64.mult".
Extract Constant Nmin => "MyInt64.min".
Extract Constant Nmax => "MyInt64.max".
Extract Constant Ndiv =>
 "fun a b -> if MyInt64.eq b MyInt64.zero then MyInt64.zero else MyInt64.div a b".
Extract Constant Nmod =>
 "fun a b -> if MyInt64.eq b MyInt64.zero then MyInt64.zero else MyInt64.modulo a b".
Extract Constant Ncompare => "MyInt64.compare_case Eq Lt Gt".

Extract Constant Zplus => "MyInt64.add".
Extract Constant Zsucc => "MyInt64.succ".
Extract Constant Zpred => "MyInt64.pred".
Extract Constant Zminus => "MyInt64.sub".
Extract Constant Zmult => "MyInt64.mult".
Extract Constant Zopp => "MyInt64.opp".
Extract Constant Zabs => "MyInt64.abs".
Extract Constant Zmin => "MyInt64.min".
Extract Constant Zmax => "MyInt64.max".
Extract Constant Zcompare => "MyInt64.compare_case Eq Lt Gt".

Extract Constant Z_of_N => "fun p -> p".
Extract Constant Zabs_N => "MyInt64.abs".

(** Zdiv and Zmod are quite complex to define in terms of (/) and (mod).
    For the moment we don't even try *)

(** Test:
Require Import ZArith NArith.

Extraction "/tmp/test.ml"
 Pplus Ppred Pminus Pmult Pcompare Npred Nminus Ndiv Nmod Ncompare
 Zplus Zmult BinInt.Zcompare Z_of_N Zabs_N Zdiv.Zdiv Zmod.
*)
