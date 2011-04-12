(* FPdNaCl
 * 
 * Copyright (C) 2011 Alexandre Pilkiewicz (@polytechnique.org)
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License as
 * published by the Free Software Foundation; either version 2 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * General Public License for more details. *)

Notation "'option_bind' f oa" :=
  (match oa with
    | Some a => f a
    | None => None
  end) (at level 10, f at next level, oa at next level, only parsing).


(* The basic idea of the do notation is that when you write

   do x <- an expression;
   another expression

   if "an expression" returns None, the hole thing returns None

   if "an expression" returns Some v, x is bound to v, and "another
   expression" is evaluated
*)


Notation "'do' '_' '<-' A ; B" :=
  (option_bind (fun _ => B) (A))
   (at level 200, A at level 100, B at level 200, format
   "'[v' 'do'  '_'  <-  A ;  '/' B ']'").

Notation "'do' X '<-' A ; B" :=
  (option_bind (fun X => B) A)
   (at level 200, X ident, A at level 100, B at level 200, format
   "'[v' 'do'  X  '<-'  A ;  '/' B ']'").

Notation "'do' ( X : T ) <- A ; B" :=
  (option_bind (fun (X: T) => B) A)
   (at level 200, X ident, A at level 100,
    T at level 100, B at level 200, only parsing).

Notation "'do' ( '_' : T ) <- A ; B" :=
  (option_bind (fun (_: T) => B) A)
   (at level 200, A at level 100, T at level 100, B at level 200, only parsing).

Notation "'do' ( X , Y ) <- A ; B" :=
  (option_bind (fun _XY_ => let '(X, Y) := _XY_ in  B) A)
   (at level 200, X ident, Y ident, A at level 100, B at level 200, format
   "'[v' 'do'  ( X ,  Y )  '<-'  A ;  '/' B ']'").

Notation "'do' ( '_' , Y ) <- A ; B" :=
  (option_bind (fun _XY_ => let '(_, Y) := _XY_ in  B) A)
   (at level 200, Y ident, A at level 100, B at level 200, format
   "'[v' 'do'  ( '_' ,  Y )  '<-'  A ;  '/' B ']'").
Notation "'do' ( X , '_' ) <- A ; B" :=
  (option_bind (fun _XY_ => let '(X, _) := _XY_ in  B) A)
   (at level 200, X ident, A at level 100, B at level 200, format
   "'[v' 'do'  ( X ,  '_' )  '<-'  A ;  '/' B ']'").



Notation "'do' ( X , Y , Z ) <- A ; B" :=
  (option_bind (fun (_XYZ_: _ * _ *_) =>
    let '(X, Y, Z) := _XYZ_ in B) A)
   (at level 200, X ident, Y ident, Z ident, A at level 100, B at level 200, format
   "'[v' 'do'  ( X ,  Y ,  Z )  '<-'  A ;  '/' B ']'").

Notation "'do' ( '_' , Y , Z ) <- A ; B" :=
  (option_bind (fun (_XYZ_: _ * _ *_) =>
    let '(_, Y, Z) := _XYZ_ in B) A)
   (at level 200,  Y ident, Z ident, A at level 100, B at level 200, format
   "'[v' 'do'  ( '_' ,  Y ,  Z )  '<-'  A ;  '/' B ']'").

Notation "'do' ( X , '_' , Z ) <- A ; B" :=
  (option_bind (fun (_XYZ_: _ * _ *_) =>
    let '(X, _, Z) := _XYZ_ in B) A)
   (at level 200, X ident, Z ident, A at level 100, B at level 200, format
   "'[v' 'do'  ( X ,  '_' ,  Z )  '<-'  A ;  '/' B ']'").


Notation "'do' ( X , Y , '_' ) <- A ; B" :=
  (option_bind (fun (_XYZ_: _ * _ *_) =>
    let '(X, Y, _) := _XYZ_ in B) A)
   (at level 200, X ident, Y ident, A at level 100, B at level 200, format
   "'[v' 'do'  ( X ,  Y ,  '_' )  '<-'  A ;  '/' B ']'").

Notation "'do' ( X , '_' , '_' ) <- A ; B" :=
  (option_bind (fun (_XYZ_: _ * _ *_) =>
    let '(X, _, _) := _XYZ_ in B) A)
   (at level 200, X ident, A at level 100, B at level 200, format
   "'[v' 'do'  ( X ,  '_' ,  '_' )  '<-'  A ;  '/' B ']'").

Notation "'do' ( '_' , Y , '_' ) <- A ; B" :=
  (option_bind (fun (_XYZ_: _ * _ *_) =>
    let '(X, Y, Z) := _XYZ_ in B) A)
   (at level 200, Y ident, A at level 100, B at level 200, format
   "'[v' 'do'  ( '_' ,  Y ,  '_' )  '<-'  A ;  '/' B ']'").

Notation "'do' ( '_' , '_' , Z ) <- A ; B" :=
  (option_bind (fun (_XYZ_: _ * _ *_) =>
    let '(_, _, Z) := _XYZ_ in B) A)
   (at level 200, Z ident, A at level 100, B at level 200, format
   "'[v' 'do'  ( '_' ,  '_' ,  Z )  '<-'  A ;  '/' B ']'").
