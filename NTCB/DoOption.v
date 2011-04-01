Notation "'option_bind' f oa" :=
  (match oa with
    | Some a => f a
    | None => None
  end) (at level 10, f at next level, oa at next level, only parsing).


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
