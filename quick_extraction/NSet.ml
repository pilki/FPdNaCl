open BinNat
open BinPos
open Datatypes

type coq_PSet =
  | PLeaf of bool
  | PNode of coq_PSet * bool * coq_PSet

(** val coq_PSet_rect :
    (bool -> 'a1) -> (coq_PSet -> 'a1 -> bool -> coq_PSet -> 'a1 -> 'a1) ->
    coq_PSet -> 'a1 **)

let rec coq_PSet_rect f f0 = function
  | PLeaf b -> f b
  | PNode (p0, b, p1) ->
      f0 p0 (coq_PSet_rect f f0 p0) b p1 (coq_PSet_rect f f0 p1)

(** val coq_PSet_rec :
    (bool -> 'a1) -> (coq_PSet -> 'a1 -> bool -> coq_PSet -> 'a1 -> 'a1) ->
    coq_PSet -> 'a1 **)

let rec coq_PSet_rec f f0 = function
  | PLeaf b -> f b
  | PNode (p0, b, p1) ->
      f0 p0 (coq_PSet_rec f f0 p0) b p1 (coq_PSet_rec f f0 p1)

(** val coq_Pempty : coq_PSet **)

let coq_Pempty =
  PLeaf false

(** val is_Pin : positive -> coq_PSet -> bool **)

let rec is_Pin pos ps =
  match pos with
    | Coq_xI pos' ->
        (match ps with
           | PLeaf b -> false
           | PNode (p, b, psI) -> is_Pin pos' psI)
    | Coq_xO pos' ->
        (match ps with
           | PLeaf b -> false
           | PNode (psO, b, p) -> is_Pin pos' psO)
    | Coq_xH -> (match ps with
                   | PLeaf b -> b
                   | PNode (p, b, p0) -> b)

(** val coq_Padd : positive -> coq_PSet -> coq_PSet **)

let rec coq_Padd pos tree =
  match pos with
    | Coq_xI pos' ->
        (match tree with
           | PLeaf b -> PNode (coq_Pempty, b, (coq_Padd pos' coq_Pempty))
           | PNode (psO, b, psI) -> PNode (psO, b, (coq_Padd pos' psI)))
    | Coq_xO pos' ->
        (match tree with
           | PLeaf b -> PNode ((coq_Padd pos' coq_Pempty), b, coq_Pempty)
           | PNode (psO, b, psI) -> PNode ((coq_Padd pos' psO), b, psI))
    | Coq_xH ->
        (match tree with
           | PLeaf b -> PLeaf true
           | PNode (psO, b, psI) -> PNode (psO, true, psI))

(** val imp_bool : bool -> bool -> bool **)

let imp_bool b1 b2 =
  if b1 then b2 else true

(** val is_Pincluded : coq_PSet -> coq_PSet -> bool **)

let rec is_Pincluded ps1 ps2 =
  match ps1 with
    | PLeaf b ->
        if b
        then (match ps2 with
                | PLeaf b2 -> imp_bool true b2
                | PNode (p, b2, p0) -> imp_bool true b2)
        else true
    | PNode (psO1, b1, psI1) ->
        (match ps2 with
           | PLeaf b2 ->
               (&&) ((&&) (imp_bool b1 b2) (is_Pincluded psO1 coq_Pempty))
                 (is_Pincluded psI1 coq_Pempty)
           | PNode (psO2, b2, psI2) ->
               (&&) ((&&) (imp_bool b1 b2) (is_Pincluded psO1 psO2))
                 (is_Pincluded psI1 psI2))

type coq_NSet = bool * coq_PSet

(** val coq_Nempty : coq_NSet **)

let coq_Nempty =
  (false, coq_Pempty)

(** val is_Nin : coq_N -> coq_NSet -> bool **)

let is_Nin n ns =
  match n with
    | N0 -> fst ns
    | Npos pos -> is_Pin pos (snd ns)

(** val coq_Nadd : coq_N -> coq_NSet -> bool * coq_PSet **)

let coq_Nadd n tree =
  match n with
    | N0 -> let (b, ps) = tree in (true, ps)
    | Npos pos -> let (b, ps) = tree in (b, (coq_Padd pos ps))

(** val is_Nincluded : coq_NSet -> coq_NSet -> bool **)

let is_Nincluded ns1 ns2 =
  (&&) (imp_bool (fst ns1) (fst ns2)) (is_Pincluded (snd ns1) (snd ns2))

