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

Require Import Lib.

(* Encoding of sets of N *)

Require MSetAVL.
Require Import NOrderedType.

Module NS := MSetAVL.Make (N_as_OT).


(* set of N *)

Definition NSet := NS.t.

Definition In_NSet: N -> NSet -> Prop := NS.In.

Definition Nincluded (ns1 ns2: NSet) := NS.Subset ns1 ns2.

Hint Unfold NSet In_NSet Nincluded: nset.

Ltac un := autounfold with nset in *.

Lemma Nincluded_trans: forall ns1 ns2 ns3, Nincluded ns1 ns2 -> Nincluded ns2 ns3 ->
  Nincluded ns1 ns3.
Proof.
  un. intros. unfold NS.Subset in *. eauto.
Qed.

Lemma Nincluded_refl: forall ns, Nincluded ns ns.
Proof.
  un. unfold NS.Subset. eauto.
Qed.
Hint Resolve Nincluded_trans Nincluded_refl: nset.


Definition Nempty: NSet := NS.empty.

Hint Unfold Nempty: nset.



Definition is_Nin n (ns:NSet) := NS.mem n ns.
Hint Unfold is_Nin: nset.


Lemma is_Nin_NIn: forall n ns, is_Nin n ns = true -> In_NSet n ns.
Proof.
  intros.
  un. rewrite NS.mem_spec in H. assumption.
Qed.

Lemma NIn_is_Nin: forall n ns, In_NSet n ns -> is_Nin n ns = true.
Proof.
  un. intros. rewrite NS.mem_spec. assumption.
Qed.


Definition Nadd (n: N) (tree: NSet) := NS.add n tree.
Hint Unfold Nadd: nset.



Lemma Nempty_empty: forall n, ~In_NSet n Nempty.
Proof.
  un. intros. apply NS.empty_spec.
Qed.

Hint Extern 1 =>
  match goal with
    H: NS.In _ NS.empty |- _ => apply NS.empty_spec in H; inv H
  end: nset.

(* Correction of Padd*)

Lemma Nadd_In: forall n ns, In_NSet n (Nadd n ns).
Proof.
  un.
  intros.
  edestruct NS.add_spec; eauto.
Qed.

Lemma Nadd_before_In: forall n1 ns, In_NSet n1 ns -> forall n2, In_NSet n1 (Nadd n2 ns).
Proof.
  un.
  intros.
  edestruct NS.add_spec; eauto.
Qed.

Lemma Nadd_In_or: forall n2 n1 ns, In_NSet n1 (Nadd n2 ns) -> n1 = n2 \/ In_NSet n1 ns.
Proof.
  un.
  intros.
  edestruct NS.add_spec; eauto.
Qed.

Lemma Nadd_Nincluded: forall n ns, Nincluded ns (Nadd n ns).
Proof.
  un. unfold NS.Subset.
  intros.
  edestruct NS.add_spec; eauto.
Qed.



Hint Resolve Nadd_In Nadd_before_In Nadd_In_or Nadd_Nincluded: nset.

Definition is_Nincluded (ns1 ns2: NSet) := NS.subset ns1 ns2.
Hint Unfold is_Nincluded: nset.


Lemma is_Nincluded_Nempty: forall ns, is_Nincluded ns Nempty = true ->
  forall n, ~In_NSet n ns.
Proof.
  un.
  intros. intro.
  apply NS.subset_spec in H. unfold NS.Subset in H.
  specialize (H n H0). auto with nset.
Qed.


Lemma is_Nincluded_included: forall ns1 ns2, is_Nincluded ns1 ns2 = true ->
  Nincluded ns1 ns2.
Proof.
  un.
  intros. apply NS.subset_spec. assumption.
Qed.


