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


(* Tree representing a set of positive *)
Inductive PSet :=
| PLeaf: bool -> PSet
| PNode:  PSet -> bool -> PSet -> PSet.

Inductive In_PSet: positive -> PSet -> Prop:=
| xH_In_PLeaf: In_PSet xH (PLeaf true)
| xH_In_PNode: forall psO psI, In_PSet xH (PNode psO true psI)
| xO_In_PNode: forall (p: positive) (psO psI: PSet) (b:bool),
  In_PSet p psO -> In_PSet (xO p) (PNode psO b psI)
| xI_In_PNode: forall (p: positive) (psO psI: PSet) (b:bool),
  In_PSet p psI -> In_PSet (xI p) (PNode psO b psI).

Hint Constructors In_PSet: nset.

Definition Pincluded ps1 ps2 := forall p, In_PSet p ps1 -> In_PSet p ps2.

Lemma Pincluded_trans: forall ps1 ps2 ps3, Pincluded ps1 ps2 -> Pincluded ps2 ps3 ->
  Pincluded ps1 ps3.
Proof.
  unfold Pincluded. intros. eauto.
Qed.

Definition Pempty := PLeaf false.

Hint Unfold Pempty: nset.

Fixpoint is_Pin pos ps :=
  match pos with
    | xH =>
      match ps with
        | PLeaf true
        | PNode _ true _ => true
        | _ => false
      end
    | xI pos' =>
      match ps with
        | PLeaf _ => false
        | PNode _ _ psI => is_Pin pos' psI
      end
    | xO pos' =>
      match ps with
        | PLeaf _ => false
        | PNode psO _ _ => is_Pin pos' psO
      end
  end.

Lemma is_Pin_PIn: forall pos ps, is_Pin pos ps = true -> In_PSet pos ps.
Proof.
  induction' pos; intros * IN; inv IN.
  Case "xI".
    destruct ps; try congruence; eauto with nset.
  Case "xO".
    destruct ps; try congruence; eauto with nset.
  Case "1%positive".
    destruct ps; destruct b; eauto with nset; congruence.
Qed.

Lemma PIn_is_Pin: forall pos ps, In_PSet pos ps -> is_Pin pos ps = true.
Proof.
  intros * IN.
  induction' IN; simpl; auto.
Qed.

Fixpoint Padd (pos: positive) (tree: PSet) :=
  match pos with
    | xH =>
      match tree with
        | PLeaf _ => PLeaf true
        | PNode psO _ psI => PNode psO true psI
      end
    | xI pos' =>
      match tree with
        | PLeaf b => PNode Pempty b (Padd pos' Pempty)
        | PNode psO b psI => PNode psO b (Padd pos' psI)
      end
    | xO pos' =>
      match tree with
        | PLeaf b => PNode (Padd pos' Pempty) b Pempty
        | PNode psO b psI => PNode (Padd pos' psO) b psI
      end
  end.

Lemma Pempty_empty: forall pos, ~In_PSet pos Pempty.
Proof.
  intros pos IN.
  unfold Pempty in IN. destruct pos; inv IN.
Qed.

Hint Extern 1 =>
  match goal with
    H: In_PSet ?p Pempty |- _ => inv H
  end: nset.

(* Correction of Padd*)

Lemma Padd_In: forall pos ps, In_PSet pos (Padd pos ps).
Proof.
  induction' pos as [pos'|pos'|]; intro ps; simpl; destruct ps; auto with nset.
Qed.

Lemma Padd_before_In: forall pos1 ps, In_PSet pos1 ps -> forall pos2, In_PSet pos1 (Padd pos2 ps).
Proof.
  intros * IN.
  induction' IN; intros pos2; destruct' pos2; simpl; auto with nset.
Qed.

Lemma Padd_In_or: forall pos2 pos1 ps, In_PSet pos1 (Padd pos2 ps) -> pos1 = pos2 \/ In_PSet pos1 ps.
Proof.
  intros pos2.
  induction' pos2; intros * IN; destruct' ps; simpl in *; inv IN; auto with nset;
  edestruct IHpos2; eauto; subst; eauto with nset.
Qed.

Lemma Padd_Pincluded: forall pos ps, Pincluded ps (Padd pos ps).
Proof.
  unfold Pincluded.
  intros. apply Padd_before_In. assumption.
Qed.

Definition imp_bool b1 b2 :=
  match b1, b2 with
    | _, true => true
    | false, false => true
    | true, false => false
  end.


Fixpoint is_Pincluded ps1 ps2 :=
  match ps1 with
    | PLeaf false => true
    | PLeaf true =>
      match ps2 with
        | PLeaf b2
        | PNode _ b2 _ => imp_bool true b2
      end
    | PNode psO1 b1 psI1 =>
      match ps2 with
        | PLeaf b2 =>
          imp_bool b1 b2 && is_Pincluded psO1 Pempty && is_Pincluded psI1 Pempty
        | PNode psO2 b2 psI2 =>
          imp_bool b1 b2 && is_Pincluded psO1 psO2 && is_Pincluded psI1 psI2
      end
  end.

Lemma is_Pincluded_Pempty: forall ps, is_Pincluded ps Pempty = true -> forall pos, ~In_PSet pos ps.
Proof.
  induction' ps; intros Pincl pos.
  Case "PLeaf".
  simpl in *.
  destruct b; try solve [inv Pincl].
  destruct pos; intro IN; inv IN.

  Case "PNode".
  simpl in Pincl.
  destruct b; simpl in *. inv Pincl.
  destruct (andb_prop _ _ Pincl) as [H1 H2].
  specialize (IHps1 H1). specialize (IHps2 H2).
  destruct' pos as [pos'|pos'|]; intro IN; inv IN; unfold not in *; eauto.
Qed.


Lemma is_Pincluded_Pincluded: forall ps1 ps2, is_Pincluded ps1 ps2 = true ->
  Pincluded ps1 ps2.
Proof.
  unfold Pincluded.
  induction' ps1; intros.
  Case "PLeaf".
  inv H0. simpl in H.
  destruct ps2; destruct b; inv H; auto with nset.

  Case "PNode".
  inv H0; simpl in *.
  destruct ps2; destruct b; simpl in *; try congruence; auto with nset.
  destruct ps2; match goal with | H: context[imp_bool ?b1 ?b2] |- _ => destruct (imp_bool b1 b2); simpl in H; try congruence;
                destruct (andb_prop _ _ H) end; eauto with nset.
  elimtype False. eapply (is_Pincluded_Pempty ps1_1); eauto.
  destruct ps2; match goal with | H: context[imp_bool ?b1 ?b2] |- _ => destruct (imp_bool b1 b2); simpl in H; try congruence;
                destruct (andb_prop _ _ H) end; eauto with nset.
  elimtype False. eapply (is_Pincluded_Pempty ps1_2); eauto.
Qed.


(* set of N *)

Definition NSet : Type := (bool * PSet)%type.

Inductive In_NSet: N -> NSet -> Prop :=
| In_N0: forall ps, In_NSet N0 (true, ps)
| In_Npos: forall pos b ps, In_PSet pos ps -> In_NSet (Npos pos) (b, ps).

Hint Constructors In_NSet: nset.

Definition Nincluded (ns1 ns2: NSet) := forall n, In_NSet n ns1 -> In_NSet n ns2.

Hint Unfold Nincluded: nset.

Lemma Nincluded_trans: forall ns1 ns2 ns3, Nincluded ns1 ns2 -> Nincluded ns2 ns3 ->
  Nincluded ns1 ns3.
Proof.
  unfold Nincluded. auto.
Qed.

Lemma Nincluded_refl: forall ns, Nincluded ns ns.
Proof.
  unfold Nincluded. auto.
Qed.
Hint Resolve Nincluded_trans Nincluded_refl: nset.


Definition Nempty: NSet := (false, Pempty).

Hint Unfold Nempty: nset.

Definition is_Nin n (ns:NSet) :=
  match n with
    | N0 => fst ns
    | Npos pos => is_Pin pos (snd ns)
  end.


Lemma is_Nin_NIn: forall n ns, is_Nin n ns = true -> In_NSet n ns.
Proof.
  intros.
  destruct' n; simpl in H; destruct ns as (b, ps).
  Case "0%N".
    destruct b; simpl in H; auto with nset; congruence.
  Case "Npos".
    simpl in H. apply is_Pin_PIn in H. auto with nset.
Qed.

Lemma NIn_is_Nin: forall n ns, In_NSet n ns -> is_Nin n ns = true.
Proof.
  intros * IN.
  inversion IN; simpl; auto using PIn_is_Pin.
Qed.

Definition Nadd (n: N) (tree: NSet) :=
  match n, tree with
    | N0, (_, ps) => (true, ps)
    | Npos pos, (b, ps) => (b, Padd pos ps)
  end.



Lemma Nempty_empty: forall n, ~In_NSet n Nempty.
Proof.
  intros n IN.
  inv IN. eapply Pempty_empty; eauto.
Qed.

Hint Extern 1 =>
  match goal with
    H: In_NSet _ Nempty |- _ => inv H
  end: nset.

(* Correction of Padd*)

Lemma Nadd_In: forall n ns, In_NSet n (Nadd n ns).
Proof.
  intros. destruct ns as (b, ps).
  destruct' n; simpl; auto using Padd_In with nset.
Qed.

Lemma Nadd_before_In: forall n1 ns, In_NSet n1 ns -> forall n2, In_NSet n1 (Nadd n2 ns).
Proof.
  intros * IN *.
  destruct ns as (b, ps).
  destruct n1; destruct n2; simpl in *; intros; inv IN; eauto using Padd_before_In with nset.
Qed.

Lemma Nadd_In_or: forall n2 n1 ns, In_NSet n1 (Nadd n2 ns) -> n1 = n2 \/ In_NSet n1 ns.
Proof.
  intros * IN.
  destruct ns as (b, ps).
  destruct n1; destruct n2; simpl in *; inv IN; eauto with nset.
  edestruct Padd_In_or; eauto with nset. subst. auto.
Qed.

Lemma Nadd_Nincluded: forall n ns, Nincluded ns (Nadd n ns).
Proof.
  unfold Nincluded.
  intros. apply Nadd_before_In. assumption.
Qed.



Hint Resolve Nadd_In Nadd_before_In Nadd_In_or Nadd_Nincluded: nset.

Definition is_Nincluded (ns1 ns2: NSet) :=
  imp_bool (fst ns1) (fst ns2) && is_Pincluded (snd ns1) (snd ns2).


Lemma is_Nincluded_Nempty: forall ns, is_Nincluded ns Nempty = true ->
  forall n, ~In_NSet n ns.
Proof.
  unfold is_Nincluded.
  intros * INCL n IN.
  destruct ns as (b, ps); destruct n; inv IN; simpl in *.
  inv INCL.
  eapply is_Pincluded_Pempty; eauto. destruct b; simpl in *; auto.
Qed.


Lemma is_Nincluded_included: forall ns1 ns2, is_Nincluded ns1 ns2 = true ->
  Nincluded ns1 ns2.
Proof.
  unfold Nincluded. unfold is_Nincluded.
  intros (b1, ps1) (b2, ps2) INC [|pos] IN.

  simpl in *. inv IN. destruct b2; auto with nset; simpl in *; congruence.

  simpl in *. destruct (andb_prop _ _ INC). inv IN.
  constructor.
  pose proof is_Pincluded_Pincluded. unfold Pincluded in *. eauto.
Qed.


