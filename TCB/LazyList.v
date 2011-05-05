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
Require Import DoOption.
Set Implicit Arguments.
Require Import BinaryProps.
CoInductive lazy (X:Type) :=
| Lazy : X -> lazy X.
Implicit Arguments Lazy [[X]].

Unset Elimination Schemes.

Inductive lazy_list (X:Type) :=
| ll_nil: lazy_list X
| ll_cons: forall (x:X) (l: lazy (lazy_list X)), lazy_list X.

Implicit Arguments ll_nil [[X]].
Implicit Arguments ll_cons [[X]].

Notation "x ::: ll" := (ll_cons x (Lazy ll)) (at level 60, right associativity).

Notation "〈 〉" := (ll_nil).

Notation "〈 x ; .. ; z 〉" := (ll_cons x (Lazy ( .. (ll_cons z (Lazy ll_nil)) .. ))).


Set Elimination Schemes.

Fixpoint lazy_list_rect (A:Type) (P : lazy_list A -> Type) (Hnil: P ll_nil)
  (Hcons: forall (a: A) ll, P ll -> P (ll_cons a (Lazy ll))) (l: lazy_list A) : P l :=
  match l as l0 return P l0 with
    | 〈〉 => Hnil
    | x ::: l' => (Hcons x l' (lazy_list_rect P Hnil Hcons l'))
  end.

Implicit Arguments lazy_list_rect [A].

Definition lazy_list_ind (A:Type) (P : lazy_list A -> Prop) (Hnil: P ll_nil)
  (Hcons: forall (a: A) ll, P ll -> P (ll_cons a (Lazy ll))) (l: lazy_list A) : P l :=
  lazy_list_rect P Hnil Hcons l.

Fixpoint to_list {X} (ll: lazy_list X) : list X :=
  match ll with
    | 〈〉 => []
    | x ::: l' => x :: to_list l'
  end.

Fixpoint ll_length {X} (l: lazy_list X) : nat :=
  match l with
    | 〈〉 => O
    | x ::: l' => S (ll_length l')
  end.

Lemma ll_length_correct: forall {X} (ll: lazy_list X),
  ll_length ll = length (to_list ll).
Proof.
  induction ll; simpl; congruence.
Qed.


Fixpoint ll_nth {X} n (ll: lazy_list X) :=
  match n, ll with
    | _ ,〈〉 => None
    | O, x ::: _ => Some x
    | S n', _ ::: ll' => ll_nth n' ll'
  end.

Lemma ll_nth_correct: forall {X} n (ll: lazy_list X),
  ll_nth n ll = nth_error (to_list ll) n.
Proof.
  induction n; simpl; intros; destruct ll as [| x [ll'] ]; simpl; auto.
Qed.

Fixpoint ll_safe_drop {X} (n: nat) (ll: lazy_list X) :=
  match n with
    | O => Some ll
    | S n' =>
      match ll with
        | 〈〉 => None
        | x ::: ll' => ll_safe_drop n' ll'
      end
  end.

  (* to lib *)
Lemma ll_safe_drop_nth {X}: forall n (ll: lazy_list X) ll',
  ll_safe_drop n ll = Some ll' ->
  forall i, ll_nth i ll' = ll_nth (n + i) ll.
Proof.
  induction' n as [|n]; auto; simpl; intros; clean.
  Case "S n".
    destruct' ll as [|x [ll]]; clean.
Qed.




Lemma ll_safe_drop_size {X} n: forall  (ll ll': lazy_list X),
  ll_safe_drop n ll = Some ll' ->
  ll_length ll = (n + ll_length ll')%nat.
Proof.
  induction' n as [|n]; simpl; intros; clean.
  Case "S n".
  destruct ll as [| ? [ll2]]; clean.
  specialize (IHn _ _ H).
  simpl in *. congruence.
Qed.


Fixpoint ll_safe_take {X} (n: nat) (ll: lazy_list X) :=
  match n with
    | O => Some 〈〉
    | S n' =>
      match ll with
        | 〈〉 => None
        | x ::: ll' =>
          do ll'' <- ll_safe_take n' ll';
          Some (x ::: ll'')
      end
  end.

Lemma ll_safe_take_size {X} n: forall  (ll ll': lazy_list X),
  ll_safe_take n ll = Some ll' ->
  ll_length ll' = n.
Proof.
  induction n; simpl;intros; clean; eauto.
  destruct ll as [|x []]; clean. inv_opt.
  simpl. f_equal. eauto.
Qed.


(*Definition byte_map := nat -> option byte.
Definition eq_byte_map (bm1 bm2: byte_map) := forall n, bm1 n = bm2 n.
Notation "bm1 ≡ bm2" := (eq_byte_map bm1 bm2) (at level 70, no associativity).


Definition start_map_from (start: nat) (bm: byte_map) : byte_map :=
  fun n => bm (start + n)%nat.

Lemma start_map_from_0: forall bm, start_map_from 0 bm ≡ bm.
Proof.
  intros bm n.
  unfold start_map_from. simpl. reflexivity.
Qed.

Lemma start_map_from_right: forall start bm n,
  (start_map_from start bm n) = bm (n + start)%nat.
Proof.
  intros; simpl. unfold start_map_from. f_equal. omega.
Qed.

Definition update_byte_map (bm: byte_map) (loc:nat) (ob: option byte): byte_map :=
  fun n =>
    if eq_nat_dec n loc then ob else bm n.


Definition byte_map_from_ll (ll: lazy_list byte) : byte_map:=
  fun n => ll_nth n ll. *)
