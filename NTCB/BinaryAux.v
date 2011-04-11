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
Require Export BinaryDefs.
Open Scope positive_scope.
Open Scope N_scope.



Fixpoint fst_n_bits_of_pos (count: nat) (pos: positive) :=
  match count, pos with
    | O, _ => 0
    | S c, xH => 1
    | S c, xI pos' =>
      match fst_n_bits_of_pos c pos' with
        | 0 => 1
        | Npos p => Npos (p ~1)
      end
    | S c, xO pos' =>
      match fst_n_bits_of_pos c pos' with
        | 0 => 0
        | Npos p => Npos (p ~0)
      end
  end.


Definition fst_8_bits_of_N n :=
  match n with
    | N0 => N0
    | Npos p => fst_n_bits_of_pos 8 p
  end.

Definition byte_of_N n :=
  match fst_8_bits_of_N n with
    | 0 => B00
    | 1 => B01
    | 2 => B02
    | 3 => B03
    | 4 => B04
    | 5 => B05
    | 6 => B06
    | 7 => B07
    | 8 => B08
    | 9 => B09
    | 10 => B0A
    | 11 => B0B
    | 12 => B0C
    | 13 => B0D
    | 14 => B0E
    | 15 => B0F
    | 16 => B10
    | 17 => B11
    | 18 => B12
    | 19 => B13
    | 20 => B14
    | 21 => B15
    | 22 => B16
    | 23 => B17
    | 24 => B18
    | 25 => B19
    | 26 => B1A
    | 27 => B1B
    | 28 => B1C
    | 29 => B1D
    | 30 => B1E
    | 31 => B1F
    | 32 => B20
    | 33 => B21
    | 34 => B22
    | 35 => B23
    | 36 => B24
    | 37 => B25
    | 38 => B26
    | 39 => B27
    | 40 => B28
    | 41 => B29
    | 42 => B2A
    | 43 => B2B
    | 44 => B2C
    | 45 => B2D
    | 46 => B2E
    | 47 => B2F
    | 48 => B30
    | 49 => B31
    | 50 => B32
    | 51 => B33
    | 52 => B34
    | 53 => B35
    | 54 => B36
    | 55 => B37
    | 56 => B38
    | 57 => B39
    | 58 => B3A
    | 59 => B3B
    | 60 => B3C
    | 61 => B3D
    | 62 => B3E
    | 63 => B3F
    | 64 => B40
    | 65 => B41
    | 66 => B42
    | 67 => B43
    | 68 => B44
    | 69 => B45
    | 70 => B46
    | 71 => B47
    | 72 => B48
    | 73 => B49
    | 74 => B4A
    | 75 => B4B
    | 76 => B4C
    | 77 => B4D
    | 78 => B4E
    | 79 => B4F
    | 80 => B50
    | 81 => B51
    | 82 => B52
    | 83 => B53
    | 84 => B54
    | 85 => B55
    | 86 => B56
    | 87 => B57
    | 88 => B58
    | 89 => B59
    | 90 => B5A
    | 91 => B5B
    | 92 => B5C
    | 93 => B5D
    | 94 => B5E
    | 95 => B5F
    | 96 => B60
    | 97 => B61
    | 98 => B62
    | 99 => B63
    | 100 => B64
    | 101 => B65
    | 102 => B66
    | 103 => B67
    | 104 => B68
    | 105 => B69
    | 106 => B6A
    | 107 => B6B
    | 108 => B6C
    | 109 => B6D
    | 110 => B6E
    | 111 => B6F
    | 112 => B70
    | 113 => B71
    | 114 => B72
    | 115 => B73
    | 116 => B74
    | 117 => B75
    | 118 => B76
    | 119 => B77
    | 120 => B78
    | 121 => B79
    | 122 => B7A
    | 123 => B7B
    | 124 => B7C
    | 125 => B7D
    | 126 => B7E
    | 127 => B7F
    | 128 => B80
    | 129 => B81
    | 130 => B82
    | 131 => B83
    | 132 => B84
    | 133 => B85
    | 134 => B86
    | 135 => B87
    | 136 => B88
    | 137 => B89
    | 138 => B8A
    | 139 => B8B
    | 140 => B8C
    | 141 => B8D
    | 142 => B8E
    | 143 => B8F
    | 144 => B90
    | 145 => B91
    | 146 => B92
    | 147 => B93
    | 148 => B94
    | 149 => B95
    | 150 => B96
    | 151 => B97
    | 152 => B98
    | 153 => B99
    | 154 => B9A
    | 155 => B9B
    | 156 => B9C
    | 157 => B9D
    | 158 => B9E
    | 159 => B9F
    | 160 => BA0
    | 161 => BA1
    | 162 => BA2
    | 163 => BA3
    | 164 => BA4
    | 165 => BA5
    | 166 => BA6
    | 167 => BA7
    | 168 => BA8
    | 169 => BA9
    | 170 => BAA
    | 171 => BAB
    | 172 => BAC
    | 173 => BAD
    | 174 => BAE
    | 175 => BAF
    | 176 => BB0
    | 177 => BB1
    | 178 => BB2
    | 179 => BB3
    | 180 => BB4
    | 181 => BB5
    | 182 => BB6
    | 183 => BB7
    | 184 => BB8
    | 185 => BB9
    | 186 => BBA
    | 187 => BBB
    | 188 => BBC
    | 189 => BBD
    | 190 => BBE
    | 191 => BBF
    | 192 => BC0
    | 193 => BC1
    | 194 => BC2
    | 195 => BC3
    | 196 => BC4
    | 197 => BC5
    | 198 => BC6
    | 199 => BC7
    | 200 => BC8
    | 201 => BC9
    | 202 => BCA
    | 203 => BCB
    | 204 => BCC
    | 205 => BCD
    | 206 => BCE
    | 207 => BCF
    | 208 => BD0
    | 209 => BD1
    | 210 => BD2
    | 211 => BD3
    | 212 => BD4
    | 213 => BD5
    | 214 => BD6
    | 215 => BD7
    | 216 => BD8
    | 217 => BD9
    | 218 => BDA
    | 219 => BDB
    | 220 => BDC
    | 221 => BDD
    | 222 => BDE
    | 223 => BDF
    | 224 => BE0
    | 225 => BE1
    | 226 => BE2
    | 227 => BE3
    | 228 => BE4
    | 229 => BE5
    | 230 => BE6
    | 231 => BE7
    | 232 => BE8
    | 233 => BE9
    | 234 => BEA
    | 235 => BEB
    | 236 => BEC
    | 237 => BED
    | 238 => BEE
    | 239 => BEF
    | 240 => BF0
    | 241 => BF1
    | 242 => BF2
    | 243 => BF3
    | 244 => BF4
    | 245 => BF5
    | 246 => BF6
    | 247 => BF7
    | 248 => BF8
    | 249 => BF9
    | 250 => BFA
    | 251 => BFB
    | 252 => BFC
    | 253 => BFD
    | 254 => BFE
    | 255 => BFF
    | _ => B00
  end.

Lemma byte_of_N_of_byte: forall b,
  byte_of_N (N_of_byte b) = b.
Proof.
  destruct b; reflexivity.
Qed.


Fixpoint translate_P_right_by trans pos: option positive :=
  match trans, pos with
    | O, _ => Some pos
    | S _, xH => None
    | S trans', xI pos'
    | S trans', xO pos' => translate_P_right_by trans' pos'
  end.

Definition translate_N_right_by trans n : N :=
  match n with
    | N0 => N0
    | Npos pos =>
      match translate_P_right_by trans pos with
        | None => N0
        | Some p => Npos p
      end
  end.

Lemma translate_N_right_left: forall n, translate_N_right_by 8 (translate_N_by_eight n) = n.
Proof.
  destruct n; auto.
Qed.


Definition fst_byte n : (byte * N) :=
  (byte_of_N n, translate_N_right_by 8 n).




Lemma translate_P_xO: forall t p, translate_P_by t (p~0) = (translate_P_by t p)~0.
Proof.
  induction' t as [|t]; simpl; intros; auto.
Qed.

Lemma translate_P_plus: forall t1 t2 p, translate_P_by t1 (translate_P_by t2 p) = translate_P_by (t1 + t2) p.
Proof.
  induction' t1 as [|t1']; simpl; intros.
  Case "0%nat".
    destruct (translate_P_by t2 p); auto.
  Case "S t1'".
    repeat rewrite translate_P_xO. f_equal.
    auto.
Qed.

Lemma translate_N_plus: forall t1 t2 n, translate_N_by t1 (translate_N_by t2 n) = translate_N_by (t1 + t2) n.
Proof.
  intros. destruct n; simpl; auto.
  f_equal. apply translate_P_plus.
Qed.



Lemma translate_N_assoc: forall t n1 n2, translate_N_by t n1 + translate_N_by t n2 = translate_N_by t (n1 + n2).
Proof.
  intros.
  destruct' n1 as [|pos1]; destruct' n2 as [|pos2]; simpl; auto.
  Case "Npos pos1"; SCase "Npos pos2".
  f_equal.
  revert pos1 pos2.
  induction' t as [|t']; intros; simpl; auto.
  SSCase "S t'".
  rewrite IHt'. reflexivity.
Qed.



(*Lemma concat_byte_aux_correct: forall n b,
  concat_byte n b = concat_byte_aux n b.
Proof.
  unfold concat_byte, concat_byte_aux.
  destruct b as (hb2, hb1).
  unfold N_of_byte, concat_half_byte. simpl.
  repeat match goal with
    | |- context[translate_N_by_four ?n] =>
      rewrite (translate_N_by_four_correct n)
  end.
  repeat match goal with
    | |- context[translate_N_by_eight ?n] =>
      rewrite (translate_N_by_eight_correct n)
  end.

  destruct' n as [|pos].
  Case "0".
  simpl. reflexivity.
  Case "Npos pos".
  remember (N_of_half_byte hb1) as nhb1. clear Heqnhb1.
  remember (N_of_half_byte hb2) as nhb2. clear Heqnhb2.
  rewrite Nplus_assoc. f_equal.
  rewrite <- (translate_N_plus 4 4).
  rewrite translate_N_assoc. reflexivity.
Qed.*)


Definition word_of_N n :=
  let (b1, n1):= fst_byte n in
  let (b2, n2):= fst_byte n1 in
  let (b3, n3):= fst_byte n2 in
  let (b4, n4):= fst_byte n3 in
  W b4 b3 b2 b1.

Lemma translate_0_by t: translate_N_by t 0 = 0.
Proof. induction t; auto. Qed.

Lemma translate_N_by_0 n: translate_N_by 0 n = n.
Proof.
  destruct n; simpl; auto.
Qed.

Lemma translate_P_tilde_0 t: forall p, translate_P_by t (p~0) = (translate_P_by t p)~0.
Proof.
  induction t; auto.
  intro p. simpl. rewrite IHt. auto.
Qed.

Lemma translate_P_and: forall t p1 p2, (exists p1', p1 = translate_P_by t p1') ->
  forall p, P_of_bool_list (list_and (bool_list_of_P p1) (bool_list_of_P p2)) = Some p ->
  exists p', p = translate_P_by t p'.
Proof.
  induction' t as [|t]; intros * EXISTS * SOME.
  Case "0%nat".
    simpl. eauto.
  Case "S t".
    destruct EXISTS as [p1' Hp1'].

    replace (S t) with (1 + t)%nat in Hp1' by reflexivity.
    rewrite <- translate_P_plus in Hp1'.
    simpl in Hp1'. subst.
    simpl in SOME.


    destruct (bool_list_of_P p2) as [] _eqn. inv SOME.
    simpl in *.
    match type of SOME with
      | match ?EXP with | Some _ => _ | None => _ end = _ =>
        destruct EXP as [] _eqn
    end; inv SOME.

    destruct' p2 as [p2|p2|]; inv Heql.
    SCase "xI p2".
      edestruct IHt; eauto. exists x. rewrite translate_P_tilde_0. congruence.
    SCase "xO p2".
      edestruct IHt; eauto. exists x. rewrite translate_P_tilde_0. congruence.
    SCase "1%positive".
      destruct (bool_list_of_P (translate_P_by t p1')); inv Heqo.
Qed.


Lemma translate_and: forall t n1 n2, (exists n1', n1 = translate_N_by t n1') ->
  exists n, N_and n1 n2 = translate_N_by t n.
Proof.
  intros.
  destruct' n1 as [|pos1]; destruct' n2 as [|pos2]; unfold N_and; simpl;
    try solve [exists 0; rewrite translate_0_by; reflexivity].
  Case "Npos pos1"; SCase "0".
    exists 0. simpl.
    destruct (bool_list_of_P pos1); reflexivity.
  Case "Npos pos1"; SCase "Npos pos2".

  destruct H. destruct x; inversion H.

  unfold N_of_bool_list.
  destruct (P_of_bool_list (list_and (bool_list_of_P (translate_P_by t p)) (bool_list_of_P pos2))) as [] _eqn.
    edestruct translate_P_and.
    exists p. eassumption.
    subst. eassumption.
    exists (Npos x). simpl. congruence.

    exists 0. simpl. reflexivity.
Qed.
