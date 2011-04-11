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

Require Import List.
Require Import Lib.
Require Import Omega.
Require Export Byte.
Open Scope positive_scope.
Open Scope N_scope.



(* add [trans] 0 bits *)

Fixpoint translate_P_by trans (p: positive) :=
  match trans with
    | O => p
    | S t' => translate_P_by t' (p~0)
  end.

Definition translate_N_by trans (n: N) :=
  match n with
    | N0 => N0
    | Npos p => Npos (translate_P_by trans p)
  end.

(* specialisation for efficiency reasons *)
Definition translate_N_by_four n :=
  match n with
    | N0 => N0
    | Npos p => Npos (p~0~0~0~0)
  end.

Definition translate_N_by_eight n :=
  match n with
    | 0 => 0
    | Npos p => Npos (p~0~0~0~0~0~0~0~0)
  end.

Lemma translate_N_by_four_correct: forall n, translate_N_by_four n = translate_N_by 4 n.
Proof.
  intros [|pos]; reflexivity.
Qed.

Lemma translate_N_by_eight_correct: forall n, translate_N_by_eight n = translate_N_by 8 n.
Proof.
  intros [|pos]; reflexivity.
Qed.


Definition N_of_byte (b: byte) : N:=
  match b with
    | B00 => 0
    | B01 => 1
    | B02 => 2
    | B03 => 3
    | B04 => 4
    | B05 => 5
    | B06 => 6
    | B07 => 7
    | B08 => 8
    | B09 => 9
    | B0A => 10
    | B0B => 11
    | B0C => 12
    | B0D => 13
    | B0E => 14
    | B0F => 15
    | B10 => 16
    | B11 => 17
    | B12 => 18
    | B13 => 19
    | B14 => 20
    | B15 => 21
    | B16 => 22
    | B17 => 23
    | B18 => 24
    | B19 => 25
    | B1A => 26
    | B1B => 27
    | B1C => 28
    | B1D => 29
    | B1E => 30
    | B1F => 31
    | B20 => 32
    | B21 => 33
    | B22 => 34
    | B23 => 35
    | B24 => 36
    | B25 => 37
    | B26 => 38
    | B27 => 39
    | B28 => 40
    | B29 => 41
    | B2A => 42
    | B2B => 43
    | B2C => 44
    | B2D => 45
    | B2E => 46
    | B2F => 47
    | B30 => 48
    | B31 => 49
    | B32 => 50
    | B33 => 51
    | B34 => 52
    | B35 => 53
    | B36 => 54
    | B37 => 55
    | B38 => 56
    | B39 => 57
    | B3A => 58
    | B3B => 59
    | B3C => 60
    | B3D => 61
    | B3E => 62
    | B3F => 63
    | B40 => 64
    | B41 => 65
    | B42 => 66
    | B43 => 67
    | B44 => 68
    | B45 => 69
    | B46 => 70
    | B47 => 71
    | B48 => 72
    | B49 => 73
    | B4A => 74
    | B4B => 75
    | B4C => 76
    | B4D => 77
    | B4E => 78
    | B4F => 79
    | B50 => 80
    | B51 => 81
    | B52 => 82
    | B53 => 83
    | B54 => 84
    | B55 => 85
    | B56 => 86
    | B57 => 87
    | B58 => 88
    | B59 => 89
    | B5A => 90
    | B5B => 91
    | B5C => 92
    | B5D => 93
    | B5E => 94
    | B5F => 95
    | B60 => 96
    | B61 => 97
    | B62 => 98
    | B63 => 99
    | B64 => 100
    | B65 => 101
    | B66 => 102
    | B67 => 103
    | B68 => 104
    | B69 => 105
    | B6A => 106
    | B6B => 107
    | B6C => 108
    | B6D => 109
    | B6E => 110
    | B6F => 111
    | B70 => 112
    | B71 => 113
    | B72 => 114
    | B73 => 115
    | B74 => 116
    | B75 => 117
    | B76 => 118
    | B77 => 119
    | B78 => 120
    | B79 => 121
    | B7A => 122
    | B7B => 123
    | B7C => 124
    | B7D => 125
    | B7E => 126
    | B7F => 127
    | B80 => 128
    | B81 => 129
    | B82 => 130
    | B83 => 131
    | B84 => 132
    | B85 => 133
    | B86 => 134
    | B87 => 135
    | B88 => 136
    | B89 => 137
    | B8A => 138
    | B8B => 139
    | B8C => 140
    | B8D => 141
    | B8E => 142
    | B8F => 143
    | B90 => 144
    | B91 => 145
    | B92 => 146
    | B93 => 147
    | B94 => 148
    | B95 => 149
    | B96 => 150
    | B97 => 151
    | B98 => 152
    | B99 => 153
    | B9A => 154
    | B9B => 155
    | B9C => 156
    | B9D => 157
    | B9E => 158
    | B9F => 159
    | BA0 => 160
    | BA1 => 161
    | BA2 => 162
    | BA3 => 163
    | BA4 => 164
    | BA5 => 165
    | BA6 => 166
    | BA7 => 167
    | BA8 => 168
    | BA9 => 169
    | BAA => 170
    | BAB => 171
    | BAC => 172
    | BAD => 173
    | BAE => 174
    | BAF => 175
    | BB0 => 176
    | BB1 => 177
    | BB2 => 178
    | BB3 => 179
    | BB4 => 180
    | BB5 => 181
    | BB6 => 182
    | BB7 => 183
    | BB8 => 184
    | BB9 => 185
    | BBA => 186
    | BBB => 187
    | BBC => 188
    | BBD => 189
    | BBE => 190
    | BBF => 191
    | BC0 => 192
    | BC1 => 193
    | BC2 => 194
    | BC3 => 195
    | BC4 => 196
    | BC5 => 197
    | BC6 => 198
    | BC7 => 199
    | BC8 => 200
    | BC9 => 201
    | BCA => 202
    | BCB => 203
    | BCC => 204
    | BCD => 205
    | BCE => 206
    | BCF => 207
    | BD0 => 208
    | BD1 => 209
    | BD2 => 210
    | BD3 => 211
    | BD4 => 212
    | BD5 => 213
    | BD6 => 214
    | BD7 => 215
    | BD8 => 216
    | BD9 => 217
    | BDA => 218
    | BDB => 219
    | BDC => 220
    | BDD => 221
    | BDE => 222
    | BDF => 223
    | BE0 => 224
    | BE1 => 225
    | BE2 => 226
    | BE3 => 227
    | BE4 => 228
    | BE5 => 229
    | BE6 => 230
    | BE7 => 231
    | BE8 => 232
    | BE9 => 233
    | BEA => 234
    | BEB => 235
    | BEC => 236
    | BED => 237
    | BEE => 238
    | BEF => 239
    | BF0 => 240
    | BF1 => 241
    | BF2 => 242
    | BF3 => 243
    | BF4 => 244
    | BF5 => 245
    | BF6 => 246
    | BF7 => 247
    | BF8 => 248
    | BF9 => 249
    | BFA => 250
    | BFB => 251
    | BFC => 252
    | BFD => 253
    | BFE => 254
    | BFF => 255
  end.


Definition byte0 : byte := B00.


Goal N_of_byte B00 = 0.
  reflexivity. Qed.
Goal N_of_byte B05 = 5.
  reflexivity. Qed.
Goal N_of_byte B24 = 36.
  reflexivity. Qed.


Definition concat_byte n (b: byte) :=
  translate_N_by_eight n + N_of_byte b.


(* a word is four byte, little endian *)
Inductive word := W : byte -> byte -> byte -> byte -> word.

Lemma word_eq_dec: forall (w1 w2: word), {w1 = w2}+{w1 <> w2}.
Proof.
  unfold eq_dec; decide equality; apply byte_eq_dec.
Qed.

Definition N_of_word w :=
  match w with
    | W b4 b3 b2 b1 =>
      let n4 := N_of_byte b4 in
      let n3 := concat_byte n4 b3 in
      let n2 := concat_byte n3 b2 in
      concat_byte n2 b1
  end.

(* 0xDEADBEEF *)
Goal N_of_word (W BDE BAD BBE BEF) = 3735928559.
  reflexivity. Qed.


(* logical and *)

Fixpoint bool_list_of_P p : list bool :=
  match p with
    | xH => true :: nil
    | xO p' => false :: bool_list_of_P p'
    | xI p' => true :: bool_list_of_P p'
  end.

Fixpoint P_of_bool_list l : option positive :=
  match l with
    | nil => None
    | false :: l' =>
      match P_of_bool_list l' with
        | None => None
        | Some p => Some (xO p)
      end
    | true :: l' =>
      match P_of_bool_list l' with
        | None => Some xH
        | Some p => Some (xI p)
      end
  end.

Lemma P_of_bool_list_of_P: forall p, P_of_bool_list (bool_list_of_P p) = Some p.
Proof.
  induction' p; auto; simpl; rewrite IHp; congruence.
Qed.

Definition bool_list_of_N n :=
  match n with
    | N0 => nil
    | Npos pos => bool_list_of_P pos
  end.

Definition N_of_bool_list l :=
  match P_of_bool_list l with
    | None => N0
    | Some pos => Npos pos
  end.

Lemma N_of_bool_list_of_N: forall n, N_of_bool_list (bool_list_of_N n) = n.
Proof.
  destruct n; unfold bool_list_of_N, N_of_bool_list; simpl.
  reflexivity.
  rewrite P_of_bool_list_of_P. reflexivity.
Qed.

Fixpoint list_and l1 l2 : list bool :=
  match l1, l2 with
    | nil, _
    | _, nil => nil
    | b1:: l1', b2::l2' => (b1 && b2)%bool :: list_and l1' l2'
  end.

Definition N_and n1 n2 :=
  N_of_bool_list (list_and (bool_list_of_N n1) (bool_list_of_N n2)).

Lemma list_and_same: forall l, list_and l l = l.
Proof.
  induction' l as [|b l]; simpl; auto.
  Case "cons b l".
  destruct b; f_equal; auto.
Qed.

Lemma N_and_same: forall n, N_and n n = n.
Proof.
  intros.
  unfold N_and. rewrite list_and_same. apply N_of_bool_list_of_N.
Qed.

