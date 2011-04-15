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
Definition translate_N_by_four n := Nval_16 * n.

Definition translate_N_by_eight n := Nval_256 * n.

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
    | B00 => Nval_0
    | B01 => Nval_1
    | B02 => Nval_2
    | B03 => Nval_3
    | B04 => Nval_4
    | B05 => Nval_5
    | B06 => Nval_6
    | B07 => Nval_7
    | B08 => Nval_8
    | B09 => Nval_9
    | B0A => Nval_10
    | B0B => Nval_11
    | B0C => Nval_12
    | B0D => Nval_13
    | B0E => Nval_14
    | B0F => Nval_15
    | B10 => Nval_16
    | B11 => Nval_17
    | B12 => Nval_18
    | B13 => Nval_19
    | B14 => Nval_20
    | B15 => Nval_21
    | B16 => Nval_22
    | B17 => Nval_23
    | B18 => Nval_24
    | B19 => Nval_25
    | B1A => Nval_26
    | B1B => Nval_27
    | B1C => Nval_28
    | B1D => Nval_29
    | B1E => Nval_30
    | B1F => Nval_31
    | B20 => Nval_32
    | B21 => Nval_33
    | B22 => Nval_34
    | B23 => Nval_35
    | B24 => Nval_36
    | B25 => Nval_37
    | B26 => Nval_38
    | B27 => Nval_39
    | B28 => Nval_40
    | B29 => Nval_41
    | B2A => Nval_42
    | B2B => Nval_43
    | B2C => Nval_44
    | B2D => Nval_45
    | B2E => Nval_46
    | B2F => Nval_47
    | B30 => Nval_48
    | B31 => Nval_49
    | B32 => Nval_50
    | B33 => Nval_51
    | B34 => Nval_52
    | B35 => Nval_53
    | B36 => Nval_54
    | B37 => Nval_55
    | B38 => Nval_56
    | B39 => Nval_57
    | B3A => Nval_58
    | B3B => Nval_59
    | B3C => Nval_60
    | B3D => Nval_61
    | B3E => Nval_62
    | B3F => Nval_63
    | B40 => Nval_64
    | B41 => Nval_65
    | B42 => Nval_66
    | B43 => Nval_67
    | B44 => Nval_68
    | B45 => Nval_69
    | B46 => Nval_70
    | B47 => Nval_71
    | B48 => Nval_72
    | B49 => Nval_73
    | B4A => Nval_74
    | B4B => Nval_75
    | B4C => Nval_76
    | B4D => Nval_77
    | B4E => Nval_78
    | B4F => Nval_79
    | B50 => Nval_80
    | B51 => Nval_81
    | B52 => Nval_82
    | B53 => Nval_83
    | B54 => Nval_84
    | B55 => Nval_85
    | B56 => Nval_86
    | B57 => Nval_87
    | B58 => Nval_88
    | B59 => Nval_89
    | B5A => Nval_90
    | B5B => Nval_91
    | B5C => Nval_92
    | B5D => Nval_93
    | B5E => Nval_94
    | B5F => Nval_95
    | B60 => Nval_96
    | B61 => Nval_97
    | B62 => Nval_98
    | B63 => Nval_99
    | B64 => Nval_100
    | B65 => Nval_101
    | B66 => Nval_102
    | B67 => Nval_103
    | B68 => Nval_104
    | B69 => Nval_105
    | B6A => Nval_106
    | B6B => Nval_107
    | B6C => Nval_108
    | B6D => Nval_109
    | B6E => Nval_110
    | B6F => Nval_111
    | B70 => Nval_112
    | B71 => Nval_113
    | B72 => Nval_114
    | B73 => Nval_115
    | B74 => Nval_116
    | B75 => Nval_117
    | B76 => Nval_118
    | B77 => Nval_119
    | B78 => Nval_120
    | B79 => Nval_121
    | B7A => Nval_122
    | B7B => Nval_123
    | B7C => Nval_124
    | B7D => Nval_125
    | B7E => Nval_126
    | B7F => Nval_127
    | B80 => Nval_128
    | B81 => Nval_129
    | B82 => Nval_130
    | B83 => Nval_131
    | B84 => Nval_132
    | B85 => Nval_133
    | B86 => Nval_134
    | B87 => Nval_135
    | B88 => Nval_136
    | B89 => Nval_137
    | B8A => Nval_138
    | B8B => Nval_139
    | B8C => Nval_140
    | B8D => Nval_141
    | B8E => Nval_142
    | B8F => Nval_143
    | B90 => Nval_144
    | B91 => Nval_145
    | B92 => Nval_146
    | B93 => Nval_147
    | B94 => Nval_148
    | B95 => Nval_149
    | B96 => Nval_150
    | B97 => Nval_151
    | B98 => Nval_152
    | B99 => Nval_153
    | B9A => Nval_154
    | B9B => Nval_155
    | B9C => Nval_156
    | B9D => Nval_157
    | B9E => Nval_158
    | B9F => Nval_159
    | BA0 => Nval_160
    | BA1 => Nval_161
    | BA2 => Nval_162
    | BA3 => Nval_163
    | BA4 => Nval_164
    | BA5 => Nval_165
    | BA6 => Nval_166
    | BA7 => Nval_167
    | BA8 => Nval_168
    | BA9 => Nval_169
    | BAA => Nval_170
    | BAB => Nval_171
    | BAC => Nval_172
    | BAD => Nval_173
    | BAE => Nval_174
    | BAF => Nval_175
    | BB0 => Nval_176
    | BB1 => Nval_177
    | BB2 => Nval_178
    | BB3 => Nval_179
    | BB4 => Nval_180
    | BB5 => Nval_181
    | BB6 => Nval_182
    | BB7 => Nval_183
    | BB8 => Nval_184
    | BB9 => Nval_185
    | BBA => Nval_186
    | BBB => Nval_187
    | BBC => Nval_188
    | BBD => Nval_189
    | BBE => Nval_190
    | BBF => Nval_191
    | BC0 => Nval_192
    | BC1 => Nval_193
    | BC2 => Nval_194
    | BC3 => Nval_195
    | BC4 => Nval_196
    | BC5 => Nval_197
    | BC6 => Nval_198
    | BC7 => Nval_199
    | BC8 => Nval_200
    | BC9 => Nval_201
    | BCA => Nval_202
    | BCB => Nval_203
    | BCC => Nval_204
    | BCD => Nval_205
    | BCE => Nval_206
    | BCF => Nval_207
    | BD0 => Nval_208
    | BD1 => Nval_209
    | BD2 => Nval_210
    | BD3 => Nval_211
    | BD4 => Nval_212
    | BD5 => Nval_213
    | BD6 => Nval_214
    | BD7 => Nval_215
    | BD8 => Nval_216
    | BD9 => Nval_217
    | BDA => Nval_218
    | BDB => Nval_219
    | BDC => Nval_220
    | BDD => Nval_221
    | BDE => Nval_222
    | BDF => Nval_223
    | BE0 => Nval_224
    | BE1 => Nval_225
    | BE2 => Nval_226
    | BE3 => Nval_227
    | BE4 => Nval_228
    | BE5 => Nval_229
    | BE6 => Nval_230
    | BE7 => Nval_231
    | BE8 => Nval_232
    | BE9 => Nval_233
    | BEA => Nval_234
    | BEB => Nval_235
    | BEC => Nval_236
    | BED => Nval_237
    | BEE => Nval_238
    | BEF => Nval_239
    | BF0 => Nval_240
    | BF1 => Nval_241
    | BF2 => Nval_242
    | BF3 => Nval_243
    | BF4 => Nval_244
    | BF5 => Nval_245
    | BF6 => Nval_246
    | BF7 => Nval_247
    | BF8 => Nval_248
    | BF9 => Nval_249
    | BFA => Nval_250
    | BFB => Nval_251
    | BFC => Nval_252
    | BFD => Nval_253
    | BFE => Nval_254
    | BFF => Nval_255
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

