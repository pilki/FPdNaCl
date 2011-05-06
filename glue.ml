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

open Byte
open BinaryDefs
open LazyList


(* build a byte from an int. This int *has* to be between 0 and
   255 included. Fails loudly if it is not the case*)

let byte_of_int = function
  | 0 -> B00
  | 1 -> B01
  | 2 -> B02
  | 3 -> B03
  | 4 -> B04
  | 5 -> B05
  | 6 -> B06
  | 7 -> B07
  | 8 -> B08
  | 9 -> B09
  | 10 -> B0A
  | 11 -> B0B
  | 12 -> B0C
  | 13 -> B0D
  | 14 -> B0E
  | 15 -> B0F
  | 16 -> B10
  | 17 -> B11
  | 18 -> B12
  | 19 -> B13
  | 20 -> B14
  | 21 -> B15
  | 22 -> B16
  | 23 -> B17
  | 24 -> B18
  | 25 -> B19
  | 26 -> B1A
  | 27 -> B1B
  | 28 -> B1C
  | 29 -> B1D
  | 30 -> B1E
  | 31 -> B1F
  | 32 -> B20
  | 33 -> B21
  | 34 -> B22
  | 35 -> B23
  | 36 -> B24
  | 37 -> B25
  | 38 -> B26
  | 39 -> B27
  | 40 -> B28
  | 41 -> B29
  | 42 -> B2A
  | 43 -> B2B
  | 44 -> B2C
  | 45 -> B2D
  | 46 -> B2E
  | 47 -> B2F
  | 48 -> B30
  | 49 -> B31
  | 50 -> B32
  | 51 -> B33
  | 52 -> B34
  | 53 -> B35
  | 54 -> B36
  | 55 -> B37
  | 56 -> B38
  | 57 -> B39
  | 58 -> B3A
  | 59 -> B3B
  | 60 -> B3C
  | 61 -> B3D
  | 62 -> B3E
  | 63 -> B3F
  | 64 -> B40
  | 65 -> B41
  | 66 -> B42
  | 67 -> B43
  | 68 -> B44
  | 69 -> B45
  | 70 -> B46
  | 71 -> B47
  | 72 -> B48
  | 73 -> B49
  | 74 -> B4A
  | 75 -> B4B
  | 76 -> B4C
  | 77 -> B4D
  | 78 -> B4E
  | 79 -> B4F
  | 80 -> B50
  | 81 -> B51
  | 82 -> B52
  | 83 -> B53
  | 84 -> B54
  | 85 -> B55
  | 86 -> B56
  | 87 -> B57
  | 88 -> B58
  | 89 -> B59
  | 90 -> B5A
  | 91 -> B5B
  | 92 -> B5C
  | 93 -> B5D
  | 94 -> B5E
  | 95 -> B5F
  | 96 -> B60
  | 97 -> B61
  | 98 -> B62
  | 99 -> B63
  | 100 -> B64
  | 101 -> B65
  | 102 -> B66
  | 103 -> B67
  | 104 -> B68
  | 105 -> B69
  | 106 -> B6A
  | 107 -> B6B
  | 108 -> B6C
  | 109 -> B6D
  | 110 -> B6E
  | 111 -> B6F
  | 112 -> B70
  | 113 -> B71
  | 114 -> B72
  | 115 -> B73
  | 116 -> B74
  | 117 -> B75
  | 118 -> B76
  | 119 -> B77
  | 120 -> B78
  | 121 -> B79
  | 122 -> B7A
  | 123 -> B7B
  | 124 -> B7C
  | 125 -> B7D
  | 126 -> B7E
  | 127 -> B7F
  | 128 -> B80
  | 129 -> B81
  | 130 -> B82
  | 131 -> B83
  | 132 -> B84
  | 133 -> B85
  | 134 -> B86
  | 135 -> B87
  | 136 -> B88
  | 137 -> B89
  | 138 -> B8A
  | 139 -> B8B
  | 140 -> B8C
  | 141 -> B8D
  | 142 -> B8E
  | 143 -> B8F
  | 144 -> B90
  | 145 -> B91
  | 146 -> B92
  | 147 -> B93
  | 148 -> B94
  | 149 -> B95
  | 150 -> B96
  | 151 -> B97
  | 152 -> B98
  | 153 -> B99
  | 154 -> B9A
  | 155 -> B9B
  | 156 -> B9C
  | 157 -> B9D
  | 158 -> B9E
  | 159 -> B9F
  | 160 -> BA0
  | 161 -> BA1
  | 162 -> BA2
  | 163 -> BA3
  | 164 -> BA4
  | 165 -> BA5
  | 166 -> BA6
  | 167 -> BA7
  | 168 -> BA8
  | 169 -> BA9
  | 170 -> BAA
  | 171 -> BAB
  | 172 -> BAC
  | 173 -> BAD
  | 174 -> BAE
  | 175 -> BAF
  | 176 -> BB0
  | 177 -> BB1
  | 178 -> BB2
  | 179 -> BB3
  | 180 -> BB4
  | 181 -> BB5
  | 182 -> BB6
  | 183 -> BB7
  | 184 -> BB8
  | 185 -> BB9
  | 186 -> BBA
  | 187 -> BBB
  | 188 -> BBC
  | 189 -> BBD
  | 190 -> BBE
  | 191 -> BBF
  | 192 -> BC0
  | 193 -> BC1
  | 194 -> BC2
  | 195 -> BC3
  | 196 -> BC4
  | 197 -> BC5
  | 198 -> BC6
  | 199 -> BC7
  | 200 -> BC8
  | 201 -> BC9
  | 202 -> BCA
  | 203 -> BCB
  | 204 -> BCC
  | 205 -> BCD
  | 206 -> BCE
  | 207 -> BCF
  | 208 -> BD0
  | 209 -> BD1
  | 210 -> BD2
  | 211 -> BD3
  | 212 -> BD4
  | 213 -> BD5
  | 214 -> BD6
  | 215 -> BD7
  | 216 -> BD8
  | 217 -> BD9
  | 218 -> BDA
  | 219 -> BDB
  | 220 -> BDC
  | 221 -> BDD
  | 222 -> BDE
  | 223 -> BDF
  | 224 -> BE0
  | 225 -> BE1
  | 226 -> BE2
  | 227 -> BE3
  | 228 -> BE4
  | 229 -> BE5
  | 230 -> BE6
  | 231 -> BE7
  | 232 -> BE8
  | 233 -> BE9
  | 234 -> BEA
  | 235 -> BEB
  | 236 -> BEC
  | 237 -> BED
  | 238 -> BEE
  | 239 -> BEF
  | 240 -> BF0
  | 241 -> BF1
  | 242 -> BF2
  | 243 -> BF3
  | 244 -> BF4
  | 245 -> BF5
  | 246 -> BF6
  | 247 -> BF7
  | 248 -> BF8
  | 249 -> BF9
  | 250 -> BFA
  | 251 -> BFB
  | 252 -> BFC
  | 253 -> BFD
  | 254 -> BFE
  | 255 -> BFF
  | _ -> assert false


(* build a byte (pair of two half byte) from a char *)

let byte_of_char c : byte =
  byte_of_int (int_of_char c)


(* some unit test *)
let _ = assert (byte_of_char (char_of_int 0xF0) = BF0)
let _ = assert (byte_of_char (char_of_int 0x1F) = B1F)
let _ = assert (byte_of_char (char_of_int 0x27) = B27)


(* build the lazy list of bytes from an input channel *)
let rec lasy_list_of_ic ic =
  try
    let c = input_char ic in
    Coq_ll_cons (byte_of_char c, lazy (Lazy (lasy_list_of_ic ic)))
  with
  | End_of_file -> Coq_ll_nil

let _ =
  if ASM.validate_program (lasy_list_of_ic stdin) then
    (print_string "The code has been validated\n"; exit 0)
  else
    (print_string "This code might be dangerous. REJECTED\n"; exit 1)
