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

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlZInt64.
Require ASM.
Require SemanticsProg.
Require Import Lib.

Extract Constant safe_minus => "MyInt64.safe_minus".

Extract Constant SemanticsProg.dividable_by_32_dec
  => "MyInt64.dividable_by_32_dec".

(* Go! *)
Cd "extraction".
Recursive Extraction Library ASM.
