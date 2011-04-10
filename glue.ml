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


open BinaryDefs
open LazyList

let half_byte_of_int = function
  | 0 -> HB0
  | 1 -> HB1
  | 2 -> HB2
  | 3 -> HB3
  | 4 -> HB4
  | 5 -> HB5
  | 6 -> HB6
  | 7 -> HB7
  | 8 -> HB8
  | 9 -> HB9
  | 10 -> HBA
  | 11 -> HBB
  | 12 -> HBC
  | 13 -> HBD
  | 14 -> HBE
  | 15 -> HBF
  | _ -> assert false

let byte_of_char c : byte =
  let i = int_of_char c in
  let hb1 = half_byte_of_int (i land 0xF) in
  let hb2 = half_byte_of_int (i lsr 4) in
  (hb2, hb1)


let lasy_list_of_ic ic =
  let buffer = String.create 1024 in
  let rec aux () = 
    let l = input ic buffer 0 1024 in
    if l = 0 then
      Coq_ll_nil
    else
      let rec build n acc = 
        if n < 0 then
          acc
        else
          build (pred n)
            (Coq_ll_cons((byte_of_char buffer.[n]),
                         Lazy.lazy_from_val(Lazy acc)))
      in
      build (l - 2)
        (Coq_ll_cons ((byte_of_char buffer.[pred l]),
                      (lazy (Lazy (aux())))))
  in
  aux ()
