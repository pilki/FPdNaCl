{
(* output the leftmost byte of an int32 *)
let output_byte_int32 oc i32 =
  output_byte oc (Int32.to_int i32)

(* output the binary representation of an int32 (little endian) *)
let output_int32 oc i32 =
  output_byte_int32 oc i32;
  output_byte_int32 oc (Int32.shift_right_logical i32 8);
  output_byte_int32 oc (Int32.shift_right_logical i32 16);
  output_byte_int32 oc (Int32.shift_right_logical i32 24)

let output_string_int32 oc str =
  output_int32 oc (Int32.of_string str)

let output_reg oc str =
  Scanf.sscanf str "%%%i" (output_byte oc)

}

let hex_char = ['0'-'9''a'-'f''A'-'F']
let int32_str = ("0x" hex_char+) | (['0'-'9']+)
let register = "%" ['1'-'8']
let space = ['\t' ' ']
let start_line = space*
let spaces = space+
let comment = space* (('#'|';') [^'\n']*)?
let newline = space* '\n'
let endline = comment newline

rule asm oc = parse

| start_line "nop" endline
{ output_byte oc 0;
  asm oc lexbuf}

| start_line
    (register as reg1) spaces "<-" spaces
    (register as reg2) spaces "and" spaces
    (int32_str as mask)
    endline
{ output_byte oc 1;
  output_reg oc reg1;
  output_string_int32 oc mask;
  output_reg oc reg2;
  asm oc lexbuf
}

| start_line
    "load" spaces (register as reg1) spaces "->" spaces
    (register as reg2) endline
{ output_byte oc 2;
  output_reg oc reg1; output_reg oc reg2;
  asm oc lexbuf}

| start_line
    "write" spaces (register as reg1) spaces "->" spaces
    (register as reg2) endline
{ output_byte oc 3;
  output_reg oc reg1; output_reg oc reg2;
  asm oc lexbuf}

| start_line
    "djmp" spaces (int32_str as i) endline
{ output_byte oc 4;
  output_string_int32 oc i;
  asm oc lexbuf}

| start_line
    "djmpif" spaces (register as reg) spaces (int32_str as i) endline
{ output_byte oc 5;
  output_reg oc reg;
  output_string_int32 oc i;
  asm oc lexbuf}

| start_line
    "ijmp" spaces (register as reg) endline
{ output_byte oc 6;
  output_reg oc reg;
  asm oc lexbuf}

| start_line
    "oscall" endline
{ output_byte oc 7;
  asm oc lexbuf}

| newline
    { asm oc lexbuf}
| comment newline
    { asm oc lexbuf}
| eof
    {()}


{
 let _ =
   let ic, oc =
     if Array.length Sys.argv = 1 then
       stdin, stdout
     else
       let in_name = Sys.argv.(1) in
       let out_name = (Filename.chop_extension in_name) ^ ".bin" in
       (open_in in_name, open_out_bin out_name) in
   let lexbuf = Lexing.from_channel ic in
   asm oc lexbuf
}
