(* error handling *)

let error_unknown_instruction () =
  Printf.eprintf "Unknown instruction\n%!"

let error_wrong_register unit =
  Printf.eprintf "Wrong register\n%!"


let error_illegal_instruction () =
  Printf.eprintf "Illegal instruction\n%!"

let error_badly_masked () =
  Printf.eprintf "Badly masked (or not at all) jump\n%!"

let error_overlaping_instruction () =
  Printf.eprintf "Instruction overlaps block\n%!"

