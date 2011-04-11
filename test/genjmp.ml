let output_small_int i =
  output_char stdout (char_of_int (i land 0xff))


let output_int i =
  output_small_int i;
  output_small_int (i lsr 8);
  output_small_int (i lsr 16);
  output_small_int (i lsr 24)

let output_jump addr =
  output_small_int 4;
  output_int (addr + 5)


let _ =
  for i = 0 to int_of_string Sys.argv.(1) do
    let addr = 65536 + 32 * i in
    for j = 0 to 5 do
      output_jump (addr + 5 * j)
    done;
    output_small_int 0;
    output_small_int 0
  done
