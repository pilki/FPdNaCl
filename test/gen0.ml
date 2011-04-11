let _ =
  for i = 1 to int_of_string Sys.argv.(1) do
    for j = 1 to 32 do
      output_char stdout '\000'
    done
  done
