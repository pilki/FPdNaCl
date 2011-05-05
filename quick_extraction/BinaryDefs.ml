open BinNat
open BinPos
open Byte
open Datatypes

(** val translate_P_by : nat -> positive -> positive **)

let rec translate_P_by trans p =
  match trans with
    | O -> p
    | S t' -> translate_P_by t' (Coq_xO p)

(** val translate_N_by : nat -> coq_N -> coq_N **)

let translate_N_by trans = function
  | N0 -> N0
  | Npos p -> Npos (translate_P_by trans p)

(** val translate_N_by_four : coq_N -> coq_N **)

let translate_N_by_four = function
  | N0 -> N0
  | Npos p -> Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO p))))

(** val translate_N_by_eight : coq_N -> coq_N **)

let translate_N_by_eight = function
  | N0 -> N0
  | Npos p -> Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
      (Coq_xO p))))))))

(** val coq_N_of_byte : byte -> coq_N **)

let coq_N_of_byte = function
  | B00 -> N0
  | B01 -> Npos Coq_xH
  | B02 -> Npos (Coq_xO Coq_xH)
  | B03 -> Npos (Coq_xI Coq_xH)
  | B04 -> Npos (Coq_xO (Coq_xO Coq_xH))
  | B05 -> Npos (Coq_xI (Coq_xO Coq_xH))
  | B06 -> Npos (Coq_xO (Coq_xI Coq_xH))
  | B07 -> Npos (Coq_xI (Coq_xI Coq_xH))
  | B08 -> Npos (Coq_xO (Coq_xO (Coq_xO Coq_xH)))
  | B09 -> Npos (Coq_xI (Coq_xO (Coq_xO Coq_xH)))
  | B0A -> Npos (Coq_xO (Coq_xI (Coq_xO Coq_xH)))
  | B0B -> Npos (Coq_xI (Coq_xI (Coq_xO Coq_xH)))
  | B0C -> Npos (Coq_xO (Coq_xO (Coq_xI Coq_xH)))
  | B0D -> Npos (Coq_xI (Coq_xO (Coq_xI Coq_xH)))
  | B0E -> Npos (Coq_xO (Coq_xI (Coq_xI Coq_xH)))
  | B0F -> Npos (Coq_xI (Coq_xI (Coq_xI Coq_xH)))
  | B10 -> Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))
  | B11 -> Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH))))
  | B12 -> Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH))))
  | B13 -> Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH))))
  | B14 -> Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH))))
  | B15 -> Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH))))
  | B16 -> Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH))))
  | B17 -> Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH))))
  | B18 -> Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH))))
  | B19 -> Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xI Coq_xH))))
  | B1A -> Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH))))
  | B1B -> Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xI Coq_xH))))
  | B1C -> Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xI Coq_xH))))
  | B1D -> Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xI Coq_xH))))
  | B1E -> Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xI Coq_xH))))
  | B1F -> Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH))))
  | B20 -> Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))
  | B21 -> Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))
  | B22 -> Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))
  | B23 -> Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))
  | B24 -> Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH)))))
  | B25 -> Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH)))))
  | B26 -> Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH)))))
  | B27 -> Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH)))))
  | B28 -> Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH)))))
  | B29 -> Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH)))))
  | B2A -> Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH)))))
  | B2B -> Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH)))))
  | B2C -> Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH)))))
  | B2D -> Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH)))))
  | B2E -> Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH)))))
  | B2F -> Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH)))))
  | B30 -> Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH)))))
  | B31 -> Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH)))))
  | B32 -> Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI Coq_xH)))))
  | B33 -> Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI Coq_xH)))))
  | B34 -> Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH)))))
  | B35 -> Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH)))))
  | B36 -> Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI Coq_xH)))))
  | B37 -> Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI Coq_xH)))))
  | B38 -> Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI Coq_xH)))))
  | B39 -> Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI Coq_xH)))))
  | B3A -> Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI Coq_xH)))))
  | B3B -> Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI Coq_xH)))))
  | B3C -> Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI Coq_xH)))))
  | B3D -> Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI Coq_xH)))))
  | B3E -> Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH)))))
  | B3F -> Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH)))))
  | B40 -> Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
  | B41 -> Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
  | B42 -> Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
  | B43 -> Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
  | B44 -> Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
  | B45 -> Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
  | B46 -> Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
  | B47 -> Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
  | B48 -> Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH))))))
  | B49 -> Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH))))))
  | B4A -> Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH))))))
  | B4B -> Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH))))))
  | B4C -> Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH))))))
  | B4D -> Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH))))))
  | B4E -> Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH))))))
  | B4F -> Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH))))))
  | B50 -> Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH))))))
  | B51 -> Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH))))))
  | B52 -> Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH))))))
  | B53 -> Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH))))))
  | B54 -> Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH))))))
  | B55 -> Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH))))))
  | B56 -> Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH))))))
  | B57 -> Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH))))))
  | B58 -> Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH))))))
  | B59 -> Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH))))))
  | B5A -> Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH))))))
  | B5B -> Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH))))))
  | B5C -> Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH))))))
  | B5D -> Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH))))))
  | B5E -> Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH))))))
  | B5F -> Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH))))))
  | B60 -> Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH))))))
  | B61 -> Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH))))))
  | B62 -> Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH))))))
  | B63 -> Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH))))))
  | B64 -> Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI Coq_xH))))))
  | B65 -> Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI Coq_xH))))))
  | B66 -> Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI Coq_xH))))))
  | B67 -> Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI Coq_xH))))))
  | B68 -> Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH))))))
  | B69 -> Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH))))))
  | B6A -> Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH))))))
  | B6B -> Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH))))))
  | B6C -> Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI Coq_xH))))))
  | B6D -> Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI Coq_xH))))))
  | B6E -> Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI Coq_xH))))))
  | B6F -> Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI Coq_xH))))))
  | B70 -> Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI Coq_xH))))))
  | B71 -> Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI Coq_xH))))))
  | B72 -> Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI Coq_xH))))))
  | B73 -> Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI Coq_xH))))))
  | B74 -> Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI Coq_xH))))))
  | B75 -> Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI Coq_xH))))))
  | B76 -> Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI Coq_xH))))))
  | B77 -> Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI Coq_xH))))))
  | B78 -> Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI Coq_xH))))))
  | B79 -> Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI Coq_xH))))))
  | B7A -> Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI Coq_xH))))))
  | B7B -> Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI Coq_xH))))))
  | B7C -> Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH))))))
  | B7D -> Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH))))))
  | B7E -> Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH))))))
  | B7F -> Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH))))))
  | B80 -> Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
      Coq_xH)))))))
  | B81 -> Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
      Coq_xH)))))))
  | B82 -> Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
      Coq_xH)))))))
  | B83 -> Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
      Coq_xH)))))))
  | B84 -> Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO
      Coq_xH)))))))
  | B85 -> Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO
      Coq_xH)))))))
  | B86 -> Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO
      Coq_xH)))))))
  | B87 -> Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO
      Coq_xH)))))))
  | B88 -> Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO
      Coq_xH)))))))
  | B89 -> Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO
      Coq_xH)))))))
  | B8A -> Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO
      Coq_xH)))))))
  | B8B -> Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO
      Coq_xH)))))))
  | B8C -> Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO
      Coq_xH)))))))
  | B8D -> Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO
      Coq_xH)))))))
  | B8E -> Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO
      Coq_xH)))))))
  | B8F -> Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO
      Coq_xH)))))))
  | B90 -> Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO
      Coq_xH)))))))
  | B91 -> Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO
      Coq_xH)))))))
  | B92 -> Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO
      Coq_xH)))))))
  | B93 -> Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO
      Coq_xH)))))))
  | B94 -> Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO
      Coq_xH)))))))
  | B95 -> Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO
      Coq_xH)))))))
  | B96 -> Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO
      Coq_xH)))))))
  | B97 -> Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO
      Coq_xH)))))))
  | B98 -> Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO
      Coq_xH)))))))
  | B99 -> Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO
      Coq_xH)))))))
  | B9A -> Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO
      Coq_xH)))))))
  | B9B -> Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO
      Coq_xH)))))))
  | B9C -> Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO
      Coq_xH)))))))
  | B9D -> Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO
      Coq_xH)))))))
  | B9E -> Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO
      Coq_xH)))))))
  | B9F -> Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO
      Coq_xH)))))))
  | BA0 -> Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO
      Coq_xH)))))))
  | BA1 -> Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO
      Coq_xH)))))))
  | BA2 -> Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO
      Coq_xH)))))))
  | BA3 -> Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO
      Coq_xH)))))))
  | BA4 -> Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO
      Coq_xH)))))))
  | BA5 -> Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO
      Coq_xH)))))))
  | BA6 -> Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO
      Coq_xH)))))))
  | BA7 -> Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO
      Coq_xH)))))))
  | BA8 -> Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO
      Coq_xH)))))))
  | BA9 -> Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO
      Coq_xH)))))))
  | BAA -> Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO
      Coq_xH)))))))
  | BAB -> Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO
      Coq_xH)))))))
  | BAC -> Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO
      Coq_xH)))))))
  | BAD -> Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO
      Coq_xH)))))))
  | BAE -> Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO
      Coq_xH)))))))
  | BAF -> Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO
      Coq_xH)))))))
  | BB0 -> Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO
      Coq_xH)))))))
  | BB1 -> Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO
      Coq_xH)))))))
  | BB2 -> Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO
      Coq_xH)))))))
  | BB3 -> Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO
      Coq_xH)))))))
  | BB4 -> Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO
      Coq_xH)))))))
  | BB5 -> Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO
      Coq_xH)))))))
  | BB6 -> Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO
      Coq_xH)))))))
  | BB7 -> Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO
      Coq_xH)))))))
  | BB8 -> Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO
      Coq_xH)))))))
  | BB9 -> Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO
      Coq_xH)))))))
  | BBA -> Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO
      Coq_xH)))))))
  | BBB -> Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO
      Coq_xH)))))))
  | BBC -> Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO
      Coq_xH)))))))
  | BBD -> Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO
      Coq_xH)))))))
  | BBE -> Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO
      Coq_xH)))))))
  | BBF -> Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO
      Coq_xH)))))))
  | BC0 -> Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI
      Coq_xH)))))))
  | BC1 -> Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI
      Coq_xH)))))))
  | BC2 -> Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI
      Coq_xH)))))))
  | BC3 -> Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI
      Coq_xH)))))))
  | BC4 -> Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI
      Coq_xH)))))))
  | BC5 -> Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI
      Coq_xH)))))))
  | BC6 -> Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI
      Coq_xH)))))))
  | BC7 -> Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI
      Coq_xH)))))))
  | BC8 -> Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI
      Coq_xH)))))))
  | BC9 -> Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI
      Coq_xH)))))))
  | BCA -> Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI
      Coq_xH)))))))
  | BCB -> Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI
      Coq_xH)))))))
  | BCC -> Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI
      Coq_xH)))))))
  | BCD -> Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI
      Coq_xH)))))))
  | BCE -> Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI
      Coq_xH)))))))
  | BCF -> Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI
      Coq_xH)))))))
  | BD0 -> Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI
      Coq_xH)))))))
  | BD1 -> Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI
      Coq_xH)))))))
  | BD2 -> Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI
      Coq_xH)))))))
  | BD3 -> Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI
      Coq_xH)))))))
  | BD4 -> Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI
      Coq_xH)))))))
  | BD5 -> Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI
      Coq_xH)))))))
  | BD6 -> Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI
      Coq_xH)))))))
  | BD7 -> Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI
      Coq_xH)))))))
  | BD8 -> Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI
      Coq_xH)))))))
  | BD9 -> Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI
      Coq_xH)))))))
  | BDA -> Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI
      Coq_xH)))))))
  | BDB -> Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI
      Coq_xH)))))))
  | BDC -> Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI
      Coq_xH)))))))
  | BDD -> Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI
      Coq_xH)))))))
  | BDE -> Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI
      Coq_xH)))))))
  | BDF -> Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI
      Coq_xH)))))))
  | BE0 -> Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI
      Coq_xH)))))))
  | BE1 -> Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI
      Coq_xH)))))))
  | BE2 -> Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI
      Coq_xH)))))))
  | BE3 -> Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI
      Coq_xH)))))))
  | BE4 -> Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI
      Coq_xH)))))))
  | BE5 -> Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI
      Coq_xH)))))))
  | BE6 -> Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI
      Coq_xH)))))))
  | BE7 -> Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI
      Coq_xH)))))))
  | BE8 -> Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI
      Coq_xH)))))))
  | BE9 -> Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI
      Coq_xH)))))))
  | BEA -> Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI
      Coq_xH)))))))
  | BEB -> Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI
      Coq_xH)))))))
  | BEC -> Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI
      Coq_xH)))))))
  | BED -> Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI
      Coq_xH)))))))
  | BEE -> Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI
      Coq_xH)))))))
  | BEF -> Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI
      Coq_xH)))))))
  | BF0 -> Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI
      Coq_xH)))))))
  | BF1 -> Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI
      Coq_xH)))))))
  | BF2 -> Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI
      Coq_xH)))))))
  | BF3 -> Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI
      Coq_xH)))))))
  | BF4 -> Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI
      Coq_xH)))))))
  | BF5 -> Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI
      Coq_xH)))))))
  | BF6 -> Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI
      Coq_xH)))))))
  | BF7 -> Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI
      Coq_xH)))))))
  | BF8 -> Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI
      Coq_xH)))))))
  | BF9 -> Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI
      Coq_xH)))))))
  | BFA -> Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI
      Coq_xH)))))))
  | BFB -> Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI
      Coq_xH)))))))
  | BFC -> Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI
      Coq_xH)))))))
  | BFD -> Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI
      Coq_xH)))))))
  | BFE -> Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI
      Coq_xH)))))))
  | BFF -> Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI
      Coq_xH)))))))

(** val byte0 : byte **)

let byte0 =
  B00

(** val concat_byte : coq_N -> byte -> coq_N **)

let concat_byte n b =
  coq_Nplus (translate_N_by_eight n) (coq_N_of_byte b)

type word =
  | W of byte * byte * byte * byte

(** val word_rect : (byte -> byte -> byte -> byte -> 'a1) -> word -> 'a1 **)

let word_rect f = function
  | W (x, x0, x1, x2) -> f x x0 x1 x2

(** val word_rec : (byte -> byte -> byte -> byte -> 'a1) -> word -> 'a1 **)

let word_rec f = function
  | W (x, x0, x1, x2) -> f x x0 x1 x2

(** val word_eq_dec : word -> word -> bool **)

let word_eq_dec w1 w2 =
  let W (x, x0, x1, x2) = w1 in
  let W (b3, b4, b5, b6) = w2 in
  if byte_eq_dec x b3
  then if byte_eq_dec x0 b4
       then if byte_eq_dec x1 b5 then byte_eq_dec x2 b6 else false
       else false
  else false

(** val coq_N_of_word : word -> coq_N **)

let coq_N_of_word = function
  | W (b4, b3, b2, b1) ->
      let n4 = coq_N_of_byte b4 in
      let n3 = concat_byte n4 b3 in
      let n2 = concat_byte n3 b2 in concat_byte n2 b1

(** val bool_list_of_P : positive -> bool list **)

let rec bool_list_of_P = function
  | Coq_xI p' -> true :: (bool_list_of_P p')
  | Coq_xO p' -> false :: (bool_list_of_P p')
  | Coq_xH -> true :: []

(** val coq_P_of_bool_list : bool list -> positive option **)

let rec coq_P_of_bool_list = function
  | [] -> None
  | y :: l' ->
      if y
      then (match coq_P_of_bool_list l' with
              | Some p -> Some (Coq_xI p)
              | None -> Some Coq_xH)
      else (match coq_P_of_bool_list l' with
              | Some p -> Some (Coq_xO p)
              | None -> None)

(** val bool_list_of_N : coq_N -> bool list **)

let bool_list_of_N = function
  | N0 -> []
  | Npos pos -> bool_list_of_P pos

(** val coq_N_of_bool_list : bool list -> coq_N **)

let coq_N_of_bool_list l =
  match coq_P_of_bool_list l with
    | Some pos -> Npos pos
    | None -> N0

(** val list_and : bool list -> bool list -> bool list **)

let rec list_and l1 l2 =
  match l1 with
    | [] -> []
    | b1 :: l1' ->
        (match l2 with
           | [] -> []
           | b2 :: l2' -> ((&&) b1 b2) :: (list_and l1' l2'))

(** val coq_N_and : coq_N -> coq_N -> coq_N **)

let coq_N_and n1 n2 =
  coq_N_of_bool_list (list_and (bool_list_of_N n1) (bool_list_of_N n2))

