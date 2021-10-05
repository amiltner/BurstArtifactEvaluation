type cmp =
  | LT
  | EQ
  | GT

let compare =
  fix (compare : nat -> nat -> cmp) =
    fun (x1 : nat) ->
      fun (x2 : nat) ->
        match (x1,x2) with
        | (O,O) -> EQ
        | (O,S _) -> LT
        | (S _,O) -> GT
        | (S x1,S x2) -> compare x1 x2
;;