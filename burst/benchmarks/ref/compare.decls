type cmp =
  | LT
  | EQ
  | GT

let compare =
  fix (compare : nat -> nat -> cmp) =
    fun (x1 : nat) ->
      fun (x2 : nat) ->
        match x1 with
        | O -> (match x2 with
                | O -> EQ
                | S _ -> LT)
        | S x1 -> (match x2 with
                | O -> GT
                | S x2 -> compare x1 x2)
;;

