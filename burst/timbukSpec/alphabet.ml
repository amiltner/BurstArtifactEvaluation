open Timbuk

module Make (Id : Set.OrderedType) (Symbol : Symbol.S) = struct
  include Dictionary.Make (Id) (Symbol)

  let print t out =
    let print_symbol _ (f, _) =
      Format.fprintf out "%t:%d " (Symbol.print f) (Symbol.arity f)
    in
    iter (print_symbol) t
end
