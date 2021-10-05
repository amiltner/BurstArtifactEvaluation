open Collections

module type S = sig
  include Map.S

  val union : ('a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t

  val union_opt : ('a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t option
end

module Make (X : Map.OrderedType) = struct
  include Map.Make (X)

  let union product a b =
    let set_type typ = function
      | Some previous_typ ->
        begin
          match product typ previous_typ with
          | Some typ -> Some typ
          | None -> raise (Invalid_argument "inconsistent substitutions.")
        end
      | None -> Some typ
    in
    let add x typ sigma = update x (set_type typ) sigma in
    fold add b a

  let union_opt product a b =
    try Some (union product a b) with
    | Invalid_argument _ -> None
end
