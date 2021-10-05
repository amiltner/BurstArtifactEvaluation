open MyStdLib
open Lang

type t =
  | TypeDeclaration of Id.t * Type.t
  | ExprDeclaration of Id.t * Expr.t
[@@deriving eq, hash, ord, show]

let fold (type a)
         ~(type_f:Id.t -> Type.t -> a)
         ~(expr_f:Id.t -> Expr.t -> a)
         (d:t) =
  match d with
  | TypeDeclaration (i,t) -> type_f i t
  | ExprDeclaration (i,e) -> expr_f i e

let type_dec (i:Id.t) (t:Type.t) : t =
  TypeDeclaration (i,t)

let expr_dec (i:Id.t) (e:Expr.t) : t =
  ExprDeclaration (i,e)
