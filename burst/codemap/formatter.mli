open Unicode

type t
(** A formatter to be printed. *)

module Highlight : sig
  type t

  type style =
    | Error
    | Warning
    | Note
end

val create : unit -> t
(** Create a new formatter. *)

val add : t -> Span.t -> string option -> Highlight.style -> unit
(** Add a span highlight to the formatter. *)

val print : t -> ?highlights_margin:int -> UChar.t Seq.t -> Span.t -> out_channel -> unit
(** Print the formatted input char sequence, with the given span. *)
