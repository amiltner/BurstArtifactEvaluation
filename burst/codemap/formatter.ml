open Unicode
open UString

module Highlight = struct
  type style =
    | Error
    | Warning
    | Note

  let style_escape_sequence = function
    | Error -> "\x1b[1;31m"
    | Warning -> "\x1b[1;33m"
    | Note -> "\x1b[1;34m"

  type t = {
    span: Span.t;
    label: Utf8String.t option;
    style: style;
    mutable nest_level: int
  }

  let create span label style =
    {
      span = span;
      label = label;
      style = style;
      nest_level = 0
    }

  let compare a b =
    Span.compare a.span b.span

  let compute_nest_level t highlights =
    let exception Found of int in
    let level = if Span.is_multi_line t.span then
        try List.fold_left (
            fun i t' ->
              if t == t' then raise (Found i);
              if Span.is_multi_line t'.span && Span.is_included t'.span t.span then i + 1 else i
          ) 1 highlights
        with Found i -> i
      else
        0
    in
    t.nest_level <- level
end

module Char = struct
  type t =
    | Free
    | Underline of Highlight.style (* Underline. *)
    | Marker of Highlight.style
    | Spanline of Highlight.style (* Horizontal bars for multi-line spans. *)
    | Connector of Highlight.style (* Vertical bars. *)
    | Label of (UChar.t * Highlight.style) (* Label. *)
    | LabelWidth (* For multi column chars. *)

  let best a b =
    match a, b with
    | Free, _ -> b
    | _, Free -> a
    | Connector _, _ -> b
    | _, Connector _ -> a
    | _ -> a
end

type pp_out = {
  channel: out_channel;
  mutable style: Highlight.style option
}

let create_pp_out out =
  {
    channel = out;
    style = None
  }

let pp_set_style out style_opt =
  if out.style = style_opt then () else begin
    let escape_sequence = match style_opt with
      | None -> "\x1b[0m"
      | Some s -> Highlight.style_escape_sequence s
    in
    output_string out.channel escape_sequence;
    out.style <- style_opt
  end

let pp_output_string out style str =
  pp_set_style out style;
  output_string out.channel str

let pp_output_char out style c =
  pp_set_style out style;
  output_char out.channel c

let pp_print_tab out style p =
  let rec print = function
    | 0 -> ()
    | n ->
      pp_output_char out style ' ';
      print (n - 1)
  in
  print (Position.tab_length p)

let pp_reset out =
  output_string out.channel "\x1b[0m";
  out.style <- None

let print_line_number margin n_opt out =
  if margin > 0 then begin
    let style = Some Highlight.Note in
    begin match n_opt with
      | Some n ->
        let rec make_string m n =
          if m = 0 then [] else
            (if n > 0 then (Stdlib.Char.chr ((n mod 10) + 0x30)) else ' ')::(make_string (m - 1) (n / 10))
        in
        let str = List.rev (make_string margin (n + 1)) in
        List.iter (pp_output_char out style) str
      | None ->
        for _ = 0 to margin - 1 do
          pp_output_char out style ' '
        done
    end;
    pp_output_string out style " | "
  end

module CharMap = struct
  type t = {
    mutable buffer: Char.t Array.t;
    mutable width: int;
    mutable height: int
  }

  let create () =
    {
      buffer = Array.make 0 Char.Free;
      width = 0;
      height = 0
    }

  let resize t w h =
    if w != t.width || h != t.height then begin
      let buffer' = Array.make (w * h) Char.Free in
      for i = 0 to (min t.height h) - 1 do
        Array.blit t.buffer (i * t.width) buffer' (i * w) (min t.width w)
      done;
      t.width <- w;
      t.height <- h;
      t.buffer <- buffer'
    end

  let index t x y =
    (y * t.width) + x

  let get t x y =
    if x < 0 || y < 0 || x >= t.width || y >= t.height then
      Char.Free
    else
      Array.get t.buffer (index t x y)

  let set t x y c =
    if x < 0 || y < 0 then raise (Invalid_argument "invalid buffer position");
    resize t (max t.width (x + 1)) (max t.height (y + 1));
    Array.set t.buffer (index t x y) (Char.best c (get t x y))

  let draw_label_char t pos c style =
    let w = UChar.width 0 c in
    for i = 0 to w - 1 do
      let k = if i = 0 then Char.Label (c, style) else Char.LabelWidth in
      set t (pos.Position.column + i) pos.line k
    done

  let of_label str style =
    let t = create () in
    ignore (Utf8String.fold_left (
        fun pos c ->
          draw_label_char t pos c style;
          Position.next c pos
      ) (Position.default) str);
    t

  (** Find a free line that can hold an horizontal line from [i] to [j] (both
      included). *)
  let find_free_line t i j =
    let exception Found of int in
    let rec find_from line =
      for col = i to j do
        match get t col line with
        | Char.Free | Char.Connector _ -> ()
        | _ -> find_from (line + 1)
      done;
      raise (Found line)
    in
    try find_from 0; 0 with Found line -> line

  let is_free_buffer_spot t line col buffer =
    let exception NotFree in
    try
      for y = line - 1 to line + buffer.height + 1 do
        for x = col - 1 to col + buffer.width + 1 do
          match get t x y with
          | Char.Free | Char.Connector _ -> ()
          | _ -> raise NotFree
        done
      done;
      true
    with
    | NotFree -> false

  let find_free_buffer_spot t line col buffer =
    if is_free_buffer_spot t line (col + 2) buffer then
      (line, col + 2)
    else
      let rec find line col =
        if is_free_buffer_spot t line col buffer then
          (line, col)
        else
          find (line + 1) col
      in
      find (line + 2) col

  let draw_underline t line i j style =
    for col = i to j do
      if line = 0 then
        set t col line (Char.Underline style)
      else begin
        if col = i || col = j then
          for k = 0 to line do
            if k = 0 then
              set t col k (Char.Marker style)
            else
              set t col k (Char.Connector style)
          done
        else
          set t col line (Char.Spanline style)
      end
    done

  let draw_line t line i j style =
    for col = i to j do
      if col = j then
        for k = 0 to line do
          if k = 0 then
            set t col k (Char.Marker style)
          else
            set t col k (Char.Connector style)
        done
      else
        set t col line (Char.Spanline style)
    done

  let draw_buffer t line col buffer =
    for y = 0 to (buffer.height - 1) do
      for x = 0 to (buffer.width - 1) do
        set t (col + x) (line + y) (get buffer x y)
      done
    done

  let draw_label_opt t line col style = function
    | None -> ()
    | Some label ->
      let buffer = of_label label style in
      let line', col' = find_free_buffer_spot t line col buffer in
      if line' > line then
        for k = 1 to (line - 1) do
          set t col k (Char.Connector style)
        done;
      draw_buffer t line' col' buffer

  let draw_highlight t source_line h =
    let first_line = (Span.first h.Highlight.span).Position.line in
    let last_line = (Span.last h.Highlight.span).Position.line in
    if first_line = source_line && last_line = source_line then
      let i = (Span.first h.Highlight.span).Position.column in
      let j = (Span.last h.Highlight.span).Position.column in
      let line = find_free_line t i j in
      draw_underline t line i j h.style;
      draw_label_opt t line j h.style h.label;
      None
    else if first_line = source_line then
      let j = (Span.first h.Highlight.span).Position.column in
      let line = find_free_line t 0 j in
      draw_line t line 0 j h.style;
      Some line
    else if last_line = source_line then
      let j = (Span.last h.Highlight.span).Position.column in
      let line = find_free_line t 0 j in
      draw_line t line 0 j h.style;
      draw_label_opt t line j h.style h.label;
      Some line
    else
      None

  let print t source_line line_number_margin margin handles out =
    for line = 0 to t.height - 1 do
      print_line_number line_number_margin None out;
      for m = 0 to margin - 1 do
        match List.find_opt (
            function
            | h, Some y ->
              if (Span.first h.Highlight.span).line = source_line then
                h.Highlight.nest_level = m + 1 && y > line
              else
                h.Highlight.nest_level = m + 1 && y <= line
            | h, None ->
              h.Highlight.nest_level = m + 1 && Span.includes_line h.Highlight.span source_line
          ) handles with
        | Some (h, _) ->
          pp_output_char out (Some h.Highlight.style) '|'
        | None ->
          pp_output_char out None ' '
      done;
      for col = 0 to t.width - 1 do
        match get t col line with
        | Char.Free -> pp_output_char out None ' '
        | Char.Underline s -> pp_output_char out (Some s) '^'
        | Char.Marker s -> pp_output_char out (Some s) '^'
        | Char.Spanline s -> pp_output_char out (Some s) '_'
        | Char.Connector s -> pp_output_char out (Some s) '|'
        | Char.Label (c, s) -> pp_output_string out (Some s) (Utf8String.of_char c)
        | Char.LabelWidth -> ()
      done;
      pp_output_char out None '\n'
    done
end

type t = {
  mutable highlights: Highlight.t list;
  mutable show_line_numbers: bool
}

let create () =
  {
    highlights = [];
    show_line_numbers = true
  }

let add t span label_opt style =
  t.highlights <- (Highlight.create span label_opt style)::t.highlights

let print_line_decoration t line_number_margin margin line out =
  let charmap = CharMap.create () in
  let handles = List.rev (List.fold_left (
      fun handles h ->
        let handle_opt = CharMap.draw_highlight charmap line h in
        (h, handle_opt)::handles
    ) [] t.highlights)
  in
  CharMap.print charmap line line_number_margin margin handles out

let line_number_margin span =
  let line = (Span.last span).line in
  int_of_float (log10 (float_of_int (line + 1))) + 1

let print t ?(highlights_margin = 1) input span out =
  (* Sort every highlight and compute their nest level. *)
  t.highlights <- List.stable_sort (Highlight.compare) t.highlights;
  List.iter (
    function h ->
      Highlight.compute_nest_level h t.highlights
  ) t.highlights;
  let margin = List.fold_right (fun h m -> max h.Highlight.nest_level m) t.highlights 0 in
  let line_number_margin = if t.show_line_numbers then
      line_number_margin span
    else
      0
  in
  let is_relevant line =
    List.exists (function h -> Span.includes_line (Span.aligned ~margin:highlights_margin h.Highlight.span) line) t.highlights
  in
  (* Print every line. *)
  let out = create_pp_out out in
  let rec print_line (skipping, empty) pos input =
    if is_relevant pos.Position.line then begin
      if skipping && not empty then
        pp_output_string out None "...\n";
      (* Print the left margin *)
      print_line_number line_number_margin (Some pos.Position.line) out;
      for m = 0 to margin - 1 do
        match List.find_opt (function h -> h.Highlight.nest_level = m + 1 && Span.includes h.Highlight.span pos) t.highlights with
        | Some h ->
          pp_output_char out (Some h.Highlight.style) '|'
        | None ->
          pp_output_char out None ' '
      done;
      (* Print the line content *)
      let rec print_chars pos input =
        if Position.compare pos (Span.next_position span) <= 0 then begin
          begin match input () with
            | Seq.Cons (c, input') ->
              begin match UChar.to_int c with
                | 0x09 -> (* \t *)
                  pp_print_tab out None pos;
                  print_chars (Position.next c pos) input'
                | 0x0a -> (* \n *)
                  pp_output_char out None '\n';
                  print_line_decoration t line_number_margin margin pos.line out;
                  print_line (false, false) (Position.next c pos) input'
                | _ ->
                  pp_output_string out None (Utf8String.of_char c);
                  print_chars (Position.next c pos) input'
              end
            | Seq.Nil ->
              pp_output_char out None '\n';
              print_line_decoration t line_number_margin margin pos.line out;
              ()
          end
        end else begin
          pp_output_char out None '\n';
          print_line_decoration t line_number_margin margin pos.line out;
        end
      in
      print_chars pos input
    end else begin
      let rec skip_chars pos input =
        if Position.compare pos (Span.next_position span) <= 0 then begin
          begin match input () with
            | Seq.Cons (c, input') ->
              begin match UChar.to_int c with
                | 0x0a -> (* \n *)
                  print_line (true, empty) (Position.next c pos) input'
                | _ ->
                  skip_chars (Position.next c pos) input'
              end
            | Seq.Nil -> ()
          end
        end
      in
      skip_chars pos input
    end
  in
  print_line (true, true) (Span.first span) input;
  pp_reset out
