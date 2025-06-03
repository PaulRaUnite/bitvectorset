module Make (K : Set.OrderedType) = struct
  module V = Fast_bitvector

  let mapping : (K.t, int) Hashtbl.t = Hashtbl.create 128
  let inverse : K.t Dynarray.t = Dynarray.create ()

  type elt = K.t
  type t = V.t

  let empty = V.create ~len:0

  let to_offset k =
    match Hashtbl.find_opt mapping k with
    | Some x -> x
    | None ->
        let x = Dynarray.length inverse in
        Hashtbl.add mapping k x;
        Dynarray.add_last inverse k;
        x

  let of_offset i = Dynarray.get inverse i

  let print_raw s =
    print_endline @@ V.Little_endian.to_debug_string s;
    flush_all ()

  let add e s =
    let e = to_offset e in
    let len_req = e + 1 in
    let s = if V.length s < len_req then V.extend s ~len:len_req else s in
    V.set_to s e true;
    s

  let singleton e =
    let e = to_offset e in
    V.create ~len:e

  let remove e s =
    let e = to_offset e in
    V.set_to s e false;
    s

  (* let add e s =
    let e = to_offset e in
    let s =
      if V.length s <= e then
        (Printf.printf "%i\n" (V.length s - e + 1);
        V.extend_inplace ~by:(V.length s - e + 1) s)
      else s
    in
    V.set_to s e true;
    s

  let singleton e =
    let e = to_offset e in
    let s = V.create ~len:e in
    V.set s e;
    s

  let remove e s =
    let e = to_offset e in
    if V.length s > e then V.set_to s e false;
    s *)

  let union x y =
    let result = V.create ~len:(Int.max (V.length x) (V.length y)) in
    V.Relaxed.union ~result x y

  let inter x y =
    let result = V.create ~len:(Int.max (V.length x) (V.length y)) in
    (* print_endline (Sexplib0.Sexp.to_string (V.sexp_of_t (result) )); *)
    V.Relaxed.intersect ~result x y

  let disjoint x y =
    let result = V.create ~len:(Int.max (V.length x) (V.length y)) in
    V.is_empty (V.Relaxed.intersect ~result x y)

  let diff x y =
    let result = V.create ~len:(Int.max (V.length x) (V.length y)) in
    V.Relaxed.difference ~result x y

  let cardinal s = V.popcount s

  let iter s f =
    let _ =
      V.fold ~init:0
        ~f:(fun offset is_set ->
          (if is_set then
             let v = of_offset offset in
             f v);
          offset + 1)
        s
    in
    ()

  let elements s = Iter.to_list (iter s)
  let of_seq seq = Seq.fold_left (Fun.flip @@ add) empty seq
  let of_iter i = Iter.fold (Fun.flip add) empty i
  let of_list l = of_seq (List.to_seq l)
  let equal = V.Relaxed.equal
  let is_empty = V.is_empty
end

module MakeSexp (K : sig
  include Set.OrderedType
  include Sexplib0.Sexpable.S with type t := t
end) =
struct
  include Make (K)

  let sexp_of_t s = Sexplib0.Sexp_conv.sexp_of_list K.sexp_of_t (elements s)
  let print s = print_endline @@ Sexplib0.Sexp.to_string @@ sexp_of_t s
end

let%test_module _ =
  (module struct
    module T = MakeSexp (struct
      include String

      let sexp_of_t = Sexplib0.Sexp_conv.sexp_of_string
      let t_of_sexp = Sexplib0.Sexp_conv.string_of_sexp
    end)

    open T

    let a = of_list [ "a" ]
    let b = of_list [ "b" ]

    (* let c = of_list [ "c" ] *)
    let ab = of_list [ "a"; "b" ]
    let bc = of_list [ "b"; "c" ]
    let%test _ = is_empty empty
    let%test _ = equal (inter a ab) a
    let%test _ = equal (inter ab bc) b
    let%test _ = equal empty (inter a b)
  end)
