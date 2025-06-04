module Make (K : Hashtbl.HashedType) = struct
  module V = Fast_bitvector
  module H = Hashtbl.Make (K)

  let mapping : int H.t = H.create 128
  let inverse : K.t Dynarray.t = Dynarray.create ()

  type elt = K.t
  type t = V.t

  let empty = V.create ~len:0

  let to_offset k =
    match H.find_opt mapping k with
    | Some x -> x
    | None ->
        let x = Dynarray.length inverse in
        H.add mapping k x;
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
    let s = V.create ~len:(e + 1) in
    V.set s e;
    s

  let remove e s =
    let e = to_offset e in
    if V.length s > e then V.set_to s e false;
    s

  let union x y =
    let result = V.create ~len:(Int.max (V.length x) (V.length y)) in
    V.Relaxed.union ~result x y

  let inter x y =
    let result = V.create ~len:(Int.max (V.length x) (V.length y)) in
    V.Relaxed.inter ~result x y

  let disjoint = V.Relaxed.disjoint

  let diff x y =
    let result = V.create ~len:(Int.max (V.length x) (V.length y)) in
    V.Relaxed.diff ~result x y

  let equal_modulo = V.Relaxed.equal_modulo

  (*TODO: semantically does not correspond to Set.S, should follow the order defined by K *)
  let fold f s init =
    V.fold_lefti ~init
      ~f:(fun acc i bit -> if bit then f (of_offset i) acc else acc)
      s

  let iter f s = V.iter_seti ~f:(Fun.compose f of_offset) s
  let rev_iter f s = V.rev_iter_seti ~f:(Fun.compose f of_offset) s
  let cardinal s = V.popcount s
  let of_iter i = i |> Iter.map to_offset |> V.of_offset_iter
  let of_list l = l |> Iter.of_list |> of_iter
  let to_seq s = s |> V.to_offset_seq |> Seq.map of_offset
  let to_rev_seq s = s |> V.to_rev_offset_seq |> Seq.map of_offset
  let of_seq seq = seq |> Seq.map to_offset |> V.of_offset_seq
  let add_seq seq s = Seq.fold_left (Fun.flip add) s seq
  let to_iter s f = iter f s
  let elements s = s |> to_iter |> Iter.to_list
  let to_list s = elements s
  let to_rev_iter s f = rev_iter f s

  (* 
  TODO: not sure this is useful for me at all
  let min_elt_opt s =
    match List.sort K.compare (elements s) with x :: _ -> Some x | [] -> None

  let max_elt_opt s =
    match List.sort (fun x y -> Int.neg (K.compare x y)) (elements s) with
    | x :: _ -> Some x
    | [] -> None

  let min_elt s = Option.get (min_elt_opt s)
  let max_elt s = Option.get (max_elt_opt s) *)

  let choose_opt s =
    let n = Random.int (cardinal s) in
    s |> to_iter |> Iter.take n |> Iter.head

  let choose s = Option.get (choose_opt s)
  let find_opt p s = s |> to_iter |> Iter.find p
  let find p s = Option.get (find_opt p s)
  let find_first = find
  let find_first_opt = find_opt
  let find_last_opt p s = s |> to_rev_iter |> Iter.find p
  let find_last p s = Option.get (find_last_opt p s)
  let map f s = s |> to_iter |> Iter.map f |> of_iter
  let filter p s = s |> to_iter |> Iter.filter p |> of_iter
  let filter_map f s = s |> to_iter |> Iter.filter_map f |> of_iter

  (*TODO: maybe make partition at the level of bitvector. *)
  let partition p s =
    ( s |> to_iter |> Iter.filter p |> of_iter,
      s |> to_iter |> Iter.filter (Fun.negate p) |> of_iter )

  let is_empty = V.is_empty
  let mem e s = V.Relaxed.mem s (to_offset e)
  let equal = V.Relaxed.equal
  let subset = V.Relaxed.subset
  let for_all p s = s |> to_iter |> Iter.for_all p
  let exists p s = s |> to_iter |> Iter.exists p
end

module MakeSexp (K : sig
  include Hashtbl.HashedType
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
