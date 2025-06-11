module BijectionToInt = struct
  module type S = sig
    type elt

    val to_offset : elt -> int
    val of_offset : int -> elt
  end

  module Int = struct
    type elt = int

    let to_offset : elt -> int = Fun.id
    let of_offset : int -> elt = Fun.id
  end

  module Hashed (K : Hashtbl.HashedType) = struct
    module H = Hashtbl.Make (K)

    type elt = K.t

    let mapping : int H.t = H.create 128
    let inverse : K.t Dynarray.t = Dynarray.create ()

    let to_offset k =
      match H.find_opt mapping k with
      | Some x -> x
      | None ->
          let x = Dynarray.length inverse in
          H.add mapping k x;
          Dynarray.add_last inverse k;
          x

    let of_offset i = Dynarray.get inverse i
  end
end

module Make (B : BijectionToInt.S) = struct
  module V = Fast_bitvector

  type elt = B.elt
  type t = V.t

  let empty = V.create ~len:0

  let[@inline always] print_raw s =
    print_endline @@ V.Little_endian.to_debug_string s;
    flush_all ()

  let[@inline always] add e s =
    let e = B.to_offset e in
    let len_req = e + 1 in
    let s =
      if V.length s < len_req then V.extend s ~len:len_req else V.copy s
    in
    V.set_to s e true;
    s

  let[@inline always] singleton e =
    let e = B.to_offset e in
    let s = V.create ~len:(e + 1) in
    V.set s e;
    s

  let[@inline always] doubleton e1 e2 =
    let e1 = B.to_offset e1 in
    let e2 = B.to_offset e2 in
    let s = V.create ~len:(Int.max e1 e2 + 1) in
    V.set s e1;
    V.set s e2;
    s

  let[@inline always] remove e s =
    let e = B.to_offset e in
    if V.length s > e then (
      let s = V.copy s in
      V.set_to s e false;
      s)
    else s

  let[@inline always] union x y =
    let result = V.create ~len:(Int.max (V.length x) (V.length y)) in
    V.Relaxed.union ~result x y

  let[@inline always] inter x y =
    let result = V.create ~len:(Int.max (V.length x) (V.length y)) in
    V.Relaxed.inter ~result x y

  let disjoint = V.Relaxed.disjoint

  let[@inline always] diff x y =
    let result = V.create ~len:(Int.max (V.length x) (V.length y)) in
    V.Relaxed.diff ~result x y

  let equal_modulo = V.Relaxed.equal_modulo

  let[@inline always] fold f s init =
    V.fold_lefti ~init
      ~f:(fun acc i bit -> if bit then f (B.of_offset i) acc else acc)
      s

  let[@inline always] iter f s = V.iter_seti ~f:(Fun.compose f B.of_offset) s

  let[@inline always] rev_iter f s =
    V.rev_iter_seti ~f:(Fun.compose f B.of_offset) s

  let[@inline always] cardinal s = V.popcount s
  let[@inline always] of_iter i = i |> Iter.map B.to_offset |> V.of_offset_iter
  let[@inline always] of_list l = l |> Iter.of_list |> of_iter
  let[@inline always] to_seq s = s |> V.to_offset_seq |> Seq.map B.of_offset

  let[@inline always] to_rev_seq s =
    s |> V.to_rev_offset_seq |> Seq.map B.of_offset

  let[@inline always] of_seq seq = seq |> Seq.map B.to_offset |> V.of_offset_seq
  let[@inline always] add_seq seq s = Seq.fold_left (Fun.flip add) s seq
  let[@inline always] to_iter s f = iter f s
  let[@inline always] elements s = s |> to_iter |> Iter.to_list
  let[@inline always] to_list s = elements s
  let[@inline always] to_rev_iter s f = rev_iter f s

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

  let[@inline always] choose_opt s =
    let n = Random.int (cardinal s) in
    s |> to_iter |> Iter.take n |> Iter.head

  let[@inline always] choose s = Option.get (choose_opt s)
  let[@inline always] find_opt p s = s |> to_iter |> Iter.find p
  let[@inline always] find p s = Option.get (find_opt p s)
  let find_first = find
  let find_first_opt = find_opt
  let[@inline always] find_last_opt p s = s |> to_rev_iter |> Iter.find p
  let[@inline always] find_last p s = Option.get (find_last_opt p s)
  let[@inline always] map f s = s |> to_iter |> Iter.map f |> of_iter
  let[@inline always] filter p s = s |> to_iter |> Iter.filter p |> of_iter

  let[@inline always] filter_map f s =
    s |> to_iter |> Iter.filter_map f |> of_iter

  (*TODO: maybe make partition at the level of bitvector. *)
  let[@inline always] partition p s =
    ( s |> to_iter |> Iter.filter p |> of_iter,
      s |> to_iter |> Iter.filter (Fun.negate p) |> of_iter )

  let is_empty = V.is_empty
  let[@inline always] mem e s = V.Relaxed.mem s (B.to_offset e)
  let equal = V.Relaxed.equal
  let subset = V.Relaxed.subset
  let[@inline always] for_all p s = s |> to_iter |> Iter.for_all p
  let[@inline always] exists p s = s |> to_iter |> Iter.exists p
  let[@inline always] pp ppe f = Format.pp_print_iter iter ppe f
end

module WithSexp
    (M : sig
      type elt
      type t

      val to_list : t -> elt list
      val of_list : elt list -> t
    end)
    (K : Sexplib0.Sexpable.S with type t = M.elt) =
struct
  let sexp_of_t s = Sexplib0.Sexp_conv.sexp_of_list K.sexp_of_t (M.to_list s)

  let t_of_sexp e =
    e |> Sexplib0.Sexp_conv.list_of_sexp K.t_of_sexp |> M.of_list

  let print s = print_endline @@ Sexplib0.Sexp.to_string @@ sexp_of_t s
end

let%test_module _ =
  (module struct
    module T = Make (BijectionToInt.Int)

    module S = struct
      include T

      include
        WithSexp
          (T)
          (struct
            type t = int

            let sexp_of_t = Sexplib0.Sexp_conv.sexp_of_int
            let t_of_sexp = Sexplib0.Sexp_conv.int_of_sexp
          end)
    end

    open T

    let a = 1
    let b = 2
    let c = 3
    let a_s = of_list [ a ]
    let b_s = add b empty
    let c_s = of_list [ c ]
    let ab_s = of_list [ a; b ]
    let bc_s = add b (add c empty)
    let%test _ = is_empty empty
    let%test _ = not @@ is_empty a_s
    let%test _ = not @@ is_empty b_s
    let%test _ = not @@ is_empty c_s
    let%test _ = equal (inter a_s ab_s) a_s
    let%test _ = equal (inter ab_s bc_s) b_s
    let%test _ = equal empty (inter a_s b_s)
    let%test _ = cardinal (add a (add b empty)) = 2
  end)
