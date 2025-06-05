open Crowbar
module BvSet = BitvectorSet.Make (Int)

module StdSet = struct
  include Set.Make (Int)

  let equal_modulo ~modulo x y = equal (inter x modulo) (inter y modulo)
end

type 'a set_op =
  | Empty
  | Singleton of 'a
  | Doubleton of 'a * 'a
  | Add of 'a * 'a set_op
  | Remove of 'a * 'a set_op
  | Union of 'a set_op * 'a set_op
  | Inter of 'a set_op * 'a set_op
  | Diff of 'a set_op * 'a set_op

let rec pp_t ppa f =
  let pp_t = pp_t0 ppa in
  function
  | Empty -> Format.fprintf f "empty"
  | Singleton x -> Format.fprintf f "singleton %a" ppa x
  | Doubleton (x, y) -> Format.fprintf f "doubleton %a %a" ppa x ppa y
  | Add (k, s) -> Format.fprintf f "add %a %a" ppa k pp_t s
  | Remove (k, s) -> Format.fprintf f "remove %a %a" ppa k pp_t s
  | Union (x, y) -> Format.fprintf f "union %a %a" pp_t x pp_t y
  | Inter (x, y) -> Format.fprintf f "inter %a %a" pp_t x pp_t y
  | Diff (x, y) -> Format.fprintf f "diff %a %a" pp_t x pp_t y

and pp_t0 ppa f = function
  | Empty -> Format.fprintf f "empty"
  | x -> Format.fprintf f "@[<1>(%a)@]" (pp_t ppa) x

let rec interpret_bitvec =
  let open BvSet in
  let interpret = interpret_bitvec in
  function
  | Empty -> empty
  | Singleton x -> singleton x
  | Doubleton (x, y) -> doubleton x y
  | Add (k, s) -> add k (interpret s)
  | Remove (k, s) -> remove k (interpret s)
  | Union (x, y) -> union (interpret x) (interpret y)
  | Inter (x, y) -> inter (interpret x) (interpret y)
  | Diff (x, y) -> diff (interpret x) (interpret y)

let rec interpret_stdset =
  let open StdSet in
  let interpret = interpret_stdset in
  function
  | Empty -> empty
  | Singleton x -> singleton x
  | Doubleton (x, y) -> add x (singleton y)
  | Add (k, s) -> add k (interpret s)
  | Remove (k, s) -> remove k (interpret s)
  | Union (x, y) -> union (interpret x) (interpret y)
  | Inter (x, y) -> inter (interpret x) (interpret y)
  | Diff (x, y) -> diff (interpret x) (interpret y)

let check_interpretation op =
  let stds = interpret_stdset op in
  let bvs = interpret_bitvec op in
  let as_bvs = stds |> StdSet.to_seq |> BvSet.of_seq in
  check_eq ~eq:BvSet.equal ~pp:(BvSet.pp Format.pp_print_int) as_bvs bvs

let set_gen : int set_op gen =
  with_printer (pp_t Format.pp_print_int)
  @@ fix (fun set_gen ->
         choose
           [
             const Empty;
             map [ int ] (fun x -> Singleton x);
             map [ int; int ] (fun x y -> Doubleton (x, y));
             map [ int; set_gen ] (fun k s -> Add (k, s));
             map [ int; set_gen ] (fun k s -> Remove (k, s));
             map [ set_gen; set_gen ] (fun x y -> Union (x, y));
             map [ set_gen; set_gen ] (fun x y -> Inter (x, y));
             map [ set_gen; set_gen ] (fun x y -> Diff (x, y));
           ])

let () =
  add_test ~name:"set operations" [ set_gen ] check_interpretation;
  add_test ~name:"disjoint" [ set_gen; set_gen ] (fun opx opy ->
      let sx, bx = (interpret_stdset opx, interpret_bitvec opx) in
      let sy, by = (interpret_stdset opy, interpret_bitvec opy) in
      check_eq ~eq:Bool.equal ~pp:Format.pp_print_bool (StdSet.disjoint sx sy)
        (BvSet.disjoint bx by));
  add_test ~name:"equal_modulo" [ set_gen; set_gen; set_gen ]
    (fun opx opy opm ->
      let sx, bx = (interpret_stdset opx, interpret_bitvec opx) in
      let sy, by = (interpret_stdset opy, interpret_bitvec opy) in
      let sm, bm = (interpret_stdset opm, interpret_bitvec opm) in
      check_eq ~eq:Bool.equal ~pp:Format.pp_print_bool
        (StdSet.equal_modulo ~modulo:sm sx sy)
        (BvSet.equal_modulo ~modulo:bm bx by));
  add_test ~name:"cardinality" [ set_gen ] (fun ops ->
      let stds = interpret_stdset ops in
      let bvs = interpret_bitvec ops in
      check_eq ~eq:Int.equal ~pp:Format.pp_print_int (StdSet.cardinal stds)
        (BvSet.cardinal bvs));
  add_test ~name:"mem" [ int; set_gen ] (fun k ops ->
      let stds = interpret_stdset ops in
      let bvs = interpret_bitvec ops in
      check_eq ~eq:Bool.equal ~pp:Format.pp_print_bool (StdSet.mem k stds)
        (BvSet.mem k bvs))
