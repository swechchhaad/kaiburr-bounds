(* ------------------------------------------------------------------------ *)
module D = Mlmpfr

(* ------------------------------------------------------------------------ *)
let pmod (x : int) (q : int) =
  let x = x mod q in
  if x < 0 then x + q else x

(* ------------------------------------------------------------------------ *)
let cmod (x : int) (q : int) =
  let x = pmod x q in
  let x = if x <= q/2 then x else x - q in
  x

(* ------------------------------------------------------------------------ *)
module Elt : sig
  type elt = private int

  val mk : int -> elt
end = struct
  type elt = int

  let mk (x : int) : elt =
    x [@@inline always]
end

(* ------------------------------------------------------------------------ *)
open Elt

(* ------------------------------------------------------------------------ *)
type distr = (D.mpfr_float * elt) list

(* ------------------------------------------------------------------------ *)
let ppf ?(log2 = false) (v : D.mpfr_float) =
  let v = if log2 then D.log2 v else v in
  D.get_formatted_str ~ktz:false ~size:10 v

(* ------------------------------------------------------------------------ *)
let yojson_of_distr (d : distr) : Yojson.Safe.t =
  let d = List.sort (fun (_, (v1 : Elt.elt)) (_, (v2 : Elt.elt)) -> compare v1 v2) d in
  `List (
    List.map (fun (p, (v : Elt.elt)) -> `List [`Int (v :> int); `String (ppf p)]) d
  )

(* ------------------------------------------------------------------------ *)
let pp_distr (fmt : Format.formatter) (d : distr) =
  let pp_point (fmt : Format.formatter) (i, (x : elt)) =
    Format.fprintf fmt "%d -> %s" (x :> int) (D.get_formatted_str i) in

  Format.fprintf fmt "[%a]"
    (Format.pp_print_list
      ~pp_sep:(fun fmt () -> Format.fprintf fmt ", ")
      pp_point)
    d

(* ------------------------------------------------------------------------ *)
module Make(P : sig val q : int end) = struct
  (* ---------------------------------------------------------------------- *)
  let dmap (f : elt -> elt -> elt) (d1 : distr) (d2 : distr) : distr =
    let aout = Array.make P.q (D.make_from_int 0) in

    List.iter (fun (i, x) ->
      List.iter (fun (j, y) ->
        let z : int = (f x y :> int) in
        aout.(z) <- D.add (D.mul i j) aout.(z)) d2
    ) d1;

    Array.fold_righti
      (fun z p d -> if D.zero_p p then d else (p, mk z) :: d)
      aout []

  (* ------------------------------------------------------------------------ *)
  let fqadd (x : elt) (y : elt) : elt = mk (pmod ((x :> int) + (y :> int)) P.q)

  (* ------------------------------------------------------------------------ *)
  let fqsub (x : elt) (y : elt) : elt = mk (pmod ((x :> int) - (y :> int)) P.q)

  (* ------------------------------------------------------------------------ *)
  let fqmul (x : elt) (y : elt) : elt = mk (pmod ((x :> int) * (y :> int)) P.q)

  (* ------------------------------------------------------------------------ *)
  let dadd = dmap fqadd
  let dsub = dmap fqsub
  let dmul = dmap fqmul

  (* ------------------------------------------------------------------------ *)
  let dexp (dm : distr) =
    let rec doit (i : int) : distr =
      match i with
      | _ when i <= 0 ->
        [(D.make_from_int 1, mk 0)]
      | _ when i = 1 ->
        dm
      | _ ->
        let d = doit (i / 2) in
        let d = dadd d d in
        let d = if i mod 2 = 0 then d else dadd d dm in
        d

    in fun i -> doit i
end
