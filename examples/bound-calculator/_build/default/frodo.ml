(* ------------------------------------------------------------------------ *)
open Core.Distr
open Core.Distr.Elt

(* ------------------------------------------------------------------------ *)
let mknoise ~(q : int) ~(zero : int) ~(onward : int list) : distr =
  let s = List.mapi (fun i v -> let i = i+1 in [(v, mk i); (v, mk (q-i))]) onward in
  let s = (zero, mk 0) :: List.flatten s in
  let t = D.make_from_int (List.sum (List.map fst s)) in
  List.map (fun (i, v) -> D.div (D.make_from_int i) t, v) s

(* ------------------------------------------------------------------------ *)
type params = {
  log2q  : int;
  n      : int;
  b      : int;
  keylen : int;
  noise  : distr;
}

(* ------------------------------------------------------------------------ *)
let frodo640 : params =
  let log2q, n, b, keylen = 15, 640, 2, 128 in
  let q = 1 lsl log2q in
  let noise =
    mknoise
      ~q ~zero:9288
      ~onward:[8720; 7216; 5264; 3384; 1918; 958; 422; 164; 56; 17; 4; 1] in
  { log2q; n; b; keylen; noise; }

(* ------------------------------------------------------------------------ *)
let frodo976 : params =
  let log2q, n, b, keylen = 16, 976, 3, 196 in
  let q = 1 lsl log2q in
  let noise =
    mknoise
      ~q ~zero:11278
      ~onward:[10277; 7774; 4882; 2545; 1101; 396; 118; 29; 6; 1] in
  { log2q; n; b; keylen; noise; }

(* ------------------------------------------------------------------------ *)
let frodo1344 : params =
  let log2q, n, b, keylen = 16, 1344, 4, 256 in
  let q = 1 lsl log2q in
  let noise =
    mknoise
      ~q ~zero:18286
      ~onward:[14320; 6876; 2023; 364; 40; 2] in
  { log2q; n; b; keylen; noise; }

(* ------------------------------------------------------------------------ *)
let params = [frodo640; frodo976; frodo1344]

(* ------------------------------------------------------------------------ *)
module type Params = sig
  val params : params
end

(* ------------------------------------------------------------------------ *)
module Estimator(P : Params) : sig
  val estimate : unit -> D.mpfr_float * distr
end = struct
  (* ---------------------------------------------------------------------- *)
  let q = 1 lsl P.params.log2q

  (* ---------------------------------------------------------------------- *)
  let estimate () =
    D.set_default_prec 500;
    D.set_default_rounding_mode D.Toward_Plus_Infinity;
  
    let module Dq = Core.Distr.Make(struct let q = q end) in
    let open Dq in

    let dm = dmul P.params.noise P.params.noise in (* chi^2 *)
      
    let d = dexp dm P.params.n in
    let d as d0 = dadd (dsub d d) P.params.noise in

    let d = d |> List.filter (fun (_, (x : elt)) ->
      let x = cmod (x :> int) q in
      let b = 1 lsl (P.params.log2q - (P.params.b+1)) in
      not (-b <= x && x < b)
    ) in
  
    let r1r2 = (P.params.keylen + P.params.b - 1) / P.params.b in
    let failure_pr = List.reduce D.add (List.map fst d) in
    let failure_pr = D.mul (D.make_from_int r1r2) failure_pr in

    (failure_pr, d0)
  end

(* ------------------------------------------------------------------------ *)
let main () =
  let log fmt =
    let buf  = Buffer.create 127 in
    let fbuf = Format.formatter_of_buffer buf in
      Format.kfprintf
        (fun _ ->
          Format.pp_print_flush fbuf ();
          Format.eprintf "%s@." (Buffer.contents buf))
        fbuf fmt in

  let do1 (p : params) =
    log "Computing probability failure for FrodoKEM-%d" p.n;
    let aout =
      let module E =
        Estimator(struct let params = p end)
      in E.estimate () in
    (p, aout) in

  let aout = List.map do1 params in

  let json_of_result ((p, (pr, d)) : params * (D.mpfr_float * distr)): Yojson.Safe.t =
    `Assoc [
      "log2q"       , `Int p.log2q;
      "n"           , `Int p.n;
      "b"           , `Int p.b;
      "keylen"      , `Int p.keylen;
      "noise"       , Core.Distr.yojson_of_distr p.noise;
      "distribution", Core.Distr.yojson_of_distr d;
      "failurepr"   , `String (Core.Distr.ppf ~log2:true pr); 
    ] in
    
  let json = `List (List.map json_of_result aout) in

  File.with_file_out "frodokem.json" (fun stream ->
    let fmt = Format.formatter_of_out_channel stream in
    Format.fprintf fmt "%a@." (Yojson.Safe.pretty_print ~std:true) json
  )

(* ------------------------------------------------------------------------ *)
let () =
  main ()
