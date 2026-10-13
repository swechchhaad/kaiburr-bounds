(* ------------------------------------------------------------------------ *)
open Core.Distr
open Core.Distr.Elt

(* ------------------------------------------------------------------------ *)
let q : int = 3329

(* ------------------------------------------------------------------------ *)
module Dq = Core.Distr.Make(struct let q = q end)
open Dq

(* ------------------------------------------------------------------------ *)
let _ = Core.Distr.D.set_default_prec 500
let _ = Core.Distr.D.set_default_rounding_mode Core.Distr.D.Toward_Plus_Infinity

(* ------------------------------------------------------------------------ *)
let mkrat (d : (elt * int) list) =
  let w = D.make_from_int (List.sum (List.map snd d)) in
  List.map (fun (v, i) -> (D.div (D.make_from_int i) w, v)) d

(* ------------------------------------------------------------------------ *)
let mksymrat ~(zero : int) ~(onward : int list) : distr =
  let s = List.mapi (fun i v -> let i = i+1 in [(v, mk i); (v, mk (q-i))]) onward in
  let s = (zero, mk 0) :: List.flatten s in
  let t = D.make_from_int (List.sum (List.map fst s)) in
  List.map (fun (i, v) -> D.div (D.make_from_int i) t, v) s

(* ------------------------------------------------------------------------ *)
let noise_f (t : int) : distr =
  mksymrat ~zero:((1 lsl (t - 1)) - 2) ~onward:[1 lsl (t - 2); 1]

(* ------------------------------------------------------------------------ *)
type params = {
  name : string;
  k    : int;
  b    : distr;
}

(* ------------------------------------------------------------------------ *)
let kaiburr1792 = { name = "kaiburr-1792"; k = 7;  b = noise_f 4; }
let kaiburr4608 = { name = "kaiburr-4608"; k = 18; b = noise_f 6; }
let kaiburr6144 = { name = "kaiburr-6144"; k = 24; b = noise_f 8; }

(* ------------------------------------------------------------------------ *)
module type MP = sig
  val p : params
end

(* ------------------------------------------------------------------------ *)
module M(X : MP) = struct
  let b : distr = X.p.b

  (* ---------------------------------------------------------------------- *)
  let log fmt =
    let buf  = Buffer.create 127 in
    let fbuf = Format.formatter_of_buffer buf in
      Format.kfprintf
        (fun _ ->
          Format.pp_print_flush fbuf ();
          Format.eprintf "[%s]: %s@." X.p.name (Buffer.contents buf))
        fbuf fmt

  (* ---------------------------------------------------------------------- *)
  (* <B, B>                                                                 *)
  let bb : distr =
    log "Computing <b, b>";
    dmul b b

  (* ---------------------------------------------------------------------- *)
  (* <B, B>_256                                                             *)
  let bb256 : distr =
    log "Computing <b, b>_256";
    dexp bb 256

  (* ---------------------------------------------------------------------- *)
  (* <B, B>_256k                                                            *)
  let bb256k : distr =
    log "Computing <b, b>_256k";
    dexp bb256 X.p.k

  (* ---------------------------------------------------------------------- *)
  (* <B, B>_256k + <B, B>_256k + B                                          *)
  let theorem_3_distr : distr =
    log "Computing <b, b>_256k + <b, b>_256k + b (theorem 3)";
    dadd (dadd bb256k bb256k) b

  (* ------------------------------------------------------------------------ *)
  let failure : D.mpfr_float =
    let max_noise = q / 4 - 1 in
    let tail = theorem_3_distr |> List.filter (fun (_, (x : elt)) ->
      abs (cmod (x :> int) q) > max_noise) in
    let p = List.fold_left (fun acc (p, _) -> D.add acc p) (D.make_zero D.Positive) tail in
    let p = D.mul (D.make_from_int 256) p in
    log "failure probability <= 2^%s" (ppf ~log2:true p);
    p

  (* ---------------------------------------------------------------------- *)
  let json : Yojson.Safe.t = `Assoc [
    "<b,b>"      , Core.Distr.yojson_of_distr bb;
    "<b,b>_256"  , Core.Distr.yojson_of_distr bb256;
    "<b,b>_256k" , Core.Distr.yojson_of_distr bb256k;
    "th3"        , Core.Distr.yojson_of_distr theorem_3_distr;
    "failure"    , `String (ppf ~log2:true failure);
  ]
end

(* ------------------------------------------------------------------------ *)
let () =
  let params : (module MP) list = [
    (module struct let p = kaiburr1792 end : MP);
    (module struct let p = kaiburr4608 end : MP);
    (module struct let p = kaiburr6144 end : MP)] in

  List.iter (fun (module MP : MP) ->
    (* Instantiating the module starts all the computations *)
    let module M = M(MP) in
    File.with_file_out (Format.sprintf "%s.json" MP.p.name) (fun stream ->
      let fmt = Format.formatter_of_out_channel stream in
      Format.fprintf fmt "%a@." (Yojson.Safe.pretty_print ~std:true) M.json 
    )
  ) params
