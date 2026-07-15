(* ------------------------------------------------------------------------ *)
(* Fast no-compression bound: with ciphertext compression removed, the noise
   collapses to  n1 = <e,r> - <s,e1> + e2  (paper Theorem 5.1), whose per-
   coefficient distribution is the single distribution
        <B,B>_256k (+) <B,B>_256k (+) B.
   Because the noise B is symmetric ("good"), all 256 coefficients are
   identically distributed, so the union bound is  256 * tail(threshold).
   This equals the calculator's estimate_cu_cv, but avoids the 256 per-index
   convolutions that make the full run slow.                                 *)

open Core.Distr
open Core.Distr.Elt

let q = 3329

module Dq = Core.Distr.Make(struct let q = q end)
open Dq

let () = Core.Distr.D.set_default_prec 500
let () = Core.Distr.D.set_default_rounding_mode Core.Distr.D.Toward_Plus_Infinity

(* symmetric rational distribution, same helper as kyber.ml *)
let mksymrat ~(zero : int) ~(onward : int list) : distr =
  let s = List.mapi (fun i v -> let i = i+1 in [(v, mk i); (v, mk (q-i))]) onward in
  let s = (zero, mk 0) :: List.flatten s in
  let t = D.make_from_int (List.sum (List.map fst s)) in
  List.map (fun (i, v) -> D.div (D.make_from_int i) t, v) s

(* noise f(n): Pr[0]=1/2-1/2^(n-1), Pr[+-1]=1/4, Pr[+-2]=1/2^n *)
let noise_f (n : int) : distr =
  mksymrat ~zero:((1 lsl (n-1)) - 2) ~onward:[ 1 lsl (n-2); 1 ]

let bound ~(k : int) ~(n : int) : D.mpfr_float =
  let b      = noise_f n in
  let bb     = dmul b b in          (* <B,B>       *)
  let bb256  = dexp bb 256 in       (* <B,B>_256   *)
  let bb256k = dexp bb256 k in      (* <B,B>_256k  *)
  let th3    = dadd (dadd bb256k bb256k) b in
  let t      = q / 4 - 1 in
  let tail   = th3 |> List.filter (fun (_, (x : elt)) ->
                 let x = cmod (x :> int) q in
                 not (-t <= x && x < t)) in
  let s = List.fold_left (fun acc (p, _) -> D.add acc p)
            (D.make_zero D.Positive) tail in
  D.mul (D.make_from_int 256) s

let () =
  let report name k n =
    let p = bound ~k ~n in
    Printf.printf "%-11s (k=%2d, no compression, noise f(%d)):  log2(failure bound) = %s\n%!"
      name k n (Core.Distr.ppf ~log2:true p) in
  report "kyber-768"  18 6;
  report "kyber-1024" 24 8
