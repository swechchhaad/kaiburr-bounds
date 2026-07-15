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
(* Noise distribution f(n): symmetric, support {-2,-1,0,1,2}.
   Pr[0] = 1/2 - 1/2^(n-1),  Pr[+-1] = 1/4,  Pr[+-2] = 1/2^n.
   Unnormalized integer weights (sum = 2^n):
     0  -> 2^(n-1) - 2 ;  +-1 -> 2^(n-2) ;  +-2 -> 1.
   f(4) reproduces CBD(eta=2), the original ML-KEM noise. *)
let noise_f (n : int) : distr =
  mksymrat ~zero:((1 lsl (n-1)) - 2) ~onward:[ 1 lsl (n-2); 1 ]

(* ------------------------------------------------------------------------ *)
let mkf (e : int) : elt =
  Elt.mk (pmod e q)

(* ------------------------------------------------------------------------ *)
let round10 =
  mkrat [
    mkf   0 , 1024;
    mkf   1 , 1024;
    mkf (-1), 1024;
    mkf   2 ,  129;
    mkf (-2),  128;
  ]

(* ------------------------------------------------------------------------ *)
let round11 =
  mkrat [
    mkf   0 , 2048;
    mkf   1 ,  641;
    mkf (-1),  640;
  ]

(* ------------------------------------------------------------------------ *)
let round4 =
  let open Enum in mkrat(
      [(mkf 104, 9); (mkf (-104), 8)]
    @ List.of_enum (Enum.map (fun i -> (mkf i, 16)) ((-103) -- 103))
  )

(* ------------------------------------------------------------------------ *)
let round5 =
  let open Enum in mkrat (
      [(mkf 52, 17); (mkf (-52), 16)]
    @ List.of_enum (Enum.map (fun i -> (mkf i, 32)) ((-51) -- 51))
  )

(* ------------------------------------------------------------------------ *)
(* No ciphertext compression: rounding error is 0 with probability 1.        *)
let no_round = mkrat [ mkf 0, 1 ]

(* ------------------------------------------------------------------------ *)
type params = {
  name      : string;
  k         : int;
  noise     : distr;
  dcu       : distr;
  dcv       : distr;
  threshold : int;
  cvmax     : int;
}

(* ------------------------------------------------------------------------ *)
let kyber768 = {
  name = "kyber-768"; k = 18; noise = noise_f 6; dcu = no_round; dcv = no_round; threshold = (q / 4) - 1; cvmax = 0;
}

(* ------------------------------------------------------------------------ *)
let kyber1024 = {
  name = "kyber-1024"; k = 24; noise = noise_f 8; dcu = no_round; dcv = no_round; threshold = (q / 4) - 1; cvmax = 0;
}

(* ------------------------------------------------------------------------ *)
module type MP = sig
  val p : params
end

(* ------------------------------------------------------------------------ *)
module M(X : MP) = struct
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
  (* Per-variant noise distribution B (= f(n) for this variant).            *)
  let b : distr = X.p.noise

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
  (* <B, Dcu>                                                               *)
  let bdcu : distr =
    log "Computing <b, Dcu>";
    dmul b X.p.dcu

  (* ---------------------------------------------------------------------- *)
  (* <B, Dcu>_k                                                             *)
  let bdcu_k : distr =
    log "Computing <b, Dcu>_k";
    dexp bdcu X.p.k

  (* ---------------------------------------------------------------------- *)
  (* <B, Dcu>_ki for i=0..256                                               *)
  let bdcu_ki : distr array =
    Array.make 257 [(D.make_from_int 1, mk 0)]

  let () =
    for i = 1 to 256 do
      log "Computing <b, Dcu>_ki [i = %d]" i;
      bdcu_ki.(i) <- dadd bdcu_k bdcu_ki.(i - 1)  
    done

  (* ---------------------------------------------------------------------- *)
  (* B + Dcu                                                                *)
  let bDdcu : distr =
    log "Computing (b + Dcu)";
    dadd b X.p.dcu

  (* ---------------------------------------------------------------------- *)
  (* <B, B + Dcu>                                                           *)
  let b_bDdcu : distr =
    log "Computing <b, b + Dcu>";
    dmul b bDdcu

  (* ---------------------------------------------------------------------- *)
  (* <B, B + Dcu>_k                                                         *)
  let b_bDdcu_k : distr =
    log "Computing <b, b + Dcu>_k";
    dexp b_bDdcu X.p.k

  (* ---------------------------------------------------------------------- *)
  (* <B, B + Dcu>_ki for i=0..256                                           *)
  let b_bDdcu_ki : distr array =
    Array.make 257 [(D.make_from_int 1, mk 0)]

  let () =
    for i = 1 to 256 do
      log "Computing <b, b + Dcu>_ki [i = %d]" i;
      b_bDdcu_ki.(i) <- dadd b_bDdcu_k b_bDdcu_ki.(i - 1)  
    done

  (* ---------------------------------------------------------------------- *)
  (* <B, B>_256k + <B, B>_256k + B                                          *)
  let theorem_3_distr : distr =
    log "Computing <b, b>_256k + <b, b>_256k + b (theorem 3)";
    dadd (dadd bb256k bb256k) b

  (* ---------------------------------------------------------------------- *)
  (* <B, Dcu>_256k(i + 1) + <B, Dcu>_256k(255 - i)                          *)
  let theorem_5_distr : distr array =
    Array.init 256 (fun i ->
      log "Computing <b, Dcu>_256k(i + 1) + <b, Dcu>_256k(255 - i) (theorem 5) [i = %d]" i;
      dsub bdcu_ki.(i + 1) bdcu_ki.(255 - i)
    )
  
  (* ---------------------------------------------------------------------- *)
  (* <B, B>_256k - (<B, B + Dcu>_256k(i + 1) - <B, B + Dcu>_256k(255 - i)) + B + Dcv *)
  let theorem_6_distr : distr array =
    let d : distr = dadd bb256k (dadd b X.p.dcv) in
    Array.init 256 (fun i ->
      log "Computing <b, b>_256k - (<b, b + Dcu>_256k(i + 1) - <b, b + Dcu>_256k(255 - i)) + b + Dcv (theorem 6) [i = %d]" i;
      let d2 = dsub b_bDdcu_ki.(i + 1) b_bDdcu_ki.(255 - i) in
      dsub d d2
    )

  (* ---------------------------------------------------------------------- *)
  (* <B, B>_256k - (<B, B + Dcu>_256k(i + 1) - <B, B + Dcu>_256k(255 - i)) + B *)
  let theorem_7_distr : distr array =
    let d : distr = dadd bb256k b in
    Array.init 256 (fun i ->
      log "Computing <b, b>_256k - (<b, b + Dcu>_256k(i + 1) - <b, b + Dcu>_256k(255 - i)) + b (theorem 7) [i = %d]" i;
      let d2 = dsub b_bDdcu_ki.(i + 1) b_bDdcu_ki.(255 - i) in
      dsub d d2
    )

  (* ------------------------------------------------------------------------ *)
  let estimate_provable =
    log "Estimate (provable)";
    let compute (tcu : int) =
      let t1 = q / 4 - 1 - X.p.cvmax - tcu in
      let t2 = tcu in
  
      let d1 = theorem_3_distr in
      let d2 = theorem_5_distr in

      let d1 = d1 |> List.filter (fun (_, (x : elt)) ->
        let x = cmod (x :> int) q in
        not (-t1 <= x && x < t1)
      ) in
      let d1 = List.reduce D.add (List.map fst d1) in
      let d1 = D.mul (D.make_from_int 256) d1 in
  
      let d2 =
        Array.reduce D.add (d2 |> Array.map (fun d2 ->
          let d2 = d2 |> List.filter (fun (_, (x : elt)) ->
            let x = cmod (x :> int) q in
            not (-t2 <= x && x < t2)
          ) in
          List.reduce D.add (List.map fst d2))) in
  
      (d1, d2, D.add d1 d2) in
  
    let prs =
      let open Enum in
      Enum.map (fun tcu -> (tcu, compute tcu)) (0 -- (q / 4 - 1 - X.p.cvmax)) in
  
    let prs = List.of_enum prs in

    let (mintcu, _) =
      List.min ~cmp:(fun (_, (_, _, p1)) (_, (_, _, p2)) -> D.cmp p1 p2) prs in

    (mintcu, prs)
  
  (* ------------------------------------------------------------------------ *)
  let estimate_cu_cv =
    log "Estimate (cu/cv)";

    let flpr = ref (D.make_zero D.Positive) in

    for i = 0 to 255 do
      let d = theorem_6_distr.(i) in
      let d = d |> List.filter (fun (_, (x : elt)) ->
        let x = cmod (x :> int) q in
        not (-X.p.threshold <= x && x < X.p.threshold)
      ) in
      flpr := D.add !flpr (List.reduce D.add (List.map fst d))
    done;
  
    !flpr
  
  (* ------------------------------------------------------------------------ *)
  let estimate_cu =
    log "Estimate (cu only)";

    let flpr = ref (D.make_zero D.Positive) in
    let threshold = X.p.threshold - X.p.cvmax in

    for i = 0 to 255 do
      let d = theorem_7_distr.(i) in
      let d = d |> List.filter (fun (_, (x : elt)) ->
        let x = cmod (x :> int) q in
        not (-threshold <= x && x < threshold)
      ) in
      flpr := D.add !flpr (List.reduce D.add (List.map fst d))
    done;
  
    !flpr

  (* ------------------------------------------------------------------------ *)
  let json : Yojson.Safe.t = `Assoc [
    "<b,b>"       , Core.Distr.yojson_of_distr bb;
    "<b,b>_256"   , Core.Distr.yojson_of_distr bb256;
    "<b,b>_256k"  , Core.Distr.yojson_of_distr bb256k;
    "<b,dcu>"     , Core.Distr.yojson_of_distr bdcu;
    "<b,dcu>_k"   , Core.Distr.yojson_of_distr bdcu_k;
    "<b,dcu>_ki"  , `List (Array.map Core.Distr.yojson_of_distr bdcu_ki |> Array.to_list);
    "b+dcu"       , Core.Distr.yojson_of_distr bDdcu;
    "<b,b+dcu>"   , Core.Distr.yojson_of_distr b_bDdcu;
    "<b,b+dcu>_k" , Core.Distr.yojson_of_distr b_bDdcu_k;
    "<b,b+dcu>_ki", `List (Array.map Core.Distr.yojson_of_distr b_bDdcu_ki |> Array.to_list);
    "th3"         , Core.Distr.yojson_of_distr theorem_3_distr;
    "th5"         , `List (Array.map Core.Distr.yojson_of_distr theorem_5_distr |> Array.to_list);
    "th6"         , `List (Array.map Core.Distr.yojson_of_distr theorem_6_distr |> Array.to_list);
    "th7"         , `List (Array.map Core.Distr.yojson_of_distr theorem_7_distr |> Array.to_list);
    "provable"    , `Assoc [
      "alltcu"    , `List (
                      List.map (fun (tcu, (p1, p2, p)) ->
                        `List [
                          `Int tcu;
                          `String (ppf ~log2:true p1);
                          `String (ppf ~log2:true p2);
                          `String (ppf ~log2:true p)
                        ]
                      ) (snd estimate_provable));
      "mintcu"    , `Int (fst estimate_provable);
    ];
    "estimate_cu_cv", `String (Core.Distr.ppf ~log2:true estimate_cu_cv);
    "estimate_cu"   , `String (Core.Distr.ppf ~log2:true estimate_cu);
  ]
end

(* ------------------------------------------------------------------------ *)
let () =
  let params : (module MP) list = [
    (module struct let p = kyber768  end : MP);
    (module struct let p = kyber1024 end : MP)] in

  List.iter (fun (module MP : MP) ->
    (* Instantiating the module starts all the computations *)
    let module M = M(MP) in
    File.with_file_out (Format.sprintf "%s.json" MP.p.name) (fun stream ->
      let fmt = Format.formatter_of_out_channel stream in
      Format.fprintf fmt "%a@." (Yojson.Safe.pretty_print ~std:true) M.json 
    )
  ) params
