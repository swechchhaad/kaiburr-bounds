require import AllCore Real List IntDiv Distr.
require (****) LWE_correctness.
require (****) DynMatrix Dmatrix.
require import ZModP.
require import Array.
require import BitEncoding.
(*---*) import BS2Int.
(*---*) import BitChunking.
require import StdOrder.
(*---*) import RField IntOrder RealOrder.

theory FrodoPKECorr.

op N : { int | 0 < N } as gt0_N.
op Nb : { int | 0 < Nb } as gt0_Nb.
op Mb : { int | 0 < Mb } as gt0_Mb.
op D : { int | 0 < D <= 16 } as D_bound.
op q : int = 2^D. 
op B : { int | 0 < B <= D } as B_bound.

lemma gt0_B: 0 < B.
proof. by smt(B_bound). qed.

hint exact: gt0_N gt0_Nb gt0_Mb D_bound B_bound gt0_B.
hint simplify (gt0_N, gt0_Nb, gt0_Mb, D_bound, B_bound, gt0_B).

require Word.

clone import Word as W8 with
  type Alphabet.t <- bool,
  op n <- 8
  proof ge0_n by trivial.

op tobytes (xs: bool list): W8.word list = map W8.mkword (chunk W8.card xs).


op chi_support: int list.

op lenChi: int = size chi_support.

axiom gt0_lenChi : 0 < lenChi.

abstract theory FrodoPKE.

abbrev mask5f = W8.mkword (int2bs W8.card 95) (* 95 = 0x5f *).
abbrev mask96 = W8.mkword (int2bs W8.card 150) (* 150 = 0x96 *).

clone DynMatrix as DM.
clone Dmatrix as Dmatrix_ with
  theory DM <- DM.


import DM.
import DM.ZR.
import Dmatrix_.

op toRowVectors (m: matrix): vector list =
  map (row m) (range 0 (rows m)).

op toColVectors (m: matrix): vector list =
  map (col m) (range 0 (cols m)).

op sample (st: bool * int): R =
  ZR.ofint ((if st.`1 then -1 else 1)*size (filter (fun i => i<st.`2) chi_support)).

op ChiFrodo : R distr = dmap ({0,1} `*` DInterval.dinter 0 (lenChi - 1)) sample.


lemma chunknil ['a] x: chunk x [<:'a>] = [<:'a list>].
proof.
rewrite /chunk /=.
exact mkseq0.
qed.

hint simplify chunknil.

op ec : int -> R.
op dc : R -> int.

op max_noise: R.
op under_noise_bound : R -> R -> bool.

axiom good_dc (k: int) (e: R):
     0 <= k < (2^B)
  => under_noise_bound e max_noise
  => dc (ec k + e) = k.

op m_encode_BV (pt: bool list list) : vector =
  let ks = map (fun bs => ec (bs2int bs)) pt in
  offunv (fun i => nth witness ks i, size pt).

op m_decode_BV (v: vector) c: bool list list =
  let dc' = fun c => int2bs B (dc c) in
  map dc' (tolist (subv v 0 c)).

lemma lt_le_addr_gt0 x y: 0 < x => 0 <= y => 0 < x + y.
proof. smt(). qed.

lemma max_eq_ge0 x: 0 <= x => max 0 x = x.
proof. smt(). qed.

lemma max_eq_gt0 x: 0 < x => max 0 x = x.
proof. smt(). qed.

hint simplify (max_eq_ge0, max_eq_gt0).
hint exact: max_eq_ge0 max_eq_gt0.

lemma size_decode_encode_BV (s: bool list list) (ev: vector):
    size (m_decode_BV (m_encode_BV s + ev) (size s)) = size s.
proof.
  rewrite /m_decode_BV /m_encode_BV /=.
  by rewrite size_map size_tolist.
qed.

hint simplify size_decode_encode_BV.
hint exact: size_decode_encode_BV.
  
lemma good_m_decode_BV (pt: bool list list) (ev: vector):
    all (fun (bs: bool list) => size bs = B) pt =>
    (forall i, 0 <= i && i < size pt => under_noise_bound ev.[i] max_noise) =>
    m_decode_BV (m_encode_BV pt + ev) (size pt) = pt.
proof.
move :ev.
elim pt.
+ move => /= ev ?.
  rewrite /m_decode_BV /=.
  rewrite (emptyv_unique (subv _ _ _)) 1:/# /= => *.
  by rewrite -map_comp size_emptyv range_geq.
+ move => p pt h_rec ev h0 h1.
  apply (eq_from_nth witness).
  + done.
  + move => i [#].
    rewrite size_decode_encode_BV => *.
    have {3}<- /= := h_rec (subv ev 1 (1+size pt)) _ _; 1,2: by smt(get_subv).
    case (i = 0) => /= [*|hi].
    + subst i => /=.
      rewrite /m_encode_BV /m_decode_BV /=.
      rewrite (nth_map witness) /=.
      + rewrite size_tolist size_subv 1:/#.
      rewrite nth_tolist /= 1:/# get_subv 1://= get_addv get_offunv 1://= /=.
      have ^ hp <-: size p = B; 1: by smt().
      rewrite good_dc.
      + by rewrite bs2int_ge0 -hp bs2int_le2Xs.
      + by apply h1.
      by rewrite bs2intK /=.
    + rewrite /m_encode_BV /m_decode_BV /=.
      rewrite -!map_comp /(\o) /=.
      rewrite !(nth_map witness) 1,2:size_range 1,2:/# /=.
      rewrite !nth_range 1,2:/#.
      rewrite !get_subv 1..3:/= 1,2:/# !get_addv !get_offunv 1..3:/# /= => /#.
qed.

op m_encode_B (pt: bool list list list) r c: matrix =
  trmx (ofcols c r (map m_encode_BV pt)).

op m_decode_B (m: matrix) r c: bool list list list =
  map (fun v => m_decode_BV v c) (toRowVectors (subm m 0 r 0 c)).

lemma size_decode_encode_B (s: bool list list list) (e: matrix) c:
    size (m_decode_B (m_encode_B s (size s) c + e) (size s) c) = size s.
proof.
  rewrite /m_decode_B /m_encode_B /=.
  rewrite -map_comp /(\o) /=.
  rewrite size_map size_range // max_eq_ge0 1:/# //.
qed.

hint simplify size_decode_encode_B.
hint exact: size_decode_encode_B.

lemma subv_row m i c:
    cols m = c =>
    row m i = subv (row m i) 0 c.
proof.
move => <-.
rewrite eq_vectorP size_row size_subv => /> *.
rewrite get_subv /#.
qed.

lemma subm_addm (m1 m2:matrix) r1 r2 c1 c2:
    subm (m1+m2) r1 r2 c1 c2 = subm m1 r1 r2 c1 c2 + subm m2 r1 r2 c1 c2.
proof.
rewrite eq_matrixP size_addm !size_subm => /> *.
rewrite get_addm !get_subm 1..6:/#.
by rewrite get_addm.
qed.

lemma good_m_decode_B (pt: bool list list list) (e: matrix) c:
    0 <= c =>
    all (fun (p: bool list list) => size p = c ) pt =>
    all (all (fun (bs: bool list) => size bs = B)) pt =>
    (forall i j, 0 <= i && i < (size pt) && 0 <= j && j < c => under_noise_bound e.[i, j] max_noise) =>
    m_decode_B (m_encode_B pt (size pt) c + e) (size pt) c = pt.
proof.
move :e c.
elim pt.
+ move => *.
  by rewrite -size_eq0 size_decode_encode_B.
+ move => p pt h_rec e c ? h0 h1 h2.
  apply (eq_from_nth witness).
  + done.
  + rewrite size_decode_encode_B => i /= *.
    have hp0 : size p = c; 1: by smt().
    have hp1 : all (fun (bs: bool list) => size bs = B) p; 1: by smt().
    have hpt0 : all (fun (p: bool list list) => size p = c) pt; 1: by smt().
    have hpt1 : all (all (fun (bs: bool list) => size bs = B)) pt; 1: by smt(). 
    
    have {4}<- := h_rec (subm e 1 (1+size pt) 0 c) c _ _; 1..4:smt(get_subm).
    case (i = 0) => /= hi *.
    + subst i.
      rewrite /m_encode_B /m_decode_B -map_comp /(\o) /=.
      rewrite (nth_map witness) 1:size_range 1:/# /=.
      rewrite subm_addm rowD -submT row_trmx.
      rewrite nth_range 1:/# /=.
      have ->: col (subm (ofcols c (1+size pt) (m_encode_BV p :: map m_encode_BV pt)) 0 c 0 (1+size pt)) 0 = m_encode_BV p.
      + rewrite eq_vectorP size_col rows_subm.
        split => *.
        + rewrite /m_encode_BV /= /#.
        + rewrite get_col get_subm 1,2:/# get_offunm 1:/# //=.
      rewrite -{2}(good_m_decode_BV p (row (subm e 0 (1+size pt) 0 c) 0) _ _) 1://. 
      + move => i *. rewrite get_row get_subm 1,2:/# /=.
        rewrite (h2 0 i) 1:/#.
      congr => /#. 
    + rewrite /m_decode_B /m_encode_B /= -!map_comp /(\o) /=.
      rewrite !(nth_map witness) 1,2:size_range 1,2:/# /=.
      rewrite !nth_range 1,2:/# /=.
      congr.
      rewrite eq_vectorP.
      rewrite !size_row !cols_subm => /= *.
      rewrite !get_subm 1..4:/#.
      rewrite 2!get_addm get_subm 1,2:/# /=.
      rewrite !get_offunm 1,2:/# /= => /#.
qed.

lemma mem_chunk_all (xs: 'a list) c ys:
    0 <= c =>
    ys \in chunk c xs => all (fun y => y \in xs) ys.
proof.
rewrite allP /= => ?.
case (c = 0) => ?.
+ subst c. rewrite chunk_le0 1:// => /#.
+ rewrite (nthP witness).
  case => i.
  rewrite size_chunk 1:/# => [#] ? ?.
  rewrite /chunk nth_mkseq 1:/# /= => <- *.
  by rewrite (mem_drop (c*i)) (mem_take c).
qed.

lemma mem_chunk (xs: 'a list) c ys y:
    0 <= c =>
    y \in ys =>
    ys \in chunk c xs => 
    y \in xs.
proof.
move => *.
have := mem_chunk_all xs c ys _ _; 1,2: trivial.
rewrite allP /= => /#.
qed.

op m_encode (pt: bool list) r c: matrix =
  let pt' = chunk c (chunk B pt) in
  m_encode_B pt' r c.

op m_decode (m: matrix) r c: bool list =
  flatten (flatten (m_decode_B m r c)).

lemma good_m_decode (pt: bool list) (e: matrix) c:
  0 <= c =>
  (B * c) %| size pt =>
  (forall i j, 0 <= i && i < size pt %/ (B * c) && 0 <= j && j < c => under_noise_bound e.[i,j] max_noise) =>
  m_decode (m_encode pt (size pt %/ (B*c)) c + e) (size pt %/ (B*c)) c = pt.
proof.
pose r := size pt %/ (B*c).
move => *.
case (c = 0) => ?.
+ subst c.
  have ? : pt = [].
  + rewrite -size_eq0 -dvd0z => /#.
  subst pt => /=.
  rewrite /m_decode /m_encode /= /m_encode_B /m_decode_B /=.
  rewrite ofcols_zerom_tr -map_comp rows_subm /r /=.
  by rewrite range_geq 1:// /= !flatten_nil.
+ have hr: size pt = B*r*c.
  + rewrite [B*_]mulzC mulzA eqz_mul 1: mulf_neq0 1:lt0r_neq0 1..6://=.

rewrite /m_encode /m_decode /=.
have := (good_m_decode_B (chunk c (chunk B pt)) e c _ _ _ _).
+ trivial.
+ by rewrite allP /= => ?; apply in_chunk_size => /#. 
+ rewrite allP => xs *.
  rewrite allP /= => x *.
  have : x \in (chunk B pt); 1: by smt(mem_chunk).
  by apply in_chunk_size.
+ rewrite !size_chunk 1:/# 1:// -divz_mul 1:// => /#.

+ rewrite !size_chunk 1,2:/# -divz_mul 1:// -/r => ->.
  rewrite !chunkK 1,3:/# //=.
  + by rewrite size_chunk 1:// hr mulzA mulKz 1:lt0r_neq0 1,2:// dvdz_mull dvdzz.
  + by rewrite hr mulzA dvdz_mulr dvdzz.
qed.


clone LWE_correctness as LWE_correctness with
  op LWE_PKE_.LWE_.Chi <- ChiFrodo,
  op LWE_PKE_.m <- N,
  op LWE_PKE_.n <- N,
  op LWE_PKE_.mb <- Mb,
  op LWE_PKE_.nb <- Nb,
  type LWE_PKE_.plaintext <- bool list,
  type LWE_PKE_.ciphertext <- matrix*matrix,
  type LWE_PKE_.pkey <- matrix * LWE_PKE_.LWE_.seed,
  type LWE_PKE_.skey <- matrix,
  op LWE_PKE_.pk_encode <- idfun,
  op LWE_PKE_.pk_decode <- idfun,
  op LWE_PKE_.sk_encode <- idfun,
  op LWE_PKE_.sk_decode <- idfun,
  op LWE_PKE_.m_encode <- fun pt => m_encode pt Mb Nb,
  op LWE_PKE_.m_decode <- fun m => m_decode m Mb Nb,
  op LWE_PKE_.c_encode <- idfun,
  op LWE_PKE_.c_decode <- idfun,
  op valid_plaintext <- fun (m: bool list) => size m = B*Mb*Nb,
  op max_noise <- max_noise,
  op under_noise_bound <- fun (m: matrix) (max_noise: R) => forall i j, 0 <= i && i < Mb && 0 <= j && j < Nb => under_noise_bound m.[i,j] max_noise,
  theory LWE_PKE_.DM <- FrodoPKE.DM
  proof
    LWE_PKE_.m_encode_rows,
    LWE_PKE_.m_encode_cols,
    LWE_PKE_.pk_encodeK by done,
    LWE_PKE_.sk_encodeK by done,
    LWE_PKE_.gt0_m,
    good_c_decode by done,
    LWE_PKE_.gt0_n by done,
    LWE_PKE_.gt0_nb by done,
    LWE_PKE_.gt0_mb by done,
    good_m_decode,
    LWE_PKE_.LWE_.Chi_ll.

realize LWE_PKE_.m_encode_rows.
proof.
move => *.
rewrite /m_encode /m_encode_B /=.
by rewrite cols_offunm.
qed.

realize LWE_PKE_.m_encode_cols.
proof.
move => *.
rewrite /m_encode /m_encode_B /=.
by rewrite rows_offunm.
qed.

realize good_m_decode.
proof.
move => pt e hpt.
have -> h : Mb = size pt %/ (B*Nb).
+ rewrite hpt mulzA -[Mb*_]mulzC -mulzA mulKz 1:lt0r_neq0 1:mulr_gt0 1..4://.
apply good_m_decode => //.
+ rewrite hpt mulzA [Mb*_]mulzC -mulzA dvdz_mulr dvdzz.
qed.

realize LWE_PKE_.LWE_.Chi_ll.
rewrite /ChiFrodo.
rewrite dmap_ll dprod_ll DBool.dbool_ll /= DInterval.dinter_ll.
smt(gt0_lenChi).
qed.

realize LWE_PKE_.gt0_m by exact gt0_N.

end FrodoPKE.


clone import ZModRing as Zq with
  op p <- q
  rename "zmod" as "Zq"
  proof ge2_p.
realize ge2_p.
    rewrite /q.
    rewrite ler_eexpr 2://.
    smt(D_bound).
qed.

section.

op round (x: real): int = floor (x + inv 2%r).

(* -------------------------------------------------------------------- *)
lemma floor_add_lt1 x y: 0%r <= y < 1%r => floor (x%r + y) = x.
proof. by move=> rg; rewrite floorP /#. qed.

lemma round_fromint x : round x%r = x.
proof. by rewrite /round floor_add_lt1 /#. qed.

lemma round_id k x : -1%r/2%r <= x < 1%r/2%r => round (k%r + x) = k.
proof. by move=> ? @/round; rewrite -addrA floor_add_lt1 //#. qed.

lemma round0 x : -1%r/2%r <= x < 1%r/2%r => round x = 0.
proof. by move=> ? @/round; rewrite floorP => /#. qed.

lemma round_eq x y: round (x + y%r) = round x + y.
proof.
by rewrite /round -addrA [y%r+_]addrC addrA from_int_floor_addr.
qed.

(* -------------------------------------------------------------------- *)
lemma ge0_B : 0 <= B.
proof. smt(B_bound). qed.

hint exact : ge0_B.

(* -------------------------------------------------------------------- *)
hint simplify eq_fromint, lt_fromint, le_fromint.

(* -------------------------------------------------------------------- *)
lemma gt0_exp2 n : 0 < 2^n.
proof. by rewrite expr_gt0. qed.

hint exact : gt0_exp2.

lemma gt0_q : 0 < q.
proof. by solve. qed.

hint exact : gt0_q.

lemma ge0_q : 0 <= q.
proof. by smt(gt0_q). qed.

hint exact : ge0_q.

lemma nz_q : q <> 0.
proof. by rewrite expf_eq0. qed.

hint exact : nz_q.

(* -------------------------------------------------------------------- *)
(* 0 <= k < 2^B. *)
op ec' (k : int) = k * q %/ 2^B. 
op dc' (c : int) = round (c%r * (2^B)%r / q%r) %% 2^B.

lemma dvd_2XB_2XD : 2^B %| 2^D.
proof. by apply/dvdz_exp2l; smt(B_bound). qed.

hint exact : dvd_2XB_2XD.

lemma good_dc k e:
     0 <= k < (2^B)
  => (-q%r/(2^(B+1))%r) <= e%r < q%r/(2^(B+1))%r
  => dc' ((ec' k) + e) = k.
proof.
case=> [ge0_k ltk] [hge glt] @/dc' @/ec' @/q.
rewrite divMr // -fromintM mulrDl -mulrA divzK //.
rewrite fromintD mulrDl fromintM mulrK ?eq_fromint //.
rewrite round_id -1: pmod_small //. split.
- rewrite -/q ler_pdivl_mulr //= [_*q%r]mulrC mulrN.
  rewrite fromintM -ler_pdivr_mulr //= !mulNr.
  by rewrite -mulrA -invfM -fromintM -exprS.
- move=> _; rewrite ltr_pdivr_mulr //= -/q fromintM.
  rewrite -ltr_pdivl_mulr // -mulrA -invfM.
  by rewrite -fromintM -exprS.
qed.

end section.

op to_sint i = ((asint i) + q%/2) %% q - q%/2.

lemma asint_addqdiv i: (asint i + q%/2) %% q = asint i + q %/ 2 || (asint i + q%/2) %% q = asint i + q %/ 2 - q.
proof.
case (asint i < q %/ 2) => *.
+ by rewrite modz_small; 1: by smt(ge0_asint).
+ have ? : asint i + q %/ 2 < q + q %/ 2. smt(gtp_asint).
  have ? : q <= asint i + q %/ 2. 
  + have {1}-> /# : q = q %/ 2 + q %/ 2; 1: by rewrite -divzDr -expr1; smt(expr1 dvdz_exp2l D_bound).
  rewrite modzE.
  have -> /# : (asint i + q %/ 2) %/ q = 1.
  + rewrite divz_eqP 1:// /= => /#.
qed.

clone FrodoPKE as FrodoPKE_ with
  op dc <- fun c => dc' (to_sint c),
  op ec <- fun k => inZq (ec' k),
  op max_noise <- inZq (q%/2^B),
  op under_noise_bound <- fun (e: Zq) (max_noise: DM.R) => -((asint max_noise)%r/2%r) <= (to_sint e)%r < (asint max_noise)%r/2%r,
  theory DM.ZR <- ZModpRing
  proof good_dc.

realize good_dc.
proof.
move => k e.
case (B = 0) => hB.
+ rewrite hB expr0 => //=.
  rewrite inZqK /= modzz /= le_fromint lt_fromint => /#.
+ rewrite inZqK pmod_small 1://.
  + rewrite divz_ge0 // ltz_divLR 1:IntOrder.expr_gt0 1://.
    rewrite IntOrder.ltr_pmulr 1:// IntOrder.exprn_egt1 //.
  rewrite /dc' /to_sint.
  rewrite addE inZqK modzDml -addrA modzDml addrA => h0 h1.
  rewrite (modzE _ q) -addrA -opprD subz_add2r /ec'.
  rewrite -fromintM !mulrDl divzK 1:dvdz_mull 1://.
  rewrite !fromintD !mulrDl -fromint_div.
  + rewrite dvdz_mull dvdzz.
  pose x := (_ + q%/2) %/ q.
  rewrite mulNr -mulrA [q*2^B]mulrC mulrA -[(-x*2^B*q)%r / q%r]fromint_div.
  + rewrite -mulNr dvdz_mull dvdzz.
  rewrite -mulNr !mulzK 1,2://.
  rewrite [k%r+_]addrC !round_eq.
  rewrite -modzDm -mulNr modzMl /= modz_mod.
  case (asint_addqdiv e) => [h|? h].
  + move :h1. rewrite h addzK => h1.
    rewrite round0.
    + rewrite ler_pdivl_mulr 1:lt_fromint 1:// ltr_pdivr_mulr 1:lt_fromint 1://.
      rewrite fromintM -ler_pdivr_mulr 1:lt_fromint 1://.
      rewrite -ltr_pdivl_mulr 1:lt_fromint 1://.
      rewrite -mulrA -mulrA -!(fromint_div q) 1:// => /#.
    by rewrite pmod_small.
  + move :h1. rewrite h -addrA -opprD subz_add2r => h1.
    pose y := (asint e * 2 ^B)%r / q%r - (2^B)%r.
    have -> : (asint e * 2^B)%r / q%r = (2^B)%r + y; 1: by smt().
    rewrite round_id.
    + rewrite ltr_subl_addl ler_subr_addr.
      rewrite ltr_pdivr_mulr 1:lt_fromint 1:// ler_pdivl_mulr 1:lt_fromint 1://.
      rewrite fromintM -ler_pdivr_mulr 1:lt_fromint 1:// -ltr_pdivl_mulr 1:lt_fromint 1://.
      rewrite !mulrDl [(2^B)%r * q%r]mulrC -[q%r*_*_]mulrA mulfV /=; 1: by smt(gt0_exp2).
      rewrite -ler_subr_addr -ltr_subl_addl -fromintB.
      rewrite -mulrA [2%r * _]mulrC invfM [q%r * (_*_)]mulrA.
      rewrite -fromint_div 1:// => /#.
    by rewrite modzDl => /#.
qed.

import FrodoPKE_.
import DM.
import LWE_correctness.
import LWE_PKE_.
import LWE_.
import Dmatrix_.
import Distrmatrix_.

abbrev DM_N_Nb = dmatrix ChiFrodo N Nb.
abbrev DM_Mb_N = dmatrix ChiFrodo Mb N.
abbrev DM_Mb_Nb = dmatrix ChiFrodo Mb Nb.

op noise_exp_gradual =
    let spe = dmap (DM_Mb_N `*` DM_N_Nb) (fun (mm : _*_) => mm.`1 * mm.`2) in
    let eps = dmap (DM_Mb_N `*` DM_N_Nb) (fun (mm : _*_) => mm.`1 * mm.`2)  in
    let speeps = dmap (spe `*` eps) (fun (mm : _*_) => mm.`1 - mm.`2)  in
      dmap (speeps `*` DM_Mb_Nb) (fun (mm : _*_) => mm.`1 + mm.`2).

abbrev unb = (fun (cc : R) => - (asint (inZq (q %/ 2 ^ B)))%r / 2%r <= (to_sint cc)%r < (asint (inZq (q %/ 2 ^ B)))%r / 2%r).

module CorrectnessBoundGrad = {
  proc main() : bool = {
     var spes,spe,epss,eps,e'',nu;
     spes <$ DM_Mb_N `*` DM_N_Nb;
     spe <- spes.`1 * spes.`2;
     epss <$ DM_Mb_N `*` DM_N_Nb;
     e'' <$ DM_Mb_Nb;
     eps <- epss.`1 * epss.`2;
     nu <- spe - eps + e'';
     return (! (forall i j, 0<=i<Mb => 0 <= j < Nb => unb nu.[i,j])) ;
  }
}.

lemma errors_match &m :
Pr[CorrectnessBound.main() @ &m : res]=
Pr[CorrectnessBoundGrad.main() @ &m : res].
byequiv => //.
proc. 
conseq (: _ ==> ={nu});1:  smt().
swap {1} 1 2; seq 2 1 : (#pre /\ s'{1} = spes{2}.`1 /\ e{1} = spes{2}.`2).
+ conseq />;rndsem {1} 0;rnd;auto => />.
  have <- : (DM_Mb_N `*` DM_N_Nb) =
    (dlet DM_Mb_N (fun (e : matrix) => dmap DM_N_Nb (fun (r : matrix) => (e, r)))); last by split; smt().
  by rewrite (dprod_dlet DM_Mb_N) /dmap /(\o) /=.
swap {1} 2 -1;swap {2} 2 -1.
seq 2 1 : (#pre /\ e'{1} = epss{2}.`1 /\ s{1} = epss{2}.`2).
+ conseq />;rndsem {1} 0;rnd;auto => />.
  have <- : (DM_Mb_N `*` DM_N_Nb) =
    (dlet DM_Mb_N (fun (e : matrix) => dmap DM_N_Nb (fun (r : matrix) => (e, r)))); last by split; smt().
  by rewrite (dprod_dlet DM_Mb_N) /dmap /(\o) /=.
auto => /> &2 epp ?; rewrite /noise_exp_val.
smt(@Matrices).
qed.

lemma error_grad &m : 
Pr[CorrectnessBoundGrad.main() @ &m : res] =
   mu noise_exp_gradual (fun (m:matrix) =>
     !(forall i j,  0<=i<Mb => 0 <= j <Nb => unb m.[i,j])).
byphoare => //;proc => /=. 
  rndsem* 0; rnd => /=. 
  conseq (: _ ==> mu
    (dlet (DM_Mb_N `*` DM_N_Nb)
       (fun (spes0 : matrix * matrix) =>
          dlet (DM_Mb_N `*` DM_N_Nb)
            (fun (epss0 : matrix * matrix) =>
               dmap DM_Mb_Nb ((+) (spes0.`1 * spes0.`2 - epss0.`1 * epss0.`2)))))
    (fun (x : matrix) =>
       ! (forall (i j : int),
            0 <= i < Mb =>
            0 <= j < Nb =>
            - (asint (inZq (q %/ 2 ^ B)))%r / 2%r <= (to_sint x.[i, j])%r < (asint (inZq (q %/ 2 ^ B)))%r / 2%r)) =
         mu noise_exp_gradual (fun (m:matrix) =>
     !(forall i j,  0<=i<Mb => 0 <= j <Nb => unb m.[i,j])));
   1: by move => _ _;split => ->; smt().
  auto => &hr;rewrite /noise_exp_gradual /=. 
  congr. 
  rewrite (dmap_dprodE (dmap
     (dmap (DM_Mb_N `*` DM_N_Nb) (fun (mm : matrix * matrix) => mm.`1 * mm.`2) `*`
      dmap (DM_Mb_N `*` DM_N_Nb) (fun (mm : matrix * matrix) => mm.`1 * mm.`2))
     (fun (mm : matrix * matrix) => mm.`1 - mm.`2))
           DM_Mb_Nb (fun (mm : matrix * matrix) => mm.`1 + mm.`2)) => /=.
pose D1 := (DM_Mb_N `*` DM_N_Nb).
rewrite (dmap_dprod D1)   /(\o) /=. 
rewrite (dmap_dprodE D1) /(\o) /=.
rewrite dlet_dmap dlet_dlet.
congr; rewrite fun_ext => e /=.
rewrite dlet_dmap.
by congr; rewrite fun_ext => ep /=.
qed.

lemma dadd_id (d : R distr) : dadd d (dunit zero) = d.
proof. 
rewrite /dadd eq_distr => cc.
rewrite dmap_dprodE /=.
have -> : (fun (x : R) => dmap (dunit zero) (fun (y : R) => x + y))
   = (fun x => dunit x).
+ by apply fun_ext => /= => xx; rewrite dmap_dunit;congr;ring.
by rewrite dlet_dunit dmap1E /(\o).
qed.

lemma dmatrix_proj (d : R distr) (r c : int) :
   is_lossless d =>
   0 <= r < Mb =>
   0 <= c < Nb =>
    dmap (dmatrix d Mb Nb) (fun (m : matrix) => m.[r, c]) = d.
move=> dll ib jb; rewrite dmatrix_dlist //=.
pose F vs := offunm (fun i j => nth witness vs (j * Mb + i), Mb, Nb).
rewrite dmap_comp /(\o).
apply eq_distr => el; rewrite dmapE /pred1 /(\o) /=.
have := DList.dlistE witness d (fun (k:int) (e:R) =>  k <> (c*Mb+r) \/ e = el) (Mb*Nb) => /=.
have -> : (fun (xs : R list) => forall (i0 : int), 0 <= i0 < Mb*Nb => i0 <> (c*Mb+r) \/ nth witness xs i0 = el) = 
     (fun (xs : R list) => nth witness xs (c*Mb+r) = el) by smt().  
have <- : mu (DList.dlist d (Mb * Nb)) (fun (xs : R list) => xs.[c * Mb + r] = el) = mu (DList.dlist d (Mb * Nb)) (fun (x : R list) => (F x).[r, c] = el).
+ apply mu_eq_support => x /=;rewrite DList.supp_dlist; 1:smt(gt0_Mb gt0_Nb). 
  rewrite /F /= => ?; rewrite get_offunm /= /#.
move => ->.
rewrite (StdBigop.Bigreal.BRM.bigD1 _ _ (c*Mb+r)) /=.
- by apply/mem_range => /#.
- by apply/iota_uniq.
rewrite StdBigop.Bigreal.BRM.big1 /=;smt().
qed.

lemma dadd_matrix_tail (d1 d2 : matrix distr) (d1c d2c : R distr) (i j:int) : 
   0 <= i < Mb =>
   0 <= j < Nb =>
   (forall m, m \in d1 => size m = (Mb,Nb)) =>
   (forall m, m \in d2 => size m = (Mb,Nb)) =>
   dmap d1 (fun (m : matrix) => m.[i,j]) = d1c =>
   dmap d2 (fun (m : matrix) => m.[i,j]) = d2c =>
   dmap (dmap (d1 `*` d2) (fun (pp : matrix*matrix) => pp.`1 + pp.`2)) (fun (m : matrix) => m.[i,j]) = dadd d1c d2c.
move => ib jb H11 H21 H12 H22.
rewrite !dmap_comp /(\o) /=.
apply eq_distr => c; rewrite dmap1E /pred1 /(\o).
rewrite (mu_eq_support _ _ (fun (x : matrix * matrix) => (x.`1.[i,j]) + (x.`2.[i,j])= c));1: by
   move  => p H; rewrite /(+) /= get_offunm //=; smt(gt0_Mb gt0_Nb supp_dprod supp_dmatrix).
 have /= := dmap_dprod_comp d1 d2  (fun (m : matrix) => m.[i,j])  (fun (m : matrix) => m.[i,j])(fun a b : R => a + b).
  rewrite eq_distr => H; move : (H c);rewrite !dmap1E /(\o) /pred1 /= => -> /#.
qed.

op dsub (d1 d2 : R distr) : R distr =
  dmap (d1 `*` d2) (fun (xy : R * R) => xy.`1 - xy.`2).

lemma dsub_matrix_tail (d1 d2 : matrix distr) (d1c d2c : R distr) (i j:int) : 
   0 <= i < Mb =>
   0 <= j < Nb =>
   (forall m, m \in d1 => size m = (Mb,Nb)) =>
   (forall m, m \in d2 => size m = (Mb,Nb)) =>
   dmap d1 (fun (m : matrix) => m.[i,j]) = d1c =>
   dmap d2 (fun (m : matrix) => m.[i,j]) = d2c =>
   dmap (dmap (d1 `*` d2) (fun (pp : matrix*matrix) => pp.`1 - pp.`2)) (fun (m : matrix) => m.[i,j]) = dsub d1c d2c.
move =>ib ij H11 H21 H12 H22.
rewrite !dmap_comp /(\o) /=.
apply eq_distr => c; rewrite dmap1E /pred1 /(\o).
rewrite (mu_eq_support _ _ (fun (x : matrix * matrix) => (x.`1.[i,j]) - (x.`2.[i,j])= c));1: by
   move  => p H; rewrite /(+) /= get_offunm //=; smt(gt0_Mb gt0_Nb supp_dprod supp_dmatrix).
 have /= := dmap_dprod_comp d1 d2  (fun (m : matrix) => m.[i,j])  (fun (m : matrix) => m.[i,j])(fun a b : R => a - b).
  rewrite eq_distr => H; move : (H c);rewrite !dmap1E /(\o) /pred1 /= => -> /#.
qed.

lemma ditr_ij i j :
  0 <= i < Mb =>
  0 <= j < Nb =>
  dmap (noise_exp_gradual) (fun (m : matrix) => m.[i,j]) =
    (dadd (dsub (dmul N ChiFrodo ChiFrodo) (dmul N ChiFrodo ChiFrodo)) ChiFrodo).
move =>  Hi Hj.
rewrite  /noise_exp_gradual /=.
pose dd := (dmap
        (dmap (DM_Mb_N `*` DM_N_Nb) (fun (mm : matrix * matrix) => mm.`1 * mm.`2) `*`
         dmap (DM_Mb_N `*` DM_N_Nb) (fun (mm : matrix * matrix) => mm.`1 * mm.`2))
        (fun (mm : matrix * matrix) => mm.`1 - mm.`2)).
have -> := dadd_matrix_tail dd DM_Mb_Nb (dmap dd (fun (m : matrix) => m.[i,j])) ChiFrodo i j Hi Hj _ _.
+ move => m; rewrite /dd.
  rewrite supp_dmap => H;elim H => mm. 
  rewrite supp_dprod => />. 
  rewrite !supp_dmap => H1 H2;elim H1 => m1; elim H2 => m2 /=.
  rewrite !supp_dprod => *.
  have ? : size mm.`1 = (Mb,Nb) by smt(size_offunm size_mulmx gt0_Mb gt0_N gt0_Nb supp_dmatrix).
  have ? : size mm.`2 = (Mb,Nb) by smt(size_offunm size_mulmx gt0_Mb gt0_N gt0_Nb supp_dmatrix).
  by smt(size_offunm).
+ by smt(supp_dmatrix).
+ done. 
+ apply dmatrix_proj;1..3:by smt(Chi_ll). 

congr => /=. 

rewrite /dd; clear dd.
pose dd1 := dmap (DM_Mb_N `*` DM_N_Nb) (fun (mm : matrix * matrix) => mm.`1 * mm.`2).

have dd1dmul : dmap dd1 (fun (m : matrix) => m.[i,j]) = dmul N ChiFrodo ChiFrodo.
+ have /= <- := dmatrixM_ll Mb N Nb ChiFrodo ChiFrodo _ _ _ _ _  i j _ _;1..7:by smt(gt0_Mb gt0_N gt0_Nb Chi_ll).
  congr;rewrite /dd1 dprod_dlet dmap_dlet;congr => /=.
  apply fun_ext => m1.
  rewrite dlet_dunit /= dmap_comp;congr. 
  by apply fun_ext => m2;smt().

have dd1size : forall (m : matrix), m \in dd1 => size m = (Mb, Nb).
+ move => m; rewrite /dd1; rewrite supp_dmap => S; elim S => A. 
  rewrite supp_dprod !supp_dmatrix; 1..4:smt(gt0_Mb gt0_N gt0_Nb). 
  by smt(size_mulmx).

have -> := dsub_matrix_tail dd1 dd1 (dmap dd1 (fun (m : matrix) => m.[i,j])) (dmap dd1 (fun (m : matrix) => m.[i,j])) i j Hi Hj _ _ _ _ .
+ by smt(). 
+ by smt(). 
+ done. 
+ done. 

by congr.
qed.

lemma NoiseBound_mu &m : 
  Pr [ CorrectnessBound.main() @ &m : res ] <=
   (Mb*Nb)%r * mu (dadd (dsub (dmul N ChiFrodo ChiFrodo) (dmul N ChiFrodo ChiFrodo)) ChiFrodo) (predC unb).
proof.
have HH : 
  forall _mr _mc, 0 <= _mr <= Mb => 0 <= _mc <= Nb =>
  mu (noise_exp_gradual) (fun (x : matrix) => ! (forall i j, 0<=i<_mr => 0<=j<_mc => unb x.[i,j])) <= 
  StdBigop.Bigreal.BRA.big predT (fun ii => StdBigop.Bigreal.BRA.big predT (fun jj => mu (noise_exp_gradual) (fun (x : matrix) => !unb x.[ii,jj])) (iota_ 0 _mc)) (iota_ 0 _mr).
+ move => _mr _mc;elim /natind:_mr.
  + move => r ???; have -> : r = 0 by smt(). 
    rewrite (iota0 0 0) //= StdBigop.Bigreal.BRA.big_nil. 
    rewrite (mu_eq _ _ pred0); 1:by smt().
    by rewrite mu0 /#.
  + move => r H Hind Hr Hc.
    move : (Hind _ _); 1,2: by smt().
    clear Hind.
    move => Hind.
    rewrite (iotaSr 0 r) 1:/# /= StdBigop.Bigreal.BRA.big_rcons /= /(predT r) /=.
    have ->  : (fun (x : matrix) =>
     ! (forall (i j : int),
          0 <= i < r + 1 =>
          0 <= j < _mc =>
          - (asint (inZq (q %/ 2 ^ B)))%r / 2%r <= (to_sint x.[i, j])%r < (asint (inZq (q %/ 2 ^ B)))%r / 2%r)) =
     predU (fun (x : matrix) =>
     ! (forall (i j : int),
          0 <= i < r =>
          0 <= j < _mc =>
          - (asint (inZq (q %/ 2 ^ B)))%r / 2%r <= (to_sint x.[i, j])%r < (asint (inZq (q %/ 2 ^ B)))%r / 2%r)) 
     (fun (x : matrix) =>
     ! (forall (j : int),
          0 <= j < _mc =>
          - (asint (inZq (q %/ 2 ^ B)))%r / 2%r <= (to_sint x.[r, j])%r < (asint (inZq (q %/ 2 ^ B)))%r / 2%r)). 
   rewrite /predU fun_ext => ? /=;by smt().
    rewrite mu_or. 
move : Hind.
pose a := mu noise_exp_gradual
  (fun (x : matrix) =>
     ! (forall (i j : int),
          0 <= i < r =>
          0 <= j < _mc =>
          - (asint (inZq (q %/ 2 ^ B)))%r / 2%r <= (to_sint x.[i, j])%r < (asint (inZq (q %/ 2 ^ B)))%r / 2%r)).
pose b := StdBigop.Bigreal.BRA.big predT
  (fun (ii : int) =>
     StdBigop.Bigreal.BRA.big predT
       (fun (jj : int) =>
          mu noise_exp_gradual
            (fun (x : matrix) =>
               ! - (asint (inZq (q %/ 2 ^ B)))%r / 2%r <= (to_sint x.[ii, jj])%r < (asint (inZq (q %/ 2 ^ B)))%r / 2%r))
       (iota_ 0 _mc)) (iota_ 0 r) .
pose d := mu noise_exp_gradual
  (predI
     (fun (x : matrix) =>
        ! (forall (i j : int),
             0 <= i < r =>
             0 <= j < _mc =>
             - (asint (inZq (q %/ 2 ^ B)))%r / 2%r <= (to_sint x.[i, j])%r < (asint (inZq (q %/ 2 ^ B)))%r / 2%r))
     (fun (x : matrix) =>
        ! (forall (j : int),
             0 <= j < _mc =>
             - (asint (inZq (q %/ 2 ^ B)))%r / 2%r <= (to_sint x.[r, j])%r < (asint (inZq (q %/ 2 ^ B)))%r / 2%r))).
have : mu noise_exp_gradual
  (fun (x : matrix) =>
     ! (forall (j : int),
          0 <= j < _mc =>
          - (asint (inZq (q %/ 2 ^ B)))%r / 2%r <= (to_sint x.[r, j])%r < (asint (inZq (q %/ 2 ^ B)))%r / 2%r))<=
 StdBigop.Bigreal.BRA.big predT
  (fun (jj : int) =>
     mu noise_exp_gradual
       (fun (x : matrix) =>
          ! - (asint (inZq (q %/ 2 ^ B)))%r / 2%r <= (to_sint x.[r, jj])%r < (asint (inZq (q %/ 2 ^ B)))%r / 2%r))
  (iota_ 0 _mc); last first. 
+ pose c := mu noise_exp_gradual
  (fun (x : matrix) =>
     ! (forall (j : int),
          0 <= j < _mc =>
          - (asint (inZq (q %/ 2 ^ B)))%r / 2%r <= (to_sint x.[r, j])%r < (asint (inZq (q %/ 2 ^ B)))%r / 2%r)) . 
  pose e := StdBigop.Bigreal.BRA.big predT
  (fun (jj : int) =>
     mu noise_exp_gradual
       (fun (x : matrix) =>
          ! - (asint (inZq (q %/ 2 ^ B)))%r / 2%r <= (to_sint x.[r, jj])%r < (asint (inZq (q %/ 2 ^ B)))%r / 2%r))
  (iota_ 0 _mc) .
  by smt(mu_bounded).

move : Hc. clear d. clear b. clear a.
+ elim /natind:_mc.
  + move => c ??; have -> : c = 0 by smt(). 
    rewrite (iota0 0 0) //= StdBigop.Bigreal.BRA.big_nil. 
    rewrite (mu_eq _ _ pred0); 1:by smt().
    by rewrite mu0 /#.
  + move => c H0 Hind Hc.
    move : (Hind _); 1: by smt().
    clear Hind.
    move => Hind.
    rewrite (iotaSr 0 c) 1:/# /= StdBigop.Bigreal.BRA.big_rcons /= /(predT c) /=.
    have ->  :
  (fun (x : matrix) =>
     ! (forall (j : int),
          0 <= j < c + 1 =>
          - (asint (inZq (q %/ 2 ^ B)))%r / 2%r <= (to_sint x.[r, j])%r < (asint (inZq (q %/ 2 ^ B)))%r / 2%r)) =
     predU 
  (fun (x : matrix) =>
     ! (forall (j : int),
          0 <= j < c  =>
          - (asint (inZq (q %/ 2 ^ B)))%r / 2%r <= (to_sint x.[r, j])%r < (asint (inZq (q %/ 2 ^ B)))%r / 2%r))
  (fun (x : matrix) =>
     ! (- (asint (inZq (q %/ 2 ^ B)))%r / 2%r <= (to_sint x.[r, c])%r < (asint (inZq (q %/ 2 ^ B)))%r / 2%r)). 
   rewrite /predU fun_ext => ? /=;by smt().
    rewrite mu_or. 
move : Hind. 
pose a := mu noise_exp_gradual
  (fun (x : matrix) =>
     ! (forall (j : int),
          0 <= j < c =>
          - (asint (inZq (q %/ 2 ^ B)))%r / 2%r <= (to_sint x.[r, j])%r < (asint (inZq (q %/ 2 ^ B)))%r / 2%r)).
pose b := StdBigop.Bigreal.BRA.big predT
  (fun (jj : int) =>
     mu noise_exp_gradual
       (fun (x : matrix) =>
          ! - (asint (inZq (q %/ 2 ^ B)))%r / 2%r <= (to_sint x.[r, jj])%r < (asint (inZq (q %/ 2 ^ B)))%r / 2%r))
  (iota_ 0 c) .
pose e := mu noise_exp_gradual
  (predI
     (fun (x : matrix) =>
        ! (forall (j : int),
             0 <= j < c =>
             - (asint (inZq (q %/ 2 ^ B)))%r / 2%r <= (to_sint x.[r, j])%r < (asint (inZq (q %/ 2 ^ B)))%r / 2%r))
     (fun (x : matrix) =>
        ! - (asint (inZq (q %/ 2 ^ B)))%r / 2%r <= (to_sint x.[r, c])%r < (asint (inZq (q %/ 2 ^ B)))%r / 2%r)).
  by smt(mu_bounded).

rewrite errors_match error_grad.
move : (HH Mb Nb _ _); 1,2: smt(gt0_Mb gt0_Nb).

pose a:= mu noise_exp_gradual (fun (x : matrix) => ! (forall (i j : int), 0 <= i < Mb => 0 <= j < Nb => unb x.[i, j])).
pose b :=  StdBigop.Bigreal.BRA.big predT
  (fun (ii : int) =>
     StdBigop.Bigreal.BRA.big predT (fun (jj : int) => mu noise_exp_gradual (fun (x : matrix) => ! unb x.[ii, jj]))
       (iota_ 0 Nb)) (iota_ 0 Mb). 
pose c :=  (Mb * Nb)%r * mu (dadd (dsub (dmul N ChiFrodo ChiFrodo) (dmul N ChiFrodo ChiFrodo)) ChiFrodo) (predC unb). 
have : b <= c; last by smt().

rewrite /b /c.
have -> := StdBigop.Bigreal.BRA.eq_big_seq  
   (fun (ii : int) =>
     StdBigop.Bigreal.BRA.big predT (fun (jj : int) => mu noise_exp_gradual (fun (x : matrix) => ! unb x.[ii, jj])) (iota_ 0 Nb))
   (fun (ii : int) =>
     StdBigop.Bigreal.BRA.big predT (fun (jj : int) =>   mu (dadd (dsub (dmul N ChiFrodo ChiFrodo) (dmul N ChiFrodo ChiFrodo)) ChiFrodo) (predC unb)) (iota_ 0 Nb)).
+ move => i  Hi /=.
  apply StdBigop.Bigreal.BRA.eq_big_seq => j Hj /=.
  have Hs := ditr_ij i j _ _; 1..2:smt(mem_iota).
  have -> : 
    mu noise_exp_gradual
  (fun (x : matrix) =>
     ! - (asint (inZq (q %/ 2 ^ B)))%r / 2%r <= (to_sint x.[i, j])%r < (asint (inZq (q %/ 2 ^ B)))%r / 2%r) =
    mu (dmap noise_exp_gradual (fun (m : matrix) => m.[i, j]))
  (fun (c : R) =>
     ! - (asint (inZq (q %/ 2 ^ B)))%r / 2%r <= (to_sint c)%r < (asint (inZq (q %/ 2 ^ B)))%r / 2%r) by rewrite dmapE /(\o) //=. 
  rewrite -Hs &(mu_eq) => ? /= /#.

have -> : iota_ 0 Nb = range 0 Nb by smt().
have -> : iota_ 0 Mb = range 0 Mb by smt().
rewrite StdBigop.Bigreal.BRA.sumri_const;1: smt(gt0_Mb).
rewrite StdBigop.Bigreal.BRA.sumri_const;1: smt(gt0_Nb).
rewrite !RField.intmulr  /#.

qed.

op epsilon_corr : real.

axiom NoiseBoundComputed &m : 
  Pr [ CorrectnessBound.main() @ &m : res ] <= epsilon_corr.

end FrodoPKECorr.
