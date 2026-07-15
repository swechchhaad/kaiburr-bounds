require import AllCore IntDiv ZModP RealExp Ring List PolyReduce Distr DistrExtra DInterval DList FloorCeil.
require import Array32 Array128 Array256 Array768 Array960 Array1152.
require (****) Matrix.
import StdOrder.IntOrder.

theory GFq.

abbrev q : int = 3329.

lemma prime_q : prime q.
rewrite /prime /= => x; case: (x = 0) => // nz_x.
rewrite -dvdz_norml => dvdxq; have := dvdz_le `|x| q _ _ => //.
rewrite ger0_norm 1:normr_ge0 [`|q|]ger0_norm // => le_xq.
have: `|x| \in range 0 (q + 1) by apply/mem_range; rewrite normr_ge0 /= /#.
move: {nz_x le_xq} => rgx; move: `|x| rgx dvdxq => {x}; apply/List.allP.
by rewrite /range -JUtils.iotaredE /(%|) /=.
qed.

clone import ZModField as Zq with 
  op p <- q 
  rename "zmod" as "coeff"
  rename "ZModp" as "Zq"
  proof  prime_p by apply prime_q
  proof *.

(* Signed representation *)
op as_sint(x : coeff) = if (q-1) %/ 2 < asint x then asint x - q else asint x.

abbrev absZq (x: coeff): int = `| as_sint x |.

(* Compression and decompression *)
op round(x : real) : int = floor (x + inv 2%r).

abbrev comp (d: int, x: real): int = round (x * (2^d)%r / q%r).
op compress(d : int, x : coeff) : int = comp d (asint x)%r %% 2^d.

abbrev decomp (d: int, y: real): int = round (y * q%r / (2^d)%r).
op decompress(d : int, x : int) : coeff = incoeff (decomp d x%r).

lemma as_sintK x:
 incoeff (as_sint x) = x.
proof. by rewrite /as_sint; smt(asintK). qed.

lemma incoeffK_sint_small n: 
 - (q-1) %/ 2 <= n <= (q-1) %/ 2 =>
 as_sint (incoeff n) = n.
proof. move=> H; rewrite /as_sint; smt(incoeffK). qed.

lemma as_sintN (x: coeff): as_sint (-x) = - as_sint x.
proof. by rewrite /as_sint oppE;smt(asintK incoeffK). qed.

lemma as_sint_range x :  - (q-1) %/2 <= as_sint x <= (q-1) %/2 by smt(rg_asint).

lemma normP (a epsilon: int):
 `| a | <= epsilon <=> -epsilon <= a <= epsilon
by smt().

lemma as_sint_bounded x y eps:
`| asint x - asint y | <= eps
 => `| as_sint (x-y) | <= eps.
proof.
rewrite !normP; move=> [Hl Hr].
rewrite /as_sint.
case: ((q - 1) %/ 2 < asint (x - y)) => C.
 smt(incoeffN incoeffK asintK).
smt(incoeffN incoeffK asintK).
qed.

lemma absZqB x y eps:
 `| asint x - asint y | <= eps => absZq (x-y) <= eps
by apply as_sint_bounded.

lemma absZqP x eps:
 absZq x <= eps 
 <=> (asint x <= eps \/ q - eps <= asint x)
by smt(rg_asint).

(* Compress-error bound *)
op Bq d = round (q%r / (2^(d+1))%r).

import StdOrder RField RealOrder IntOrder.
lemma Bq_le_half d:
 0 < d =>
 (q%r / (2^(d+1))%r) <= (q-1)%r/2%r.
proof.
move=> gt0; rewrite /Bq /round //.
rewrite exprS 1:/# fromintM.
have ?: q%r / (2 ^ d)%r + 1%r <= q%r - 1%r by smt(lt_pow expr_gt0).
apply ler_pdivl_mulr;1:smt().
rewrite (RField.mulrC (2%r)) invrM;1,2:by smt(lt_pow expr_gt0).
by rewrite RField.mulrC (RField.mulrA (q%r)) (RField.mulrC (q%r)) !RField.mulrA /#.
qed.

lemma dvdzN_q_2d (d: int):
 0 < d =>
 q %% 2^d <> 0.
proof.
elim/natind: d; first smt().
move=> d Hd IH _.
case: (0<d) => HHd; last first.
 by have ->/=/#: d=0 by smt(). 
rewrite exprD_nneg // expr1.
move: (IH HHd); apply contra.
by rewrite -!dvdzE /#.
qed.

op frac (x: real) = x - (floor x)%r.

lemma frac_bound x: 0%r <= frac x < 1%r
by smt(floor_bound).

lemma floorDz (x:int) y:
 floor (x%r + y) = x + floor y.
proof.
rewrite (floorE (x+floor y)) //.
smt(floor_bound).
qed.


lemma le_floorE n x:
 (n <= floor x) = (n%r <= x)
by smt(floor_bound).

lemma floor_ltE x n:
 (floor x < n) = (x < n%r)
by smt(floor_bound).

lemma divz_floor (x y: int):
 0 < y =>
 x %/ y = floor (x%r / y%r).
proof.
move=> gt0.
have ->: x%r / y%r = (x %/ y)%r + (x %% y)%r / y%r.
 by rewrite {1}(divz_eq x y); field; smt(). 
rewrite floorDz.
have ?: 0%r <= (x %% y)%r / y%r < 1%r. 
  rewrite ltr_pdivr_mulr /=; 1: smt().
  split; smt(le_fromint divr_ge0).
by smt(floor_bound).
qed.

lemma modz_floor (x y: int):
 0 < y =>
 x %% y = x - y * floor (x%r / y%r).
proof.
move=> gt0.
rewrite -divz_floor //; smt(divz_eq).
qed.
lemma fracDz x n: frac (n%r + x) = frac x
  by have := floorDz n x; rewrite /frac => -> /= /#.

lemma floor_frac_eq x: x = (floor x)%r + frac x
by smt().

lemma frac0_dvdz (m n: int):
 0 < n =>
 frac (m%r / n%r) = 0%r <=> n %| m.
proof. 
move=> ygt0; rewrite dvdzE modz_floor // /frac. 
split; rewrite -divz_floor; 1,3:smt(). 
+ move => H; have -> : n * (m %/ n) = m; last by ring.
  rewrite mulrC -eq_fromint fromintM.
  by have ->: (m %/ n)%r  = m%r / n%r; smt().
move => H.
by have -> : m = n * (m %/ n); smt().
qed.

lemma from_int_frac n: frac n%r = 0%r
by smt(from_int_floor).

lemma frac_halfP x:
 frac x = inv 2%r => frac (2%r*x) = 0%r.
proof.
move => E; rewrite (floor_frac_eq x) /= mulrDr.
by rewrite -fromintM fracDz E divrr // from_int_frac.
qed.

lemma frac_halfN x:
 frac (2%r*x) <> 0%r => frac x <> inv 2%r
by smt(frac_halfP).

lemma frac_div_eq0 (m n: int):
 0 < n =>
 frac (m%r / n%r) = 0%r
 <=> n %| m.
proof.
move=> gt0.
split => H.
 have E: m%r / n%r = (m %/ n)%r.
  rewrite (floor_frac_eq (m%r / n%r)) H/= divz_floor /#.
 have : m%r = (m %/ n)%r * n%r + (m %% n)%r by smt(dvdz_eq).
 by rewrite -E dvdzE /#.
have : m%r = (m %/ n)%r * n%r + (m %% n)%r.
+ have := divz_eq m n;smt().
rewrite H /= => ->.
rewrite /frac.
have -> : ((m %/ n)%r * n%r / n%r) = (m %/ n)%r by smt().
by have := floorE (m%/n); smt(). 
qed.

lemma frac_inv_gt1 x: 1%r < x => frac (inv x) = inv x.
proof. by move=> H; rewrite /frac; smt(floor_bound). qed.

lemma Bq_noties d:
 0 < d =>
 2^d < q =>
 frac (q%r / (2 ^ (d + 1))%r) <> inv 2%r.
proof.
move=> Hd0 Hd.
rewrite exprS 1:/#.
have ->: q%r / (2 * 2 ^ d)%r
         = inv 2%r * q%r / (2 ^ d)%r by smt().
apply frac_halfN.
rewrite !mulrA divrr //= frac_div_eq0.
 smt(expr_gt0).
by apply dvdzN_q_2d.
qed.

lemma round_divz x y:
 0 < y => 
 round (x%r / y%r) = (2*x+y) %/ (2*y).
proof.
move=> H; rewrite /round.
have ->: x%r / y%r + inv 2%r = (2* x + y)%r / (2*y)%r.
 rewrite fromintD !fromintM; field; smt().
by rewrite divz_floor /#.
qed.

lemma Bq1E: Bq 1 = 832
by rewrite /Bq /= round_divz 1://.

lemma Bq4E: Bq 4 = 104
by rewrite /Bq /= round_divz 1://.

lemma Bq5E: Bq 5 = 52
by rewrite /Bq /= round_divz 1://.

lemma round_bound x:
 x - inv(2%r) < (round x)%r <= x + inv(2%r)
by smt(floor_bound).

lemma from_int_round n: round n%r = n.
proof. by rewrite /round (floorE n) /#. qed. 

lemma round_mono (x y: real):
 x <= y => round x <= round y
by smt(floor_mono).

lemma le_roundE n x:
 (n <= round x) = (n%r <= x + inv 2%r)
by smt(le_floorE).

lemma round_ltE x n:
 (round x < n) = (x + inv 2%r < n%r)
by smt(floor_ltE).

lemma roundDz (x:int) y:
 round (x%r + y) = x + round y.
proof. by rewrite /round -addrA floorDz. qed.

lemma roundN x:
 frac x <> inv 2%r => round (-x) = -round x.
proof.
move => H.
pose nn := round (-x).
have <-:= floorE (round x) (-nn%r+inv 2%r).
 have [??]:= round_bound (-x).
 have ?: -nn%r < x + inv 2%r by smt().
 have ?: x - inv 2%r <= -nn%r by smt().
 have ?: x - inv 2%r < -nn%r.
  have /#: x - inv 2%r <> -nn%r.
  apply (contra _ (frac x = inv 2%r)).
  move => E.
  have ->: x = (-nn)%r + inv 2%r by smt().
   by rewrite fracDz frac_inv_gt1 /#.
  smt().
 smt(round_bound). 
by rewrite -fromintN floorDz; smt(floorE).
qed.

(* Compression and decompression are used as operations between 
   polynomials over coeff, but we first define the basic operations 
   over coefficients. *)

lemma comp_bound d x:
 0 < d =>
 2^d < q =>
 x * (2 ^ d)%r / q%r - inv 2%r
 < (comp d x)%r <= x * (2 ^ d)%r / q%r + inv 2%r.
proof. smt(round_bound). qed.

lemma comp_asint_bound d x:
 0 < d =>
 2^d < q =>
 (asint x)%r * (2 ^ d)%r - q%r / 2%r < q%r * (comp d (asint x)%r)%r
 && q%r * (comp d (asint x)%r)%r <= (asint x)%r * (2 ^ d)%r + q%r / 2%r.
proof. smt(round_bound). qed.

lemma comp_asint_range d x:
 0 < d =>
 2^d < q =>
 0 <= comp d (asint x)%r <= 2^d.
proof.
move=> *; split.
 rewrite -(from_int_round 0); apply round_mono.
 smt(expr_gt0 rg_asint divr_ge0).
move=> _.
have /#: (comp d (asint x)%r)%r < q%r * (2^d)%r / q%r + inv 2%r.
apply (RealOrder.ler_lt_trans ((asint x)%r*(2^d)%r/q%r+ inv 2%r)); first smt(comp_bound).
by rewrite ltr_add2r ltr_pmul2r 1:/# RealOrder.ltr_pmul2r; smt(expr_gt0 rg_asint).
qed.

lemma comp_over d x:
 0 < d =>
 2^d < q =>
 comp d (asint x)%r = 2^d
 <=> q%r - q%r / (2^(d+1))%r <= (asint x)%r.
proof.
move=> Hd0 Hd.
have ->: (comp d (asint x)%r = 2^d) <=> (2^d <= comp d (asint x)%r) by smt(comp_asint_range).
rewrite le_roundE -RealOrder.ler_subl_addr ler_pdivl_mulr 1:/# RField.mulrBl.
rewrite -eqboolP eq_sym eqboolP.
rewrite RealOrder.ler_subl_addl -RealOrder.ler_subl_addr ler_pdivl_mulr.
 smt(expr_gt0).
by rewrite exprD_nneg 1..2:/# /= fromintM /#.
qed.

lemma compress0L d x:
 0 < d =>
 2^d < q =>
 q%r - q%r / (2^(d+1))%r <= (asint x)%r =>
 compress d x = 0.
proof.
move=> Hd0 Hd Hx; rewrite /compress.
have ->: comp d (asint x)%r = 2^d.
 by rewrite comp_over // modzz.
by rewrite modzz.
qed.

lemma compress_small d x:
 0 < d =>
 2^d < q =>
 (asint x)%r < q%r - q%r / (2^(d+1))%r =>
 compress d x = comp d (asint x)%r.
proof.
move=> Hd0 Hd Hx.
rewrite /compress.
rewrite modz_small 2:/# ger0_norm.
 smt(expr_ge0).
have ?: comp d (asint x)%r <> 2^d by rewrite comp_over // /#. 
smt(comp_asint_range).
qed.

lemma compress1_is0 x:
 compress 1 x = 0 <=> absZq x <= Bq 1.
proof.
have L: forall y m, 0 <= y <= m => y %% m = 0 <=> y=0 \/ y=m.
 move=> y m H; case: (y=m) => E.
  by rewrite E modzz /#.
 by rewrite modz_small /#.
rewrite Bq1E /compress L.
 by apply comp_asint_range => //= /#.
by rewrite absZqP /= -fromintM round_divz 1:/# /=; smt(rg_asint).
qed.

lemma decompress0 d:
 decompress d 0 = Zq.zero
by rewrite /decompress /= from_int_round.

lemma decomp_bound d x:
 0 < d =>
 2^d < q =>
 0 <= x < 2^d =>
 0 <= decomp d x%r < q.
proof. 
move=> Hd0 Hd Hx; split; 1: by smt(round_bound). 
have H := (round_bound (x%r * q%r / (2 ^ d)%r)).  
move => H0.
have ? : x%r * q%r / (2 ^ d)%r + inv 2%r < q%r; last by smt().
rewrite RField.mulrC RField.mulrA. 
have : x%r * q%r + (2 ^ d)%r * inv 2%r < (2 ^ d)%r * q%r by smt().
have -> : x%r * q%r + (2 ^ d)%r / 2%r =
          (2 ^ d)%r  * (inv (2 ^ d)%r * x%r * q%r + inv 2%r).
   by rewrite RField.mulrDr RField.mulrA RField.mulrA RField.divrr;  smt(expr_gt0). 
apply RealOrder.ltr_pmul2l.
  smt(expr_gt0).
qed.

lemma decomp_mono d (x y: real):
 0 < d =>
 2^d < q =>
 x <= y =>
 decomp d x <= decomp d y. 
proof.
move=> ???; rewrite /decomp.
apply round_mono.
rewrite -!mulrA ler_pmul2r // mulrC.
smt(RealOrder.divr_gt0 expr_gt0).
qed.

(* These operations introduce a rounding error, which we see additively *)
op compress_err(d : int, c: coeff) : coeff = decompress d (compress d c) - c.

lemma decompress_errE c d : 
   0 < d => 2^d < q => decompress d (compress d c) = c + (compress_err d c)
by rewrite /compress_err => *; ring.

lemma decomp_comp d x:
 0 < d =>
 2^d < q =>
 x - Bq d <= decomp d (comp d x%r)%r <= x + Bq d.
proof.
move=> Hd0 Hd.
have [Hl Hr]:= comp_bound d x%r Hd0 Hd.
have Hl': x%r * (2 ^ d)%r / q%r - inv 2%r <= (comp d x%r)%r by smt().
split.
 move: (decomp_mono d _ _ Hd0 Hd Hl').
 have ->: decomp d (x%r * (2 ^ d)%r / q%r - inv 2%r) = x - Bq d.
  rewrite /decomp.
  have ->: ((x%r * (2 ^ d)%r / q%r - inv 2%r) * q%r / (2 ^ d)%r) = x%r - q%r / (2 ^ (d+1))%r.
   by field; smt(IntOrder.expr_gt0 IntID.exprS).
  rewrite roundDz roundN.
   by apply Bq_noties. 
  smt().
 smt().
move=> _.
move: (decomp_mono d _ _ Hd0 Hd Hr).
have ->: decomp d (x%r * (2 ^ d)%r / q%r + inv 2%r) = x + Bq d.
 rewrite /decomp.
 have ->: ((x%r * (2 ^ d)%r / q%r + inv 2%r) * q%r / (2 ^ d)%r) = x%r + q%r / (2 ^ (d+1))%r. 
  by field; smt(IntOrder.expr_gt0 IntID.exprS).
 by rewrite roundDz /#.
smt().
qed.

lemma bound_abs: forall (i j : int), 0 <= i < j => 0 <= i < `|j|by smt().

lemma round_ge0 x: 0%r <= x => 0 <= round x
by smt(floor_bound).

(* This lemma is stated in the Spec *)
lemma compress_decompress d x:
 0 < d =>
 2^d < q =>
 absZq (x - decompress d (compress d x)) <= Bq d.
proof.
move=> Hd0 Hd.
case: ((asint x)%r < q%r - q%r / (2^(d+1))%r).
 move=> Hx; rewrite compress_small //.
 apply absZqB; apply normP.
 have XX: forall (b x y: int), y-b <= x <= y+b => -b <= y-x <= b by smt().
 apply XX. clear XX.
 rewrite incoeffK modz_small; last first.
  by apply decomp_comp.
 apply bound_abs.
 apply decomp_bound => //.
 have [_ Hc]:= (comp_bound d (asint x)%r _ _) => //.
 split.
  by apply round_ge0; smt(expr_gt0 rg_asint).
 move => _.
 have /#: (comp d (asint x)%r)%r < (2^d)%r.
 apply (RealOrder.ltr_le_trans ((q%r-q%r / (2 ^ (d + 1))%r) * (2 ^ d)%r / q%r + inv 2%r)) => //.
  apply (RealOrder.ler_lt_trans ((asint x)%r * (2 ^ d)%r / q%r + inv 2%r)) => //.
  apply RealOrder.ltr_add2r.
  rewrite -!mulrA; apply RealOrder.ltr_pmul2r.
   smt(expr_gt0).
  smt().
 rewrite exprS 1:/# fromintM. 
 have ->: (q%r - q%r / (2%r * (2 ^ d)%r)) * (2 ^ d)%r / q%r = (2^d)%r - inv 2%r by field; smt(expr_gt0).
 smt().
move=> Hx.
rewrite compress0L // 1:/# /absZq decompress0 /= ZqField.oppr0 ZqField.addr0.
have ?:= Bq_le_half d.
rewrite /as_sint.
have ?: q%r - q%r / (2 ^ (d + 1))%r <= (asint x)%r by smt().
have ->/=: (q - 1) %/ 2 < asint x.
 rewrite -lerNgt in Hx.
 rewrite divz_floor //.
 have ?: (floor ((q - 1)%r / 2%r))%r < (asint x)%r; last by smt().
 apply (RealOrder.ler_lt_trans ((q - 1)%r / 2%r)).
  by apply floor_le.
 smt().
rewrite ltr0_norm.
 smt(rg_asint).
rewrite IntID.opprB. 
smt(round_bound).
qed.

(* As a corollary we get a bound on the additive error term *)
lemma compress_err_bound (c:coeff) d : 
   0 < d => 2^d < q =>
     `| as_sint (compress_err d c) | <= round (q%r / (2^(d+1))%r).
proof.
move => *.
have ->: compress_err d c 
         = -(c - decompress d (compress d c))%Zq.
 by rewrite decompress_errE //; ring.
rewrite as_sintN normrN.
by apply compress_decompress.
qed.


end GFq.

export GFq Zq.

(******************************************************)
(* Representations of polynomials in Zq[X]/(X^256+1)  *)
(* We use an array representation for both Rq and ntt *)
(* domain.                                            *)
(******************************************************)

theory Rq.

type poly = coeff Array256.t.

op zero : poly = Array256.create Zq.zero.
op one : poly = zero.[0<-Zq.one].

(* Ring multiplication: schoolbook multiplication in this
ring is essentially generating a square matrix of coefficient
multiplications and summing over the columns. *)
op (&*) (pa pb : poly) : poly =
  Array256.init (fun (i : int) => foldr (fun (k : int) (ci : coeff) =>
  if (0 <= i - k) 
  then ci + pa.[k] * pb.[i - k] 
  else ci - pa.[k] * pb.[256 + (i - k)]) 
  Zq.zero (iota_ 0 256)).

op (&+) (pa pb : poly) : poly = 
  map2 (fun a b : coeff  => Zq.(+) a b) pa pb.

op (&-) (p : poly) : poly =  map Zq.([-]) p.

op unit(p : poly) = exists q, q &* p = Rq.one.
op invr(p : poly) = choiceb (fun q => q &* p = Rq.one) p.

(* Compression/decompression of polys *)

op compress_poly(d : int, p : poly) : int Array256.t =  map (compress d) p.

op decompress_poly(d : int, p : int Array256.t) : poly =  map (decompress d) p.

clone import PolyReduce as RqTheory with
   op n <- 256,
   type BasePoly.coeff <- coeff,
   op BasePoly.Coeff.(+) <- Zq.(+),
   op BasePoly.Coeff.( *) <- Zq.( *),
   op BasePoly.Coeff.zeror <- Zq.zero,
   op BasePoly.Coeff.oner <- Zq.one,
   op BasePoly.Coeff.([-]) <- Zq.([-]),
   op BasePoly.Coeff.invr <- Zq.inv,
   pred BasePoly.Coeff.unit <- Zq.unit
   rename "polyXnD1" as "AlgR"
   rename "poly" as "basepoly"
   proof BasePoly.Coeff.addrA by apply ZqRing.addrA
   proof BasePoly.Coeff.addrC by apply ZqRing.addrC
   proof BasePoly.Coeff.add0r by apply ZqRing.add0r 
   proof BasePoly.Coeff.addNr by apply ZqRing.addNr 
   proof BasePoly.Coeff.oner_neq0 by apply ZqRing.oner_neq0
   proof BasePoly.Coeff.mulrA by apply ZqRing.mulrA
   proof BasePoly.Coeff.mulrC by apply ZqRing.mulrC 
   proof BasePoly.Coeff.mul1r by apply ZqRing.mul1r 
   proof BasePoly.Coeff.mulrDl by apply ZqRing.mulrDl 
   proof BasePoly.Coeff.mulVr by apply ZqRing.mulVr
   proof BasePoly.Coeff.unitP by apply ZqRing.unitP 
   proof BasePoly.Coeff.unitout by apply ZqRing.unitout
   proof gt0_n by auto
   proof *.


op poly2polyr(p : poly) : AlgR = pi (oget (BasePoly.to_basepoly 
                              (fun i => if 0<=i<256 then p.[i] else Zq.zero))).
op polyr2poly(p : AlgR) : poly = Array256.init (fun i => p.[i]).

lemma poly2polyrP i p :  0<=i<256 => (poly2polyr p).[i] = p.[i].
move => ib.
have H := (BasePoly.to_basepolyT (fun (i0 : int) => if 0 <= i0 && i0 < 256 then p.[i0] else Zq.zero) _); 1: by smt().
rewrite /poly2polyr /"_.[_]".
rewrite piK. 
+ rewrite reducedP /=; 1: by smt(BasePoly.deg_leP).
by smt().
qed.

lemma polyr2polyP i p :  0<=i<256 => (polyr2poly p).[i] = p.[i].
move => ib;rewrite /polyr2poly /"_.[_]" initiE //=.
qed.


lemma polyr2polyK : cancel poly2polyr polyr2poly.
rewrite /cancel => x; apply Array256.tP => i ib.
by rewrite polyr2polyP // poly2polyrP //=.
qed.

lemma poly2polyrK : cancel polyr2poly poly2polyr.
rewrite /cancel => x;  apply AlgR_eqP => i ib.
by rewrite poly2polyrP // polyr2polyP //=.
qed.

lemma add_lift a b : a &+ b = polyr2poly (poly2polyr a + poly2polyr b). 
apply Array256.tP => i ib.
rewrite polyr2polyP // rcoeffD !poly2polyrP //.
by rewrite /(&+) /= map2E /= initiE //=.
qed.

lemma sub_lift a : (&-) a = polyr2poly (- poly2polyr a). 
apply Array256.tP => i ib.
rewrite polyr2polyP // -rcoeffN !poly2polyrP //.
by rewrite /(&-) /= mapE /= initiE //=.
qed.

lemma mul_lift a b : a &* b = polyr2poly (poly2polyr a * poly2polyr b). 
apply Array256.tP => i ib.
rewrite polyr2polyP // rcoeffM //. 
rewrite /(&*) /= /BasePoly.BigCf.BCA.big filter_predT /range /= initiE  //= foldr_map /=.
have : forall x, x \in (iota_ 0 256) => 0 <= x < 256 by smt(mem_iota).
elim (iota_ 0 256).
+ by auto.
move => x l H H1 /=.
case (0 <= i - x).
 + move => * /=.
   rewrite (H _) /=; 1: by smt(). 
   ring.
   have -> : (poly2polyr b).[256 + i - x] = Zq.zero by smt(lt0_rcoeff gered_rcoeff).
   rewrite poly2polyrP; 1: by smt(mem_head). 
   rewrite poly2polyrP; 1: by smt().
   by ring.
move => * /=.
rewrite (H _) /=; 1: by smt(). 
ring.
rewrite poly2polyrP; 1: smt().
rewrite poly2polyrP; 1: by smt(mem_head). 
   have -> : (poly2polyr b).[i - x] = Zq.zero by smt(lt0_rcoeff gered_rcoeff).
   have -> : 256 + (i - x) = 256 + i - x by smt().
   by ring.
qed.

lemma zero_lift : Rq.zero = polyr2poly zeroXnD1. 
apply Array256.tP => i ib.
by rewrite polyr2polyP // /Rq.zero /create initiE //= rcoeff0.
qed.

lemma one_lift : Rq.one = polyr2poly oneXnD1. 
apply Array256.tP => i ib.
rewrite polyr2polyP // /Rq.one /Rq.zero /create.
case (i = 0).
move => *;rewrite set_eqiE //;1: 
  by smt(BasePoly.lc1 creprK piK reduced1 BasePoly.deg1).
by move => *; rewrite set_neqiE // initiE //=;
 smt(BasePoly.gedeg_coeff creprK piK reduced1 BasePoly.deg1).
qed.

lemma polyr2poly_inj : injective polyr2poly.
by apply (can_inj _ poly2polyr); apply poly2polyrK.
qed.

lemma poly2polyr_inj : injective poly2polyr.
by apply (can_inj _ polyr2poly); apply polyr2polyK.
qed.

op compress_poly_err(d : int, p : poly) : poly =  map (compress_err d) p.

lemma round_poly_errE p d : p &+ (compress_poly_err d p) = decompress_poly d (compress_poly d p).
proof. 
rewrite /compress_poly_err /decompress_poly /(&+); apply Array256.ext_eq => /> x xl xh.
rewrite map2iE //= mapiE //= !mapiE // /compress_err. by ring.
qed.

end Rq.

export Rq RqTheory.

theory VecMat.

op kvec : int. 
axiom gt0_kvec : 0 < kvec.

(* 
theory PolyVec.
type polyvec.
op "_.[_]" (v : polyvec) (i : int) : poly.
op "_.[_<-_]" (v : polyvec) (i : int) (c : poly) : polyvec.
op mapv(f : poly -> poly, v : polyvec) : polyvec.
op zerov : polyvec.
op (+) : polyvec -> polyvec -> polyvec.
end PolyVec.

theory PolyMat.
type polymat.
op "_.[_]" (m : polymat) (ij : int * int) : poly.
op "_.[_<-_]" (m : polymat) (ij : int * int) (c : poly) : polymat.
op mapm(f : poly -> poly, m : polymat) : polymat.
op zerom : polymat. 
end PolyMat.
*)
type polyvec.
type polymat.
clone import Matrix as MLKEM_Matrix with
    op size = kvec,
    type ZR.t = poly,
    op ZR.zeror = Rq.zero,
    op ZR.oner = Rq.one,
    pred ZR.unit = Rq.unit,
    op ZR.(+) = Rq.(&+),
    op ZR.([-]) = Rq.(&-),
    op ZR.( * ) = Rq.(&*),
    op ZR.invr = Rq.invr,
    type vector = polyvec,
    type Matrix.matrix = polymat
    proof ZR.addrA by smt(add_lift  poly2polyrK addrA)
    proof ZR.addrC by smt(add_lift  poly2polyrK addrC)
    proof ZR.add0r by smt(zero_lift add_lift poly2polyrK add0r polyr2polyK)
    proof ZR.addNr by smt(zero_lift sub_lift add_lift poly2polyrK addNr polyr2polyK)
    proof ZR.oner_neq0 by smt(zero_lift  poly2polyrK one_lift oner_neq0)
    proof ZR.mulrA by smt(mul_lift  poly2polyrK mulrA)
    proof ZR.mulrC by smt(mul_lift  poly2polyrK mulrC)
    proof ZR.mul1r by smt(one_lift mul_lift poly2polyrK mul1r polyr2polyK)
    proof ZR.mulrDl by smt(add_lift mul_lift poly2polyrK mulrDl polyr2polyK)
    proof ZR.mulVr by smt(choicebP)
    proof ZR.unitP by  smt()
    proof ZR.unitout by smt(choiceb_dfl)
    proof ge0_size by smt(gt0_kvec).

(* 
op "_.[_<-_]" = fun v i c => offunv (fun i' => if i = i' then c else (tofunv v) i').
op "_.[_<-_]" = fun m ij c =>  offunm (fun i j => if (i,j) = ij then c else (tofunm m) i j).
*)
op mapv = fun f v => offunv (fun i => f (tofunv v i)).
op mapm = fun f m => offunm (fun i j => f (tofunm m i j)).

(* Fixme PY: is this nowhere? *)
instance ring with R
  op rzero = Rq.zero
  op rone  = Rq.one
  op add   = Rq.(&+)
  op opp   = Rq.(&-)
  op mul   = Rq.(&*)
  op expr  = ZR.exp
  op ofint = ZR.ofint

  proof oner_neq0 by apply ZR.oner_neq0
  proof addrA     by apply ZR.addrA
  proof addrC     by apply ZR.addrC
  proof addr0     by apply ZR.addr0
  proof addrN     by apply ZR.addrN
  proof mulr1     by apply ZR.mulr1
  proof mulrA     by apply ZR.mulrA
  proof mulrC     by apply ZR.mulrC
  proof mulrDl    by apply ZR.mulrDl
  proof expr0     by apply ZR.expr0
  proof ofint0    by apply ZR.ofint0
  proof ofint1    by apply ZR.ofint1
  proof exprS     by apply ZR.exprS
  proof ofintS    by apply ZR.ofintS
  proof ofintN    by apply ZR.ofintN.

import Vector.

lemma simp_ZRplus : ZR.(+) = (&+) by auto.
lemma simp_ZRminus : ZR.([-]) = (&-) by auto.
lemma simp_ZRtimes : ZR.( * ) = (&*) by auto.
lemma simp_ZRzero : ZR.zeror = zero by auto.


end VecMat.

export VecMat MLKEM_Matrix.

hint simplify (simp_ZRplus, simp_ZRminus, simp_ZRtimes, simp_ZRzero).


theory Sampling.
(* The binomial distribution over a field element *)

op eta_ : int = 2.

op dshort_elem : coeff distr = dmap (dcbd eta_) incoeff.

lemma dshort_elem_ll: is_lossless dshort_elem.
proof.
by apply dmap_ll; apply ll_dcbd;smt().
qed.

(* Definition of the support *)
lemma supp_dshort_elem x:
 x \in dshort_elem <=> -eta_ <= as_sint x <= eta_.
proof.
rewrite supp_dmap; split.
 move=> [y []]; rewrite supp_dcbd.
 move=> H ->; rewrite incoeffK_sint_small /=; smt(). 
move=> H; exists (as_sint x); rewrite supp_dcbd.
split => //.
by rewrite as_sintK.
qed.


lemma dshort_elem1E_m2 : mu1 dshort_elem (incoeff (-2)) = 1%r / 16%r.
proof.
rewrite /dshort_elem (in_dmap1E_can (dcbd 2) _ as_sint).
  by rewrite as_sintK.
 move=> y; rewrite supp_dcbd; move=> ? <-.
 by rewrite incoeffK_sint_small /#.
rewrite incoeffK_sint_small /q //=.
by rewrite dcbd1E mcbd_2_2N.
qed.

lemma dshort_elem1E_1 : mu1 dshort_elem (incoeff 1) = 1%r / 4%r.
proof.
rewrite /dshort_elem  (in_dmap1E_can (dcbd 2) _ as_sint).
  by rewrite as_sintK.
 move=> y; rewrite supp_dcbd; move=> ? <-.
 by rewrite incoeffK_sint_small /#.
rewrite incoeffK_sint_small /q //=.
by rewrite dcbd1E mcbd_2_1.
qed.

lemma dshort_elem1E_m1 : mu1 dshort_elem (incoeff (-1)) = 1%r / 4%r.
proof.
rewrite /dshort_elem (in_dmap1E_can (dcbd 2) _ as_sint).
  by rewrite as_sintK.
 move=> y; rewrite supp_dcbd; move=> ? <-.
 by rewrite incoeffK_sint_small /#.
rewrite incoeffK_sint_small /q //=.
by rewrite dcbd1E mcbd_2_1N.
qed.

lemma dshort_elem1E_0 : mu1 dshort_elem (incoeff 0) = 3%r / 8%r. 
proof.
rewrite /dshort_elem (in_dmap1E_can (dcbd 2) _ as_sint).
  by rewrite as_sintK.
 move=> y; rewrite supp_dcbd; move=> ? <-.
 by rewrite incoeffK_sint_small /#.
rewrite incoeffK_sint_small /q //=.
by rewrite dcbd1E mcbd_2_0.
qed.


(* The uniform distribution over a field element *)
op duni_elem : coeff distr = DZmodP.dunifin.

lemma duni_elem_ll: is_lossless duni_elem
 by exact DZmodP.dunifin_ll.

(* Definition of the support *)
lemma supp_duni_elem x:
 0 <= asint x < q <=> x \in duni_elem.
proof.
rewrite /duni_elem DZmodP.dcoeffE supp_dmap; split.
 move=> H; exists (asint x); split.
  rewrite supp_dinter; smt(rg_asint).
 by rewrite asintK.
move=> [a []]; rewrite supp_dinter => ? ->.
by rewrite incoeffK /#.
qed.

(* The probability of each value in the support. *)
op pe = 1%r /q%r.
lemma duni_elem1E x: mu1 duni_elem x = pe.
proof.
rewrite duniform1E_uniq.
 exact DZmodP.Support.enum_uniq.
by rewrite DZmodP.Support.enumP size_map size_range /#.
qed.

lemma duni_elemE: duni_elem = dmap [0..q-1] incoeff.
proof.
apply eq_distr => x.
rewrite duni_elem1E dmap1E /(\o) /=.
rewrite (mu_eq_support _ _ (pred1 (asint x))).
 move=> y; rewrite supp_dinter /pred1 => /> *.
 rewrite eqboolP; split.
  by move=> <-; rewrite incoeffK modz_small /#.
 by move => ->; rewrite asintK.
by rewrite dinter1E ifT; smt(rg_asint).
qed.

lemma duni_elem_uni : is_uniform duni_elem 
  by rewrite /is_uniform => *; rewrite !duni_elem1E.

lemma duni_elem_fu : is_full duni_elem
  by rewrite /is_full /support => x; rewrite duni_elem1E; smt().

(* The distribution of ring elements of small norm as an operator *)

op darray256 ['a] (d: 'a distr): ('a Array256.t) distr =
 dmap (dlist d 256) (Array256.of_list witness).

lemma darray256_ll ['a] (d: 'a distr):
 is_lossless d => is_lossless (darray256 d).
proof.  by rewrite /darray32 => ?; apply dmap_ll; apply dlist_ll. qed.


lemma supp_darray256 ['a] (d: 'a distr) a:
 a \in darray256 d <=> all (support d) (Array256.to_list a).
proof.
rewrite /darray256 supp_dmap; split.
 move=> [x]; rewrite supp_dlist // => /> *.
 by rewrite Array256.of_listK // /#.
move=> H; exists (to_list a); rewrite supp_dlist // H Array256.size_to_list /=.
by rewrite Array256.to_listK.
qed.

lemma darray256_uni ['a] (d: 'a distr):
 is_uniform d => is_uniform (darray256 d).
proof.
rewrite /darray256=> ?; apply dmap_uni_in_inj.
 move=> x y; rewrite !supp_dlist //; move => [? _] [? _] H.
 by rewrite -(Array256.of_listK witness x) // H of_listK.
by apply dlist_uni.
qed.

lemma darray256_fu ['a] (d: 'a distr):
 is_full d => is_full (darray256 d).
proof.
rewrite /darray256 => H; apply dmap_fu_in.
move=> x; exists (to_list x); rewrite to_listK supp_dlist //=.
rewrite Array256.size_to_list /= allP => *.
by apply H.
qed.



abbrev dR (d: coeff distr): poly distr = darray256 d.

lemma dR_ll d:
 is_lossless d => is_lossless (dR d)
by exact darray256_ll.

lemma supp_dR d p:
 p \in dR d <=> all (support d) (Array256.to_list p)
by exact supp_darray256.

lemma dR_fu d:
 is_full d => is_full (dR d)
by exact darray256_fu.

lemma dR_uni d:
 is_uniform d => is_uniform (dR d)
by exact darray256_uni.



op dshort_R : poly distr = dR dshort_elem.

lemma dshort_R_ll : is_lossless dshort_R
by smt(dR_ll dshort_elem_ll).

(* The uniform distribution of ring elements as an operator *)

op duni_R : poly distr =  dR duni_elem.

lemma duni_R_ll : is_lossless duni_R
by smt(dR_ll duni_elem_ll).

lemma duni_R_uni : is_uniform duni_R
by smt(dR_uni duni_elem_uni).

lemma duni_R_fu : is_full duni_R
by smt(dR_fu duni_elem_fu).


end Sampling.

export Sampling.

theory InnerPKE.

theory W8.
  clone include Word with op n = 8 proof ge0_n by auto.
  type t = Alphabet.t.
  op w2bits : t -> bool list.
end W8.
type pkey = W8.t Array1152.t * W8.t Array32.t.
type skey = W8.t Array1152.t.
type plaintext = W8.t Array32.t.
type ciphertext = W8.t Array960.t * W8.t Array128.t.

end InnerPKE.

export InnerPKE.

(* We now instantiate our proofs for MLKEM. *)

op vbits : int.
op ubits : int.
op rnd_err_v = compress_poly_err vbits. 
op rnd_err_u = mapv (compress_poly_err ubits). 

op max_noise = q %/ 4 - 1.
op under_noise_bound (p : poly) (b : int) =
     all (fun cc => `| as_sint cc| <= b) p.

op cv_bound_max : int. 

type ipoly = int Array256.t.
op toipoly(p : poly) : ipoly = map asint p.
op ofipoly(p : ipoly)  : poly = map incoeff p.

require import BitEncoding.
import BitChunking BS2Int.

op BytesToBits(bytes : W8.t list) : bool list = flatten (map W8.w2bits bytes).
op decode(l : int, bits : bool list) = map bs2int (chunk l (take (256*l) bits)).

op encode1 : ipoly -> W8.t Array32.t.
op decode1 : W8.t Array32.t -> ipoly.
axiom sem_decode1K  : cancel decode1  encode1.
axiom sem_encode1K (x : ipoly) : 
   (forall i, 0 <= i < 256 => 0 <= x.[i] < 2) =>
     x = (decode1 (encode1 x)).
axiom decode1_bnd a k : 0<=k<256 => 0<= (decode1 a).[k] < 2.


op m_encode(m : plaintext) : poly = decompress_poly 1 (decode1 m).
op m_decode(p : poly) : plaintext = encode1 (compress_poly 1 p). 

lemma add_polyE (pa pb : poly) : (&+) pa pb = map2 (fun (a b : coeff) => a + b) pa pb by auto.

require import MLWE_PKE.
clone import MLWE_PKE as MLWEPKE with
  theory MLWE_.Matrix_ <= MLKEM_Matrix,
  type plaintext <- plaintext,
  type ciphertext <- W8.t Array960.t * W8.t Array128.t,
  type pkey <- pkey,
  type skey <- W8.t Array1152.t,
  op MLWE_.duni_R <- duni_R,
  op MLWE_.dshort_R <- dshort_R,
  op m_encode <- m_encode,
  op m_decode <- m_decode,
  op under_noise_bound <- under_noise_bound,
  op max_noise <- max_noise,
  op cv_bound_max <- cv_bound_max,
  op rnd_err_u <- rnd_err_u,
  op rnd_err_v <- rnd_err_v
  proof MLWE_.dshort_R_ll  by apply dshort_R_ll
  proof MLWE_.duni_R_ll by apply duni_R_ll
  proof MLWE_.duni_R_fu by apply duni_R_fu
  proof good_decode
  proof noise_commutes
  proof noise_preserved.
  (* We inherit the following axioms 
  proof *.
  MLWE_.duni_R_uni: is_uniform duni_R
 MLWE_.dseed_ll: is_lossless dseed
 pk_encodeK: cancel pk_encode pk_decode
 sk_encodeK: cancel sk_encode sk_decode
 PKE_ROM.dplaintext_ll: is_lossless dplaintext
 encode_noise: forall (u : vector) (v : R), c_decode (c_encode (u, v)) = (u + rnd_err_u u, v &+ rnd_err_v v) 
  cv_bound_valid: forall (_A : matrix) (s e r : vector) (e2 : R) (m : plaintext),
                   s \in MLWE_.dshort =>
                   e \in MLWE_.dshort =>
                   _A \in MLWE_.duni_matrix =>
                   r \in MLWE_.dshort =>
                   e2 \in dshort_R =>
                   let t = _A *^ s + e in
                   let v = (t `<*>` r) &+ e2 &+ m_encode m in under_noise_bound (rnd_err_v v) cv_bound_max
*)


realize good_decode.
rewrite /under_noise_bound /m_encode /m_decode /compress_poly 
        /decompress_poly /max_noise /= => m n.
rewrite allP  => /=  hgood.
have : decode1 (encode1 (map (compress 1) (map (decompress 1) (decode1 m) &+ n))) = 
       (decode1 m); last by smt(sem_decode1K).
apply Array256.ext_eq => /> x h0x hx256. 
rewrite -sem_encode1K. 
+ move => i ib; rewrite !mapiE /= 1:ib /compress /= /#.
rewrite /(&+) mapiE 1:/# map2E /= initiE /= 1:/# mapiE 1:/#.
have [->|->] /=: (decode1 m).[x]=0 \/ (decode1 m).[x]=1
 by smt(decode1_bnd).
 rewrite /decompress /=.
 rewrite from_int_round.
 rewrite -{1}zeroE asintK Zq.ZModule.add0r compress1_is0 // Bq1E.
 smt().
rewrite /decompress /round /=.
have ->: 1665%r = (q%r+1%r)/2%r.
 by field; smt().
rewrite -fromintD -divz_floor //=.
have: compress 1 (incoeff 1665 + n.[x]) <> 0.
 rewrite compress1_is0 Bq1E.
 move: (hgood x _) => //. 
 rewrite (_:832=831+1) 1://. 
 move=> /absZqP [H|].
 rewrite absZqP negb_or; split.
  smt(incoeffK).
 rewrite /=. 
  smt(incoeffK).
 rewrite /=.
 smt(incoeffK).
by rewrite /compress /=; smt(ltz_pmod modz_ge0).
qed.

realize noise_commutes.
move => n n' maxn b H H0.
move : H H0; rewrite /under_noise_bound.
rewrite !allP.
move => Hn Hnp i ib.
move : (Hn i ib). 
move : (Hnp i ib) => /=. 
rewrite /as_sint /MLKEM_Matrix.ZR.(+) /(&+) map2E  !initiE //= Zq.addE /= !StdOrder.IntOrder.ler_norml /= => Hni Hnpi.
by smt().
qed.

realize noise_preserved.
move => n maxn. 
rewrite /under_noise_bound.
rewrite !allP. 
rewrite eq_iff; split => /=. 
move => H i ib; move : (H i ib).
rewrite /(&-) mapiE 1:/#.
rewrite as_sintN /= /#. 
move => H i ib; move : (H i ib).
rewrite /(&-) mapiE 1:/#.
rewrite as_sintN /= /#. 
qed.

(*******************************************************************)
(* We now set the ground for computing the probabilities           *)
(*******************************************************************)


require import Distrmatrix.  
clone import Distrmatrix as MyDM with  
   theory DM.ZR <- Zq.ZqRing.

(* Some lemmas to bound the probability *)
pred is_good(d : coeff distr) = 
  is_lossless d /\ mu1 d zero < 1%r
  (* symmetric *)
  /\ all (fun c => mu1 d c = mu1 d (-c)) (DZmodP.Support.enum).

lemma is_good_dshort_elem : is_good dshort_elem.
proof.
  rewrite /dshort_elem.
  rewrite /is_good; do split.
  + by apply dmap_ll; apply DistrExtra.ll_dcbd => //;smt().
  + rewrite dmap1E  /(\o) /pred1 /= /DistrExtra.dcbd dmapE /(\o) /=.  
    rewrite (mu_eq_support _ _ (pred1 2)).
    + move => i Hin. 
      have supp_dbin /= := (supp_dbin (inv 2%r) 4 i _ _); 1,2: smt().
      rewrite /pred1 /=.
      by apply eq_iff; split; rewrite -eq_incoeff /#.
    rewrite dbin1E /=;1:smt().  
    by rewrite  DistrExtra.bin_4_2 /=; smt(@Real).
  + rewrite List.allP => cc _ /=.
    rewrite !dmap1E /(\o) /pred1 /=.
    rewrite /DistrExtra.dcbd !dmapE /(\o) /=.  
    rewrite {1}(mu_eq_support _ _ (pred1 ((asint cc+2) %% 3329))).
    + move => i Hin. 
      have supp_dbin /= := (supp_dbin (inv 2%r) 4 i _ _); 1,2: smt().
      rewrite /pred1 /=.
      apply eq_iff.
      have := (eq_incoeff ( (i - 2)) (asint cc)). 
      rewrite asintK => <-;split;  smt(). 
    rewrite (mu_eq_support (dbin (inv 2%r) 4) (fun (x : int) => Zq.incoeff (x - 2) = -cc) (pred1 (((3329-asint cc)+2) %% 3329))).
    + move => i Hin. 
      have supp_dbin /= := (supp_dbin (inv 2%r) 4 i _ Hin); 1: smt().
      rewrite /pred1 /=.
      apply eq_iff.
      have := (eq_incoeff ( (i - 2)) ((3329 - asint cc) %% 3329)). 
      by rewrite /= => *; split => /#.
    have Hin1 := supp_dbin (inv 2%r) 4 ((asint cc + 2) %% GFq.q) _;1:smt().
    have Hin2 := supp_dbin (inv 2%r) 4 ((GFq.q - asint cc + 2) %% GFq.q) _;1:smt().
    case ((asint cc + 2) %% GFq.q = 0) => H.
    + rewrite !dbin1E 1,2:/#. 
      have ->  /=: asint cc = 3329-2;1: by smt(@Zq). 
      by smt(@DistrExtra).
    case ((asint cc + 2) %% GFq.q = 1) => H1.
    + rewrite !dbin1E 1,2:/#. 
      have ->  /=: asint cc = 3329-1;1: by smt(@Zq). 
      by smt(@DistrExtra).
    case ((asint cc + 2) %% GFq.q = 2) => H2.
    + rewrite !dbin1E 1,2:/#. 
      have ->  /=: asint cc = 0;1: by smt(@Zq). 
      by smt(@DistrExtra).
    case ((asint cc + 2) %% GFq.q = 3) => H3.
    + rewrite !dbin1E 1,2:/#. 
      have ->  /=: asint cc = 1;1: by smt(@Zq). 
      by smt(@DistrExtra).
    case ((asint cc + 2) %% GFq.q = 4) => H4.
    +     rewrite !dbin1E 1,2:/#.
       have ->  /=: asint cc = 2;1: by smt(@Zq). 
       by smt(@DistrExtra).
    smt(@Distr).  
qed.

op dcadd(d1 d2 : coeff distr) = dadd d1 d2.

op dcsub(d1 d2 : coeff distr) = 
  dmap (d1 `*` d2) (fun (cc : _*_) => cc.`1 - cc.`2).

op dcmul(d1 d2 : coeff distr) = 
  dmap (d1 `*` d2) (fun (cc : _*_) => cc.`1 * cc.`2).
     
lemma exists_n0(d : coeff distr) : 
  is_lossless d => (
   mu1 d zero < 1%r <=>
    exists c, c \in d /\ c <> zero).
proof.
move=> lld.
have := mu_disjointL d (predC1 Zq.zero) (pred1 Zq.zero) _ => //=.
rewrite predCU lld => /eq_sym ?; split=> [?|].
- by have := witness_support (predC1 Zq.zero) d; smt().
case=> c [cd nz_c]; suff: 0%r < mu d (predC1 Zq.zero) by smt().
by apply/witness_support; exists c.
qed.

lemma exists_sym(d : coeff distr) (c : coeff) : 
   is_good d => c \in d => -c \in d.
rewrite /is_good; rewrite /support => [# lld non0 sym hin].
rewrite allP in sym.
smt(DZmodP.Support.enumP).
qed.

lemma add_good(d1 d2 : coeff distr) :
  is_good d1 =>
  is_good d2 =>
  is_good (dcadd d1 d2).
rewrite /is_good /dcadd /dadd => [# ll1 z1 sym1] [# ll2 z2 sym2].
have := (exists_n0 _ ll1); rewrite z1 /= => H1; elim H1 => c1 [Hc11 Hc12].
have := (exists_n0 _ ll2); rewrite z2 /= => H2; elim H2 => c2 [Hc21 Hc22].
have Hc2s := exists_sym d2 c2 _ _;1,2: by rewrite /is_good;smt(). 
do split.
+ by apply dmap_ll;apply dprod_ll => /#.
+ have : exists c, c \in dcadd d1 d2 /\ c <> zero; last by smt(exists_n0 dmap_ll dprod_ll). 
  rewrite /dcadd /dadd; case (c1 + c2 <> zero).
  + move => Non0; exists (c1+c2); split; 2: by smt().
    rewrite supp_dmap;exists (c1,c2) => /=; smt(supp_dprod).
    move => Is0. exists (c1-c2); split; 1:
      by rewrite supp_dmap;exists (c1,-c2);smt(supp_dprod).  
    have : c2 + c2 <> zero; last by smt(ZqRing.addr_eq0).
    have : c2 <> -c2; last by smt(ZqRing.addr_eq0).
    smt(@Zq).

rewrite allP => c Hc /=; rewrite !dmap1E /(\o) /pred1 /=.
have -> := mu_eq (d1 `*` d2) (fun (x0 : coeff * coeff) => x0.`1 + x0.`2 = c) (fun (x0 : coeff * coeff) => (c - x0.`1) = x0.`2); 1: by move => x /=; rewrite eq_iff;split;[by move => <-;ring | by move => <-;ring].  
have -> := mu_eq (d1 `*` d2) (fun (x0 : coeff * coeff) => x0.`1 + x0.`2 = -c) (fun (x0 : coeff * coeff) => (- c - (- (-x0.`1))) = x0.`2); 1: by move => x /=; rewrite eq_iff;split;[by move => <-;ring | by move => <-;ring]. rewrite !dprod_partition /=.
have -> : (fun (a : coeff) => mu d2 (fun (b : coeff) => (-c) - - -a = b) * mu1 d1 a) = (fun (a : coeff) => mu d2 (fun (b : coeff) => (-c) - - -a = b) * mu1 d1 (-a)) by apply fun_ext => cc; rewrite allP /= in sym1; smt(DZmodP.Support.enumP).  
have /= HH:= dprod_partition (fun (x0 : coeff * coeff) => (- c - (- (x0.`1))) = x0.`2) d1 d2.
+ have := (RealSeries.sum_reindex (fun (c : coeff) => -c) (fun (a : coeff) => mu d2 ((=) ((-c) - - -a)) * mu1 d1 (-a)) _ _); 1: by  apply inv_bij => /=;apply BasePoly.Coeff.opprK.    
  have -> :  (fun (a : coeff) => mu d2 ((=) ((-c) - - -a)) * mu1 d1 (-a)) =
              (fun (a : coeff) => mu1 d1 (-a) * mu d2 ((=) ((-c) - - -a))) by smt(fun_ext). 
  have  /= := summable_mu1_wght d1 (fun a => mu d2 ((=) ((-c) - - -a))) _;1: smt(mu_bounded).
  have -> :  (fun (x : coeff) => mu1 d1 x * mu d2 ((=) ((-c) - - -x)))  =  (fun (a : coeff) => mu1 d1 (-a) * mu d2 ((=) ((-c) - - -a))); last by smt().
  by apply fun_ext => cc; rewrite allP /= in sym1; smt(DZmodP.Support.enumP).
  move => <-;rewrite /(\o) /=.
  congr => /=;apply fun_ext => cc;congr; last  by smt(BasePoly.Coeff.opprK).
  have -> :  ((=) ((-c) - - - -cc)) =  ((=) (- (c -cc))) by  congr; ring.
  move : sym2; rewrite allP /=.
  move=> h; rewrite -[(=) (c - cc)]pred1E -[(=) (- (c - cc))]pred1E.
  by rewrite h ?DZmodP.Support.enumP.
qed.

lemma mul_good(d1 d2 : coeff distr) :
  is_good d1 =>
  is_good d2 =>
  is_good (dcmul d1 d2).
rewrite /is_good /dcmull => [# ll1 z1 sym1] [# ll2 z2 sym2].
have := (exists_n0 _ ll1); rewrite z1 /= => H1; elim H1 => c1 [Hc11 Hc12].
have := (exists_n0 _ ll2); rewrite z2 /= => H2; elim H2 => c2 [Hc21 Hc22].
have Hc2s := exists_sym d2 c2 _ _;1,2: by rewrite /is_good;smt(). 
do split.
+ by apply dmap_ll;apply dprod_ll => /#.
+ have : exists c, c \in dcmul d1 d2 /\ c <> zero; last by smt(exists_n0 dmap_ll dprod_ll). 
  rewrite /dcmul; exists (c1*c2); split; 1:
  by rewrite supp_dmap;exists (c1,c2);smt(supp_dprod).
  smt(ZqField.unitrMr).

rewrite allP => c Hc /=; rewrite !dmap1E /(\o) /pred1 /=.
rewrite (mu_split _ _ (fun (x : coeff * coeff)  => x.`1 = zero \/ x.`2 = zero)).
rewrite (mu_split (d1 `*` d2) (fun (x : coeff * coeff) => x.`1 * x.`2 = -c) (fun (x : coeff * coeff)  => x.`1 = zero \/ x.`2 = zero)).
congr.  
+ congr; rewrite /predI /= fun_ext => x. 
  rewrite eq_iff; split;case (!(x.`1 = Zq.zero \/ x.`2 = Zq.zero));1,3: by smt().
  + by move => /= H;elim H => -> /= <-;ring. 
  + by move => /= H;elim H => -> /=;rewrite -ZqRing.eqr_oppLR => <-;ring.
rewrite /predI /predC /=.
have -> := mu_eq (d1 `*` d2) (fun (x0 : coeff * coeff) => x0.`1 * x0.`2 = c /\ ! (x0.`1 = Zq.zero \/ x0.`2 = Zq.zero)) (fun (x0 : coeff * coeff) => (c / x0.`1) = x0.`2 /\ ! (x0.`1 = Zq.zero \/ x0.`2 = Zq.zero)).
  move => x /=; rewrite eq_iff; case ((x.`1 = Zq.zero \/ x.`2 = Zq.zero)) => /=; 1: by smt().
   move => *;split.
   + by move => ?;rewrite -(ZqField.divr1 x.`2) ZqField.eqf_div 1:/#;smt(ZqRing.oner_neq0 ComRing.mul1r).
   by rewrite -{1}(ZqField.divr1 x.`2) ZqField.eqf_div 1:/#;smt(ZqRing.oner_neq0 ComRing.mul1r).
have -> := mu_eq (d1 `*` d2) (fun (x0 : coeff * coeff) => x0.`1 * x0.`2 = -c /\ ! (x0.`1 = Zq.zero \/ x0.`2 = Zq.zero)) (fun (x0 : coeff * coeff) => (- (c / x0.`1)) = x0.`2 /\ ! (x0.`1 = Zq.zero \/ x0.`2 = Zq.zero)).
 move => x /=; rewrite eq_iff; case ((x.`1 = Zq.zero \/ x.`2 = Zq.zero)) => /=; 1: by smt().
   move => *;split.
   + by move => ?;rewrite -ZqField.mulNr -(ZqField.divr1 x.`2) ZqField.eqf_div 1:/#;smt(ZqRing.oner_neq0 ComRing.mul1r).
   by rewrite -ZqField.mulNr -{1}(ZqField.divr1 x.`2) ZqField.eqf_div 1:/#;smt(ZqRing.oner_neq0 ComRing.mul1r).

 rewrite !dprod_partition /=;congr => /=; rewrite fun_ext => cc;congr.
 case (cc = zero); 1: by smt(mu0).
 move => ? /=.
 case (c = zero) => ?;1: by congr;rewrite fun_ext => *;smt(@Zq). 
 rewrite allP /= in sym2.
 move : (sym2 (c / cc) _);1:   smt(DZmodP.Support.enumP). 
 have <- : mu1 d2 (c / cc) = mu d2 (fun (b : coeff) => c / cc = b /\ b <> Zq.zero);1: by
   congr;rewrite fun_ext;smt(@Zq).
 have <- : mu1 d2 (-c / cc) = mu d2 (fun (b : coeff) =>- c / cc = b /\ b <> Zq.zero);1: by
   congr;rewrite fun_ext;smt(@Zq).
  by smt().
qed.

lemma add_sub(d1 d2 : coeff distr) : 
   is_good d2 => dcadd d1 d2 = dcsub d1 d2.
move => H2.
rewrite /dcadd /dcsub.
apply eq_distr => x.
rewrite !dmap1E /(\o) /pred1 /=.
have -> := mu_eq (d1 `*` d2) (fun (x0 : coeff * coeff) => x0.`1 + x0.`2 = x) (fun (x0 : coeff * coeff) => (x - x0.`1) = x0.`2); 1: by move => c /=;smt(@Zq). 
have -> := mu_eq (d1 `*` d2) (fun (x0 : coeff * coeff) => x0.`1 - x0.`2 = x) (fun (x0 : coeff * coeff) => (- (x - x0.`1))=x0.`2); 1: by move => c /=;smt(@Zq). 
rewrite !dprod_partition /=;congr => /=; apply fun_ext => c;congr.
move : H2; rewrite /is_good => [# ??]; rewrite allP /= => H2.  
have -> : ((=) (x - c)) = pred1  (x - c) by smt().
have -> : ((=) (-(x - c))) = pred1  (-(x - c)) by smt().
by smt(DZmodP.Support.enumP).
qed.


lemma dadd_poly (d1 d2 : coeff distr): 
   dmap ((darray256 d1) `*` (darray256 d2)) (fun (pp : poly*poly) => Rq.(&+) pp.`1 pp.`2) = darray256 (dcadd d1 d2). 
rewrite /darray256.
have -> : dmap (dmap (dlist d1 256) (Array256.of_list witness) `*` dmap (dlist d2 256) (Array256.of_list witness))
  (fun (pp : poly * poly) => pp.`1 &+ pp.`2) =
  dmap ((dlist d1 256)  `*` (dlist d2 256))
  (fun (pp : coeff list * coeff list) => (Array256.of_list witness pp.`1) &+ (Array256.of_list witness pp.`2)) by rewrite -dmap_dprod_comp.  
have -> : dmap (dlist d1 256 `*` dlist d2 256)
  (fun (pp : coeff list * coeff list) => (Array256.of_list witness pp.`1) &+ (Array256.of_list witness pp.`2)) = 
 dmap (dmap (dlist d1 256 `*` dlist d2 256)
  (fun (pp : coeff list * coeff list) => (mkseq (fun (i : int) => nth witness pp.`1 i + nth witness pp.`2 i) 256))) (Array256.of_list witness ).
+ rewrite dmap_comp /(\o) /=; congr. 
  apply fun_ext => ll. 
  rewrite /(&+) tP => i ib.
  by rewrite map2E initiE //= !get_of_list // nth_mkseq //. 
  congr.
   have  <- :=  MyDM.dlistD 256 d1 d2 _  => //. 
   by rewrite dmap_dprodE;congr; apply fun_ext => cl1;congr;apply fun_ext => cl2 => /=.
qed.


clone import Distrmatrix as MyDMV with  
    type DM.ZR.t = poly,
    op DM.ZR.zeror <- Rq.zero,
    op DM.ZR.oner <- Rq.one,
    pred DM.ZR.unit = Rq.unit,
    op DM.ZR.(+) <- Rq.(&+),
    op DM.ZR.([-]) <- Rq.(&-),
    op DM.ZR.( * ) <- Rq.(&*),
    op DM.ZR.invr <- Rq.invr.


lemma dadd_vector (d1 d2 : coeff distr): 
   dmap ((dvector (darray256 d1)) `*` (dvector (darray256 d2))) (fun (pp : polyvec*polyvec) => pp.`1 + pp.`2) = dvector (darray256 (dcadd d1 d2)).
rewrite /dvector -!dlist_djoin;1..3:smt(gt0_kvec).  
rewrite -dmap_dprod_comp /=. 
rewrite -dadd_poly.
have <- := MyDMV.dlistD kvec (dR d1) (dR d2) _  => //=. 
have := dmap_dprodE (dlist (dR d1) kvec) (dlist (dR d2) kvec) (fun (xsys : poly list * poly list) => mkseq (fun (i : int) => (nth witness xsys.`1 i) &+ (nth witness xsys.`2 i)) kvec).
have -> : (dlet (dlist (dR d1) kvec)
     (fun (xs : DM.R list) =>
        dmap (dlist (dR d2) kvec) (fun (ys : DM.R list) => mkseq (fun (i : int) => nth witness xs i &+ nth witness ys i) kvec))) = dlet (dlist (dR d1) kvec)
  (fun (x : poly list) =>
     dmap (dlist (dR d2) kvec)
       (fun (y : poly list) =>
          (fun (xsys : poly list * poly list) => mkseq (fun (i : int) => nth witness xsys.`1 i &+ nth witness xsys.`2 i) kvec) (x, y))) by congr;rewrite fun_ext => xx;congr; rewrite fun_ext =>yy /= /#.
move => <-.
rewrite dmap_comp;congr;1:smt(). 
rewrite fun_ext =>yy /=;apply eq_vectorP => i ib.
rewrite !offunvE 1,2:/# nth_mkseq 1:/# /= /(+) /= offunvE 1:/# /= !offunvE /#.
qed.


abbrev proj(i : int, p : poly) = p.[i].
lemma dadd_poly_tail (d1 d2 : poly distr) (d1c d2c : coeff distr) (i:int) : 
   0 <= i < 256 =>
   dmap d1 (proj i) = d1c =>
   dmap d2 (proj i) = d2c =>
   dmap (dmap (d1 `*` d2) (fun (pp : poly*poly) => Rq.(&+) pp.`1 pp.`2)) (proj i) = dcadd d1c d2c.
move => ib H1 H2.
rewrite !dmap_comp /(\o) /=.
have -> : (fun (x : poly * poly) => proj i (x.`1 &+ x.`2)) =
  (fun (x : poly * poly) => (proj i x.`1) + (proj i x.`2)) by
   rewrite fun_ext => p; rewrite /(&+) map2E initiE 1,2:/# /=.
 have /= -> := dmap_dprod_comp d1 d2 (proj i) (proj i) (+)%Zq.
rewrite H1 H2.
done.
qed.

lemma dsub_poly_tail_good (d1 d2 : poly distr) (d1c d2c : coeff distr) (i:int) : 
   is_good d2c =>
   0 <= i < 256 =>
   dmap d1 (proj i) = d1c =>
   dmap d2 (proj i) = d2c =>
   dmap (dmap (d1 `*` d2) (fun (pp : poly*poly) => Rq.(&+) pp.`1 (Rq.(&-) pp.`2))) (proj i) = dcadd d1c d2c.
move => G2 ib H1 H2.
rewrite !dmap_comp /(\o) /=.
have -> : (fun (x : poly * poly) => proj i (MLWE_.(&-) x.`1  x.`2)) =
  (fun (x : poly * poly) => (proj i x.`1) - (proj i x.`2)). 
   rewrite fun_ext => p; rewrite /ZR.(+) /(&+) /(&-) /= map2E initiE 1:/# /= mapiE 1:/# //=.
 have /= -> := dmap_dprod_comp d1 d2 (proj i) (proj i) (-)%Zq.
rewrite H1 H2.
by rewrite add_sub //.
qed.

lemma dsub_poly_tail (d1 d2 : poly distr) (d1c d2c : coeff distr) (i:int) : 
   0 <= i < 256 =>
   dmap d1 (proj i) = d1c =>
   dmap d2 (proj i) = d2c =>
   dmap (dmap (d1 `*` d2) (fun (pp : poly*poly) => Rq.(&+) pp.`1 (Rq.(&-) pp.`2))) (proj i) = dcsub d1c d2c.
move => ib H1 H2.
rewrite !dmap_comp /(\o) /=.
have -> : (fun (x : poly * poly) => proj i (MLWE_.(&-) x.`1  x.`2)) =
  (fun (x : poly * poly) => (proj i x.`1) - (proj i x.`2)). 
   rewrite fun_ext => p; rewrite /ZR.(+) /(&+) /(&-) /= map2E initiE 1:/# /= mapiE 1:/# //=.
 have /= -> := dmap_dprod_comp d1 d2 (proj i) (proj i) (-)%Zq.
by rewrite H1 H2.
qed.

lemma darray_proj d i :
  is_lossless d =>
  0 <= i < 256 =>
   dmap (dR d) (fun (p : poly) => proj i p) = d.
move => Hll ib.
rewrite dmap_comp /(\o).
rewrite -(eq_dmap _ (fun x => nth witness x i)) /=;1:
  by apply fun_ext => /=; apply fun_ext => x;rewrite get_of_list 1:/#.
apply eq_distr => cc; rewrite dmapE /pred1 /(\o) /=.
have := dlistE witness d (fun (k:int) (c:coeff) =>  k <> i \/ c = cc) 256 => /=.
have -> : (fun (xs : coeff list) => forall (i0 : int), 0 <= i0 < 256 => i0 <> i \/ nth witness xs i0 = cc) = 
     (fun (x : coeff list) => nth witness x i = cc) by smt().
move => ->.
rewrite (StdBigop.Bigreal.BRM.bigD1 _ _ i) /=;1,2: smt(mem_iota iota_uniq).
rewrite StdBigop.Bigreal.BRM.big1 /=;smt().
qed.

lemma dadd_id d :
  dadd (dunit Zq.zero) d = d.
rewrite eq_distr =>cc.  
rewrite /dadd dprodC  /= dprod_dlet /= dmap_comp dmap_dlet /(\o) /=. 
have -> : (fun (a : MyDM.DM.R) =>
        dmap (dlet (dunit Zq.zero) (fun (b : MyDM.DM.R) => dunit (a, b)))
          (fun (x : MyDM.DM.R * MyDM.DM.R) => x.`2 + x.`1)) =
         (fun (a : MyDM.DM.R) => dunit (Zq.zero + a)).
+ rewrite fun_ext => a.
  by rewrite dlet_dunit /= dmap_comp /(\o) /= dmap_dunit /=.
rewrite dlet_dunit /= dmapE /(\o) /pred1 /=;congr.
apply fun_ext => x. 
by have -> : Zq.zero +x = x by ring.
qed. 


lemma dmulS1 n d1 d2 : 
   0 <= n => MyDM.dmul (n+1) d1 d2 = dadd (dmul n d1 d2) (dmul 1 d1 d2).
move => nb; rewrite dmulE 1:/# iterS 1:/# /=;congr.
+ by rewrite dmulE 1:/#; done.
by rewrite dmulE 1:/# iter1 /= dadd_id.
qed.

lemma dadd_assoc d1 d2 d3 :
  dadd (MyDM.dadd d1 d2) d3 = dadd d1 (dadd d2 d3).
rewrite /dadd.
rewrite !(dmap_dprodE) /= /dmap /(\o) /=!dlet_dlet. 
congr; apply fun_ext => x1 /=.
rewrite !dlet_dlet.
congr; apply fun_ext => x2 /=.
rewrite !dlet_dunit dmap_comp /(\o) /= dlet_unit /= dlet_dunit /=. 
by congr => /=; apply fun_ext => * /=;ring.
qed.

lemma dadd_dmul n1 n2 d1 d2 :
   0 <= n1 => 0 <= n2 =>
     dadd (MyDM.dmul n1 d1 d2) (dmul n2 d1 d2) = dmul (n1 + n2) d1 d2.
move =>  + ge02; elim n1; 1: by rewrite dmul0E dadd_id.
move => n1 ge01.
have -> : (n1 + 1 + n2) = (n1 + n2) + 1 by ring.
rewrite !dmulS1 1,2:/# => <-.
smt(MyDM.dadd_sym dadd_assoc).
qed.
 
lemma dmulS n b d1 d2 :
   0 <= n => 0 <= b =>
  MyDM.dmul ((n + 1) * b) d1 d2 = dadd (dmul (n * b) d1 d2) (dmul b d1 d2).
elim n; 1: by rewrite dmul0E dadd_id.
move => n nb; pose nn := n+1; move => H Hb; move : (H Hb) => ->;clear H.
rewrite !dadd_dmul /#.
qed.

lemma dmul_good n d :
  0 < n =>
  is_good d =>
  is_good (dmul n d d).
move => nb Gd.
pose nn := n -1.
have : 0 <= nn by smt().
have -> : n = nn + 1 by smt().
elim nn.
+ by rewrite  /= dmulE // iter1 /= dadd_id mul_good //.
move => i ib.
have /= -> := dmulS (i+1) 1 d d;1:smt().
move => *;rewrite add_good //.
by rewrite  /= dmulE // iter1 /= dadd_id mul_good //.
qed.


lemma dprod_dmap_cross_in ['a 'b 'c 'd 'e 'ab 'ac 'bd 'cd]
  (da : 'a distr) (db : 'b distr) (dc : 'c distr) (dd : 'd distr)
  (Fab : 'a * 'b -> 'ab)
  (Fcd : 'c * 'd -> 'cd)
  (F   : 'ab -> 'cd -> 'e)
  (Fac : 'a * 'c -> 'ac)
  (Fbd : 'b * 'd -> 'bd)
  (G   : 'ac -> 'bd -> 'e)
:
  (forall a b c d, a \in da => b \in db => c \in dc => d \in dd =>F (Fab (a, b)) (Fcd (c, d)) = G (Fac (a, c)) (Fbd (b, d))) =>

  dlet
    (dmap (da `*` db) Fab)
    (fun ab =>
      dmap
        (dmap (dc `*` dd) Fcd)
        (fun cd => F ab cd))
  = dlet
      (dmap (da `*` dc) Fac)
      (fun ac =>
        dmap
          (dmap (db `*` dd) Fbd)
          (fun bd => G ac bd)).
proof.
pose D1 := dlet (da `*` db)
  (fun ab => dlet dc (fun c => dmap dd (fun d => F (Fab ab) (Fcd (c, d))))).
move=> eq; rewrite dlet_dmap /=.
have -> : dlet (da `*` db) (fun (a : 'a * 'b) => dmap (dmap (dc `*` dd) Fcd) (F (Fab a)))  = D1. 
- by rewrite &(eq_dlet) // => ab /=; rewrite dmap_comp dmap_dprodE.
pose D2 := dlet (da `*` dc)
  (fun ac => dlet db (fun b => dmap dd (fun d => G (Fac ac) (Fbd (b, d))))).
rewrite dlet_dmap /=.
have -> : D1 = D2;last first.
- by rewrite &(eq_dlet) // => ac /=; rewrite dmap_comp dmap_dprodE.
rewrite /D1 /D2.
rewrite !dprod_dlet !dlet_dlet /= &(in_eq_dlet) // => a Ha /=.
rewrite dlet_dlet /= dlet_swap &(in_eq_dlet) // => b Hb /=.
rewrite 2!(dlet_dunit, dlet_unit) /= dlet_dmap.
rewrite &(in_eq_dlet) // => c Hc /=. 
 rewrite &(eq_dmap_in) // => d Hd /=.
by apply eq.
qed.

lemma dmul_poly_tail (d1 d2 : coeff distr) (i:int) : 
   is_lossless d1 =>
   is_lossless d2 =>
   0 <= i < 256 =>
   dmap (dmap (dR d1 `*` dR d2) (fun (pp : poly*poly) => Rq.(&*) pp.`1 pp.`2)) (proj i) = dcsub (dmul (i+1) d1 d2) (dmul (256-i-1) d1 d2).
move =>  d1ll d2ll ib.
rewrite /(&*) dmap_comp /(\o) /=. 
have -> : 
   (fun (x : poly * poly) =>
     proj i
       (Array256.init
          (fun (i0 : int) =>
             foldr
               (fun (k : int) (ci : coeff) =>
                  if 0 <= i0 - k then ci + proj k x.`1 * proj (i0 - k) x.`2
                  else ci - proj k x.`1 * proj (256 + (i0 - k)) x.`2) Zq.zero (
               iota_ 0 256))))
   = 
    (fun (x : poly * poly) =>
        foldr
               (fun (k : int) (ci : coeff) =>
                  if 0 <= i - k then ci + proj k x.`1 * proj (i - k) x.`2
                  else ci - proj k x.`1 * proj (256 + (i - k)) x.`2) Zq.zero (
               iota_ 0 256)) by rewrite fun_ext => x;rewrite initiE 1:/# /=.

have -> : 
    dR d2 =
    dmap (dR d2) (fun p =>
      (Array256.init (fun k => if 0<= i-k then proj (i-k) p else  proj (256+i-k) p))).
pose F := (fun (p : poly) =>
     Array256.init (fun (k : int) => if 0 <= i - k then proj (i - k) p else  proj (256 + i - k) p)).
pose G :=  (fun (p : poly) =>
     Array256.init (fun (k : int) => if 0 <= i - k then proj (i - k) p else proj (256 + i - k) p)).
have -> //:= dmap_bij (dR d2) (dR d2) F G _ _ _ _.
+ move => x; rewrite !supp_dmap => He; elim He => l [Hp1 Hp2].
  exists (to_list (F x)); rewrite to_listK /=. 
  rewrite Hp2 /F /= supp_dlist 1:/# size_to_list /= allP => cc.
  move => H. 
  have <- := nth_index witness cc _ H.
  pose pos := index cc
  (to_list
     (Array256.init
        (fun (k : int) =>
           if 0 <= i - k then proj (i - k) (Array256.of_list witness l)
           else proj (256 + i - k) (Array256.of_list witness l)))).
  have Hpos : 0 <= pos < 256 by smt(@List).
  rewrite get_to_list initiE /= 1:/#.   
  move : Hp1; rewrite supp_dlist // => [#??].
  case (0 <= i - pos) => *. 
  + rewrite get_of_list;1: smt(). 
    by smt(@List).
  + rewrite get_of_list; 1: by smt().
    by smt(@List).
+ move => x; rewrite !supp_dmap => He; elim He => l [Hp1 Hp2].
  rewrite  !dmap1E /pred1 /(\o) /= /x.  
  pose P1:= fun (i : int) (a : coeff), nth witness l i = a.
  pose P2:= fun (i : int) (a : coeff), nth witness (to_list (G x)) i = a.
  rewrite {1}(mu_eq  _ _ ( (fun (xs : coeff list) => forall (i : int), 0 <= i < 256 => P1 i (nth witness xs i)))).
  + by move => c;rewrite Hp2 /P1 tP eq_iff;split => H ii iib; move : (H ii iib); rewrite !get_of_list /#. 
  rewrite (mu_eq (dlist d2 256) (fun (x0 : coeff list) => Array256.of_list witness x0 = G x) ( (fun (xs : coeff list) => forall (i : int), 0 <= i < 256 => P2 i (nth witness xs i)))).
  + by move => c;rewrite Hp2 /P2 /G tP eq_iff;split => H ii iib; move : (H ii iib); rewrite !get_of_list /#. 
  rewrite !dlistE; rewrite /P1 /P2 /G /=. 
  rewrite (StdBigop.Bigreal.BRM.eq_big_perm _ _ (range 0 256) (map (fun k => if 0<= i - k then  i-k else 256 + i - k) (range 0 256))).
+ apply uniq_perm_eq_size; 1: smt(range_uniq). 
  + apply map_inj_in_uniq;2:smt(range_uniq).   
    move => kk1 kk2;rewrite !mem_iota /= => *;  smt().
  + smt(size_map size_iota).
  + move => kk; rewrite mem_iota => /= kkr. 
    rewrite mapP /=. 
    exists (if 0 <= i - kk then i - kk else 256 + i - kk); smt(mem_iota).
  rewrite StdBigop.Bigreal.BRM.big_map /(\o) /=.
  have -> : (fun (x0 : int) => predT (if 0 <= i - x0 then i - x0 else 256 + i - x0)) = predT by smt().
   apply StdBigop.Bigreal.BRM.eq_big_seq => kk; rewrite mem_iota /= => kkb. 
   case (0<= i - kk) => ?.
   + by apply mu_eq => cc; rewrite initiE 1:/# /= Hp2 get_of_list /#. 
   rewrite (mu_eq d2
  ((=)
     (proj kk (Array256.init (fun (k : int) => if 0 <= i - k then proj (i - k) x else  proj (256 + i - k) x)))) ((=) ( proj (256 + i - kk) x)));
    1: by move => cc;rewrite initiE 1:/# /= Hp2 ifF /#.
    rewrite Hp2  get_of_list 1:/#; smt(@Zq).
+ rewrite /G /F => a *; rewrite tP => k kb.
  rewrite !initiE /= 1:/#.
  case (0 <= i - k) => * /=; rewrite initiE 1: /#; [ by smt() | by  smt(@Zq)].  
+ rewrite /G /F => a *; rewrite tP => k kb.
  rewrite !initiE /= 1:/#.
  case (0 <= i - k) => * /=; rewrite initiE 1: /#; [ by smt() | by  smt(@Zq)].  
 
rewrite dmap_dprodR /= dmap_comp /(\o) /=.
have -> : 
 (fun (x : poly * poly) =>
     foldr
    (fun (k : int) (ci : coeff) =>
          if 0 <= i - k then
            ci +
            proj k x.`1 *
            proj (i - k)
              (Array256.init
                 (fun (k0 : int) => if 0 <= i - k0 then proj (i - k0) x.`2 else proj (256 + i - k0) x.`2) )
          else
            ci -
            proj k x.`1 *
            proj (256 + (i - k))
              (Array256.init
                 (fun (k0 : int) => if 0 <= i - k0 then proj (i - k0) x.`2 else proj (256 + i - k0) x.`2))) Zq.zero (
               iota_ 0 256)) =
    (fun (x : poly * poly) =>
        foldr
               (fun (k : int) (ci : coeff) =>
                  if 0 <= i-k then ci + proj k x.`1 * proj k x.`2 else ci - proj k x.`1 * proj k x.`2) Zq.zero (
               iota_ 0 256)).
+ apply fun_ext => pp. 
  apply eq_in_foldr => //.
  move => kk; rewrite mem_iota /= => kkb;apply fun_ext => cc.
  by case  (0 <= i - kk) => /= *; rewrite initiE /=;1,3:smt();[ rewrite ifT /# | rewrite ifF 1:/# => /=; smt(@Zq) ]. 

have /= <- := dmap_dprod_comp (dlist d1 256) 
                        (dlist d2 256) 
                        (Array256.of_list witness)
                         (Array256.of_list witness)
                         (fun (x1 x2 : poly) =>
     foldr (fun (k : int) (ci : coeff) => if 0 <= i-k then ci + proj k x1 * proj k x2 else ci - proj k x1 * proj k x2) Zq.zero (iota_ 0 256)).
have -> : 
    (fun (xy : coeff list * coeff list) =>
     foldr
       (fun (k : int) (ci : coeff) =>
          if 0 <= i - k then ci + proj k (Array256.of_list witness xy.`1) * proj k (Array256.of_list witness xy.`2)
          else ci - proj k (Array256.of_list witness xy.`1) * proj k (Array256.of_list witness xy.`2)) Zq.zero
       (iota_ 0 256))
= 
     (fun (xy : coeff list * coeff list) =>
     foldr
       (fun (k : int) (ci : coeff) =>
          if 0 <= i-k then ci + nth witness xy.`1 k * nth witness xy.`2 k else ci - nth witness xy.`1 k * nth witness xy.`2 k )  Zq.zero (
       iota_ 0 256)).
+ apply fun_ext => xx; apply eq_in_foldr => //.
 +  move  => kk;rewrite !mem_iota /= => kkb;apply fun_ext => cc;congr =>//;
    rewrite !get_of_list /#.

have H : forall nn, 0 <= nn <= 256 => 
   dmap (dlist d1 (nn) `*` dlist d2 (nn))
  (fun (xy : coeff list * coeff list) =>
     foldr (fun (k : int) (ci : coeff) => ci + nth witness xy.`1 k * nth witness xy.`2 k) Zq.zero (iota_ 0 (nn))) =
dmul (nn) d1 d2.

move => kk; elim /natind:kk.
+ move => n ??; have -> /=: n = 0 by smt().
  by rewrite iota0 //= dmul0E /= dmap_cst; smt(dprod_ll dlist_ll).  

move => n? H ?; move : (H _); 1: smt(); move => Hind.
have /= -> := dmulS n 1;1:smt().
rewrite iotaSr 1:/# /= -cats1. 
have -> : 
  (fun (xy : coeff list * coeff list) =>
     foldr (fun (k : int) (ci : coeff) => ci + nth witness xy.`1 k * nth witness xy.`2 k) Zq.zero (iota_ 0 n ++ [n]))=
 (fun (xy : coeff list * coeff list) =>
     foldr (fun (k : int) (ci : coeff) => ci + nth witness xy.`1 k * nth witness xy.`2 k) Zq.zero (iota_ 0 n) +
            nth witness xy.`1 n * nth witness xy.`2 n).
+ apply fun_ext => pp;rewrite (foldr_rem n) //= => *; 1: by ring.
  + by smt(mem_iota mem_cat).
  have -> : rem n (iota_ 0 n ++ [n]) = iota_ 0 n; last  by done.
  rewrite rem_filter;1: by apply cat_uniq; rewrite iota_uniq /=;smt(mem_iota).
  rewrite filter_cat. 
  by rewrite (eq_in_filter_pred0 _ [n]) /= 1:/# eq_in_filter_predT;smt(mem_iota).
 
rewrite !(dlistSr _ n) 1..2:/# /=.  
  rewrite !(dmap_dprodL (dlist d1 n `*` d1)) !dmap_comp /(\o) /=. 
  have -> := dmap_dprodR (dlist d1 n `*` d1) (dlist d2 n `*` d2) (fun (xy : coeff list * coeff) => rcons xy.`1 xy.`2).
  rewrite !dmap_comp /(\o) /=. 

  pose F := fun (xs : coeff list) (x : coeff) (ys : coeff list) (y : coeff) =>
    (foldr
       (fun (k : int) (ci : coeff) =>
          ci + (nth witness xs k * nth witness ys k)) Zq.zero (
       iota_ 0 n)) + x * y.
have Hcr := dprod_cross  (dlist d1 n) d1 (dlist d2 n) d2 F.
have -> : 
  dmap (dlist d1 n `*` d1 `*` (dlist d2 n `*` d2))
  (fun (x : (coeff list * coeff) * (coeff list * coeff)) =>
     foldr (fun (k : int) (ci : coeff) => ci + nth witness (rcons x.`1.`1 x.`1.`2) k * nth witness (rcons x.`2.`1 x.`2.`2) k) Zq.zero
       (iota_ 0 n) +
     nth witness (rcons x.`1.`1 x.`1.`2) n * nth witness (rcons x.`2.`1 x.`2.`2) n)
  =   
  dlet (dlist d1 n `*` d1)
       (fun (ab : coeff list * coeff) =>
          dmap (dlist d2 n `*` d2) (fun (cd : coeff list * coeff) => F ab.`1 ab.`2 cd.`1 cd.`2)). 
+ rewrite /F.
  rewrite dprod_dlet /=.
  rewrite dmap_dlet.
  apply in_eq_dlet => pp Hpp /=.
  rewrite dmap_dlet /= /dmap. 
  apply in_eq_dlet => vv Hvv /=.
  rewrite /(\o) /=. 
  rewrite dlet_dunit dmap_dunit /=;apply eq_distr => cc.
  rewrite !dunit1E /=.  
  rewrite supp_dprod supp_dlist  /= in Hpp; 1: smt(). 
  rewrite supp_dprod supp_dlist  /= in Hvv; 1: smt(). 
  congr;congr;congr=>//; last by smt(nth_rcons).
  by apply  eq_in_foldr; smt(nth_rcons mem_iota).

rewrite Hcr -Hind /dadd. 
rewrite (dmap_dprodL  (dlist d1 n `*` dlist d2 n) _
     (fun (xy : coeff list * coeff list) =>
        foldr (fun (k : int) (ci : coeff) => ci + nth witness xy.`1 k * nth witness xy.`2 k) Zq.zero (iota_ 0 n))) /=  dmap_comp /(\o) /=.
rewrite dmap_dprodE /=.
by apply in_eq_dlet => xx ? /=;rewrite dmulE //= /dmul1 iter1 /= dadd_id /= dmap_comp /= /(\o) /F.

have -> : 256 = (i + 1) + (256 - i - 1) by ring.
rewrite !(dlist_add _ (i+1)) 1..4:/#.
rewrite dmap_dprod /= dmap_comp /= /(\o) /=.

pose Fab:= fun (ll : coeff list * coeff list) => ll.`1 ++ ll.`2.
pose Fcd:= fun (ll : coeff list * coeff list) => ll.`1 ++ ll.`2.
pose Fac:= fun (ll : coeff list * coeff list) => 
   foldr
       (fun (k : int) (ci : coeff) =>
           ci + nth witness ll.`1 k * nth witness ll.`2 k) Zq.zero (iota_ 0 (i+1)).
pose Fbd:= fun (ll : coeff list * coeff list) => 
   foldr
       (fun (k : int) (ci : coeff) =>
           ci + nth witness ll.`1 k * nth witness ll.`2 k) Zq.zero (iota_ 0 (255-i)).
pose F := fun (l1 l2 : coeff list) => 
   foldr
       (fun (k : int) (ci : coeff) =>
         if 0 <= i - k then   ci + nth witness l1 k * nth witness l2 k else   ci - nth witness l1 k * nth witness l2 k) Zq.zero (iota_ 0 256).
pose G := fun (c1 c2 : coeff) => c1 - c2.
pose dh1 := (dlist d1 (i + 1)).
pose dt1 :=  (dlist d1 (255 - i)) .
pose dh2 := (dlist d2 (i + 1)).
pose dt2 :=  (dlist d2 (255 - i)) .


have := dprod_dmap_cross_in dh1 dt1 dh2 dt2 Fab Fcd F Fac Fbd G _.
+ move => h1 t1 h2 t2 h1supp h2supp h3supp h4supp ; rewrite /F /Fab /Fcd /G /Fac /Fbd. 
   have := (foldr_cat (fun (k : int) (ci : coeff) =>
     if 0 <= i - k then ci + nth witness ((h1, t1).`1 ++ (h1, t1).`2) k * nth witness ((h2, t2).`1 ++ (h2, t2).`2) k
     else ci - nth witness ((h1, t1).`1 ++ (h1, t1).`2) k * nth witness ((h2, t2).`1 ++ (h2, t2).`2) k) Zq.zero (iota_ 0 (i+1)) (iota_ (i+1) (255 - i))).
   rewrite -(iota_add 0 (i+1) (255 - i)) 1,2:/# /=.
   have -> : i + 1 + (255 - i) = 256 by ring.
   move => ->. 

   have -> : (foldr
     (fun (k : int) (ci : coeff) =>
        if 0 <= i - k then ci + nth witness (h1 ++ t1) k * nth witness (h2 ++ t2) k else ci - nth witness (h1 ++ t1) k * nth witness (h2 ++ t2) k) Zq.zero
     (iota_ (i + 1) (255 - i))) =
    Zq.zero - foldr (fun (k : int) (ci : coeff) => ci + nth witness t1 k * nth witness t2 k) Zq.zero (iota_ 0 (255 - i)). 

+ have /= -> := eq_in_foldr (fun (k : int) (ci : coeff) =>
     if 0 <= i - k then ci + nth witness (h1 ++ t1) k * nth witness (h2 ++ t2) k else ci - nth witness (h1 ++ t1) k * nth witness (h2 ++ t2) k)
   (fun (k : int) (ci : coeff) => ci - nth witness t1 (k - (i+1)) * nth witness t2 (k - (i+1))) Zq.zero Zq.zero (iota_ (i + 1) (255 - i))  (iota_ (i + 1) (255 - i))  _.

+ move => x; rewrite mem_iota /= => *.
  apply fun_ext => c .
  rewrite ifF 1:/# !nth_cat /=;1: smt(supp_dlist).
  have -> : (iota_ (i + 1) (255 - i)) = map ((+) (i+1))  (iota_ 0 (255 - i)) by rewrite -iota_addl. 
  rewrite foldr_map /=.
  have Hladd : forall (nn : int) (l1 l2 : coeff list), size l1 = size l2 => 0 <= nn <= size l1 => 
     foldr (fun (k : int) (ci : coeff) => ci - nth witness l1 k * nth witness l2 k) Zq.zero (iota_ 0 nn) =
     Zq.zero - foldr (fun (k : int) (ci : coeff) => ci + nth witness l1 k * nth witness l2 k) Zq.zero (iota_ 0 nn); last by have := Hladd (255-i) t1 t2 _ _; smt(supp_dlist).
  move => nn l1 l2 ? [#  Hn0 Hn]; move : Hn0 Hn; elim nn.
  + by move => _; rewrite iota0 //=; ring.
  move => ii iib Hind Hs. 
  move : (Hind _); 1:smt().
  rewrite !iotaSr 1:/# /=. 
  have  Hp : perm_eq (rcons (iota_ 0 ii) ii)  (ii :: iota_ 0 ii) by smt(@List).
  rewrite !(foldr_perm  _ _ _ _ _ Hp) /=; 1,2: by auto => /> *;ring.
  by move => ->; ring.

pose x0 := (Zq.zero - foldr (fun (k : int) (ci : coeff) => ci + nth witness t1 k * nth witness t2 k) Zq.zero (iota_ 0 (255 - i))).

rewrite (eq_in_foldr (fun (k : int) (ci : coeff) =>
     if 0 <= i - k then ci + nth witness (h1 ++ t1) k * nth witness (h2 ++ t2) k else ci - nth witness (h1 ++ t1) k * nth witness (h2 ++ t2) k) (fun (k : int) (ci : coeff) =>ci + nth witness h1 k * nth witness h2 k) x0 x0 (iota_ 0 (i + 1)) (iota_ 0 (i + 1))) => //.
+ move => ii;rewrite mem_iota /= => Hii /=. 
  rewrite fun_ext => cc /=.
  rewrite ifT 1:/# !(nth_cat witness);1: smt(supp_dlist).
have /= := foldr_perm (fun (k : int) (ci : coeff) => ci + if (k = i + 1) then x0 else nth witness h1 k * nth witness h2 k) Zq.zero ((i+1)::(iota_ 0 (i + 1))) (rcons(iota_ 0 (i + 1)) (i+1)) _ _.
+ by move => a b cc /=; case (a = i+1); case (b = i+1); move => *; ring.
+ by smt(@List).
rewrite foldr_rcons /=.

have -> : foldr (fun (k : int) (ci : coeff) => ci + if k = i + 1 then x0 else nth witness h1 k * nth witness h2 k) (Zq.zero + x0) (iota_ 0 (i + 1)) = 
  foldr (fun (k : int) (ci : coeff) => ci + nth witness h1 k * nth witness h2 k) x0 (iota_ 0 (i + 1)) .
+ have -> : (Zq.zero + x0) = x0 by ring.
  by apply eq_in_foldr; smt(mem_iota).

have -> : foldr (fun (k : int) (ci : coeff) => ci + if k = i + 1 then x0 else nth witness h1 k * nth witness h2 k) Zq.zero (iota_ 0 (i + 1)) = foldr (fun (k : int) (ci : coeff) => ci + nth witness h1 k * nth witness h2 k) Zq.zero (iota_ 0 (i + 1)).
+  by apply eq_in_foldr; smt(mem_iota).

by move => <-; rewrite /x0; ring.

have -> : dlet (dmap (dh1 `*` dt1) Fab)
  (fun (ab : coeff list) => dmap (dmap (dh2 `*` dt2) Fcd) (fun (cd : coeff list) => F ab cd))  =
  dmap (dh1 `*` dt1 `*` (dlist d2 (i + 1) `*` dlist d2 (255 - i)))
  (fun (x : (coeff list * coeff list) * (coeff list * coeff list)) =>
     foldr
       (fun (k : int) (ci : coeff) =>
          if 0 <= i - k then ci + nth witness (x.`1.`1 ++ x.`1.`2) k * nth witness (x.`2.`1 ++ x.`2.`2) k
          else ci - nth witness (x.`1.`1 ++ x.`1.`2) k * nth witness (x.`2.`1 ++ x.`2.`2) k) Zq.zero (
       iota_ 0 (i + 1 + (255 - i)))).
+ rewrite /Fab /Fcd /F.
  rewrite dlet_dmap /= (dprod_dlet (dh1 `*` dt1)) !dmap_dlet /=;apply in_eq_dlet => l1 Hl1 /=.  
  rewrite dmap_comp dmap_dlet /= /(dmap  (dh2 `*` dt2) ) /(\o);apply in_eq_dlet => l2 Hl2 /=.  
  rewrite dmap_dunit;congr => /=.
  by smt().
move=> ->; rewrite /G.
rewrite /dcsub /(dmap (MyDM.dmul _ _ _ `*` _) _) /(\o) /=. 
rewrite (dprod_dlet (dmul (i+1) d1 d2)) /= dlet_dunit. 
have -> : (dmap (dh1 `*` dh2) Fac) = dmul (i+1) d1 d2.
+ move : (H (i+1) _) => /=;1:smt().
  move => <-. rewrite /dt1 /dt2;apply eq_dmap_in => ll; rewrite supp_dprod supp_dlist 1:/# =>[# *] /=. 
  done.
rewrite dmap_dlet; apply in_eq_dlet => cc ? /=.
rewrite dlet_dunit /=.
have -> : (dmap (dt1 `*` dt2) Fbd) = dmul (256 -i -1) d1 d2.
+ move : (H (255-i) _) => /=;1:smt().
  move => <-. rewrite /dt1 /dt2;apply eq_dmap_in => ll; rewrite supp_dprod supp_dlist 1:/# =>[# *] /=. 
  done.
by rewrite !dmap_comp /(\o) /=. 
qed. 

lemma dmul_poly_tail_good (d1 d2 : coeff distr) (i:int) : 
   is_good d1 =>
   is_good d2 =>
   0 <= i < 256 =>
   dmap (dmap (dR d1 `*` dR d2) (fun (pp : poly*poly) => Rq.(&*) pp.`1 pp.`2)) (proj i) = dmul 256 d1 d2.
move => G1 G2 ib.
rewrite /(&*) dmap_comp /(\o) /=. 
have -> : 
   (fun (x : poly * poly) =>
     proj i
       (Array256.init
          (fun (i0 : int) =>
             foldr
               (fun (k : int) (ci : coeff) =>
                  if 0 <= i0 - k then ci + proj k x.`1 * proj (i0 - k) x.`2
                  else ci - proj k x.`1 * proj (256 + (i0 - k)) x.`2) Zq.zero (
               iota_ 0 256))))
   = 
    (fun (x : poly * poly) =>
        foldr
               (fun (k : int) (ci : coeff) =>
                  if 0 <= i - k then ci + proj k x.`1 * proj (i - k) x.`2
                  else ci - proj k x.`1 * proj (256 + (i - k)) x.`2) Zq.zero (
               iota_ 0 256)) by rewrite fun_ext => x;rewrite initiE 1:/# /=.

have -> : 
    dR d2 =
    dmap (dR d2) (fun p =>
      (Array256.init (fun k => if 0<= i-k then proj (i-k) p else Zq.zero - proj (256+i-k) p))).
pose F := (fun (p : poly) =>
     Array256.init (fun (k : int) => if 0 <= i - k then proj (i - k) p else Zq.zero - proj (256 + i - k) p)).
pose G :=  (fun (p : poly) =>
     Array256.init (fun (k : int) => if 0 <= i - k then proj (i - k) p else Zq.zero - proj (256 + i - k) p)).
have -> //:= dmap_bij (dR d2) (dR d2) F G _ _ _ _.
+ move => x; rewrite !supp_dmap => He; elim He => l [Hp1 Hp2].
  exists (to_list (F x)); rewrite to_listK /=. 
  rewrite Hp2 /F /= supp_dlist 1:/# size_to_list /= allP => cc.
  move => H. 
  have <- := nth_index witness cc _ H.
  pose pos := index cc
  (to_list
     (Array256.init
        (fun (k : int) =>
           if 0 <= i - k then proj (i - k) (Array256.of_list witness l)
           else Zq.zero - proj (256 + i - k) (Array256.of_list witness l)))).
  have Hpos : 0 <= pos < 256 by smt(@List).
  rewrite get_to_list initiE /= 1:/#.   
  move : Hp1; rewrite supp_dlist // => [#??].
  case (0 <= i - pos) => *. 
  + rewrite get_of_list;1: smt(). 
    by smt(@List).
  + rewrite get_of_list; 1: by smt().
    move : G2; rewrite /is_good => [#] ??; rewrite allP => H2.
    move : (H2 (nth witness l (256 + i - pos))); rewrite DZmodP.Support.enumP /=.
    rewrite /support. 
    have {1}-> : (- nth witness l (256 + i - pos)) = Zq.zero - nth witness l (256 + i - pos)  by ring. 
    move => <-. have : (nth witness l (256 + i - pos) \in l); last by smt(List.allP).
    smt(@List).
+ move => x; rewrite !supp_dmap => He; elim He => l [Hp1 Hp2].
  rewrite  !dmap1E /pred1 /(\o) /= /x.  
  pose P1:= fun (i : int) (a : coeff), nth witness l i = a.
  pose P2:= fun (i : int) (a : coeff), nth witness (to_list (G x)) i = a.
  rewrite {1}(mu_eq  _ _ ( (fun (xs : coeff list) => forall (i : int), 0 <= i < 256 => P1 i (nth witness xs i)))).
  + by move => c;rewrite Hp2 /P1 tP eq_iff;split => H ii iib; move : (H ii iib); rewrite !get_of_list /#. 
  rewrite (mu_eq (dlist d2 256) (fun (x0 : coeff list) => Array256.of_list witness x0 = G x) ( (fun (xs : coeff list) => forall (i : int), 0 <= i < 256 => P2 i (nth witness xs i)))).
  + by move => c;rewrite Hp2 /P2 /G tP eq_iff;split => H ii iib; move : (H ii iib); rewrite !get_of_list /#. 
  rewrite !dlistE; rewrite /P1 /P2 /G /=. 
  rewrite (StdBigop.Bigreal.BRM.eq_big_perm _ _ (range 0 256) (map (fun k => if 0<= i - k then  i-k else 256 + i - k) (range 0 256))).
+ apply uniq_perm_eq_size; 1: smt(range_uniq). 
  + apply map_inj_in_uniq;2:smt(range_uniq).   
    move => kk1 kk2;rewrite !mem_iota /= => *;  smt().
  + smt(size_map size_iota).
  + move => kk; rewrite mem_iota => /= kkr. 
    rewrite mapP /=. 
    exists (if 0 <= i - kk then i - kk else 256 + i - kk); smt(mem_iota).
  rewrite StdBigop.Bigreal.BRM.big_map /(\o) /=.
  have -> : (fun (x0 : int) => predT (if 0 <= i - x0 then i - x0 else 256 + i - x0)) = predT by smt().
   apply StdBigop.Bigreal.BRM.eq_big_seq => kk; rewrite mem_iota /= => kkb. 
   case (0<= i - kk) => ?.
   + by apply mu_eq => cc; rewrite initiE 1:/# /= Hp2 get_of_list /#. 
   rewrite (mu_eq d2
  ((=)
     (proj kk (Array256.init (fun (k : int) => if 0 <= i - k then proj (i - k) x else Zq.zero - proj (256 + i - k) x)))) ((=) (Zq.zero - proj (256 + i - kk) x)));
    1: by move => cc;rewrite initiE 1:/# /= Hp2 ifF /#.
   move : G2;rewrite /is_good => [# ??];rewrite allP /= => G2. 
    move : (G2 (nth witness l (256 + i - kk)) _); 1: smt(DZmodP.Support.enumP).
    rewrite Hp2  get_of_list 1:/#; smt(@Zq).
+ rewrite /G /F => a *; rewrite tP => k kb.
  rewrite !initiE /= 1:/#.
  case (0 <= i - k) => * /=; rewrite initiE 1: /#; [ by smt() | by  smt(@Zq)].  
+ rewrite /G /F => a *; rewrite tP => k kb.
  rewrite !initiE /= 1:/#.
  case (0 <= i - k) => * /=; rewrite initiE 1: /#; [ by smt() | by  smt(@Zq)].  
 
rewrite dmap_dprodR /= dmap_comp /(\o) /=.
have -> : 
 (fun (x : poly * poly) =>
     foldr
    (fun (k : int) (ci : coeff) =>
          if 0 <= i - k then
            ci +
            proj k x.`1 *
            proj (i - k)
              (Array256.init
                 (fun (k0 : int) => if 0 <= i - k0 then proj (i - k0) x.`2 else Zq.zero - proj (256 + i - k0) x.`2) )
          else
            ci -
            proj k x.`1 *
            proj (256 + (i - k))
              (Array256.init
                 (fun (k0 : int) => if 0 <= i - k0 then proj (i - k0) x.`2 else Zq.zero - proj (256 + i - k0) x.`2))) Zq.zero (
               iota_ 0 256)) =
    (fun (x : poly * poly) =>
        foldr
               (fun (k : int) (ci : coeff) =>
                   ci + proj k x.`1 * proj k x.`2) Zq.zero (
               iota_ 0 256)).
+ apply fun_ext => pp. 
  apply eq_in_foldr => //.
  move => kk; rewrite mem_iota /= => kkb;apply fun_ext => cc.
  by case  (0 <= i - kk) => /= *; rewrite initiE /=;1,3:smt();[ rewrite ifT /# | rewrite ifF 1:/# => /=; smt(@Zq) ]. 

have /= <- := dmap_dprod_comp (dlist d1 256) 
                        (dlist d2 256) 
                        (Array256.of_list witness)
                         (Array256.of_list witness)
                         (fun (x1 x2 : poly) =>
     foldr (fun (k : int) (ci : coeff) => ci + proj k x1 * proj k x2) Zq.zero (iota_ 0 256)).
have -> : 
    (fun (xy : coeff list * coeff list) =>
     foldr
       (fun (k : int) (ci : coeff) =>
          ci + proj k (Array256.of_list witness xy.`1) * proj k (Array256.of_list witness xy.`2))  Zq.zero (
       iota_ 0 256))
= 
     (fun (xy : coeff list * coeff list) =>
     foldr
       (fun (k : int) (ci : coeff) =>
          ci + nth witness xy.`1 k * nth witness xy.`2 k)  Zq.zero (
       iota_ 0 256)).
+ apply fun_ext => xx; apply eq_in_foldr => //.
 +  move  => kk;rewrite !mem_iota /= => kkb;apply fun_ext => cc;congr =>//.
    rewrite !get_of_list /#.

have H : forall nn, 0 <= nn < 256 => 
   dmap (dlist d1 (nn+1) `*` dlist d2 (nn+1))
  (fun (xy : coeff list * coeff list) =>
     foldr (fun (k : int) (ci : coeff) => ci + nth witness xy.`1 k * nth witness xy.`2 k) Zq.zero (iota_ 0 (nn+1))) =
dmul (nn+1) d1 d2; last by move : (H 255 _) => /=; done.

move => kk; elim /natind:kk.
+ move => n ??; have -> /=: n = 0 by smt().
  rewrite iota1 /=.
  have -> : (fun (xy : coeff list * coeff list) => Zq.zero + nth witness xy.`1 0 * nth witness xy.`2 0)  = 
              (fun (xy : coeff list * coeff list) => nth witness xy.`1 0 * nth witness xy.`2 0)  by apply fun_ext => *;ring.
  have /= -> := dmap_dprod_comp (dlist d1 1) (dlist d2 1 ) (fun l => nth witness l 0) (fun l => nth witness l 0)  (fun (x y : coeff ) =>x * y). 
   rewrite !dlist1 /= !dmap_comp /(\o) /= !dmap_id.
   by rewrite  dmulE // iter1 /= dadd_id // /dmul1. 

move => n? H ?; move : (H _); 1: smt(); pose nn := n+1; move => Hind.
have /= -> := dmulS nn 1;1:smt().
rewrite iotaSr 1:/# /= -cats1. 
have -> : 
  (fun (xy : coeff list * coeff list) =>
     foldr (fun (k : int) (ci : coeff) => ci + nth witness xy.`1 k * nth witness xy.`2 k) Zq.zero (iota_ 0 nn ++ [nn]))=
 (fun (xy : coeff list * coeff list) =>
     foldr (fun (k : int) (ci : coeff) => ci + nth witness xy.`1 k * nth witness xy.`2 k) Zq.zero (iota_ 0 nn) +
            nth witness xy.`1 nn * nth witness xy.`2 nn).
+ apply fun_ext => pp;rewrite (foldr_rem nn) //= => *; 1: by ring.
  + by smt(mem_iota mem_cat).
  have -> : rem nn (iota_ 0 nn ++ [nn]) = iota_ 0 nn; last  by done.
  rewrite rem_filter;1: by apply cat_uniq; rewrite iota_uniq /=;smt(mem_iota).
  rewrite filter_cat. 
  by rewrite (eq_in_filter_pred0 _ [nn]) /= 1:/# eq_in_filter_predT;smt(mem_iota).
 
rewrite !(dlistSr _ nn) 1..2:/# /=.  
  rewrite !(dmap_dprodL (dlist d1 nn `*` d1)) !dmap_comp /(\o) /=. 
  have -> := dmap_dprodR (dlist d1 nn `*` d1) (dlist d2 nn `*` d2) (fun (xy : coeff list * coeff) => rcons xy.`1 xy.`2).
  rewrite !dmap_comp /(\o) /=. 

  pose F := fun (xs : coeff list) (x : coeff) (ys : coeff list) (y : coeff) =>
    (foldr
       (fun (k : int) (ci : coeff) =>
          ci + (nth witness xs k * nth witness ys k)) Zq.zero (
       iota_ 0 nn)) + x * y.
have Hcr := dprod_cross  (dlist d1 nn) d1 (dlist d2 nn) d2 F.
have -> : 
  dmap (dlist d1 nn `*` d1 `*` (dlist d2 nn `*` d2))
  (fun (x : (coeff list * coeff) * (coeff list * coeff)) =>
     foldr (fun (k : int) (ci : coeff) => ci + nth witness (rcons x.`1.`1 x.`1.`2) k * nth witness (rcons x.`2.`1 x.`2.`2) k) Zq.zero
       (iota_ 0 nn) +
     nth witness (rcons x.`1.`1 x.`1.`2) nn * nth witness (rcons x.`2.`1 x.`2.`2) nn)
  =   
  dlet (dlist d1 nn `*` d1)
       (fun (ab : coeff list * coeff) =>
          dmap (dlist d2 nn `*` d2) (fun (cd : coeff list * coeff) => F ab.`1 ab.`2 cd.`1 cd.`2)). 
+ rewrite /F.
  rewrite dprod_dlet /=.
  rewrite dmap_dlet.
  apply in_eq_dlet => pp Hpp /=.
  rewrite dmap_dlet /= /dmap. 
  apply in_eq_dlet => vv Hvv /=.
  rewrite /(\o) /=. 
  rewrite dlet_dunit dmap_dunit /=;apply eq_distr => cc.
  rewrite !dunit1E /=.  
  rewrite supp_dprod supp_dlist  /= in Hpp; 1: smt(). 
  rewrite supp_dprod supp_dlist  /= in Hvv; 1: smt(). 
  congr;congr;congr=>//; last by smt(nth_rcons).
  by apply  eq_in_foldr; smt(nth_rcons mem_iota).

rewrite Hcr -Hind /dadd. 
rewrite (dmap_dprodL  (dlist d1 nn `*` dlist d2 nn) _
     (fun (xy : coeff list * coeff list) =>
        foldr (fun (k : int) (ci : coeff) => ci + nth witness xy.`1 k * nth witness xy.`2 k) Zq.zero (iota_ 0 nn))) /=  dmap_comp /(\o) /=.
rewrite dmap_dprodE /=.
by apply in_eq_dlet => xx ? /=;rewrite dmulE //= /dmul1 iter1 /= dadd_id /= dmap_comp /= /(\o) /F.
qed. 

import MLKEM_Matrix. 

lemma dcsub_dcadd_commute d1 d2 d3 d4 :
  dcadd (dcsub d1 d2) (dcsub d3 d4) =
   dcsub (dcadd d1 d3) (dcadd d2 d4).
rewrite /dcadd /dcsub /dadd !dmap_dprod !dmap_comp /(\o) /=. 
have := dprod_cross d1 d2 d3 d4 
  (fun (a b c d : coeff) => a - b + (c - d)).
rewrite (dmap_dprodE (d1 `*` d2)) => /=.
rewrite (dmap_dprodE (d1 `*` d3)) => /=.
move => ->.
congr;rewrite fun_ext => ac;congr;rewrite fun_ext => bd.
by ring.
qed.

lemma dotp_tail (d1 d2 : coeff distr) (i : int): 
  is_lossless d1 =>
  is_lossless d2 =>
  0 <= i < 256 =>
   dmap (dmap ((dvector (darray256 d1)) `*` (dvector (darray256 d2))) (fun (vv : polyvec*polyvec) => MLWE_.(`<*>`) vv.`1 vv.`2)) (proj i) = 
     dcsub (dmul (kvec*(i+1)) d1 d2) (dmul (kvec*(256 - i - 1)) d1 d2).
move => d1ll d2ll bi.
rewrite /MLWE_.(`<*>`) /dvector /size.
have := gt0_kvec.
pose kk := kvec - 1.
have ->/= : kvec = kk + 1 by auto.
have : kk < kvec by smt().
elim /natind:kk. 
+ move => n ???; have -> /= : n=0 by smt().
  rewrite /range /= iota1.
  have -> : (fun (vv : polyvec * polyvec) => Big.BAdd.big predT (fun (i0 : int) => (vv.`1.[i0] &* vv.`2.[i0])) [0]) =
    (fun (vv : polyvec * polyvec) => vv.`1.[0] &* vv.`2.[0])
   by rewrite fun_ext => *;apply MLWE_.Matrix_.Big.BAdd.big_seq1.
  rewrite  /dvector -!dlist_djoin; 1..2:smt(gt0_kvec).
  rewrite !dlist1 (dmap_comp _ _ (dR d1))  /(\o) /=. 
  rewrite (dmap_comp _ _ (dR d2))  /(\o) /= dmap_dprod /= dmap_comp  /(\o) .
  rewrite (dmap_comp _ _ (dR d1 `*` dR d2)) /(\o) /= .
  have -> : (fun (x : poly * poly) => proj i ((offunv (nth witness [x.`1])).[0] &* (offunv (nth witness [x.`2])).[0])) =
    (fun (x : poly * poly) => proj i (x.`1 &* x.`2)) by
      apply fun_ext => *;congr; smt(offunvE gt0_kvec).
  have := (dmul_poly_tail d1 d2 i d1ll d2ll bi). 
  by rewrite dmap_comp.

move => n ?; pose nn := n+1; move => H ??.
move : (H _ _); 1,2: smt(). 
rewrite -!dlist_djoin; 1..4:smt(gt0_kvec).
move => Hind.
rewrite dmulS;1,2:smt().
rewrite !(dlistS _ nn) 1..2:/# /=.
pose F := fun (x : poly) (xs : poly list) (y : poly) (ys : poly list) =>
             (MLWE_.Matrix_.Big.BAdd.bigi predT (fun (i0 : int) => nth witness xs i0 &* nth witness ys i0) 0 (nn)) &+ (x &* y).
have Hcr := dprod_cross (dR d1) (dlist (dR d1) nn) (dR d2) (dlist (dR d2) nn) F.
have -> : 
  (dmap
     (dmap (dmap (dR d1 `*` dlist (dR d1) nn) (fun (xy : MLKEM_Matrix.R * MLKEM_Matrix.R list) => xy.`1 :: xy.`2))
        (fun (xs : MLKEM_Matrix.R list) => offunv (nth witness xs)) `*`
      dmap (dmap (dR d2 `*` dlist (dR d2) nn) (fun (xy : MLKEM_Matrix.R * MLKEM_Matrix.R list) => xy.`1 :: xy.`2))
        (fun (xs : MLKEM_Matrix.R list) => offunv (nth witness xs)))
     (fun (vv : polyvec * polyvec) =>
        MLWE_.Matrix_.Big.BAdd.bigi predT (fun (i0 : int) => vv.`1.[i0] &* vv.`2.[i0]) 0 (nn + 1))) = 
    dlet (dR d1 `*` dlist (dR d1) nn)
       (fun (ab : poly * poly list) =>
          dmap (dR d2 `*` dlist (dR d2) nn) (fun (cd : poly * poly list) => F ab.`1 ab.`2 cd.`1 cd.`2)) .
+ rewrite /F.
  rewrite !dmap_comp /(\o) /=.
  rewrite dprod_dlet /=.
  rewrite dlet_dmap /= dmap_dlet; congr.
  rewrite fun_ext => pp /=.
  rewrite dlet_dmap /= dmap_dlet /= /dmap;congr.
  rewrite /(\o);rewrite fun_ext => vv.
  rewrite dlet_dunit dmap_dunit;congr => /=.
  rewrite MLWE_.Matrix_.Big.BAdd.big_int_recl 1:/# /=. 
  rewrite MLWE_.Matrix_.ZR.addrC /ZR.(+); congr;last by smt(offunvE gt0_kvec).
  apply MLWE_.Matrix_.Big.BAdd.eq_big_seq => x;rewrite /range mem_iota => Hx /=.
  by smt(offunvE gt0_kvec).
rewrite Hcr.
have := dmap_dprodE_swap  (dlist (dR d1) nn `*` dlist (dR d2) nn)  (dR d1 `*` dR d2)
         (fun (x :  (poly list * poly list) *  (poly * poly) ) =>
              F x.`2.`1 x.`1.`1 x.`2.`2 x.`1.`2).
rewrite /F /= => <-.
have /= := dmap_dprod (dlist (dR d1) nn `*` dlist (dR d2) nn) (dR d1 `*` dR d2)
     (fun (xsys : poly list * poly list) => MLWE_.Matrix_.Big.BAdd.bigi predT (fun (i0 : int) => nth witness xsys.`1 i0 &* nth witness xsys.`2 i0 ) 0 nn ) (fun (xy : poly * poly) => xy.`1 &* xy.`2) .

have -> : 
 (dmap (dlist (dR d1) nn `*` dlist (dR d2) nn `*` (dR d1 `*` dR d2))
     (fun (x : (poly list * poly list) * (poly * poly)) =>
        MLWE_.Matrix_.Big.BAdd.bigi predT (fun (i0 : int) => nth witness x.`1.`1 i0 &* nth witness x.`1.`2 i0) 0 nn &+ (x.`2.`1 &* x.`2.`2))) 
 = dmap (dmap (dlist (dR d1) nn `*` dlist (dR d2) nn `*` (dR d1 `*` dR d2))
  (fun (xy : (poly list * poly list) * (poly * poly)) =>
     (MLWE_.Matrix_.Big.BAdd.bigi predT (fun (i0 : int) => nth witness xy.`1.`1 i0  &* nth witness xy.`1.`2 i0) 0 nn, xy.`2.`1 &* xy.`2.`2))) (fun (xy : poly * poly) => xy.`1 &+ xy.`2) by  
    rewrite dmap_comp /= /(\o) //=.

move => <-.
have -> := dadd_poly_tail (dmap (dlist (dR d1) nn `*` dlist (dR d2) nn)
        (fun (xsys : poly list * poly list) =>
           MLWE_.Matrix_.Big.BAdd.bigi predT (fun (i0 : int) => nth witness xsys.`1 i0 &* nth witness xsys.`2 i0) 0 nn)) (dmap (dR d1 `*` dR d2) (fun (xy : poly * poly) => xy.`1 &* xy.`2)) (dcsub (dmul (nn * (i + 1)) d1 d2) (dmul (nn * (255 - i)) d1 d2)) (dcsub (dmul (i + 1) d1 d2) (dmul (255 - i) d1 d2)) i bi.
+ rewrite  -Hind.  
  congr. 
  have /= <- := dmap_dprod_comp (dlist (dR d1) nn) (dlist (dR d2) nn) (fun (xs : MLKEM_Matrix.R list) => offunv (nth witness xs)) (fun (xs : MLKEM_Matrix.R list) => offunv (nth witness xs)) (fun (vv1 vv2 : polyvec) => MLWE_.Matrix_.Big.BAdd.bigi predT (fun (i0 : int) => vv1.[i0] &* vv2.[i0]) 0 nn).
  congr; apply fun_ext => v.
  apply MLWE_.Matrix_.Big.BAdd.eq_big_seq => /=.
  move => ii; rewrite /range;smt(mem_iota offunvE).
+ by apply dmul_poly_tail.
rewrite dcsub_dcadd_commute.
rewrite /dcadd;congr.
by rewrite (dmulS (nn) (255-i)) 1,2:/#.
qed.

lemma dotp_tail_good (d1 d2 : coeff distr) (i : int): 
  is_good d1 =>
  is_good d2 =>
  0 <= i < 256 =>
   dmap (dmap ((dvector (darray256 d1)) `*` (dvector (darray256 d2))) (fun (vv : polyvec*polyvec) => MLWE_.(`<*>`) vv.`1 vv.`2)) (proj i) = dmul (kvec*256) d1 d2.
move => G1 G2 bi.
rewrite /MLWE_.(`<*>`) /dvector /size.
have := gt0_kvec.
pose kk := kvec - 1.
have ->/= : kvec = kk + 1 by auto.
have : kk < kvec by smt().
elim /natind:kk. 
+ move => n ???; have -> /= : n=0 by smt().
  rewrite /range /= iota1.
  have -> : (fun (vv : polyvec * polyvec) => Big.BAdd.big predT (fun (i0 : int) => (vv.`1.[i0] &* vv.`2.[i0])) [0]) =
    (fun (vv : polyvec * polyvec) => vv.`1.[0] &* vv.`2.[0])
   by rewrite fun_ext => *;apply MLWE_.Matrix_.Big.BAdd.big_seq1.
  rewrite  /dvector -!dlist_djoin; 1..2:smt(gt0_kvec).
  rewrite !dlist1 (dmap_comp _ _ (dR d1))  /(\o) /=. 
  rewrite (dmap_comp _ _ (dR d2))  /(\o) /= dmap_dprod /= dmap_comp  /(\o) .
  rewrite (dmap_comp _ _ (dR d1 `*` dR d2)) /(\o) /= .
  have -> : (fun (x : poly * poly) => proj i ((offunv (nth witness [x.`1])).[0] &* (offunv (nth witness [x.`2])).[0])) =
    (fun (x : poly * poly) => proj i (x.`1 &* x.`2)) by
      apply fun_ext => *;congr; smt(offunvE gt0_kvec).
  have := (dmul_poly_tail_good d1 d2 i G1 G2 bi). 
  by rewrite dmap_comp.

move => n ?; pose nn := n+1; move => H ??.
move : (H _ _); 1,2: smt(). 
rewrite -!dlist_djoin; 1..4:smt(gt0_kvec).
move => Hind.
rewrite dmulS;1,2:smt().
rewrite !(dlistS _ nn) 1..2:/# /=.
pose F := fun (x : poly) (xs : poly list) (y : poly) (ys : poly list) =>
             (MLWE_.Matrix_.Big.BAdd.bigi predT (fun (i0 : int) => nth witness xs i0 &* nth witness ys i0) 0 (nn)) &+ (x &* y).
have Hcr := dprod_cross (dR d1) (dlist (dR d1) nn) (dR d2) (dlist (dR d2) nn) F.
have -> : 
  (dmap
     (dmap (dmap (dR d1 `*` dlist (dR d1) nn) (fun (xy : MLKEM_Matrix.R * MLKEM_Matrix.R list) => xy.`1 :: xy.`2))
        (fun (xs : MLKEM_Matrix.R list) => offunv (nth witness xs)) `*`
      dmap (dmap (dR d2 `*` dlist (dR d2) nn) (fun (xy : MLKEM_Matrix.R * MLKEM_Matrix.R list) => xy.`1 :: xy.`2))
        (fun (xs : MLKEM_Matrix.R list) => offunv (nth witness xs)))
     (fun (vv : polyvec * polyvec) =>
        MLWE_.Matrix_.Big.BAdd.bigi predT (fun (i0 : int) => vv.`1.[i0] &* vv.`2.[i0]) 0 (nn + 1))) = 
    dlet (dR d1 `*` dlist (dR d1) nn)
       (fun (ab : poly * poly list) =>
          dmap (dR d2 `*` dlist (dR d2) nn) (fun (cd : poly * poly list) => F ab.`1 ab.`2 cd.`1 cd.`2)) .
+ rewrite /F.
  rewrite !dmap_comp /(\o) /=.
  rewrite dprod_dlet /=.
  rewrite dlet_dmap /= dmap_dlet; congr.
  rewrite fun_ext => pp /=.
  rewrite dlet_dmap /= dmap_dlet /= /dmap;congr.
  rewrite /(\o);rewrite fun_ext => vv.
  rewrite dlet_dunit dmap_dunit;congr => /=.
  rewrite MLWE_.Matrix_.Big.BAdd.big_int_recl 1:/# /=. 
  rewrite MLWE_.Matrix_.ZR.addrC /ZR.(+); congr;last by smt(offunvE gt0_kvec).
  apply MLWE_.Matrix_.Big.BAdd.eq_big_seq => x;rewrite /range mem_iota => Hx /=.
  by smt(offunvE gt0_kvec).
rewrite Hcr.
have := dmap_dprodE_swap  (dlist (dR d1) nn `*` dlist (dR d2) nn)  (dR d1 `*` dR d2)
         (fun (x :  (poly list * poly list) *  (poly * poly) ) =>
              F x.`2.`1 x.`1.`1 x.`2.`2 x.`1.`2).
rewrite /F /= => <-.
have /= := dmap_dprod (dlist (dR d1) nn `*` dlist (dR d2) nn) (dR d1 `*` dR d2)
     (fun (xsys : poly list * poly list) => MLWE_.Matrix_.Big.BAdd.bigi predT (fun (i0 : int) => nth witness xsys.`1 i0 &* nth witness xsys.`2 i0 ) 0 nn ) (fun (xy : poly * poly) => xy.`1 &* xy.`2) .

have -> : 
 (dmap (dlist (dR d1) nn `*` dlist (dR d2) nn `*` (dR d1 `*` dR d2))
     (fun (x : (poly list * poly list) * (poly * poly)) =>
        MLWE_.Matrix_.Big.BAdd.bigi predT (fun (i0 : int) => nth witness x.`1.`1 i0 &* nth witness x.`1.`2 i0) 0 nn &+ (x.`2.`1 &* x.`2.`2))) 
 = dmap (dmap (dlist (dR d1) nn `*` dlist (dR d2) nn `*` (dR d1 `*` dR d2))
  (fun (xy : (poly list * poly list) * (poly * poly)) =>
     (MLWE_.Matrix_.Big.BAdd.bigi predT (fun (i0 : int) => nth witness xy.`1.`1 i0  &* nth witness xy.`1.`2 i0) 0 nn, xy.`2.`1 &* xy.`2.`2))) (fun (xy : poly * poly) => xy.`1 &+ xy.`2) by  
    rewrite dmap_comp /= /(\o) //=.
move => <-.
have -> := dadd_poly_tail (dmap (dlist (dR d1) nn `*` dlist (dR d2) nn)
        (fun (xsys : poly list * poly list) =>
           MLWE_.Matrix_.Big.BAdd.bigi predT (fun (i0 : int) => nth witness xsys.`1 i0 &* nth witness xsys.`2 i0) 0 nn)) (dmap (dR d1 `*` dR d2) (fun (xy : poly * poly) => xy.`1 &* xy.`2)) (dmul (nn * 256) d1 d2) (dmul 256 d1 d2) i bi.
+ rewrite  -Hind.  
  congr. 
  have /= <- := dmap_dprod_comp (dlist (dR d1) nn) (dlist (dR d2) nn) (fun (xs : MLKEM_Matrix.R list) => offunv (nth witness xs)) (fun (xs : MLKEM_Matrix.R list) => offunv (nth witness xs)) (fun (vv1 vv2 : polyvec) => MLWE_.Matrix_.Big.BAdd.bigi predT (fun (i0 : int) => vv1.[i0] &* vv2.[i0]) 0 nn).
  congr; apply fun_ext => v.
  apply MLWE_.Matrix_.Big.BAdd.eq_big_seq => /=.
  move => ii; rewrite /range;smt(mem_iota offunvE).
+ by apply dmul_poly_tail_good.
done. 
qed.


lemma union_bound d t :
  mu d (fun (x : poly) => ! (under_noise_bound x t)) <= 
    StdBigop.Bigreal.BRA.big predT (fun k => mu d (fun (x : poly) => t < absZq x.[k])) (iota_ 0 256).
proof.
have : forall n, 0<=n<=256 =>
  mu d (fun (x : poly) => ! (all (fun (k : int) => absZq (proj k x) <= t) (iota_ 0 n))) <= 
    StdBigop.Bigreal.BRA.big predT (fun k => mu d (fun (x : poly) => t < absZq x.[k])) (iota_ 0 n); last first.
+ move => Hn; move : (Hn 256 _) => //.

move => n.
elim /natind:n. 
  + move => n H H0; have -> /= : n = 0 by smt(). 
    rewrite iota0 //= StdBigop.Bigreal.BRA.big_nil.
    rewrite mu0 /#.
  + move => n H Hind Hn.
    move : (Hind _); 1: by smt().
    move => Hindd. rewrite {2}iotaSr 1:/# /= StdBigop.Bigreal.BRA.big_rcons /= /(predT n) /=.
    have ->  : (fun (x : poly) => ! all (fun (kk : int) => absZq x.[kk] <= t) (iota_ 0 (n+1))) =
     predU (fun (x : poly) => ! all (fun (kk : int) => absZq x.[kk] <=t) (iota_ 0 n)) (fun (x : poly) =>  !(absZq x.[n] <= t)). rewrite /predU fun_ext => p /=;by smt(@List).
    rewrite mu_or. 
    have  : mu d (fun (x : poly) => ! absZq x.[n] <=t)  = mu d (fun (x : poly) => t < absZq x.[n]) by congr; smt(). 
move : Hindd.
pose a := mu d (fun (x : poly) => ! all (fun (kk : int) => absZq x.[kk] <= t) (iota_ 0 n)).
pose b:= StdBigop.Bigreal.BRA.big predT
  (fun (k : int) => mu d (fun (x : poly) => t < absZq x.[k])) (
  iota_ 0 n).
pose c:= mu d (fun (x : poly) => t < absZq x.[n]) .
pose dd:=mu d
  (predI (fun (x : poly) => ! all (fun (kk : int) => absZq x.[kk] <= t) (iota_ 0 n))
     (fun (x : poly) => ! absZq x.[n] <= t)).
  smt(mu_bounded).
qed.

lemma union_bound_cst d p t :
  (forall i, 0 <= i < 256 => 
     mu d (fun (x : poly) => (t < absZq x.[i])) = p) =>
  mu d (fun (x : poly) => ! (all (fun (kk : int) => absZq x.[kk] <= t) (iota_ 0 256))) <= 256%r * p.
move => Hi.
have //= := union_bound d t.
have -> : StdBigop.Bigreal.BRA.big predT (fun (k : int) => mu d (fun (x : poly) => t < absZq (proj k x))) (iota_ 0 256)  = 256%r * p; last by done.
rewrite (StdBigop.Bigreal.BRA.eq_big_seq _ (fun _ => p)). 
+ move => x; rewrite mem_iota /=  => *; apply Hi; smt().
rewrite StdBigop.Bigreal.BRA.big_const /= count_predT size_iota /max /= - StdBigop.Bigreal.Num.Domain.AddMonoid.iteropE /= -StdOrder.RealOrder.Domain.intmulpE //= RField.intmulr;ring. 
qed.

(* These instantiated lemmas allow bounding the probability of  decryption error in a provably secure way.
  Uncommenting the prints permits seeing the content below
  produced by EasyCrypt 


print correctness_provable.
print CB_Provable.
print noise_exp_no_rounding.
print noise_exp_u_uni.

lemma correctness_provable:
  forall (A(H : PKE_ROM.POracle) <: PKE_ROM.CORR_ADV{-MLWE_.MLWE_ROM.RO.RO, -MLWE_.MLWE_ROM.RO.LRO, -CB}) &m
    (cu_bound : int) (failprob1 failprob2 : real),
    (forall (O <: MLWE_.MLWE_ROM.RO.RO), islossless O.get => islossless A(O).find) =>
    Pr[CB_Provable.main_uni(cu_bound) @ &m : ! under_noise_bound CB_Provable.n1 (max_noise - cv_bound_max - cu_bound)] <=
    failprob1 =>
    Pr[CB_Provable.main_uni(cu_bound) @ &m : ! under_noise_bound CB_Provable.n2 cu_bound] <= failprob2 =>
    Pr[PKE_ROM.Correctness_Adv(MLWE_.MLWE_ROM.RO.LRO, MLWE_PKE, A).main() @ &m : res] <=
    failprob1 + failprob2 + epsmlwe.

module CB_Provable = {
  var n1 : ZR.t
  
  var n2 : ZR.t
    
  proc main_uni(cu_bound : int) : bool = {
    var r : MLKEM_Matrix.vector;
    var s : MLKEM_Matrix.vector;
    var e : MLKEM_Matrix.vector;
    var e1 : MLKEM_Matrix.vector;
    var e2 : MLKEM_Matrix.R;
    var u : MLKEM_Matrix.vector;
    
    r <$ MLWE_.dshort;
    s <$ MLWE_.dshort;
    e <$ MLWE_.dshort;
    e1 <$ MLWE_.dshort;
    e2 <$ dshort_R;
    u <$ MLWE_.duni;
    CB_Provable.n1 <- noise_exp_no_rounding s e r e1 e2;
    CB_Provable.n2 <- noise_exp_u_uni s u;
    
    return
      ! under_noise_bound CB_Provable.n1 (max_noise - cv_bound_max - cu_bound) \/
      ! under_noise_bound CB_Provable.n2 cu_bound;
  }
}.


op noise_exp_no_rounding (s e r e1 : vector) (e2 : ZR.t) : ZR.t = (e `<*>` r) &- (s `<*>` e1) &+ e2.

op noise_exp_u_uni (s u : vector) : ZR.t = let cu = rnd_err_u u in ZR.zeror &- (s `<*>` cu).

*)

(* To compute the bound based on this lemma, we need to compute two probabilities *)

import MLWE_.

op dround_elem : coeff distr = dmap duni_elem (compress_err ubits).

op dround_polyvec : polyvec distr = 
    MLWE_.Matrix_.Matrix.dvector (darray256 dround_elem).

module CB_Provable_Grad = {

  proc main_grad1(cu_bound : int) : bool = {
    var ers, er,se1s, se1,  e2,n;     
    ers <$ MLWE_.dshort `*` MLWE_.dshort;
    er <- ers.`1 `<*>` ers.`2;
    se1s <$ dshort `*` MLWE_.dshort;
    se1 <- se1s.`1 `<*>` se1s.`2;
    e2 <$ dshort_R;
    n <- (er &- se1 &+ e2)%MLWE_;
    return ! under_noise_bound n (max_noise - cv_bound_max - cu_bound);
  }

  proc main_grad2(cu_bound : int) : bool = {
    var scus,n;     
    scus <$ MLWE_.dshort `*` dround_polyvec;
    n <- scus.`1 `<*>` scus.`2;
    return ! under_noise_bound n (cu_bound);
  }

}.

op provable_distr1_gradual  =
  let er = dmap (MLWE_.dshort `*` MLWE_.dshort) (fun (vv : polyvec * polyvec) => vv.`1 `<*>` vv.`2) in
  let se1 = dmap (MLWE_.dshort `*` dshort) (fun (vv : polyvec * polyvec) =>vv.`1 `<*>` vv.`2) in 
  let erse1 = dmap (er `*` se1) (fun (vv : poly * poly) => vv.`1 &-  vv.`2) in 
      dmap (erse1 `*` dshort_R) (fun (vv : poly * poly) =>  Rq.(&+) vv.`1 vv.`2). 

op provable_distr2_gradual  =
  dmap (MLWE_.dshort `*` dround_polyvec) (fun (vv : polyvec * polyvec) => vv.`1 `<*>` vv.`2).

lemma provable_grad_distr1 &m cub:
 Pr [ CB_Provable_Grad.main_grad1(cub) @ &m : res ] =
    mu (provable_distr1_gradual)
     (fun (x : poly) => ! under_noise_bound x (max_noise - cv_bound_max - cub)).
byphoare (: cu_bound = cub ==> _) => //;proc => /=. 
  rndsem* 0; rnd => /=. 
  conseq (: _ ==> mu
    (dlet (dshort `*` dshort)
       (fun (ers0 : MLKEM_Matrix.vector * MLKEM_Matrix.vector) =>
          dlet (dshort `*` dshort)
            (fun (se1s0 : MLKEM_Matrix.vector * MLKEM_Matrix.vector) =>
               dmap dshort_R (MLWE_.(&+) ((ers0.`1 `<*>` ers0.`2) &- (se1s0.`1 `<*>` se1s0.`2))))))
    (fun (x : ZR.t) => ! under_noise_bound x (max_noise - cv_bound_max - cu_bound)) =
          mu provable_distr1_gradual (fun (x : poly) => ! under_noise_bound x (max_noise - cv_bound_max - cub))); 1: by move => &hr <-;done.
  auto => &hr <-;rewrite /provable_distr1_gradual /=. 
  congr.
pose D1 := dshort `*` dshort.
pose D2 := dshort_R.
rewrite (dmap_dprodL D1) dmap_comp. 
rewrite (dmap_dprodE D1) /(\o) /=.
rewrite (dmap_dprodE _ D2) /= (dlet_dlet D1) /=. 
congr; rewrite fun_ext => er.
rewrite dmap_comp /(\o) /=.
rewrite dlet_dmap  /(\o) /=.
congr; rewrite fun_ext => se1 /=.
congr; rewrite fun_ext => e2 /=.
smt(@Rq).
qed.

lemma provable_grad_distr2 &m cub:
 Pr [ CB_Provable_Grad.main_grad2(cub) @ &m : res ] =
    mu (provable_distr2_gradual)
     (fun (x : poly) => ! under_noise_bound x (cub)).
byphoare (: cu_bound = cub ==> _) => //;proc => /=. 
  rndsem* 0; rnd => /=. 
  conseq (: _ ==> mu
    (dmap (dshort `*` dround_polyvec)
       (fun (scus0 : MLKEM_Matrix.vector * MLKEM_Matrix.vector) => scus0.`1 `<*>` scus0.`2))
    (fun (x : ZR.t) => ! under_noise_bound x cu_bound) =
          mu provable_distr2_gradual (fun (x : poly) => ! under_noise_bound x cub)); 1: by move => &hr <-;done.
  by auto. 
qed.


lemma provables_match1 cub &m :
Pr[CB_Provable.main_uni(cub) @ &m : ! under_noise_bound CB_Provable.n1 (max_noise - cv_bound_max - cub)] = 
Pr [ CB_Provable_Grad.main_grad1(cub) @ &m : res ].
byequiv => //;proc.
swap {1} 3 -2. 
seq 2 1 : (#pre /\ e{1} = ers{2}.`1 /\ r{1} = ers{2}.`2).
+ conseq />;rndsem {1} 0;rnd;auto => />.
  have <- : (dshort `*` dshort) =
    (dlet dshort (fun (e : polyvec) => dmap dshort (fun (r : polyvec) => (e, r)))); last by split;smt().
  by rewrite (dprod_dlet dshort ) /dmap /(\o) /=.
swap {2} 2 -1.
seq 2 1 : (#pre /\ s{1} = se1s{2}.`1 /\ e1{1} = se1s{2}.`2).
+ conseq />;rndsem {1} 0;rnd;auto => />.
  have <- : (dshort `*` dshort) =
    (dlet dshort (fun (e : polyvec) => dmap dshort (fun (r : polyvec) => (e, r)))); last by split;smt().
  by rewrite (dprod_dlet dshort ) /dmap /(\o) /=.
wp;rnd{1}.
by auto => />;smt(duni_ll).
qed.

lemma cheat_rewrite s u :
  noise_exp_u_uni s u =  ZR.zeror &- (s `<*>` (rnd_err_u u)) by auto. 
lemma provables_match2 cub &m :
Pr[CB_Provable.main_uni(cub) @ &m : ! under_noise_bound CB_Provable.n2 cub] = 
Pr [ CB_Provable_Grad.main_grad2(cub) @ &m : res ].
byequiv => //;proc.
swap {1} [3..5] -2.
seq 4 0 : #pre;1: by auto;smt(dshort_ll dshort_R_ll). 
swap {1} 4 -1;wp 3 2. 
proc rewrite {1} 3 cheat_rewrite.
alias {1} 3 aa = rnd_err_u u.
wp 3 2. 
transitivity {1} { s <$ dshort; u <$ duni; aa <- rnd_err_u u; }
   ( cu_bound{2} = cub /\ cu_bound{1} = cub ==>
       ={s} /\    aa{2} = rnd_err_u u{1})
   (cu_bound{2} = cub /\ cu_bound{1} = cub ==>
       ! under_noise_bound (ZR.zeror &- (s{1} `<*>` aa{1})) cub <=> ! under_noise_bound n{2} cu_bound{2}). smt(). smt().  auto => />. 

seq 3 1: (#pre /\ s{1} = scus.`1{2} /\ aa{1} = scus.`2{2}).
rndsem* {1} 0; rnd;  auto => />.
have -> /= : dshort `*` dround_polyvec =
  (dlet dshort (fun (s : MLKEM_Matrix.vector) => dmap duni (fun (u : MLKEM_Matrix.vector) => (s, rnd_err_u u)))); last by done. 
rewrite (dprod_dlet dshort).
congr;rewrite fun_ext => s.
rewrite /noise_exp_u_uni /dround_poly /duni /dround_polyvec /dround_elem /= /duni_R /rnd_err_u /compress_poly_err.
rewrite /dvector -!dlist_djoin;1,2: smt(gt0_kvec). 
rewrite !dmap_comp /(\o) /= /darray256 !dlist_dmap !dmap_comp /(\o).
rewrite dlet_dmap /= dlet_dunit /=.
apply eq_dmap_in => x; rewrite supp_dlist;1:smt(gt0_kvec).
move => Hx /=. 
rewrite /mapv /=.
apply eq_vectorP => kk kkr.
rewrite !offunvE 1,2:/# /= offunvK /vclamp /= kkr /= (nth_map witness);1: by rewrite size_map 1:/#.
apply Array256.tP => ii iir.
rewrite get_of_list //= mapiE //= !(nth_map witness) 1:/#. 
move : Hx; rewrite allP => [# Hx1 Hx2].
move : (Hx2 (nth witness x kk) _). smt(@List). rewrite supp_dlist. smt(). smt(). smt(). rewrite get_of_list /#. 

auto => /> &2; rewrite /under_noise_bound !allP /=.
pose n := (scus{2}.`1 `<*>` scus{2}.`2).  
split=>H i ib; move : (H i ib); 
rewrite /ZR.([-]) /ZR.(+) /Rq.zero /= /Rq.(&-) /Rq.(&+) /= map2E initiE 1:/# /= mapiE 1:/# /= /Array256.create initiE 1:/# /=;
 smt(StdOrder.IntOrder.normrN @Zq).
qed.

lemma provable_distr1_i i :
  0 <= i < 256 =>
  dmap (provable_distr1_gradual) (fun (p : poly) => p.[i]) =
   dcadd (dcadd (dmul (kvec*256) dshort_elem dshort_elem) 
          (dmul (kvec*256) dshort_elem dshort_elem)) dshort_elem.
move => Hi.
rewrite  /provable_distr1_gradual  /=.
pose dd := dmap
        (dmap (dshort `*` dshort) (fun (vv : polyvec * polyvec) => vv.`1 `<*>` vv.`2) `*`
         dmap (dshort `*` dshort) (fun (vv : polyvec * polyvec) => vv.`1 `<*>` vv.`2))
        (fun (vv : poly * poly) => ZR.(+) vv.`1 (ZR.([-]) vv.`2)).
have -> := dadd_poly_tail dd dshort_R (dmap dd (proj i)) dshort_elem i Hi _ _. 
+ done.
+ by apply eq_distr => cc;rewrite /dshort_R darray_proj ;1,2: by smt(dshort_elem_ll).
congr => /=. 
rewrite /dd; clear dd.
pose dd1 := dmap (dshort `*` dshort) (fun (vv : polyvec * polyvec) => vv.`1 `<*>` vv.`2) .
have -> //:= dsub_poly_tail dd1 dd1 (dmap dd1 (proj i))  (dmap dd1 (proj i)) i Hi _ _.
+ done.
+ done.
+ rewrite add_sub. apply dmul_good;1: smt(gt0_kvec). apply is_good_dshort_elem.
congr. 
+ by rewrite /dd1; apply dotp_tail_good => //; apply is_good_dshort_elem.
rewrite /dd1. 
by apply dotp_tail_good => //; apply is_good_dshort_elem.
qed.

lemma provable_distr2_i i :
  0 <= i < 256 =>
  dmap (provable_distr2_gradual) (fun (p : poly) => p.[i]) =
   dcsub (dmul (kvec * (i + 1)) dshort_elem dround_elem) (dmul (kvec * (256 - i - 1)) dshort_elem dround_elem).
move => ib;rewrite /provable_distr2_gradual.
apply dotp_tail.
apply dshort_elem_ll.
apply dmap_ll. apply duni_elem_ll. smt().
qed.

import ZR.
lemma provable_mu1 &m cub : 
  Pr[CB_Provable.main_uni(cub) @ &m : ! under_noise_bound CB_Provable.n1 (max_noise - cv_bound_max - cub)]<=
  256%r *
   mu (dcadd (dcadd (dmul (kvec*256) dshort_elem dshort_elem) 
          (dmul (kvec*256) dshort_elem dshort_elem)) dshort_elem)
     (fun (c : coeff) => (max_noise - cv_bound_max - cub) < absZq c).
have -> := (provables_match1 cub &m).
have -> := provable_grad_distr1.
apply union_bound_cst => i ib.
have <- := provable_distr1_i i ib.
by rewrite dmapE /= /(\o) /=.
qed.

lemma provable_mu2 &m cub : 
  Pr[CB_Provable.main_uni(cub) @ &m : ! under_noise_bound CB_Provable.n2 (cub)]<=
   StdBigop.Bigreal.BRA.big predT (fun k => mu (dcsub (dmul (kvec * (k + 1)) dshort_elem dround_elem) (dmul (kvec * (256 - k - 1)) dshort_elem dround_elem)) (fun (c : coeff) => cub < absZq c)) (iota_ 0 256).
have -> := (provables_match2 cub &m).
have -> := provable_grad_distr2.
have := union_bound provable_distr2_gradual cub.
have -> : StdBigop.Bigreal.BRA.big predT (fun (k : int) => mu provable_distr2_gradual (fun (x : poly) => cub < absZq (proj k x)))
  (iota_ 0 256) =
   StdBigop.Bigreal.BRA.big predT
  (fun (k : int) =>
     mu (dcsub (dmul (kvec * (k + 1)) dshort_elem dround_elem) (dmul (kvec * (256 - k - 1)) dshort_elem dround_elem))
       (fun (c : coeff) => cub < absZq c)) (iota_ 0 256); last by auto.
apply StdBigop.Bigreal.BRA.eq_big_seq => x.
rewrite mem_iota /= => *.
by rewrite -provable_distr2_i 1:/# dmapE /= /(\o) /= /provable_distr2_gradual dmap_comp /(\o) dmapE /(\o).
qed.

op epsilon_provable1 : real.
op cub_provable : int.
op epsilon_provable2 : real.

axiom epsilon_provable1_result &m :
 Pr[CB_Provable.main_uni(cub_provable) @ &m : ! under_noise_bound CB_Provable.n1 (max_noise - cv_bound_max - cub_provable) ] <= epsilon_provable1.

axiom epsilon_provable2_result &m :
 Pr[CB_Provable.main_uni(cub_provable) @ &m : ! under_noise_bound CB_Provable.n2 (cub_provable) ] <= epsilon_provable2.

lemma correctness_provable_inst (A <: PKE_ROM.CORR_ADV{-MLWE_.MLWE_ROM.RO.RO, -MLWE_.MLWE_ROM.RO.LRO, -CB}) &m epsmlwe:
    (forall (O <: MLWE_.MLWE_ROM.RO.RO), islossless O.get => islossless A(O).find) =>
Bcb2.cu_bound{m} = cub_provable =>
    `|Pr[MLWE(Bcb2).main(true) @ &m : res] - Pr[MLWE(Bcb2).main(false) @ &m : res]| <= epsmlwe =>
    Pr[PKE_ROM.Correctness_Adv(MLWE_.MLWE_ROM.RO.LRO, MLWE_PKE, A).main() @ &m : res] <=
    epsilon_provable1 + epsilon_provable2 + epsmlwe. 
move => All Bst Bb.
by apply (correctness_provable (A) &m cub_provable epsilon_provable1 epsilon_provable2 epsmlwe All Bst Bb (epsilon_provable1_result &m) (epsilon_provable2_result &m)).
qed.

(* These instantiated lemmas allow bounding the probability of
  decryption error when maxing out the rounding term for cv.
  Uncommenting the prints permits seeing the content below
  produced by EasyCrypt 
 

print correctness_max.
print CB1.
print noise_exp_rounding.

lemma correctness_max:
    forall (A(H : PKE_ROM.POracle) <: PKE_ROM.CORR_ADV {-MLWE_.MLWE_ROM.RO.RO, -MLWE_.MLWE_ROM.RO.LRO, -CB}) &m
      (failprob : real),
      (forall (O <: MLWE_.MLWE_ROM.RO.RO), islossless O.get => islossless A(O).find) =>
      Pr[CB1.main(cv_bound_max) @ &m : res] <= failprob =>
      Pr[PKE_ROM.Correctness_Adv(MLWE_.MLWE_ROM.RO.LRO, MLWE_PKE, A).main() @ &m : res] <= failprob. 

module CB1 = {
  proc main(cv_bound : int) : bool = {
    var _A : Matrix.matrix;
    var r : MLKEM_Matrix.vector;
    var s : MLKEM_Matrix.vector;
    var e : MLKEM_Matrix.vector;
    var e1 : MLKEM_Matrix.vector;
    var e2 : MLKEM_Matrix.R;
    var n : ZR.t;
    
    _A <$ MLWE_.duni_matrix;
    r <$ MLWE_.dshort;
    s <$ MLWE_.dshort;
    e <$ MLWE_.dshort;
    e1 <$ MLWE_.dshort;
    e2 <$ dshort_R;
    n <- noise_exp_rounding _A s e r e1 e2;
    
    return ! under_noise_bound n (max_noise - cv_bound);
  }
}.

op noise_exp_rounding (_A : matrix) (s e r e1 : vector) (e2 : ZR.t) : ZR.t =
  let u = trmx _A *^ r + e1 in let cu = rnd_err_u u in (e `<*>` r) &- (s `<*>` e1) &+ e2 &- (s `<*>` cu).
*)

(* To compute the bound based on this lemma, we apply the heuristic
  of taking cu as a polyvec that comes out of rounding a uniform vector, 
  which is the Kyber heuristic *)

op noise_exp_part1_heuristic  (cu s e r e1 : polyvec) (e2 : poly) : poly =
  ((e `<*>` r) &- (s `<*>` e1) &+ e2 &- (s `<*>` cu))%MLWE_.

module CB1_heuristic = {
  proc main(cv_bound : int) : bool = {
    var cu : polyvec;
    var r : polyvec;
    var s : polyvec;
    var e : polyvec;
    var e1 : polyvec;
    var e2 : poly;
    var n : poly;
    
    cu <$ dround_polyvec;
    r <$ MLWE_.dshort;
    s <$ MLWE_.dshort;
    e <$ MLWE_.dshort;
    e1 <$ MLWE_.dshort;
    e2 <$ dshort_R;
    n <- noise_exp_part1_heuristic cu s e r e1 e2;
    
    return ! under_noise_bound n (max_noise - cv_bound);
  }

  proc main_grad(cv_bound : int) : bool = {
    var ers, er, e1cus, e1cu,s,  se1cu,  e2,n;     
    ers <$ MLWE_.dshort `*` MLWE_.dshort;
    er <- ers.`1 `<*>` ers.`2;
    s <$ dshort;
    e1cus <$ MLWE_.dshort `*` dround_polyvec;
    e1cu <- e1cus.`1 + e1cus.`2;
    se1cu <- s `<*>` e1cu;
    e2 <$ dshort_R;
    n <- (er &- se1cu &+ e2)%MLWE_;
    return ! under_noise_bound n (max_noise - cv_bound);
  }


}.

op cb1_heuristic_distr_gradual  =
  let er = dmap (MLWE_.dshort `*` MLWE_.dshort) (fun (vv : polyvec * polyvec) => vv.`1 `<*>` vv.`2) in
  let e1cu = dmap (MLWE_.dshort `*` dround_polyvec) (fun (vv : polyvec * polyvec) => (+) vv.`1 vv.`2) in 
  let se1cu = dmap (MLWE_.dshort `*` e1cu) (fun (vv : polyvec * polyvec) => vv.`1 `<*>` vv.`2) in 
  let erse1cu = dmap (er `*` se1cu) (fun (vv : poly * poly) =>  vv.`1 &- vv.`2) in 
        dmap (erse1cu `*` dshort_R) (fun (vv : poly * poly) =>  Rq.(&+) vv.`1 vv.`2). 


lemma main_grad_distr &m cvb:
 Pr [ CB1_heuristic.main_grad(cvb) @ &m : res ] =
    mu (cb1_heuristic_distr_gradual)
     (fun (x : poly) => ! under_noise_bound x (max_noise - cvb)).
byphoare (: cv_bound = cvb ==> _) => //;proc => /=. 
  rndsem* 0; rnd => /=. 
  conseq (: _ ==> mu
    (dlet (dshort `*` dshort)
       (fun (ers0 : MLKEM_Matrix.vector * MLKEM_Matrix.vector) =>
          dlet dshort
            (fun (s0 : MLKEM_Matrix.vector) =>
               dlet (dshort `*` dround_polyvec)
                 (fun (e1cus0 : MLKEM_Matrix.vector * MLKEM_Matrix.vector) =>
                    dmap dshort_R (MLWE_.(&+) ((ers0.`1 `<*>` ers0.`2) &- (s0 `<*>` e1cus0.`1 + e1cus0.`2)))))))
    (fun (x : ZR.t) => ! under_noise_bound x (max_noise - cv_bound))  =
         mu (cb1_heuristic_distr_gradual) 
         (fun (x : poly) => ! under_noise_bound x 
          (max_noise - cvb))); 1: by move => &hr <-;done.
  auto => &hr <-;rewrite /cb1_heuristic_distr_gradual /=. 
  congr.
  rewrite (dmap_dprodE (dshort) (dmap (dshort `*` dround_polyvec) (fun (vv : polyvec * polyvec) => vv.`1 + vv.`2))) => /=.
pose D1 := dshort `*` dshort.
pose D3 := dshort `*` dround_polyvec.
pose D2 := dshort.
pose D4 := dshort_R.
simplify.
rewrite (dmap_dprodL D1) dmap_comp. 
rewrite (dmap_dprodE D1) /(\o) /=.
rewrite (dmap_dprodE _ D4) /= (dlet_dlet D1) /=. 
congr; rewrite fun_ext => er.
rewrite dmap_dlet  /(\o) /=.
rewrite (dlet_dlet D2).
congr; rewrite fun_ext => s /=.
rewrite !dmap_comp.
rewrite (dlet_dmap D3) => /=.
congr; rewrite fun_ext => e1cu /=.
congr; rewrite fun_ext => e2 /=.
smt(@Rq).
qed.

lemma heuristics_match cvb &m :
Pr [ CB1_heuristic.main(cvb) @ &m : res ] = 
Pr [ CB1_heuristic.main_grad(cvb) @ &m : res ].
byequiv => //;proc.
swap {1} 4 -3. swap {1} 3 -1. 
seq 2 1 : (#pre /\ e{1} = ers{2}.`1 /\ r{1} = ers{2}.`2).
+ conseq />;rndsem {1} 0;rnd;auto => />.
  have <- : (dshort `*` dshort) =
    (dlet dshort (fun (e : polyvec) => dmap dshort (fun (r : polyvec) => (e, r)))); last by split;smt().
  by rewrite (dprod_dlet dshort ) /dmap /(\o) /=.
swap {1} 2 -1; swap {2} 2 -1; seq 1 1 : (#pre /\ ={s}); 1: by auto.
swap {1} 2 -1; swap {2} 2 -1.
seq 2 1 : (#pre /\ e1{1} = e1cus{2}.`1 /\ cu{1} = e1cus{2}.`2).
+ conseq />;rndsem {1} 0;rnd;auto => />.
  have <- : (dshort `*` dround_polyvec) =
    (dlet dshort (fun (e : polyvec) => dmap dround_polyvec (fun (r : polyvec) => (e, r)))); last by split;smt().
  by rewrite (dprod_dlet dshort ) /dmap /(\o) /=.
auto => /> &2 ??;congr;congr.
rewrite /noise_exp_part1_heuristic.
 rewrite  !dotpDr ZR.opprD /=.
 smt(@ZR).
qed.

lemma cb1_heuristic_distr_i i :
  0 <= i < 256 =>
  dmap (cb1_heuristic_distr_gradual) (fun (p : poly) => p.[i]) =
    dcadd (dcsub (dmul (kvec*256) dshort_elem dshort_elem)
            (dcsub (dmul (kvec*(i+1)) dshort_elem (dcadd dshort_elem  dround_elem)) 
                   (dmul (kvec*(255-i)) dshort_elem (dcadd dshort_elem  dround_elem)))) dshort_elem.
move => Hi.
rewrite  /cb1_heuristic_distr_gradual /=.
pose dd := dmap (dmap (dshort `*` dshort) (fun (vv : polyvec * polyvec) => vv.`1 `<*>` vv.`2) `*`
         dmap (dshort `*` dmap (dshort `*` dround_polyvec) (fun (vv : polyvec * polyvec) => vv.`1 + vv.`2))
           (fun (vv : polyvec * polyvec) => vv.`1 `<*>` vv.`2)) (fun (vv : poly * poly) => vv.`1 &- vv.`2).
have -> := dadd_poly_tail dd dshort_R (dmap dd (proj i)) dshort_elem i Hi _ _. 
+ done.
+ by apply eq_distr => cc;rewrite /dshort_R darray_proj ;1,2: by smt(dshort_elem_ll).
congr => /=. 
rewrite /dd; clear dd.
pose dd1 := dmap (dshort `*` dshort) (fun (vv : polyvec * polyvec) => vv.`1 `<*>` vv.`2) .
rewrite dadd_vector /=.

pose dd2 := dmap (dshort `*` dvector (dR (dcadd dshort_elem dround_elem)))
        (fun (vv : polyvec * polyvec) => vv.`1 `<*>` vv.`2).
have -> //:= dsub_poly_tail dd1 dd2 (dmap dd1 (proj i))  (dmap dd2 (proj i)) i Hi _ _.
+ done.
+ done.

congr.
+ by rewrite /dd1; apply dotp_tail_good => //;apply is_good_dshort_elem.
rewrite /dd2. 
apply dotp_tail => //;1:apply dshort_elem_ll.
 apply dmap_ll;apply dprod_ll;split; 1: by smt(dshort_elem_ll).
rewrite dmap_ll;smt(duni_elem_ll).
qed.

import ZR.
lemma CB1_heuristic_mu &m cvb : 
  Pr [ CB1_heuristic.main(cvb) @ &m : res ] <=
   StdBigop.Bigreal.BRA.big predT  (fun k => 
     mu (dcadd (dcsub (dmul (kvec*256) dshort_elem dshort_elem)
            (dcsub (dmul (kvec*(k+1)) dshort_elem (dcadd dshort_elem  dround_elem)) 
                   (dmul (kvec*(255-k)) dshort_elem (dcadd dshort_elem  dround_elem)))) dshort_elem)
                      (fun (c : coeff) => (max_noise - cvb) < absZq c)) (iota_ 0 256).
have -> := (heuristics_match cvb &m).
rewrite main_grad_distr.
have  := union_bound cb1_heuristic_distr_gradual (max_noise - cvb).
have -> : mu (cb1_heuristic_distr_gradual)
  (fun (x : poly) => ! all (fun (kk : int) => absZq x.[kk] <= max_noise - cvb) (iota_ 0 256))
  = mu (cb1_heuristic_distr_gradual) (fun (x : poly) => ! under_noise_bound x (max_noise - cvb)).
+ congr;rewrite fun_ext => x /=.
  rewrite /under_noise_bound allP allP;smt(mem_iota).

have -> :
 StdBigop.Bigreal.BRA.big predT
  (fun (k : int) => mu cb1_heuristic_distr_gradual (fun (x : poly) => max_noise - cvb < absZq (proj k x)))
  (iota_ 0 256) =
  StdBigop.Bigreal.BRA.big predT
  (fun (k : int) =>
     mu
       (dcadd
          (dcsub (dmul (kvec * 256) dshort_elem dshort_elem)
             (dcsub (dmul (kvec * (k + 1)) dshort_elem (dcadd dshort_elem dround_elem))
                (dmul (kvec * (255 - k)) dshort_elem (dcadd dshort_elem dround_elem)))) dshort_elem)
       (fun (c : coeff) => max_noise - cvb < absZq c)) (iota_ 0 256);last by smt().
apply  StdBigop.Bigreal.BRA.eq_big_seq => k; rewrite mem_iota /= => Hk. 
  have Hs := cb1_heuristic_distr_i k _;1:smt(). 
  have -> : 
    mu (cb1_heuristic_distr_gradual) (fun (x : poly) => max_noise - cvb < absZq x.[k]) =
    mu (dmap (cb1_heuristic_distr_gradual) (fun (p : poly) => p.[k])) (fun cc => max_noise - cvb < absZq cc) by rewrite dmapE /(\o) //=. 
  by smt().
qed.

op epsilon_max : real.

axiom epsilon_computed_max &m :
 Pr [ CB1_heuristic.main(cv_bound_max) @ &m : res ] <= epsilon_max.

(* These instantiated lemmas allow bounding the probability of
  decryption error when extending the heuristic to cv.
  Uncommenting the prints permits seeing the content below
  produced by EasyCrypt  
 
print correctness.
print CorrectnessAdvNoise.
print noise_exp_val.

lemma correctness:
  forall (A(H : PKE_ROM.POracle) <: PKE_ROM.CORR_ADV{-MLWE_ROM.RO.LRO}) &m,
    (forall (O <: MLWE_ROM.RO.RO), islossless O.get => islossless A(O).find) =>
    Pr[PKE_ROM.Correctness_Adv(MLWE_ROM.RO.LRO, MLWE_PKE, A).main() @ &m : res] <=
    Pr[CorrectnessAdvNoise(A).main() @ &m : res].

module CorrectnessAdvNoise(A : PKE_ROM.CORR_ADV) = {
  proc main() : bool = {
    var sd : seed;
    var s : polyvec;
    var e : polyvec;
    var _A : MLWE_ROM.RO.out_t;
    var r : polyvec;
    var e1 : polyvec;
    var e2 : poly;
    var m : plaintext;
    var n : poly;
    
    MLWE_ROM.RO.LRO.init();
    sd <$ dseed;
    _A <@ MLWE_ROM.RO.LRO.get(sd);
    r <$ dshort;
    s <$ dshort;
    e <$ dshort;
    e1 <$ dshort;
    e2 <$ dshort_R;
    m <@ A(MLWE_ROM.RO.LRO).find(pk_encode (_A *^ s + e, sd), sk_encode s);
    n <- noise_exp _A s e r e1 e2 m;
    
    return ! under_noise_bound n max_noise;
  }
}.

lemma noise_exp_val:
  forall (_A : polymat) (s e r e1 : polyvec) (e2 : poly) (m : plaintext),
    noise_exp _A s e r e1 e2 m =
    let t = _A *^ s + e in
    let u = Matrix_.Matrix.trmx _A *^ r + e1 in
    let v = (t `<*>` r) &+ e2 &+ m_encode m in
    let cu = rnd_err_u u in let cv = rnd_err_v v in (e `<*>` r) &- (s `<*>` e1) &- (s `<*>` cu) &+ e2 &+ cv.

*)

(* To compute the bound based on this lemma, we apply the heuristic
  of taking cu nd vc as vector/poly that comes out of rounding a uniform vector/poly, 
  which is the Kyber heuristic *)

op dround_elem_v : coeff distr = dmap duni_elem (compress_err vbits).

op dround_poly : poly distr =  (darray256 dround_elem_v).

op noise_exp_heuristic  (cu s e r e1 : polyvec) (e2 cv : poly) : poly =
  ((e `<*>` r) &- (s `<*>` e1) &- (s `<*>` cu) &+ e2 &+ cv)%MLWE_.


module CorrectnessAdvNoise_Heuristic = {
  proc main() : bool = {
    var cu : polyvec;
    var s : polyvec;
    var e : polyvec;
    var r : polyvec;
    var e1 : polyvec;
    var e2 : poly;
    var cv : poly;
    var n : poly;
    
    cu <$ dround_polyvec;
    r <$ dshort;
    s <$ dshort;
    e <$ dshort;
    e1 <$ dshort;
    e2 <$ dshort_R;
    cv <$ dround_poly;
    n <- noise_exp_heuristic cu s e r e1 e2 cv;
    
    return ! under_noise_bound n max_noise;
  }


  proc main_grad() : bool = {
    var ers, er, e1cus, e1cu,s,  se1cu,  e2,n,cv,ncv;     
    ers <$ MLWE_.dshort `*` MLWE_.dshort;
    er <- ers.`1 `<*>` ers.`2;
    s <$ dshort;
    e1cus <$ MLWE_.dshort `*` dround_polyvec;
    e1cu <- e1cus.`1 + e1cus.`2;
    se1cu <- s `<*>` e1cu;
    e2 <$ dshort_R;
    n <- (er &- se1cu &+ e2)%MLWE_;
    cv <$ dround_poly;
    ncv <- n + cv;
    return ! under_noise_bound ncv max_noise;
  }


}.

op heuristic_distr_gradual  =
  let er = dmap (MLWE_.dshort `*` MLWE_.dshort) (fun (vv : polyvec * polyvec) => vv.`1 `<*>` vv.`2) in
  let e1cu = dmap (MLWE_.dshort `*` dround_polyvec) (fun (vv : polyvec * polyvec) => (+) vv.`1 vv.`2) in 
  let se1cu = dmap (MLWE_.dshort `*` e1cu) (fun (vv : polyvec * polyvec) => vv.`1 `<*>` vv.`2) in 
  let erse1cu = dmap (er `*` se1cu) (fun (vv : poly * poly) =>  vv.`1 &- vv.`2) in 
  let ncv =   dmap (erse1cu `*` dshort_R) (fun (vv : poly * poly) =>  Rq.(&+) vv.`1 vv.`2) in
       dmap (ncv `*` dround_poly) (fun (vv : poly * poly) =>  Rq.(&+) vv.`1 vv.`2).


lemma main_grad_distr_cv &m:
 Pr [ CorrectnessAdvNoise_Heuristic.main_grad() @ &m : res ] =
    mu (heuristic_distr_gradual)
     (fun (x : poly) => ! under_noise_bound x max_noise).
byphoare=> //;proc => /=. 
  rndsem* 0; rnd => /=. 
  auto => &hr;rewrite /heuristic_distr_gradual /=. 
  congr.
  rewrite (dmap_dprodE (dshort) (dmap (dshort `*` dround_polyvec) (fun (vv : polyvec * polyvec) => vv.`1 + vv.`2))) => /=.
pose D1 := dshort `*` dshort.
pose D3 := dshort `*` dround_polyvec.
pose D2 := dshort.
pose D4 := dshort_R.
pose D5 := dround_poly.
simplify.
rewrite (dmap_dprodL D1) dmap_comp. 
rewrite (dmap_dprodE D1) /(\o) /=. 
rewrite (dmap_dprodE _ D4) /= (dlet_dlet D1) /=. 
rewrite (dmap_dprodE _ D5) /= (dlet_dlet D1) /=.
congr; rewrite fun_ext => er.
rewrite dmap_dlet  /(\o) /=.
rewrite (dlet_dlet D2).
rewrite (dlet_dlet D2).
congr; rewrite fun_ext => s /=.
rewrite !dmap_comp.
rewrite (dlet_dmap D3)  /(\o) /=. 
rewrite (dlet_dlet D3)  /(\o) /=. 
congr; rewrite fun_ext => e1cus /=.
rewrite (dlet_dmap D4)  /(\o) /=. 
congr; rewrite fun_ext => e2 /=.
congr; rewrite fun_ext => cv /=.
smt(@Rq).
qed.

lemma heuristics_match_cv &m :
Pr [ CorrectnessAdvNoise_Heuristic.main() @ &m : res ] = 
Pr [ CorrectnessAdvNoise_Heuristic.main_grad() @ &m : res ].
byequiv => //;proc.
swap {1} 4 -3. swap {1} 3 -1. 
seq 2 1 : (#pre /\ e{1} = ers{2}.`1 /\ r{1} = ers{2}.`2).
+ conseq />;rndsem {1} 0;rnd;auto => />.
  have <- : (dshort `*` dshort) =
    (dlet dshort (fun (e : polyvec) => dmap dshort (fun (r : polyvec) => (e, r)))); last by split;smt().
  by rewrite (dprod_dlet dshort ) /dmap /(\o) /=.
swap {1} 2 -1; swap {2} 2 -1; seq 1 1 : (#pre /\ ={s}); 1: by auto.
swap {1} 2 -1; swap {2} 2 -1.
seq 2 1 : (#pre /\ e1{1} = e1cus{2}.`1 /\ cu{1} = e1cus{2}.`2).
+ conseq />;rndsem {1} 0;rnd;auto => />.
  have <- : (dshort `*` dround_polyvec) =
    (dlet dshort (fun (e : polyvec) => dmap dround_polyvec (fun (r : polyvec) => (e, r)))); last by split;smt().
  by rewrite (dprod_dlet dshort ) /dmap /(\o) /=.
auto => /> &2 ???? ;congr;congr.
rewrite /noise_exp_heuristic.
 rewrite  !dotpDr ZR.opprD /=.
 smt(@ZR).
qed.

lemma heuristic_distr_i i :
  0 <= i < 256 =>
  dmap (heuristic_distr_gradual) (fun (p : poly) => p.[i]) =
    dcadd (dcadd (dcsub (dmul (kvec*256) dshort_elem dshort_elem)
            (dcsub (dmul (kvec*(i+1)) dshort_elem (dcadd dshort_elem  dround_elem)) 
                   (dmul (kvec*(255-i)) dshort_elem (dcadd dshort_elem  dround_elem)))) dshort_elem)
                       dround_elem_v.
move => Hi.
rewrite  /heuristic_distr_gradual /=.
pose dd := dmap ((dmap
           (dmap (dshort `*` dshort) (fun (vv : polyvec * polyvec) => vv.`1 `<*>` vv.`2) `*`
            dmap (dshort `*` dmap (dshort `*` dround_polyvec) (fun (vv : polyvec * polyvec) => vv.`1 + vv.`2))
              (fun (vv : polyvec * polyvec) => vv.`1 `<*>` vv.`2)) (fun (vv : poly * poly) => vv.`1 &+ - vv.`2) `*`
         dshort_R))%MLWE_  (fun (vv : poly * poly) => vv.`1 &+ vv.`2)%Rq.
have -> := dadd_poly_tail dd dround_poly (dmap dd (proj i)) dround_elem_v i Hi _ _. 
+ done.
+ by apply eq_distr => cc;rewrite  /dround_poly /dround_elem_v /= darray_proj 2,3:/#; rewrite dmap_ll;1:smt(duni_elem_ll).  

congr => /=. 
rewrite /dd; clear dd.

pose dd := dmap (dmap (dshort `*` dshort) (fun (vv : polyvec * polyvec) => vv.`1 `<*>` vv.`2) `*`
         dmap (dshort `*` dmap (dshort `*` dround_polyvec) (fun (vv : polyvec * polyvec) => vv.`1 + vv.`2))
           (fun (vv : polyvec * polyvec) => vv.`1 `<*>` vv.`2)) (fun (vv : poly * poly) => vv.`1 &- vv.`2).
have -> := dadd_poly_tail dd dshort_R (dmap dd (proj i)) dshort_elem i Hi _ _. 
+ done.
+ by apply eq_distr => cc;rewrite /dshort_R darray_proj ;1,2: by smt(dshort_elem_ll).
congr => /=. 
rewrite /dd; clear dd.
pose dd1 := dmap (dshort `*` dshort) (fun (vv : polyvec * polyvec) => vv.`1 `<*>` vv.`2) .
rewrite dadd_vector /=.

pose dd2 := dmap (dshort `*` dvector (dR (dcadd dshort_elem dround_elem)))
        (fun (vv : polyvec * polyvec) => vv.`1 `<*>` vv.`2).
have -> //:= dsub_poly_tail dd1 dd2 (dmap dd1 (proj i))  (dmap dd2 (proj i)) i Hi _ _.
+ done.
+ done.

congr.
+ by rewrite /dd1; apply dotp_tail_good => //;apply is_good_dshort_elem.
rewrite /dd2. 
apply dotp_tail => //;1: apply dshort_elem_ll.

apply dmap_ll;apply dprod_ll; split; 1: by smt(dshort_elem_ll).
rewrite /dround_elem dmap_ll;smt(duni_elem_ll).

qed.

import ZR.
lemma heuristic_mu &m : 
  Pr [ CorrectnessAdvNoise_Heuristic.main() @ &m : res ] <=
   StdBigop.Bigreal.BRA.big predT  (fun k => 
     mu (dcadd (dcadd (dcsub (dmul (kvec*256) dshort_elem dshort_elem)
            (dcsub (dmul (kvec*(k+1)) dshort_elem (dcadd dshort_elem  dround_elem)) 
                   (dmul (kvec*(255-k)) dshort_elem (dcadd dshort_elem  dround_elem)))) dshort_elem)
                       dround_elem_v)
                      (fun (c : coeff) => (max_noise) < absZq c)) (iota_ 0 256).
have -> := (heuristics_match_cv &m).
rewrite main_grad_distr_cv.
have  := union_bound heuristic_distr_gradual (max_noise).


have -> : mu (heuristic_distr_gradual)
  (fun (x : poly) => ! all (fun (kk : int) => absZq x.[kk] <= max_noise) (iota_ 0 256))
  = mu (heuristic_distr_gradual) (fun (x : poly) => ! under_noise_bound x (max_noise)).
+ congr;rewrite fun_ext => x /=.
  rewrite /under_noise_bound allP allP;smt(mem_iota).
have -> :
 StdBigop.Bigreal.BRA.big predT
  (fun (k : int) => mu heuristic_distr_gradual (fun (x : poly) => max_noise < absZq (proj k x)))
  (iota_ 0 256) =
  StdBigop.Bigreal.BRA.big predT
  (fun (k : int) =>
     mu
       (dcadd (dcadd (dcsub (dmul (kvec*256) dshort_elem dshort_elem)
            (dcsub (dmul (kvec*(k+1)) dshort_elem (dcadd dshort_elem  dround_elem)) 
                   (dmul (kvec*(255-k)) dshort_elem (dcadd dshort_elem  dround_elem)))) dshort_elem)
                       dround_elem_v)
       (fun (c : coeff) => max_noise < absZq c)) (iota_ 0 256);last by smt().
apply  StdBigop.Bigreal.BRA.eq_big_seq => k; rewrite mem_iota /= => Hk. 
  have Hs := heuristic_distr_i k _; 1:smt().
  have -> : 
    mu (heuristic_distr_gradual) (fun (x : poly) => max_noise < absZq x.[k]) =
    mu (dmap (heuristic_distr_gradual) (fun (p : poly) => p.[k])) (fun cc => max_noise < absZq cc) by rewrite dmapE /(\o) //=. 
  by smt().
qed.


(* We compute these bounds for concrete variants MLKEM-768 and MLKEM-1024 in separate files. *)


op epsilon : real.


axiom epsilon_computed &m :
 Pr [ CorrectnessAdvNoise_Heuristic.main() @ &m : res ] <= epsilon.

