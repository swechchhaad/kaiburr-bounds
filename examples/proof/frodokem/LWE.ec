require import AllCore Distr List StdOrder FMap PROM.
require (****) Dmatrix.
require (****) DynMatrix.
(****) import IntOrder.
require (****) Hybrid.

clone import DynMatrix as DM.
clone import Dmatrix as Dmatrix_ with
  theory DM <- DM.

clone import SampleLWE.
clone import SampleM.

instance ring with R
  op rzero = ZR.zeror
  op rone  = ZR.oner
  op add   = ZR.( + )
  op opp   = ZR.([-])
  op mul   = ZR.( * )
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

(* --------------------------------------------------------------------------- *)
(* Uniform distribution over R *)
op [lossless uniform full] duni_R : R distr.
hint exact: duni_R_ll duni_R_uni duni_R_fu.
hint simplify (duni_R_ll, duni_R_uni, duni_R_fu).

lemma duni_R_funi : is_funiform duni_R.
proof. by apply is_full_funiform. qed.

(* --------------------------------------------------------------------------- *)
(* Distribution over R (short values) *)

op [lossless] Chi  : R distr.
hint exact: Chi_ll.
hint simplify Chi_ll.

type seed.
op [lossless] dseed: seed distr.

(* --------------------------------------------------------------------------- *)
(* Extension distribution to matrix *)

hint exact: dmatrix_ll dmatrix_uni dvector_ll.
hint simplify (dmatrix_ll, dmatrix_uni, dvector_ll).

lemma duni_matrix_ll m n : is_lossless (dmatrix duni_R m n).
proof. by trivial. qed.


lemma duni_matrix_fu m n A_:
     0 <= m => 0 <= n =>  A_ \in (dmatrix duni_R m n) <=> size A_ = (m, n).
proof.
move => ge0m ge0n.
by apply /supp_dmatrix_full.
qed.

lemma duni_matrix_uni m n : is_uniform (dmatrix duni_R m n).
proof. by trivial. qed.

lemma Chi_matrix_ll m n : is_lossless (dmatrix Chi m n).
proof. by trivial. qed.

hint simplify (duni_matrix_uni, duni_matrix_ll, Chi_matrix_ll).

(* --------------------------------------------------------------------------- *)
(*                                                                             *)
(* --------------------------------------------------------------------------- *)

module type Adv_M = {
   proc guess(_A: matrix, u : matrix) : bool
}.

module type Adv_V = {
   proc guess(_A: matrix, v : vector) : bool
}.

abstract theory LWE.

op l : { int | 0 < l } as gt0_l.
op m: { int | 0 < m } as gt0_m.
op n : { int | 0 < n } as gt0_n.

hint exact: gt0_m gt0_n gt0_l.
hint simplify (gt0_m, gt0_n, gt0_l).

module LWE_M(Adv: Adv_M) = {
  proc main(b : bool) : bool = {
    var b', s, e, u0, u1, _A;

    _A <$ dmatrix duni_R m n;

    s <$ dmatrix Chi n l;
    e <$ dmatrix Chi m l;
    u0 <- _A * s + e;
    u1 <$ dmatrix duni_R m l;

    b' <@ Adv.guess(_A, if b then u1 else u0);
    return b';
   }
}.

(* LWE Matrix adversary *)
module LWE_M_Loop(Adv: Adv_M) = {
  proc main(b : bool) : bool = {
    var b', i, sc, ec, u0, u1, u0c, u1c, u0cs, u1cs, _A;

    _A <$ dmatrix duni_R m n;

    u0cs <- [];
    u1cs <- [];
    i <- 0;

    while (i < l) {
        sc <$ dvector Chi n;
        ec <$ dvector Chi m;
        u0c <- _A *^ sc + ec;
        u0cs <- rcons u0cs u0c;

        u1c <$ dvector duni_R m;
        u1cs <- rcons u1cs u1c;

        i <- i + 1;
    }

    u0 <- ofcols m l u0cs;
    u1 <- ofcols m l u1cs;

    b' <@ Adv.guess(_A, if b then u1 else u0);
    return b';
   }
}.

(* LWE Vector adversary *)
module LWE_V(Adv: Adv_V) = {
  proc main(b: bool) : bool = {
    var b', sc, ec, u0, u1, _A;

    _A <$ dmatrix duni_R m n;

    sc <$ dvector Chi n;
    ec <$ dvector Chi m;
    u0 <- _A *^ sc + ec;
    u1 <$ dvector duni_R m;

    b' <@ Adv.guess(_A, if b then u1 else u0);
    return b';
   }
}.

lemma LWE_M_Loop_eq (A <: Adv_M{-LWE_M, -LWE_M_Loop}):
    equiv[LWE_M(A).main ~ LWE_M_Loop(A).main : ={glob A, b} ==> ={res}].
proof.
proc.
fission{2} 5!1 @ 4,6.
swap{2} 8 -2; swap{2} 3 4.
seq 1 1: (
  ={glob A, b, _A}
  /\ size _A{1} = (m, n)
  /\ size _A{2} = (m, n)
).
+ auto => /> ?.
  by rewrite supp_dmatrix.
outline{2} [1-4] u0 <@ SampleLWE.LWE_M_Loop.sampleG.
outline{2} [2-5] u1 <@ SampleM.VectorRowsLoopRcons.sample.
rewrite equiv[{2} 1 -SampleLWE.LWE_M_Loop_eqG].
rewrite equiv[{2} 2 -SampleM.Matrix_VectorRowsLoopRcons_eq].
inline *; call (:true).
do 3! cfold{2} 10; wp; rnd.
swap{2} 3 1; do 3! cfold{2} 1; wp; auto => />.
+ by auto => /> /#.
+ call (:true); inline{1} 2.
  do 3! cfold{1} 2; wp; while (i0{1} = i{2} /\ vs{1} = u1cs{2}); auto => />. smt().
  call (:true). wp. while (={d,x,y,i,r,vs,a}); auto => />.
  auto => />.
+ inline *; do 2! cfold {1} 1; do 2! cfold{1} 2; wp.
  call (:true); wp.
  while (={i,u1cs}).
  + sim.
  + wp; while (={_A} /\ i0{1} = i{2} /\ vs{1} = u0cs{2} /\ a{1} = _A{1});
    auto => />.
qed.

lemma LWE_M_Loop_Eq (A <: Adv_M{-LWE_M, -LWE_M_Loop}) b &m:
    Pr[LWE_M(A).main(b) @ &m: res] = Pr[LWE_M_Loop(A).main(b) @ &m: res].
proof.
byequiv (_: ={glob A, b} ==> ={res}) => //.
exact (LWE_M_Loop_eq A).
qed.

(* --------------------------------------------------------------------------- *)
(* Hybrid game model for LWE                                                   *)
(* --------------------------------------------------------------------------- *)
clone import Hybrid as Hyb with
type input    <- unit,
type output   <- vector,
type inleaks  <- unit,
type outleaks <- matrix,
type outputA  <- bool,
op q <- l
proof q_ge0 by trivial
proof *.

module type Adv_M_Orclb (Adv: Adv_M, Ob: Orclb, O: Orcl)= {
  proc main() : bool
}.

module LWE_Ob : Orclb = {
  var _A: matrix

  proc leaks(): matrix = {
    _A <$ dmatrix duni_R m n;
    return _A;
  }

  proc orclL (): vector = {
    var sc, ec, v;
    sc <$ dvector Chi n;
    ec <$ dvector Chi m;
    v <- _A *^ sc + ec;

    return v;
  }

  proc orclR (): vector = {
    var v;

    v <$ dvector duni_R m;
    return v;
  }
}.

(* mock hybrid Ob oracle *)
module ObFake = {
  var _A: matrix

  proc leaks(): matrix = {
    return _A;
  }

  proc orclL (): vector = {
      var sc, ec, v;
      sc <$ dvector Chi n;
      ec <$ dvector Chi m;
      v <- _A *^ sc + ec;

      return v;
  }

  proc orclR (): vector = {
      var v';
      v' <$ dvector duni_R m;
      return v';
  }
}.

(* For linking LWE matrix adversary to LWE non-hybrid game adversary *)
module C(Adv : Adv_M) (Ob: Orclb) (O: Orcl) = {
  var _A: matrix

  proc main(): bool = {
    var b', i, u, c, cs, _A;

    _A <@ Ob.leaks();

    cs <- [];
    i <- 0;

    while (i < l) {
        c <@ O.orcl();
        cs <- rcons cs c;

        i <- i + 1;
    }

    u <- ofcols m l cs;

    b' <@ Adv.guess(_A, u);
    return b';
  }
}.

(* --------------------------------------------------------------------------------*)
(* For linking LWE vector adversary to LWE Hybrid Game adversary using PROM theory *)
(* ------------------------------------------------------------------------------- *)
clone FullRO as Hyb_RO with
  type in_t <- matrix * bool, (* (_A,sample) *)
  type out_t <- vector,
  type d_in_t <- bool,
  type d_out_t <- bool,
  op dout <- fun (din: matrix * bool) =>
    if din.`2
    then dvector duni_R m
    else dlet (dvector Chi n) (fun (s: vector) =>
            dmap (dvector Chi m) (fun (e: vector) => din.`1 *^ s + e))
  proof *.

(* mock hybrid game for vector adversary, so that we can link LWE vector adversary with LWE Hybrid Game adversary *)
module Hyb_Mock(Adv : Adv_M): Adv_V = {
  var v: vector

  module OFake = {
    proc orcl(): vector = {
      return v;
    }
  }

  proc guess(_A: matrix, v': vector) : bool = {
    var b;
    v <- v';
    ObFake._A <- _A;

    b <@ HybGame(C(Adv), ObFake, OFake).main();
    return b;
  }
}.


(* LWE matrix computation *)
lemma LWE_M_L (A<: Adv_M{-Count, -LWE_Ob, -LWE_M_Loop}) &m:
    Pr[LWE_M_Loop(A).main(false) @ &m : res] = Pr[Ln(LWE_Ob, C(A)).main() @ &m: res].
proof.
move => *.
byequiv => //=.
proc; inline *; wp.
call (: true) => //=; wp.
+ while (={i} /\ u0cs{1} = cs{2} /\
      _A{1} = LWE_Ob._A{2}
  ).
  wp. rnd{1}; auto => />. 
+ auto => />.
qed.

(* LWE matrix random sampling *)
lemma LWE_M_R (A<: Adv_M{-Count, -LWE_Ob, -LWE_M_Loop}) &m:
    Pr[LWE_M_Loop(A).main(true) @ &m : res] = Pr[Rn(LWE_Ob, C(A)).main() @ &m: res].
proof.
move => *.
byequiv => //.
proc; inline *; wp.
call (: true) => //=; wp.
+ while (={i} /\ u1cs{1} = cs{2} /\
      _A{1} = LWE_Ob._A{2}
  ).
  + by auto => /#.
  + by auto => /#.
qed.

(* auxiliary game for linking vector adversary with hybrid mock and LWE Hybrid Game adversary utilizing PROM *)
module LWE_V_Aux (Adv: Adv_M) (O: Hyb_RO.RO) = {
  var b: bool

  module OFake = {
    proc orcl(): vector = {
      var v;
      v <@ O.get(ObFake._A, b);
      return v;
    }
  }

  proc distinguish(b': bool): bool = {
    b <- b';
    ObFake._A <$ dmatrix duni_R m n;
    O.sample(ObFake._A, b);
    b <@ HybGame(C(Adv), ObFake, OFake).main();
    return b;
  }
}.

lemma LWE_V_Aux (A <: Adv_M{-Hyb_RO.RO, -Hyb_Mock, -LWE_V_Aux, -LWE_V}) b &m:
    Pr[LWE_V(Hyb_Mock(A)).main(b) @ &m: res] = Pr[Hyb_RO.MainD(LWE_V_Aux(A), Hyb_RO.RO).distinguish(b) @ &m: res].
proof.
byequiv => //.
proc; inline *; wp.
call (: ={ObFake._A}); wp.
while (={i, cs, HybOrcl.l0, HybOrcl.l, ObFake._A} /\
  Hyb_Mock.v{1} = r1{2} /\
  Hyb_RO.RO.m{2}.[(ObFake._A{2},LWE_V_Aux.b{2})] = Some r1{2}
).
+ sp.
    + if => //=.
      auto.
    + if => //=.
      wp. auto => //= /> &2.
      case (LWE_V_Aux.b{2}).
      + rewrite //= domNE => /> /#.
      + rewrite //= domNE dlet_ll => /> *.
        + by rewrite dmap_ll.
        rewrite /#.
    + by auto.
+ wp. rnd. wp.
  case (b).
  + rnd; wp; rnd{1}; rnd{1}; auto => //= /> *.
    by rewrite /dom emptyE //= get_set_sameE.
  + rnd{1}.
    rndsem*{1} 1.
    auto => //= /> *.
    by rewrite get_setE /dom emptyE.
qed.

lemma LWE_V_L_Aux (A <: Adv_M{-LWE_Ob, -Hyb_RO.RO, -LWE_V_Aux}) &m:
    Pr[Hyb_RO.MainD(LWE_V_Aux(A), Hyb_RO.LRO).distinguish(false) @ &m: res] = Pr[HybGame(C(A), LWE_Ob, L(LWE_Ob)).main() @ &m: res].
proof.
byequiv => //.
proc; inline *; wp.
call (: ObFake._A{1} = LWE_Ob._A{2}); wp.
while (={i, HybOrcl.l0, HybOrcl.l, cs} /\
  ObFake._A{1} = LWE_Ob._A{2} /\
  Hyb_RO.RO.m{1}.[(ObFake._A{1}, LWE_V_Aux.b{1})] = (HybOrcl.l0{1} < HybOrcl.l{1}) ? Some v0{1} : None /\
  !LWE_V_Aux.b{1}
).
+ sp.
  + if => //=.
    by auto => /#.
  + if => //=.
    wp 3 5.
    rndsem*{2} 1.
    auto => //= />.
    move=> &1 &2; rewrite domE => *.
    rewrite get_set_sameE /#.
  + by auto => /#.
+ swap {2} [1..2] 2.
  auto => //= /> ? ? ? ?.
  by rewrite emptyE DInterval.supp_dinter /#.
qed.

lemma LWE_V_L (A <: Adv_M{-Hyb_Mock, -LWE_Ob, -Hyb_RO.RO, -Hyb_RO.FRO, -LWE_V, -LWE_V_Aux}) &m:
      Pr[LWE_V(Hyb_Mock(A)).main(false) @ &m: res] = Pr[HybGame(C(A),LWE_Ob,L(LWE_Ob)).main() @ &m: res].
proof.
rewrite (LWE_V_Aux A false _) -(LWE_V_L_Aux A _).
byequiv (Hyb_RO.FullEager.RO_LRO (LWE_V_Aux(A)) _) => // x.
case (x.`2) => h //.
by rewrite dlet_ll // => *; rewrite dmap_ll.
qed.

lemma LWE_V_R_Aux (A <: Adv_M{-LWE_Ob, -Hyb_RO.RO, -LWE_V_Aux}) &m:
    Pr[Hyb_RO.MainD(LWE_V_Aux(A), Hyb_RO.LRO).distinguish(true) @ &m: res] = Pr[HybGame(C(A), LWE_Ob, R(LWE_Ob)).main() @ &m: res].
proof.
byequiv => //.
proc; inline *; wp.
call (: ObFake._A{1} = LWE_Ob._A{2}); wp.
while (={i, HybOrcl.l0, HybOrcl.l, cs} /\
  ObFake._A{1} = LWE_Ob._A{2} /\
  Hyb_RO.RO.m{1}.[(ObFake._A{1}, LWE_V_Aux.b{1})] = (HybOrcl.l0{1} < HybOrcl.l{1}) ? Some v0{1} : None /\
  LWE_V_Aux.b{1}
).
+ sp.
  + if => //=.
    by auto => /#.
  + if => //=.
    auto => //= /> *.
    rewrite get_set_sameE => //= /#.
  + by auto => /#.
+ swap {2} [1..2] 2.
  auto => //= /> ? ? ? ?.
    by rewrite DInterval.supp_dinter emptyE => /#.
qed.

lemma LWE_V_R (A <: Adv_M{-Hyb_Mock, -LWE_Ob, -Hyb_RO.RO, -Hyb_RO.FRO, -LWE_V, -LWE_V_Aux}) &m:
      Pr[LWE_V(Hyb_Mock(A)).main(true) @ &m: res] = Pr[HybGame(C(A),LWE_Ob,R(LWE_Ob)).main() @ &m: res].
proof.
rewrite (LWE_V_Aux A true _) -(LWE_V_R_Aux A _).
byequiv (Hyb_RO.FullEager.RO_LRO (LWE_V_Aux(A)) _) => // x.
case (x.`2) => h //.
by rewrite dlet_ll // => *; rewrite dmap_ll.
qed.

lemma LWE_Hybrid (A <: Adv_M{-Count, -LWE_Ob, -LWE_M, -Hyb_Mock, -Hyb_RO.RO, -Hyb_RO.FRO, -LWE_V, -LWE_V_Aux}) &m :
    islossless A.guess =>
    Pr[LWE_M(A).main(false) @ &m : res] - Pr[LWE_M(A).main(true) @ &m : res]
  = l%r * (Pr[LWE_V(Hyb_Mock(A)).main(false) @ &m : res] - Pr[LWE_V(Hyb_Mock(A)).main(true) @ &m : res]).
proof.
move => A_ll.
rewrite !(LWE_M_Loop_Eq A).
rewrite (LWE_M_L A) (LWE_M_R A) (LWE_V_L A) (LWE_V_R A).
apply (Hybrid_restr LWE_Ob (C(A)) _ _ _ _ _ &m (fun _ _ _ r => r)).
move => *.
proc; inline *.
wp. call (:true). wp.
while (i = Count.c /\ i <= l).
+ auto. call(:true). auto => />. by move=> &hr; rewrite ltzE.
+ auto => //=.
+ auto => //=.
+ by islossless.
+ by islossless.
+ by islossless.
+ move => *.
  proc; call (:true); wp.
  while (i <= l) (l - i) => *;
  wp; call (:true);  auto => /> /#.
qed.

theory LWE_ROM.

clone import FullRO as RO with
  type in_t    = seed,
  type out_t   = matrix,
  op   dout    = fun (x: seed) => dmatrix duni_R m n,
  type d_in_t  = bool,
  type d_out_t = bool.

module type POracle = { include RO [get] }.

module type ROAdv_M(O : POracle) = {
   proc guess(sd : seed, u : matrix) : bool
}.

module LWE_RO(Adv : ROAdv_M, O : RO) = {
  proc main(b : bool) : bool = {
    var sd, s, e, _A, u0, u1, b';

    O.init();
    sd <$ dseed;
    s <$ dmatrix Chi n l;
    e <$ dmatrix Chi m l;
    _A <@ O.get(sd);
    u0 <- _A * s + e;
    u1 <$ dmatrix duni_R m l;

    b' <@ Adv(O).guess(sd, if b then u1 else u0);
    return b';
   }
}.

module FakeRO (O : RO)  = {
  var _sd : seed
  var __A : matrix

  proc get(sd : seed) : matrix = {
      var _Ares;
      _Ares <- __A;
      if (sd <> _sd) {
          O.sample(sd);
          _Ares <@ O.get(sd);
      }
      return _Ares;
  }
}.

module BM(A : ROAdv_M, O : RO) : Adv_M = {
  proc guess(_A : matrix, u : matrix) : bool = {
    var b, sd;
    sd <$ dseed;
    FakeRO._sd <- sd;
    FakeRO.__A <- _A;
    O.init();
    b <@ A(FakeRO(O)).guess(sd,u);
    return b;
  }
}.

module B(A: ROAdv_M, O: RO): Adv_V = {
  proc guess(_A: matrix, v': vector) : bool = {
    var b;
    b <@ Hyb_Mock(BM(A, O)).guess(_A, v');
    return b;
  }
}.

lemma Hyb_Mock_eq (A <: ROAdv_M {-Hyb_Mock, -FakeRO, -LRO}):
    equiv[ B(A, LRO).guess ~ Hyb_Mock(BM(A, LRO)).guess : ={arg, glob A} ==> ={res}].
proof.
proc. sp. inline *. sp. sim.
qed.

lemma LWE_RO_equiv b &m (A <: ROAdv_M {-LRO,-B}):
  Pr[  LWE_RO(A,LRO).main(b) @ &m : res ] =
  Pr[  LWE_M(BM(A,LRO)).main(b) @ &m : res].
proof.
byequiv => //.
proc; inline BM(A,LRO).guess.

swap {1} 5 -2.
swap {2} 8 -7.
swap {2} 11 -10.
swap {2} 8 -4.
swap {2} [10..11] -5.

seq 3 6: (#pre /\ ={b, _A, sd} /\ RO.m{1}.[FakeRO._sd{2}] = Some FakeRO.__A{2} /\
  FakeRO._sd{2} = sd{2} /\
  FakeRO.__A{2} = _A{2} /\
  (forall x, x <> FakeRO._sd{2} => RO.m{1}.[x] = RO.m{2}.[x])
).
+ inline *; auto => />; smt(@FMap).
wp.
call (: RO.m{1}.[FakeRO._sd{2}] = Some FakeRO.__A{2} /\
  (forall x, x <> FakeRO._sd{2} => RO.m{1}.[x] = RO.m{2}.[x])
).
+ proc. inline *.
  case (sd{2} = FakeRO._sd{2}).
  + rcondf{2} 2; first by auto => />.
    rcondf{1} 2; auto => /> /#.
  + rcondt{2} 2; first by auto.
    auto => />.
    smt(get_setE).
by auto => />.
qed.

lemma LWE_RO_Hybrid &m (A <: ROAdv_M {-LRO, -B,
    -LWE_M, -Count, -LWE_Ob, -Hyb_RO.RO, -Hyb_RO.FRO, -LWE_V_Aux, -LWE_V}):
   (forall (O <: POracle), islossless O.get => islossless A(O).guess) =>
   Pr[LWE_RO(A, LRO).main(false) @ &m : res] - Pr[LWE_RO(A, LRO).main(true) @ &m : res]
  = l%r * (Pr[LWE_V(B(A, LRO)).main(false) @ &m : res] - Pr[LWE_V(B(A, LRO)).main(true) @ &m : res]).
proof.
have h0 : forall b, Pr[LWE_V(B(A, LRO)).main(b) @ &m: res] =
  Pr[LWE_V(Hyb_Mock(BM(A, LRO))).main(b) @ &m: res].
+ move => *.
  byequiv => //; proc. 
  rewrite equiv[{1} 6 (Hyb_Mock_eq A)]; sim.
rewrite !h0 !(LWE_RO_equiv _ &m A) => h.
apply (LWE_Hybrid (BM(A, LRO)) &m).
islossless.
apply (h (FakeRO(LRO))).
islossless.
qed.

end LWE_ROM.

end LWE.
