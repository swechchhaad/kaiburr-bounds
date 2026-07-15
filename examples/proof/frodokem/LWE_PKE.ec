require import AllCore Distr List FMap Dexcepted PKE_ROM StdOrder.
require (****) RndExcept LWE DynMatrix.
(*****) import IntOrder.

abstract theory LWE_PKE.
clone import DynMatrix as DM.

clone import LWE as LWE_ with
  theory DM <- DM.

import LWE_.Dmatrix_.

op m : { int | 0 < m } as gt0_m.
op n : { int | 0 < n } as gt0_n.
op nb : { int | 0 < nb } as gt0_nb.
op mb : { int | 0 < mb } as gt0_mb.

hint exact: gt0_m gt0_n gt0_nb gt0_mb.
hint simplify (gt0_m, gt0_n, gt0_nb, gt0_mb).

type plaintext.
type ciphertext.

type raw_ciphertext = matrix * matrix.

op m_encode : plaintext -> matrix.
op m_decode : matrix -> plaintext.

axiom m_encode_rows m : rows (m_encode m) = mb.
axiom m_encode_cols m : cols (m_encode m) = nb.

hint exact: m_encode_rows m_encode_cols.
hint simplify (m_encode_rows, m_encode_cols).

op c_encode : raw_ciphertext -> ciphertext.
op c_decode : ciphertext -> raw_ciphertext.

type pkey.
type skey.

type raw_pkey  = matrix * seed.
type raw_skey  = matrix.

op pk_encode : raw_pkey -> pkey.
op sk_encode : raw_skey -> skey.
op pk_decode : pkey -> raw_pkey.
op sk_decode : skey -> raw_skey.

axiom pk_encodeK : cancel pk_encode pk_decode.

axiom sk_encodeK : cancel sk_encode sk_decode.

(******************************************************************)
(*    The Security Games                                          *)
clone import PKE_ROM as PKEROM with 
  type RO.in_t    = seed,
  type RO.out_t   = matrix,  
  op   RO.dout    = fun (x: seed) => dmatrix duni_R m n,  
  type RO.d_in_t  = bool, 
  type RO.d_out_t = bool,
  type pkey <- pkey,
  type skey <- skey,
  type plaintext <- plaintext,
  type ciphertext <- ciphertext.

import RO.

module LWE_PKE (H: POracle) = {
  proc kg(): pkey * skey = {
    var sd,_A,s,e,t;
    sd <$ dseed;
    _A <@ H.get(sd);
    s  <$ dmatrix Chi n nb;
    e  <$ dmatrix Chi m nb;
    t  <- _A * s + e;
    return (pk_encode (t,sd),sk_encode s);
  }

  proc enc(pk : pkey, u : plaintext) : ciphertext = {
    var sd, _A, _B,s',e',e'',b',v;
    (_B, sd) <- pk_decode pk;
    _A <@ H.get(sd);
    s'  <$ dmatrix Chi mb m;
    e' <$ dmatrix Chi mb n;
    e'' <$ dmatrix Chi mb nb;
    b'  <- s' * _A + e';
    v  <- s' * _B + e'';
    return c_encode (b',v + m_encode u);
  }

  proc dec(sk : skey, c : ciphertext) : plaintext option = {
    var c1,c2;
    (c1,c2) <- c_decode c;
    return (Some (m_decode (c2 + -(c1 * sk_decode sk))));
  }
}.

(* Hop 1 *)

lemma doutE x : PKEROM.RO.dout x = dmatrix duni_R m n by auto.


clone LWE as LWE1 with
  op l <- nb,
  op m <- m,
  op n <- n
  proof
    gt0_l by done,
    gt0_m by done,
    gt0_n by done,
    *.

lemma doutE1 x : LWE1.LWE_ROM.RO.dout x = dmatrix duni_R m n by auto.

module LWE_PKE1 (H: PKEROM.POracle) = {
  proc kg() : pkey * skey = {
    var sd,_A,s,t;
    sd <$ dseed;
    _A <@ H.get(sd); 
    s  <$ dmatrix Chi n nb;
    t  <$ dmatrix duni_R m nb;
    return (pk_encode (t, sd), sk_encode s);
  }

  include LWE_PKE(H) [-kg]
}.

module (B1(A : Adversary) : LWE1.LWE_ROM.ROAdv_M) (H: LWE1.LWE_ROM.POracle) = {
  proc guess(sd: seed, u : matrix) : bool = {
    var pk, m0, m1, c, b, b';
    pk <- pk_encode (u, sd);
    (m0, m1) <@ A(H).choose(pk);
    b <$ {0,1};
    c <@ LWE_PKE1(H).enc(pk, if b then m1 else m0);
    b' <@ A(H).guess(c);
    return b' = b;
  }
}.

section.

declare module A <: Adversary {-PKEROM.RO.LRO, -LWE1.LWE_ROM.RO.LRO,-B1}.

lemma hop1_left &m:
  Pr[CPA(PKEROM.RO.LRO, LWE_PKE, A).main() @ &m : res] =
  Pr[LWE1.LWE_ROM.LWE_RO(B1(A), LWE1.LWE_ROM.RO.LRO).main(false) @ &m : res].
proof.
byequiv => //.
proc; inline *; wp.
call(:(glob PKEROM.RO.LRO){1} = (glob LWE1.LWE_ROM.RO.LRO){2}).
+ proc;inline *;auto.
auto.
call(:(glob PKEROM.RO.LRO){1} = (glob LWE1.LWE_ROM.RO.LRO){2}).
+ proc;inline *;auto.
swap{2} 10 -9.
swap{1} [7..8] -4.
auto => />.
qed.

lemma hop1_right &m:
  Pr[LWE1.LWE_ROM.LWE_RO(B1(A), LWE1.LWE_ROM.RO.LRO).main(true) @ &m : res] =
  Pr[CPA(PKEROM.RO.LRO,LWE_PKE1,A).main() @ &m : res].
proof.
byequiv => //.
proc; inline *; wp.
call(:(glob LWE1.LWE_ROM.RO.LRO){1} = (glob PKEROM.RO.LRO){2}).
+ proc;inline *;auto.
auto.
call(:(glob LWE1.LWE_ROM.RO.LRO){1} = (glob PKEROM.RO.LRO){2}).
+ proc;inline *;auto.
swap{2} 7 1;swap{1} 9 2;swap{1} [3..4] 6.
wp;do 2! rnd{1};rnd{2}.
auto => />.
qed.

end section.

(* Hop 2 *)

clone LWE as LWE2 with
  op l <- mb,
  op m <- n+nb,
  op n <- m
  proof
    gt0_l by done,
    gt0_m by smt(addr_gt0 gt0_n gt0_nb),
    gt0_n by done,
    *.

lemma doutE2 x : LWE2.LWE_ROM.RO.dout x = dmatrix duni_R (n+nb) m by auto.

module LWE_PKE2 (H: PKEROM.POracle) = {

  proc enc(pk : pkey, u : plaintext) : ciphertext = {
    var b', v;
    b' <$ dmatrix duni_R mb n;
    v <$ dmatrix duni_R mb nb;
    return c_encode (b',v + m_encode u);  }

  include LWE_PKE1(H) [-enc]

}.

  module B2_RO_Fake (H: LWE2.LWE_ROM.POracle) = {
  var _sd: seed
  var __A: matrix

    proc get(sd: seed): matrix = {
      var _AB, _A;
      _AB <@ H.get(sd);
      _A <- subm (trmx _AB) 0 m 0 n;
      return _A;
    }
  }.

module (B2(A : Adversary): LWE2.LWE_ROM.ROAdv_M) (H: LWE2.LWE_ROM.POracle) = {

  proc guess(sd: seed, b'v : matrix) : bool = {
    var _AB, _B, pk, u0, u1, c, b, u, b';
    B2_RO_Fake._sd <- sd;
    _AB <@ H.get(sd);
    B2_RO_Fake.__A <- subm (trmx _AB) 0 m 0 n;
    _B <- subm (trmx _AB) 0 m n (n + nb);
    pk <- pk_encode (_B, sd);

    (u0, u1) <@ A(B2_RO_Fake(H)).choose(pk);
    b <$ {0,1};
    u <- if b then u1 else u0;
    c <- c_encode((subm (trmx b'v) 0 mb 0 n, subm (trmx b'v) 0 mb n (n + nb) + m_encode u));
    b' <@ A(B2_RO_Fake(H)).guess(c);
    return b' = b;
  }

}.

section.

declare module A <: Adversary {-PKEROM.RO.LRO, -LWE2.LWE_ROM.RO.LRO, -B2}.

local module RO_Fake_Aux : PKEROM.POracle = {
   proc get(sd: seed): matrix = {
      var  _A, r;
    
      r <$ LWE2.LWE_ROM.RO.dout sd;
      _A <- subm (trmx r) 0 m 0 n;
      r <- trmx (_A || (subm (trmx r) 0 m n (n+nb)));
      if (sd \notin LWE2.LWE_ROM.RO.RO.m) {
         LWE2.LWE_ROM.RO.RO.m.[sd] <- r;
         
      }
      return (subm (trmx (oget LWE2.LWE_ROM.RO.RO.m.[sd])) 0 m 0 n);
    }
}.

lemma aux (_AB: matrix) :
 rows _AB = n + nb =>
 cols _AB = m =>
mu1 (dmap (dmatrix duni_R (n + nb) m) (fun (r0_0 : matrix) => subm (trmx r0_0) 0 m 0 n))
  (subm (trmx _AB) 0 m 0 n) =
mu1 (dmatrix duni_R m n) (subm (trmx _AB) 0 m 0 n).
move => Hrs Hc. 
rewrite dmap1E /(\o) /pred1 /=.
rewrite (mu_eq_support (dmatrix duni_R (n + nb) m) _  (fun (x : matrix) => subm x 0 n 0 m = subm _AB 0 n 0 m)).
+ by move => x Hx /=; rewrite eq_iff /= -2!submT inj_eq 1:trmx_inj.
  have -> : (dmatrix duni_R (n + nb) m)  =
    dmap ((dmatrix duni_R m (n + nb))) (trmx).
    apply eq_distr => x; rewrite (dmap1E (dmatrix _ _ _)) /(\o) /pred1 /=. 
    case (size x <> (n+nb, m)).
    + move => *; rewrite !mu0_false; smt(supp_dmatrix @Matrices).
    move => ? /=; rewrite dmatrix_tr1E ~-1://# /= &(mu_eq) => y @/pred1.
    by rewrite -[y = _](inj_eq trmx) 1:trmx_inj trmxK.
   rewrite dmatrix_add_r;1..3:smt(gt0_m gt0_n gt0_nb).
   rewrite dmap_comp /(\o) /= dmapE /(\o).
   rewrite (mu_eq_support _ _
     (fun (x : matrix * matrix) => ((fun mm => trmx mm = subm _AB 0 n 0 m))  x.`1));1: by  smt(gt0_n gt0_m gt0_nb supp_dprod supp_dmatrix @Matrices).
   rewrite dprodEl /=. 
   rewrite (: weight (dmatrix duni_R m nb) = 1%r) /=; 1: smt(dmatrix_ll duni_R_ll gt0_m gt0_n).    
    apply mu_eq_support; by  smt(gt0_n gt0_m gt0_nb supp_dprod supp_dmatrix @Matrices).
qed.

lemma RO_sample:
equiv [LRO.get ~ B2_RO_Fake(LWE2.LWE_ROM.RO.LRO).get :
        ={arg} /\
        B2_RO_Fake._sd{2} \in RO.m{1} /\
        oget RO.m{1}.[B2_RO_Fake._sd{2}] = B2_RO_Fake.__A{2} /\
        fdom RO.m{1} = fdom LWE2.LWE_ROM.RO.RO.m{2} /\
        forall sd, sd \in RO.m{1} =>
          oget RO.m{1}.[sd] = subm (trmx (oget LWE2.LWE_ROM.RO.RO.m{2}.[sd])) 0 m 0 n
        ==> ={res} /\
        B2_RO_Fake._sd{2} \in RO.m{1} /\
        oget RO.m{1}.[B2_RO_Fake._sd{2}] = B2_RO_Fake.__A{2} /\
        fdom RO.m{1} = fdom LWE2.LWE_ROM.RO.RO.m{2} /\
        forall sd, sd \in RO.m{1} =>
          oget PKEROM.RO.RO.m{1}.[sd] = subm (trmx (oget LWE2.LWE_ROM.RO.RO.m{2}.[sd])) 0 m 0 n].
proof.
exlim arg{2}, LWE2.LWE_ROM.RO.RO.m{2} => _sd mm.
case(_sd \notin mm) => H.
+ proc*.
  transitivity {2} { r <@ RO_Fake_Aux.get(sd); }
      ( LWE2.LWE_ROM.RO.RO.m{2} = mm 
        /\ B2_RO_Fake._sd{2} \in PKEROM.RO.RO.m{1}
        /\ oget PKEROM.RO.RO.m{1}.[B2_RO_Fake._sd{2}] = B2_RO_Fake.__A{2}
        /\ sd{2} = _sd 
        /\  x{1} = sd{2} 
        /\ fdom PKEROM.RO.RO.m{1} = fdom LWE2.LWE_ROM.RO.RO.m{2} 
        /\ forall (sd0 : in_t), sd0 \in RO.m{1} => 
             oget PKEROM.RO.RO.m{1}.[sd0] = subm (trmx (oget LWE2.LWE_ROM.RO.RO.m{2}.[sd0])) 0 m 0 n 
        ==> 
           ={r} 
        /\ B2_RO_Fake._sd{2} \in PKEROM.RO.RO.m{1}
        /\ oget PKEROM.RO.RO.m{1}.[B2_RO_Fake._sd{2}] = B2_RO_Fake.__A{2} 
        /\ fdom PKEROM.RO.RO.m{1} = fdom LWE2.LWE_ROM.RO.RO.m{2} 
        /\ forall (sd0 : in_t), sd0 \in PKEROM.RO.RO.m{1} => 
             oget PKEROM.RO.RO.m{1}.[sd0] = subm (trmx (oget LWE2.LWE_ROM.RO.RO.m{2}.[sd0])) 0 m 0 n)

      ( ={sd,glob LWE2.LWE_ROM.RO.RO, B2_RO_Fake._sd, B2_RO_Fake.__A} 
        /\ LWE2.LWE_ROM.RO.RO.m{2} = mm 
        /\ sd{2} = _sd 
        ==> 
        ={r, glob LWE2.LWE_ROM.RO.RO, B2_RO_Fake._sd, B2_RO_Fake.__A}); 1,2: smt(); last first.
  + inline *.
    rcondt{2}4; first by auto => />.
    rcondt{1}5; first by auto => />; smt(mem_fdom).
    auto => /> rl ?;rewrite !get_set_eqE /=;1,2:smt().  
    split. 
    + by rewrite subm_catmrCl.
    + by  smt( catmc_subm duni_matrix_fu gt0_n gt0_nb gt0_m).
  + inline *. 
    rcondt{2}5; first by auto => />.
    rcondt{1}3; first by auto => />; smt(mem_fdom).
    sp;wp 1 2 => /=;conseq  (: _ ==> r0{1} = _A{2} /\ r0{1} \in dout _sd).  
    + auto => /= &1 &2 [#] ->> ->> ->> ? ? ->> ->> ? H1 r1 _A2 _r2 [#] ->> H2; rewrite !get_setE //=; do split. 
      + smt(subm_catmrCl supp_dmatrix gt0_n gt0_nb gt0_m).
      + smt(@FMap @FSet).
      + smt(@FMap @FSet).
      + smt(fdom_set).
      + move => _sd'; case (_sd = _sd'); last by smt(@FMap @FSet).
        move => -> ?;rewrite !get_set_eqE 1,2:/# /=.
        smt(subm_catmrCl supp_dmatrix gt0_n gt0_nb gt0_m).
    rndsem* {2} 0;rnd; auto => /> &1 *; do split.
    + rewrite /dout /=. 
      move => _A2;rewrite supp_dmap => He. elim He => /= [#] _AB.
      rewrite supp_dmatrix 1,2: //.
      move => [#] *.
      have :=  mu1_dmatrix_fu duni_R _A2 _;1:smt(duni_R_funi).
      subst _A2.
      rewrite rows_subm cols_subm //= !lez_maxr 1..3:// => ?.
      by smt(aux).
    + move => ? rr ?;rewrite supp_dmap. exists (trmx rr / zerom nb m); split. 
      + rewrite duni_matrix_fu;1,2: by  smt(duni_matrix_fu gt0_n gt0_nb gt0_m).
        rewrite size_catmc;smt(duni_matrix_fu size_tr size_matrixc gt0_n gt0_nb gt0_m) => /=. 
      + smt(supp_dmatrix subm_catmrCl gt0_m gt0_n gt0_nb).
+ proc; inline *.
  rcondf{2}3; first by auto => />.
  rcondf{1}2; first by auto => />; smt(mem_fdom).
  wp;rnd{1};rnd{2};auto => />;smt(mem_fdom). 
qed.


lemma hop2_left &m:
  Pr[CPA(PKEROM.RO.LRO,LWE_PKE1,A).main() @ &m : res] =
  Pr[LWE2.LWE_ROM.LWE_RO(B2(A), LWE2.LWE_ROM.RO.LRO).main(false) @ &m : res].
proof.
byequiv => //.
proc; inline *; wp.
proc rewrite {1} 4 (doutE).
proc rewrite {2} 6 (doutE2).
proc rewrite {1} 16 (doutE).
swap {1} 8 -3.
swap {1} 8 -6.
call (:
  B2_RO_Fake._sd{2} \in RO.m{1} /\
  oget RO.m{1}.[B2_RO_Fake._sd{2}] = B2_RO_Fake.__A{2} /\
  fdom (glob PKEROM.RO.LRO){1} = fdom (glob LWE2.LWE_ROM.RO.LRO){2} /\
  forall sd, sd \in PKEROM.RO.RO.m{1} =>
  oget PKEROM.RO.RO.m{1}.[sd] = subm (trmx (oget LWE2.LWE_ROM.RO.RO.m{2}.[sd])) 0 m 0 n
); 1: by exact RO_sample.
swap{1} [19..21] -15; swap{1} 19 -6; swap{1} 17 4; swap{1} 15 5; wp; rnd.
rcondt{1} 10; 1: by auto => />; smt(mem_empty).
rcondt{2} 7; 1: by auto => />; smt(mem_empty).
rcondf{2} 16; 1: by auto => />;smt(get_setE).
rcondf{1} 18.
+ auto => />.
  seq 13 : #post; 1: by auto => />; smt(mem_set pk_encodeK).
  exlim (pk_decode pk).`2 => sd.
  call (: sd \in RO.m); 1: by proc; auto; smt(mem_set).
  auto.
wp.
seq 13 19: (
  #pre /\ ={pk, sd} /\
  B2_RO_Fake._sd{2} = sd{2} /\
  B2_RO_Fake.__A{2} = subm (trmx (oget LWE2.LWE_ROM.RO.RO.m{2}.[B2_RO_Fake._sd{2}])) 0 m 0 n /\
  trmx s'{1} = s{2} /\
  trmx (e'{1} || e''{1}) = e{2} /\
  trmx (r{1} || t{1}) = r{2} /\
  r{1} = oget RO.m{1}.[sd{1}] /\
  b'v{2} = r{2} * s{2} + e{2} /\
  pk{1} = pk_encode (t{1}, sd{1}) /\
  sd{2} \in RO.m{1} /\
  fdom RO.m{1} = fdom LWE2.LWE_ROM.RO.RO.m{2} /\
  (forall sd, sd \in RO.m{1} => oget RO.m{1}.[sd] = subm (trmx (oget LWE2.LWE_ROM.RO.RO.m{2}.[sd])) 0 m 0 n) /\
  rows s{2} = m /\ cols s{2} = mb /\
  rows e'{1} = mb /\ cols e'{1} = n /\
  rows e''{1} = mb /\ cols e''{1} = nb /\
  rows r{1} = m /\ cols r{1} = n /\
  rows t{1} = m /\ cols t{1} = nb
).
+ rnd{1};wp;rnd{2};wp;rnd{2};wp.
  rndsem*{1} 7;
  rnd (fun (x: matrix*matrix) => trmx (x.`1 || x.`2)) (fun x => (subm (trmx x) 0 m 0 n, subm (trmx x) 0 m n (n+nb))).
  wp.
  rndsem*{1} 4;
  rnd (fun (x: matrix*matrix) => trmx (x.`1 || x.`2)) (fun x => (subm (trmx x) 0 mb 0 n, subm (trmx x) 0 mb n (n+nb))).
  rnd trmx trmx.
  auto => />.
  move => s hs sd hsd.
  split => [? | *].
  + smt(dmatrix_tr1E supp_dmatrix gt0_m gt0_mb).
  + split => *.
    + smt(supp_dmatrix_tr gt0_m gt0_mb).
    + split => [?|*].
      + smt(gt0_n gt0_mb gt0_nb ltz_addl catmc_subm supp_dmatrix).
      + split => [*|? ?].
        + rewrite -(dmap_dprodE _ _ idfun) dmatrix_tr1E 2://; 1,2: by smt(supp_dmatrix gt0_n gt0_nb gt0_mb).
          by rewrite (in_dmap1E_can _ idfun idfun) 1,2:// dmatrix_catmr1E 1..2://;
          1: smt(dmatrix_catmr1E size_tr supp_dmatrix gt0_n gt0_nb gt0_mb).
        + rewrite -(dmap_dprodE _ _ idfun) supp_dmap.
          elim => [[e' e'']].
          rewrite supp_dprod !supp_dmatrix 1..6:// size_catmc /idfun /= => [#] hre' hce' he' hre'' hce'' he'' -> /=.
          rewrite hre' hce' hre'' hce'' /=.
          split => [i j [#]|*].
          + smt (rows_tr cols_tr rows_catmc cols_catmc get_catmc trmxE getm0E ltzNge ZR.addr0 ZR.add0r).
          + split => *.
            + smt(subm_catmrCr subm_catmrCl).
            + split => ?.
              + smt(supp_dmatrix gt0_n gt0_nb gt0_m catmc_subm). 
              + split => [*|? [r1 r2]].
                + rewrite -dprod_dlet.
                  smt(dmatrix_tr1E supp_dmatrix size_tr dmatrix_catmr1E gt0_n gt0_nb gt0_m).
                + rewrite -dprod_dlet supp_dprod /=.
                  rewrite !supp_dmatrix 1..6:// => [#] *.
                  do split.
                  + smt(rows_catmc rows_tr).
                  + smt(cols_catmc cols_tr).
                  + smt(rows_catmc cols_catmc rows_tr cols_tr get_catmc trmxE getm0E ZR.addr0 ZR.add0r).
                  + move => *.
                  + split => [|[#]hr1 hr2 ? ? ? ? ? ?].
                    + smt(subm_catmrCr subm_catmrCl).
                    + rewrite !get_setE /= !fdom_set -hr2 mem_set /=.
                      split => [?|].
                      by rewrite !get_setE mem_set mem_empty /=.
                      + smt(supp_dmatrix gt0_m gt0_n gt0_mb gt0_nb).
call (:
  B2_RO_Fake._sd{2} \in RO.m{1} /\
  oget RO.m{1}.[B2_RO_Fake._sd{2}] = B2_RO_Fake.__A{2} /\
  fdom (glob PKEROM.RO.LRO){1} = fdom (glob LWE2.LWE_ROM.RO.LRO){2} /\
  forall sd, sd \in PKEROM.RO.RO.m{1} =>
  oget PKEROM.RO.RO.m{1}.[sd] = subm (trmx (oget LWE2.LWE_ROM.RO.RO.m{2}.[sd])) 0 m 0 n
); 1: by exact RO_sample.
auto => //= &1 &2 [#].
move => ? -> -> -> -> -> -> <- <- <- -> -> -> ? <- //= h *;
do split;
1,3: rewrite //.
+ by apply h.
move => [#] ? ? ? rl ? ? ? ? ? [#] -> -> ? h' -> * => />.
+ rewrite pk_encodeK /= h' -h 1://.
  rewrite catmrDr addm_catmr; 1: by rewrite cols_mulmx => /#.
  pose r := oget _.
  have -> : subm (s'{1} * r + e'{1} || s'{1} * t{1} + e''{1}) 0 mb 0 n = s'{1} * r + e'{1}.
  + smt(subm_catmrCl rows_addm cols_addm rows_mulmx cols_mulmx).
  have -> : subm (s'{1} * r + e'{1} || s'{1} * t{1} + e''{1}) 0 mb n (n+nb) = s'{1} * t{1} + e''{1}.
  + smt(subm_catmrCr rows_addm cols_addm rows_mulmx cols_mulmx).
  trivial.
qed.

lemma hop2_right &m:
  Pr[LWE2.LWE_ROM.LWE_RO(B2(A),LWE2.LWE_ROM.RO.LRO).main(true) @ &m : res] =
  Pr[CPA(PKEROM.RO.LRO,LWE_PKE2,A).main() @ &m : res].
proof.
rewrite eq_sym.
byequiv => //.
proc; inline *; wp.
call (:
  B2_RO_Fake._sd{2} \in RO.m{1} /\
  oget RO.m{1}.[B2_RO_Fake._sd{2}] = B2_RO_Fake.__A{2} /\
  fdom (glob PKEROM.RO.LRO){1} = fdom (glob LWE2.LWE_ROM.RO.LRO){2} /\
  forall sd, sd \in PKEROM.RO.RO.m{1} =>
  oget PKEROM.RO.RO.m{1}.[sd] = subm (trmx (oget LWE2.LWE_ROM.RO.RO.m{2}.[sd])) 0 m 0 n
); 1: by apply RO_sample.
swap{2} 12 11; swap{2} [9..10] 12; swap{1} 8 -3.
wp; rndsem*{1} 13; rnd (fun (u: matrix*matrix) => trmx (u.`1||u.`2)) (fun u => (subm (trmx u) 0 mb 0 n, subm (trmx u) 0 mb n (n+nb))); wp; rnd.
call (:
  B2_RO_Fake._sd{2} \in RO.m{1} /\
  oget RO.m{1}.[B2_RO_Fake._sd{2}] = B2_RO_Fake.__A{2} /\
  fdom (glob PKEROM.RO.LRO){1} = fdom (glob LWE2.LWE_ROM.RO.LRO){2} /\
  forall sd, sd \in PKEROM.RO.RO.m{1} =>
  oget PKEROM.RO.RO.m{1}.[sd] = subm (trmx (oget LWE2.LWE_ROM.RO.RO.m{2}.[sd])) 0 m 0 n
); 1: by apply RO_sample.

rcondt{1} 6; 1: by auto; smt(mem_empty).
rcondt{2} 7; 1: by auto; smt(mem_empty).
rcondf{2} 13; 1: by auto; smt(mem_set).
proc rewrite{2} 6 (doutE2).
proc rewrite{1} 4 (doutE).
wp; rnd{2}; rnd{1}; wp.
rndsem*{1} 3; rnd (fun (r: matrix*matrix) => trmx(r.`1||r.`2)) (fun r => (subm (trmx r) 0 m 0 n, subm (trmx r) 0 m n (n+nb))).
wp;do 2! rnd{2}; auto => />.

move => sd ? s hs e he.
split => [?|*].
+ smt(supp_dmatrix gt0_nb gt0_n gt0_m catmc_subm).
+ split => [?|? [r1 r2]].
  + rewrite -dprod_dlet.
    smt(dmatrix_tr1E supp_dmatrix size_tr dmatrix_catmr1E gt0_n gt0_nb gt0_m).
  + rewrite -dprod_dlet supp_dprod /= !supp_dmatrix 1..7:// size_catmc !rows_tr !cols_tr => [#] *.
    do split; 1,2: by rewrite /#.
    + smt (rows_catmc cols_catmc rows_tr cols_tr get_catmc trmxE getm0E ZR.addr0 ZR.add0r).
    + move => [#] *; split => [|? s' hs' r hr].
      + smt(subm_catmrCr subm_catmrCl).
      + do split.
        + smt(get_setE subm_catmcCr catmcT trmxK).
        + smt(mem_set).
        + smt(get_setE subm_catmcCl catmcT trmxK).
        + smt(fdom_set).
        + smt(mem_set mem_empty get_setE subm_catmcCl catmcT trmxK).
        + move => *.
          split => [?|*].
          + smt(supp_dmatrix gt0_mb addr_ge0 gt0_n gt0_nb addr_ge0 catmc_subm lez_addl).
          + split => [?|? [b' v]]. 
            + rewrite -dprod_dlet; smt(dmatrix_tr1E size_tr dmatrix_catmr1E gt0_mb gt0_n gt0_nb supp_dmatrix).
            + rewrite -dprod_dlet supp_dprod /= !supp_dmatrix 1..7:// size_catmc !rows_tr !cols_tr => [#] *.
              do split; 1,2: by rewrite /#.
              + smt (rows_catmc cols_catmc get_catmc rows_tr cols_tr getm0E trmxE ZR.addr0 ZR.add0r).
              + move => *; smt(subm_catmrCr subm_catmrCl).
qed.

end section.

(* Final game analysis *)

section.

declare module A <: Adversary {-LRO, -B1, -B2,
  -LWE1.LWE_ROM.RO.LRO, -LWE1.LWE_ROM.B,
  -LWE1.LWE_M, -LWE1.Hyb.Count, -LWE1.LWE_Ob, -LWE1.Hyb_RO.RO, -LWE1.Hyb_RO.FRO, -LWE1.LWE_V_Aux, -LWE1.LWE_V,
  -LWE2.LWE_ROM.RO.LRO, -LWE2.LWE_ROM.B,
  -LWE2.LWE_M, -LWE2.Hyb.Count, -LWE2.LWE_Ob, -LWE2.Hyb_RO.RO, -LWE2.Hyb_RO.FRO, -LWE2.LWE_V_Aux, -LWE2.LWE_V
}.

local module Game2RO(A: Adversary) = {
  proc main() = {
    var sd, _A, _B, m0, m1, _B', v, c, b, b';
    LRO.init();
    sd <$ dseed;
    _A <@ LRO.get(sd); 
    _B <$ dmatrix duni_R m nb;
    (m0, m1) <@ A(LRO).choose(pk_encode (_B, sd));
    b <$ {0,1};
    _B' <$ dmatrix duni_R mb n;
    v <$ dmatrix duni_R mb nb;
    c <- c_encode(_B', v);
    b' <@ A(LRO).guess(c);
    return b = b';
  }
}.

local lemma game2_equiv &m :
  Pr[CPA(LRO, LWE_PKE2,A).main() @ &m : res] =
  Pr[Game2RO(A).main() @ &m : res].
proof.
byequiv => //.
proc; inline *.
call (: ={glob LRO}); 1: by sim.
wp. rnd (fun z => z + m_encode u{1}) (fun z => z - m_encode u{1}). rnd; wp; rnd.
call (: ={glob LRO}); 1: by sim.
wp; rnd; rnd{1}; auto => /> *.
rewrite mem_empty /= => *.  
split => [|*].
+ smt(supp_dmatrix addmA addmC addmN addm0 m_encode_rows m_encode_cols).
+ split => *.
  + rewrite !mu1_uni 1,2:duni_matrix_uni.
  + smt(supp_dmatrix duni_matrix_fu rows_addm rows_neg cols_addm cols_neg m_encode_rows m_encode_cols).
  + split => *.
    + smt(duni_matrix_fu rows_addm rows_neg cols_addm cols_neg m_encode_rows m_encode_cols).
    + split => [|/#].
      + smt(addmA addmN m_encode_rows m_encode_cols addm0).
qed.

local lemma game2_prob &m :
  (forall (O <: POracle), islossless O.get => islossless A(O).guess) =>
  (forall (O <: POracle), islossless O.get => islossless A(O).choose) =>
  Pr[Game2RO(A).main() @ &m : res] = 1%r / 2%r.
proof.
move => A_guess_ll A_choose_ll.
move : (A_guess_ll (LRO) _); 1: by islossless; smt(duni_matrix_ll).
move : (A_choose_ll (LRO) _);  1: by islossless; smt(duni_matrix_ll).
move => _A_choose_ll _A_guess_ll.
byphoare => //;proc.
swap 6 4.
rnd  (pred1 b')=> //=; conseq (: _ ==> true).
+ by move=> />; apply DBool.dbool1E.
by islossless;smt(duni_matrix_ll duni_ll dshort_ll).
qed.

lemma main_theorem &m :
  (forall (O <: POracle), islossless O.get => islossless A(O).guess) =>
  (forall (O <: POracle), islossless O.get => islossless A(O).choose) =>
  Pr[CPA(LRO,LWE_PKE,A).main() @ &m : res] -  1%r / 2%r =
    nb%r * (Pr[LWE1.LWE_V(LWE1.LWE_ROM.B(B1(A), LWE1.LWE_ROM.RO.LRO)).main(false) @ &m : res]
            - Pr[LWE1.LWE_V(LWE1.LWE_ROM.B(B1(A), LWE1.LWE_ROM.RO.LRO)).main(true) @ &m : res]) +
    mb%r * (Pr[LWE2.LWE_V(LWE2.LWE_ROM.B(B2(A), LWE2.LWE_ROM.RO.LRO)).main(false) @ &m : res]
            - Pr[LWE2.LWE_V(LWE2.LWE_ROM.B(B2(A), LWE2.LWE_ROM.RO.LRO)).main(true) @ &m : res]).
proof.                                            
move => A_guess_ll A_choose_ll.
have <- := LWE1.LWE_ROM.LWE_RO_Hybrid &m (B1(A)) _.
+ move => O hO.
  proc;call(A_guess_ll O).
  call(: true);1: by islossless.
  by rnd;call(A_choose_ll O);islossless.
have <- := LWE2.LWE_ROM.LWE_RO_Hybrid &m (B2(A)) _.
+ move => O hO.
  proc;call(A_guess_ll (B2_RO_Fake(O)));1: by islossless.
  by wp;rnd;call(A_choose_ll (B2_RO_Fake(O)));islossless.
rewrite (hop1_left A &m).
rewrite (hop1_right A &m).
rewrite (hop2_left A &m).
rewrite (hop2_right A &m).
rewrite game2_equiv.
rewrite game2_prob 1,2://.
by ring.
qed.                                            

end section.

end LWE_PKE.
