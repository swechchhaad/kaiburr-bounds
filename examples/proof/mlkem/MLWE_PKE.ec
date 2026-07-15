require import AllCore Distr List FMap Dexcepted PKE_ROM.
require (****) RndExcept StdOrder MLWE.

theory MLWE_PKE.

clone import MLWE as MLWE_.
import MLWE_ROM.

import StdOrder.IntOrder Matrix_ Big.BAdd.

type plaintext.
type ciphertext.

type raw_ciphertext = vector * R.

op m_encode : plaintext -> R. 
op m_decode : R -> plaintext.

op c_encode : raw_ciphertext -> ciphertext.
op c_decode : ciphertext -> raw_ciphertext.

type pkey.
type skey.

type raw_pkey  = vector * seed.
type raw_skey  = vector.

op pk_encode : raw_pkey -> pkey.
op sk_encode : raw_skey -> skey.
op pk_decode : pkey -> raw_pkey.
op sk_decode : skey -> raw_skey.

axiom pk_encodeK : cancel pk_encode pk_decode.
axiom sk_encodeK : cancel sk_encode sk_decode.


(******************************************************************)
(*    The Security Games                                          *)
clone import PKE_ROM with 
  type RO.in_t    = seed,
  type RO.out_t   = Matrix_.Matrix.matrix,  
  op   RO.dout    = fun _ => duni_matrix,  
  type RO.d_in_t  = bool, 
  type RO.d_out_t = bool,
  type pkey <- pkey,
  type skey <- skey,
  type plaintext <- plaintext,
  type ciphertext <- ciphertext.

import MLWE_ROM.RO.

(******************************************************************)
(*                    The Encryption Scheme                       *)

(* Encryption schemes in the ROM always take RO. *)


module MLWE_PKE(H : POracle) (* : Scheme *) = {
  proc kg() : pkey * skey = {
    var sd,s,e,_A,t;
    sd <$ dseed;
    s  <$ dshort;
    e  <$ dshort;
    _A <@ H.get(sd);
    t  <- _A *^ s + e;
    return (pk_encode (t,sd),sk_encode s);
  }
  
  proc enc(pk : pkey, m : plaintext) : ciphertext = {
    var sd,t,r,e1,e2,_A,u,v;
    (t,sd) <- pk_decode pk;
    r  <$ dshort;
    e1 <$ dshort;
    e2 <$ dshort_R;
    _A <@ H.get(sd);
    u  <- trmx _A *^ r + e1;
    v  <- (t `<*>` r) &+ e2 &+ (m_encode m);
    return (c_encode (u,v));
  }
  
  proc dec(sk : skey, c : ciphertext) : plaintext option = {
    var u,v;
    (u,v) <- c_decode c;
    return Some (m_decode (v &- (sk_decode sk `<*>` u)));
  }
}.


(*****************************************************)
(*       Game Hopping Security                       *)
(*****************************************************)


(* Hop 1 *)

module MLWE_PKE1(H : POracle) = {
  proc kg() : pkey * skey = {
    var _A,sd,s,t;
    sd <$ dseed;
    s  <$ dshort;
    t  <$ duni;
    _A <@ H.get(sd);
    return (pk_encode (t,sd),sk_encode s);
  }

  include MLWE_PKE(H) [-kg]

}.

module (B1(A : Adversary) : ROAdv_T) (H : POracle) = {
  proc guess(sd : seed, t : vector, uv : vector * R) : bool = {
    var pk,  m0, m1, c, b, b';
    pk <- (uv.`1,sd);
    (m0, m1) <@ A(H).choose(pk_encode pk);
    b <$ {0,1};
    c <@ MLWE_PKE(H).enc(pk_encode pk, if b then m1 else m0);
    b' <@ A(H).guess(c);
    return b' = b;
  }
}.

section.

declare module A <: Adversary {-LRO,-B1}.

lemma hop1_left_s &m: 
  Pr[CPA(LRO,MLWE_PKE,A).main() @ &m : res] =
  Pr[MLWE_RO(B1(A),LRO).main(false,false) @ &m : res].
proof.
byequiv => //.
proc.
seq 1 1 : (!b{2} /\ !tr{2} /\ ={glob A,glob RO}); 1: by  inline *; conseq => />; sim. 
inline {1} MLWE_PKE(LRO).kg MLWE_PKE(LRO).enc.
inline {2} B1(A,LRO).guess MLWE_PKE(LRO).enc.
wp; call(: ={glob RO}); 1: by sim.
wp; call(: ={glob RO});1: by sim.
rnd;rnd;rnd;wp;rnd;wp. 
call(_: ={glob RO}); 1: by sim.
swap {2} [7..8] -6.
wp;rnd{2};wp;rnd{2};wp.
wp; call(: ={glob RO});1: by sim.
by wp;rnd;rnd;rnd;auto => />;smt(dshort_ll duni_ll).
qed.

lemma hop1_right_s &m: 
  Pr[CPA(LRO,MLWE_PKE1,A).main() @ &m : res] =
  Pr[MLWE_RO(B1(A),LRO).main(false,true) @ &m : res].
proof.
byequiv => //.
proc.
seq 1 1 : (b{2} /\ !tr{2} /\ ={glob A,glob RO}); 1 : by inline *;conseq => />;sim.
inline {1} MLWE_PKE1(LRO).kg MLWE_PKE(LRO).enc.
inline {2} MLWE_PKE1(LRO).enc B1(A,LRO).guess.
wp; call(: ={glob RO}); 1: by sim.
wp; call(: ={glob RO});1: by sim.
rnd;rnd;rnd;wp;rnd;wp. 
call(_: ={glob RO}); 1: by sim.
wp;rnd{2};wp;rnd{2};wp;rnd{2};wp. 
swap{2} 3 -2.
swap{2} 7 -3.
wp; call(: ={glob RO});1: by sim.
by wp;rnd;rnd;rnd;auto => />;smt(dshort_ll duni_ll).
qed.

end section.

(* Hop 2 *)

module MLWE_PKE2(O : POracle) = {

  proc enc(pk : pkey, m : plaintext) : ciphertext = {
    var _A,u, v;
    _A <@ O.get((pk_decode pk).`2);
    u <$duni;
    v <$duni_R;
    return (c_encode (u,v &+ m_encode m));
  }

  include MLWE_PKE1(O) [-enc]

}.


module (B2(A : Adversary) : ROAdv_T) (H : POracle) = {
  var _sd : seed
  var _A : matrix
  proc guess(sd : seed, t : vector, uv : vector * R) : bool = {
    var c, b, b', pk, m0, m1;
    _sd <-sd;
    _A <@ H.get(sd); (* this makes the proof easier *)
    b <$ {0,1};
    pk <- pk_encode (t,sd);
    (m0, m1) <@ A(H).choose(pk);
    c <- c_encode (uv.`1, uv.`2 &+ m_encode (if b then m1 else m0));
    b' <@ A(H).guess(c);
    return b' = b;
  }

}.

section.

declare module A <: Adversary {-B2, -LRO}.

lemma hop2_left_s &m: 
  Pr[CPA(LRO,MLWE_PKE1,A).main() @ &m : res] =
  Pr[MLWE_RO(B2(A),LRO).main(true,false) @ &m : res].
proof.
byequiv => //.
proc.
seq 1 1 : (!b{2} /\ tr{2} /\ ={glob A,glob RO}); 1: by inline *;conseq/>;sim.
inline {1} MLWE_PKE1(LRO).kg MLWE_PKE1(LRO).enc.
inline {2} B2(A,LRO).guess.
wp; call(: ={glob RO}); 1: by sim.
swap {1} 2 -1.
swap {1} [11..13] -7.
swap {2} 11 -10.
swap {2} 8 -7.
swap {2} 9 -5.
swap {2} 10 -3.
swap {2} 17 2.
inline *.
wp;rnd{1};wp;rnd.
seq 11 23 : (={glob RO,pk,sd, glob A} 
     /\ _A{1} = trmx _A{2} 
     /\ trmx _A{1} *^ r{1} + e1{1} = uv{2}.`1 
     /\ (t{1} `<*>` r{1}) &+ e2{1}  = uv{2}.`2
     /\ (pk_decode pk{1}).`2 = sd{1} 
     /\ (pk_decode pk{2}).`1 = t{1} 
     /\ sd{1} \in RO.m{1} 
     /\ _A{1} = oget RO.m{1}.[sd{1}]
     /\ B2._A{2} = _A{1} 
     /\ B2._sd{2} = sd{1}).
+ by wp;rnd{2};wp;rnd;wp;rnd;rnd;rnd;rnd;rnd;rnd{1};rnd{2};rnd{2}; 
    auto => />;smt(duni_ll dshort_ll duni_matrix_ll mem_set pk_encodeK trmxK).
call(: ={glob RO} /\ B2._sd{2} \in RO.m{2} /\ oget RO.m{2}.[B2._sd{2}] = B2._A{2}); 
   1: by proc;auto => />;smt(mem_set get_setE).
by auto => />;smt(duni_matrix_ll).
qed.

lemma hop2_right_s &m: 
  Pr[CPA(LRO,MLWE_PKE2,A).main() @ &m : res] =
  Pr[MLWE_RO(B2(A),LRO).main(true,true) @ &m : res].
proof.
byequiv => //.
proc.
seq 1 1 : (b{2} /\ tr{2} /\ ={glob A, glob RO}); 1: by inline *;conseq />;sim.
inline {1} MLWE_PKE2(LRO).kg MLWE_PKE2(LRO).enc.
inline {2} B2(A,LRO).guess.
wp; call(: ={glob RO}); 1: by sim.
swap {1} 2 -1.
swap {1} [11..12] -7.
swap {2} 9 -8. 
swap {2} 9 -6.
swap {2} 9 -5.
swap {2} 11 -4.
swap {2} 17 2.
inline *.
rcondf{1} 17.
+ move => *;wp;rnd;wp;rnd. 
  seq 10 : (sd \in RO.m /\ (pk_decode pk).`2 = sd);1: by auto;smt(pk_encodeK mem_set).
  exlim sd => _sd.
  call(: _sd \in RO.m);1: by proc;inline*; auto; smt(get_setE).
  by auto.
rcondf{2} 21;1: by move => *;auto => />;smt(mem_set).
wp;rnd{1};wp;rnd.
call (: ={glob RO}); 1: by sim.
by wp;rnd{2};wp;rnd;wp;rnd;rnd{2};rnd{2};rnd;rnd;rnd;rnd{1};rnd{2};
auto;
smt(duni_ll dshort_ll duni_matrix_ll mem_set pk_encodeK trmxK).
qed.

end section.

(* Final game analysis *)

section.

declare module A <: Adversary {-LRO, -B1, -B2,  -MLWE_vs_MLWE_ROM.B,  -MLWE_vs_MLWE_ROM.Bt}.

local module Game2RO(A : Adversary) = {
  proc main() = {
    var sd, _A, s, t, m0, m1, u, v, b, b';
    LRO.init();
    sd <$ dseed;
    _A <@ LRO.get(sd);
    s <$ dshort;
    t <$ duni;
    (m0, m1) <@ A(LRO).choose(pk_encode (t,sd));
    _A <@ LRO.get(sd);
    u <$duni;
    v <$duni_R;
    b' <@ A(LRO).guess(c_encode (u,v));
    b <$ {0,1};
    return b = b';
  }
}.


local lemma game2_equiv_s &m : 
  Pr[CPA(LRO,MLWE_PKE2,A).main() @ &m : res] = 
  Pr[Game2RO(A).main() @ &m : res].
proof.
byequiv => //.
proc; inline *.
swap {2} [7..8] -4.
swap {2} 17 -7.
wp; call(_: ={glob LRO}); 1: by sim.  
wp;rnd (fun z, z &+ m_encode (if b then m1 else m0){2})
       (fun z, z &- m_encode (if b then m1 else m0){2}).
rcondf{1} 16. 
+ move => *;wp;rnd;wp;rnd. 
  seq 9 : (sd \in RO.m /\ (pk_decode pk).`2 = sd);1: by auto;smt(pk_encodeK mem_set).
  exlim sd => _sd.
  call(: _sd \in RO.m);1: by proc;inline*; auto; smt(get_setE).
  by auto.
rcondf{2} 13. 
+ move => *;wp;rnd;wp;rnd. 
  seq 8 : (sd \in RO.m);1: by auto;smt(pk_encodeK mem_set).
  exlim sd => _sd.
  call(: _sd \in RO.m);1: by proc;inline*; auto; smt(get_setE).
  by auto.
rnd;wp;rnd;wp;rnd;call(_: ={glob LRO}); 1: by sim.  
wp;rnd;wp;rnd;rnd;rnd. 
auto => />.
+ move => *; do split. 
+ move => *; do split. 
  + by move => *; ring. 
+ move => *; do split. 
  + by move => *; ring. 
by smt(). 
+ move => *; split; 1: by move => *; ring.
+ move => *; split; 1: by move => *; ring.
by smt().
qed.

local lemma game2_prob_s &m :
  (forall (O <: POracle), islossless O.get => islossless A(O).guess) =>
  (forall (O <: POracle), islossless O.get => islossless A(O).choose) =>
  Pr[Game2RO(A).main() @ &m : res] = 1%r / 2%r.
proof.
move => A_guess_ll A_choose_ll.
move : (A_guess_ll (LRO) _); 1: by islossless; smt(duni_matrix_ll).
move : (A_choose_ll (LRO) _);  1: by islossless; smt(duni_matrix_ll).
move => _A_choose_ll _A_guess_ll.
byphoare => //;proc.
rnd  (pred1 b')=> //=; conseq (: _ ==> true).
+ by move=> />; apply DBool.dbool1E.
by islossless;smt(duni_matrix_ll duni_ll dshort_ll).
qed.

import MLWE_vs_MLWE_ROM.
lemma main_theorem_s &m :
  (forall (O <: POracle), islossless O.get => islossless A(O).guess) =>
  (forall (O <: POracle), islossless O.get => islossless A(O).choose) =>
  Pr[CPA(LRO,MLWE_PKE,A).main() @ &m : res] -  1%r / 2%r =
    Pr[MLWE(B(B1(A),LRO)).main(false) @ &m : res] -
       Pr[MLWE(B(B1(A),LRO)).main(true) @ &m : res] + 
    Pr[MLWE(Bt(B2(A),LRO)).main(false) @ &m : res] -
       Pr[MLWE(Bt(B2(A),LRO)).main(true) @ &m : res].
proof.
move => A_guess_ll A_choose_ll.
rewrite -(MLWE_vs_MLWE_ROM.MLWE_RO_equiv false &m (B1(A))).
rewrite -(MLWE_vs_MLWE_ROM.MLWE_RO_equiv true &m (B1(A))).
rewrite -(MLWE_vs_MLWE_ROM.MLWE_RO_equiv_t false &m (B2(A))).
rewrite -(MLWE_vs_MLWE_ROM.MLWE_RO_equiv_t true &m (B2(A))).
rewrite (hop1_left_s A &m).
rewrite -(hop1_right_s A &m).
rewrite (hop2_left_s A &m).
rewrite -(hop2_right_s A &m).
rewrite (game2_equiv_s &m).
rewrite (game2_prob_s &m _ _) //.
by ring.
qed.

(* TO DO: Go down to MLWE using general lemma in MLWE_ROM *)

end section.

(******************************************************************)
(*                        Correctness                             *)
(* We consider adversarial correctness, where the attacker can    *)
(* choose the message where correctness is checked after seeing   *)
(* the public-key. This setting seems to be the one in which      *)
(* failure probability is considered in the FO construction.      *)
(******************************************************************)

(* We want to prove a concrete bound on the probability of failure
   for MLKEM. We will do so generically by first showing at this
   level that it all comes down to the noise distribution. *)

(* We express rounding errors as additive noise *)

op noise_exp _A s e r e1 e2 m = 
    let t = _A *^ s + e in
    let u = m_transpose _A *^ r + e1 in
    let v = (t `<*>` r) &+ e2 &+ (m_encode m) in
    let (u',v') = c_decode (c_encode (u,v)) in
        v' &- (s `<*>` u') &- (m_encode m).

(* We can derive the noise expression by introducing
   operators that compute the rounding error *)

op rnd_err_v : R -> R.
op rnd_err_u : vector -> vector.

axiom encode_noise u v :
   c_decode (c_encode (u,v)) = 
      (u + rnd_err_u u, v &+ rnd_err_v v).

lemma matrix_props1 _A s e r :
  (_A *^ s + e) `<*>` r = 
  (s ^* m_transpose _A `<*>` r) &+ (e `<*>` r).
proof. by rewrite dotpDl -mulmxTv trmxK. qed.

lemma matrix_props2 s _A r e1 cu :
  s `<*>` (m_transpose _A *^ r + e1 + cu) = 
  (s ^* m_transpose _A `<*>` r) &+ 
    (s `<*>` e1) &+ (s `<*>` cu).
proof. by rewrite !dotpDr dotpC dotp_mulmxv dotpC. qed.

lemma noise_exp_val _A s e r e1 e2 m :
  noise_exp _A s e r e1 e2 m = 
  let t = _A *^ s + e in
  let u = m_transpose _A *^ r + e1 in
  let v = (t `<*>` r) &+ e2 &+ (m_encode m) in
  let cu = rnd_err_u u in
  let cv = rnd_err_v v in
  ((e `<*>` r) &- (s `<*>` e1) &- (s `<*>` cu) &+ e2) &+ cv.
proof.
  rewrite /noise_exp /= encode_noise /= matrix_props1 matrix_props2; ring. 
qed.

(* The above noise expression is computed over the abstract
   rings that define the scheme. Noise bounds are checked and
   computed over the integers. *)

op max_noise : int.
op under_noise_bound : R -> int -> bool.

axiom good_decode m n :
  under_noise_bound n max_noise =>
  m_decode (m_encode m &+ n) = m.

(* We now rewrite the correctness game in terms of noise *)
module CorrectnessAdvNoise(A : CORR_ADV) = {
  proc main() = {
    var sd,s,e,_A,r,e1,e2,m,n;
    LRO.init();
    sd <$ dseed;
    _A <@ LRO.get(sd);
    r <$ dshort;
    s <$ dshort;
    e <$ dshort;
    e1 <$ dshort;
    e2 <$ dshort_R;
    m <@ A(LRO).find(pk_encode (_A *^ s + e,sd),sk_encode s);
    n <- noise_exp _A s e r e1 e2 m;
    return (!under_noise_bound n max_noise);
  }
}.

section.

declare module A <: CORR_ADV {-LRO}.

lemma correctness &m:
  (forall (O <: RO), islossless O.get => islossless A(O).find) =>
  Pr[ Correctness_Adv(LRO,MLWE_PKE,A).main() @ &m : res]  <= 
       Pr[ CorrectnessAdvNoise(A).main() @ &m : res].
proof.
move => A_ll.
byequiv => //=.
proc.  
inline *.
rcondt {1} 7; 1: by auto;smt(mem_empty).
rcondt {2} 5; 1: by auto;smt(mem_empty).
rcondf {1} 20.
+ move => *. wp;rnd;wp;rnd;rnd;rnd;wp. 
  seq 10 : (sd \in RO.m /\ sd = (pk_decode pk).`2);1: by auto;smt(pk_encodeK mem_set).
  exlim sd => _sd.
  call(: _sd \in RO.m);1: by proc;inline*; auto; smt(get_setE).
  by auto.
swap {2} [10..11] 1.
swap {2} 7 3.
wp;rnd{1};wp;rnd;rnd;rnd;wp. 
seq 10 8 : (={glob A, glob RO, sd, s, e,_A} /\
    pk{1} = pk_encode (oget RO.m{2}.[sd{1}] *^ s{2} + e{2}, sd{1}) /\ sk{1} = sk_encode s{2} /\
   sd{1} \in RO.m{1} /\ _A{1} = oget (RO.m{1}.[sd{1}])); 1: by swap {2} [7..8] -4; auto => />;  smt(mem_set get_setE).
exlim sd{1}, _A{1} => _sd1 _A1.
call(: ={glob RO} /\ _sd1 \in RO.m{1} /\ _A1 = oget (RO.m{1}.[_sd1])); 1: by proc;inline *;auto => />; smt(get_setE mem_set). 
auto => /> &1 &2 m2 rom2 ? H r1 _ e11 _ e21 _;split;  1: smt(duni_matrix_ll).
move => ???.
+ rewrite  encode_noise /= !pk_encodeK !sk_encodeK /= -H.
  rewrite (_: 
     ((oget RO.m{1}.[_sd1] *^ s{1} + e{1} `<*>` r1) &+ e21 &+ m_encode m2 &+
    rnd_err_v ((oget RO.m{1}.[_sd1] *^ s{1} + e{1} `<*>` r1) &+ e21 &+ m_encode m2) &- (s{1} `<*>` trmx (oget RO.m{1}.[_sd1]) *^ r1 + e11 + rnd_err_u (trmx (oget RO.m{1}.[_sd1]) *^ r1 + e11)))= 
  m_encode m2 &+ noise_exp (oget RO.m{1}.[_sd1]) s{1}  e{1} r1 e11 e21 m2).   
   by rewrite noise_exp_val /= !matrix_props1 !matrix_props2;ring.
by smt(good_decode).
qed.

end section.

axiom noise_commutes n n' maxn (b : int) : 
  under_noise_bound n' b =>
  under_noise_bound n (maxn - b) =>
  under_noise_bound (n &+ n') maxn.

axiom noise_preserved n maxn :
  under_noise_bound n maxn = 
  under_noise_bound (ZR.([-]) n) maxn.

op noise_exp_no_rounding s e r e1 e2 = 
    ((e `<*>` r) &- (s `<*>` e1) &+ e2).

op noise_exp_rounding _A s e r e1 e2 = 
  let u = m_transpose _A *^ r + e1 in
  let cu = rnd_err_u u in
    ((e `<*>` r) &- (s `<*>` e1) &+ e2 &- (s `<*>` cu)).

op noise_exp_u _A s r e1 = 
  let u = m_transpose _A *^ r + e1 in
  let cu = rnd_err_u u in
  (ZR.zeror &- (s `<*>` cu)).

op noise_exp_v _A s e r e2 m =
  let t = _A *^ s + e in
  let v = (t `<*>` r) &+ e2 &+ (m_encode m) in
  let cv = rnd_err_v v in
  cv.


lemma parts_work_rounding _A s e r e1 e2 m :
  noise_exp _A s e r e1 e2 m =
  noise_exp_rounding _A s e r e1 e2  &+ noise_exp_v _A s e r e2 m by rewrite noise_exp_val /noise_exp_simpl /noise_exp_rounding /noise_exp_v /=; ring. 

lemma parts_work _A s e r e1 e2 :
  noise_exp_rounding _A s e r e1 e2 =
  noise_exp_no_rounding s e r e1 e2 &+ noise_exp_u _A s r e1 by rewrite  /noise_exp_rounding /noise_exp_no_rounding /noise_exp_u /=; ring. 

module CB(A : CORR_ADV) = {
  var s : vector
  var e : vector
  var _A : matrix
  var r : vector
  var e1 : vector
  var e2 : R
  var n1 : R
  var n2 : R
  var u : vector
  var cu : vector
  var m : plaintext


  proc main() = {
    var sd;
    LRO.init();
    sd <$ dseed;
    _A <@ LRO.get(sd);
    r <$ dshort;
    s <$ dshort;
    e <$ dshort;
    e1 <$ dshort;
    e2 <$ dshort_R;
    m <@ A(LRO).find(pk_encode (_A *^ s + e,sd),sk_encode s);
    n1 <- noise_exp_rounding _A s e r e1 e2;
    n2 <- noise_exp_v _A s e r e2 m;
  }
}.

(** OVER ESTIMATE THE LAST TERM **)

op cv_bound_max : int.
axiom cv_bound_valid _A s e r e2 m :
  s \in dshort =>
  e \in dshort =>
  _A \in duni_matrix =>
  r \in dshort =>
  e2 \in dshort_R =>
  let t = _A *^ s + e in
  let v = (t `<*>` r) &+ e2 &+ (m_encode m) in
  under_noise_bound (rnd_err_v v) cv_bound_max.


section.

declare module A <: CORR_ADV {-LRO,-RO, -CB}.

lemma correctness_split_aux &m cv_bound failprob1 failprob2:
  (forall (O <: RO), islossless O.get => islossless A(O).find) =>

  Pr[ CB(A).main() @ &m : 
        !under_noise_bound CB.n1 (max_noise - cv_bound)] <= failprob1 =>

  Pr[ CB(A).main() @ &m : 
        !under_noise_bound CB.n2 (cv_bound)] <= failprob2 =>

  Pr[ CorrectnessAdvNoise(A).main() @ &m : res] <=
       failprob1 + failprob2.
proof.
move =>  A_ll bd1 bd2.
have  : Pr[CorrectnessAdvNoise(A).main() @ &m : res] <=
  Pr[CB(A).main() @ &m : 
        ! under_noise_bound CB.n1 (max_noise - cv_bound) \/
        ! under_noise_bound CB.n2 cv_bound ]; last by rewrite Pr[mu_or];smt(mu_bounded).
byequiv => //.
proc; inline *.
rcondt{1}5; 1: by move => *;  auto => />;smt(mem_empty).
rcondt{2}5; 1: by move => *; auto => />;smt(mem_empty).
wp;call(_: ={glob RO});1: by sim.
conseq />;1:by smt(). 
by auto => />;smt(parts_work_rounding noise_commutes noise_preserved).
qed.

(*******)

module CB1 = {

  proc main(cv_bound : int) = {
    var _A, r,s,e,e1,e2,n;
    _A <$ duni_matrix;
    r <$ dshort;
    s <$ dshort;
    e <$ dshort;
    e1 <$ dshort;
    e2 <$ dshort_R;
    n <- noise_exp_rounding _A s e r e1 e2;
    return !under_noise_bound n (max_noise - cv_bound);
  }
}.

lemma cb1 &m  cv_bound : 
  (forall (O <: RO), islossless O.get => islossless A(O).find) =>
  Pr[ CB(A).main() @ &m : 
        !under_noise_bound CB.n1 (max_noise - cv_bound)] =
  Pr[ CB1.main(cv_bound) @ &m : res].
move => A_ll.
byequiv => //; proc; inline *.
wp;call{1}(_: true ==> true);1: by apply (A_ll (LRO)); apply RO_get_ll; smt(duni_matrix_ll). 
rcondt{1}5; 1: by move => *; auto => />;smt(mem_empty).
by auto => />; smt(get_setE duni_matrix_ll).
qed.


module CB2(A : CORR_ADV) = {
  proc main(cv_bound : int) = {
    var sd,_A,r,s,e,e1,e2,m,n;
    LRO.init();
    sd <$ dseed;
    _A <@ LRO.get(sd);
    r <$ dshort;
    s <$ dshort;
    e <$ dshort;
    e1 <$ dshort;
    e2 <$ dshort_R;
    m <@ A(LRO).find(pk_encode (_A *^ s + e,sd),sk_encode s);
    n <- noise_exp_v _A s e r e2 m;
    return !under_noise_bound n cv_bound;
  }
}.

lemma cb2 &m cv_bound : 
  Pr[ CB(A).main() @ &m : 
        !under_noise_bound CB.n2 cv_bound] =
  Pr[ CB2(A).main(cv_bound) @ &m : res].
byequiv => //; proc; inline *.
wp;call(_: ={glob LRO}); 1: by sim.
rcondt{1}5; 1: by move => *; auto => />;smt(mem_empty). 
rcondt{2}5; 1: by move => *; auto => />;smt(mem_empty). 
by auto => />;smt(get_set_sameE).
qed.

(*******)


lemma correctness_split &m cv_bound failprob1 failprob2 :
  (forall (O <: RO), islossless O.get => islossless A(O).find) =>
  Pr[ CB1.main(cv_bound) @ &m : res] <= failprob1 =>
  Pr[ CB2(A).main(cv_bound) @ &m : res] <= failprob2 =>

  Pr[ Correctness_Adv(LRO,MLWE_PKE,A).main() @ &m : res]  <=
       failprob1 + failprob2.
move => A_ll fp1 fp2.
have := (correctness A  &m A_ll).
rewrite -(cb1 &m cv_bound A_ll) in fp1.
rewrite -(cb2 &m cv_bound) in fp2.
have := (correctness_split_aux &m cv_bound failprob1 failprob2  A_ll fp1 fp2). 
by smt().
qed.

lemma cb2_max &m : 
  Pr[ CB2(A).main(cv_bound_max) @ &m : res] = 0%r.
byphoare (_: cv_bound = cv_bound_max ==> res) => //.
hoare; proc; inline *.
wp;call(_: true); 1: by auto.
rcondt 5; 1: by move => *; auto => />;smt(mem_empty). 
by auto => />; smt(get_set_sameE cv_bound_valid).
qed.

lemma correctness_max &m failprob :
  (forall (O <: RO), islossless O.get => islossless A(O).find) =>
  Pr[ CB1.main(cv_bound_max) @ &m : res] <= failprob =>
  Pr[ Correctness_Adv(LRO,MLWE_PKE,A).main() @ &m : res]  <= failprob.
move => A_ll fp.
have := (correctness_split &m cv_bound_max failprob 0%r A_ll fp _).
+ by have := cb2_max &m; smt().
by smt().
qed.

end section.

op noise_exp_u_uni s u =
  let cu = rnd_err_u u in ZR.zeror &- (s `<*>` cu).
module CB_Provable = {
  var n1, n2 : ZR.t
  proc main(cu_bound : int) = {
    var _A, r,s,e,e1,e2;
    _A <$ duni_matrix;
    r <$ dshort;
    s <$ dshort;
    e <$ dshort;
    e1 <$ dshort;
    e2 <$ dshort_R;
    n1 <- noise_exp_no_rounding s e r e1 e2;
    n2 <- noise_exp_u _A s r e1;
    return (!under_noise_bound n1 (max_noise - cv_bound_max - cu_bound)) \/ (!under_noise_bound n2 (cu_bound));
  }

 proc main_uni(cu_bound : int) = {
    var r,s,e,e1,e2,u;
    r <$ dshort;
    s <$ dshort;
    e <$ dshort;
    e1 <$ dshort;
    e2 <$ dshort_R;
    u <$ duni;
    n1 <- noise_exp_no_rounding s e r e1 e2;
    n2 <- noise_exp_u_uni s u;
    return (!under_noise_bound n1 (max_noise - cv_bound_max - cu_bound)) \/ (!under_noise_bound n2 (cu_bound));
  }
}.

section.

declare module A <: CORR_ADV {-LRO,-RO, -CB}.

lemma correctness_provable_1 &m cu_bound failprob1 failprob2 :
  (forall (O <: RO), islossless O.get => islossless A(O).find) =>
  Pr[ CB_Provable.main(cu_bound) @ &m : !(under_noise_bound CB_Provable.n1 (max_noise - cv_bound_max - cu_bound))] <= failprob1 =>
  Pr[ CB_Provable.main(cu_bound) @ &m : !(under_noise_bound CB_Provable.n2 (cu_bound))] <= failprob2 =>
  Pr[ Correctness_Adv(LRO,MLWE_PKE,A).main() @ &m : res]  <= failprob1 + failprob2.
move => A_ll fp1 fp2.
apply (correctness_max A &m (failprob1+failprob2) A_ll).
have  : Pr[CB1.main(cv_bound_max) @ &m : res] <=
  Pr[ CB_Provable.main(cu_bound) @ &m : res].
+ byequiv => //;proc.
  auto => /> A _ r _ s _ e _ e1 _ e2 _. 
  by smt(noise_commutes parts_work).

have : Pr[CB_Provable.main(cu_bound) @ &m : res] = 
  Pr[CB_Provable.main(cu_bound) @ &m : (! under_noise_bound CB_Provable.n1 (max_noise - cv_bound_max - cu_bound)) \/  (! under_noise_bound CB_Provable.n2 cu_bound)] by byequiv => //;proc;auto.

rewrite Pr[mu_or].
smt(mu_bounded). 

qed.

module Bcb2 : MLWE_.Adv_T = {
  var cu_bound : int
  proc guess(_A : matrix, t : vector, uv : vector * R) : bool = {
    var u,s,cu,n;
    s <$ dshort;
    u <- uv.`1; 
    cu <- rnd_err_u u;
    n <- ZR.zeror &-(s `<*>` cu);
    return !under_noise_bound n cu_bound;
  }
}.

lemma cb2_mlwe_left &m cu_bound :
  (glob Bcb2){m} = cu_bound =>
  Pr[ CB_Provable.main(cu_bound) @ &m : !(under_noise_bound CB_Provable.n2 cu_bound)] =
  Pr[MLWE(Bcb2).main(false) @ &m : res].
proof.
move => cub_val.
byequiv => //; rewrite cub_val.
proc; inline *. 
wp. swap {2} 13 -10;wp;rnd{2};wp;rnd{2};wp;rnd{2};rnd{2};wp. swap {1} 4 1. rnd{1}. rnd{1}. rnd;rnd;rnd;rnd (fun _A => trmx _A);auto => />.
move => *; split; 1: by move => *; rewrite trmxK. 
move => *; split. 
+ move => *; rewrite !mu1_uni /=; 1,2: smt(duni_matrix_uni).
  by rewrite !duni_matrix_fu /=.
move => *; split; 1: by rewrite duni_matrix_fu. 
move => *; split; 1: by move => *; rewrite trmxK. 
by move => *; rewrite duni_ll dshort_ll /noise_exp_u /= => *.
qed.

lemma cb2_mlwe_right &m cu_bound :
  (glob Bcb2){m} = cu_bound =>
  Pr[ CB_Provable.main_uni(cu_bound) @ &m : !(under_noise_bound CB_Provable.n2 cu_bound)]  =
  Pr[MLWE(Bcb2).main(true) @ &m : res].
proof.
move => cub_val.
byequiv => //; rewrite cub_val.
proc; inline *. 
swap {2} 13 -12. 
wp;rnd{2};wp;rnd{2};rnd{2};rnd;wp;rnd{2};rnd{2};rnd{2}. swap {1} 4 1. rnd{1}. rnd{1}. rnd{1}; auto => />.
by move => *; rewrite duni_matrix_ll dshort_ll duni_ll /noise_exp_u_uni /= => *.
qed.

lemma n2_carry &m cu_bound:
  Pr[ CB_Provable.main(cu_bound) @ &m : !(under_noise_bound CB_Provable.n1 (max_noise - cv_bound_max - cu_bound))]  =
  Pr[ CB_Provable.main_uni(cu_bound) @ &m : !(under_noise_bound CB_Provable.n1 (max_noise - cv_bound_max - cu_bound))].
byequiv => //.
by proc;auto;rnd{2};auto => />; rewrite duni_matrix_ll duni_ll /=.
qed.

lemma correctness_provable &m cu_bound failprob1 failprob2 epsmlwe :
  (forall (O <: RO), islossless O.get => islossless A(O).find) =>
  (glob Bcb2){m} = cu_bound =>
  `| Pr[MLWE(Bcb2).main(true) @ &m : res] - Pr[MLWE(Bcb2).main(false) @ &m : res] | <= epsmlwe =>
  Pr[ CB_Provable.main_uni(cu_bound) @ &m : !(under_noise_bound CB_Provable.n1 (max_noise - cv_bound_max - cu_bound))] <= failprob1 =>
  Pr[ CB_Provable.main_uni(cu_bound) @ &m : !(under_noise_bound CB_Provable.n2 (cu_bound))] <= failprob2 =>
  Pr[ Correctness_Adv(LRO,MLWE_PKE,A).main() @ &m : res]  <= failprob1 + failprob2 + epsmlwe.
move => All Bcbst.
have <- := n2_carry &m cu_bound.
have <- := cb2_mlwe_left &m cu_bound Bcbst.
have <- := cb2_mlwe_right &m cu_bound Bcbst.
move => mlweB FP1 FP2.
have := correctness_provable_1 &m cu_bound failprob1 (failprob2 + epsmlwe) All FP1 _;smt().
qed.

end section.

end MLWE_PKE.
