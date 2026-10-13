require import AllCore Ring Distr FMap PROM.

require (****) Matrix.

clone import Matrix as Matrix_.

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

lemma duni_R_funi : is_funiform duni_R.
proof. apply is_full_funiform; [apply duni_R_fu | apply duni_R_uni]. qed.

(* --------------------------------------------------------------------------- *)
(* Distribution over R (short values) *)

op [lossless] dshort_R  : R distr.

(* --------------------------------------------------------------------------- *)
(* Extention of those definitions to vector *) 
op duni = dvector duni_R.
op dshort = dvector dshort_R.

lemma duni_ll : is_lossless duni.
proof. apply/dvector_ll/duni_R_ll. qed.

lemma duni_fu : is_full duni.
proof. apply /dvector_fu /duni_R_fu. qed.

lemma duni_uni : is_uniform duni.
proof. apply /dvector_uni/duni_R_uni. qed.

lemma duni_funi : is_funiform duni.
proof. apply /is_full_funiform; [apply duni_fu | apply duni_uni]. qed.

lemma dshort_ll : is_lossless dshort.
proof. apply/dvector_ll/dshort_R_ll. qed.

(* --------------------------------------------------------------------------- *)
(* Extention of those definitions to matrix *) 

op duni_matrix = dmatrix duni_R.

lemma duni_matrix_ll : is_lossless duni_matrix.
proof. apply/dmatrix_ll/duni_R_ll. qed.

lemma duni_matrix_fu : is_full duni_matrix.
proof. apply /dmatrix_fu/duni_R_fu. qed.

lemma duni_matrix_uni : is_uniform duni_matrix.
proof. apply /dmatrix_uni/duni_R_uni. qed.

lemma duni_matrix_funi : is_funiform duni_matrix.
proof. apply /is_full_funiform; [apply duni_matrix_fu | apply duni_matrix_uni]. qed.

module type Adv_T = {
   proc guess(A : matrix, t : vector, uv : vector * R) : bool
}.

abbrev [-printing] m_transpose = trmx.
abbrev (`<*>`) = dotp.
abbrev (&+) = ZR.(+).
abbrev (&-) = ZR.(-).

module MLWE(Adv : Adv_T) = {

  proc main(b : bool) : bool = {
    var s, e, _A, u0, u1, t, e', v0, v1, b';
    
    _A <$ duni_matrix;
    s <$ dshort;
    e <$ dshort;
    u0 <- _A *^ s + e;
    u1 <$ duni;
    
    t <$ duni;
    e' <$ dshort_R;
    v0 <- (t `<*>` s) &+ e';
    v1 <$ duni_R;
    
    b' <@ Adv.guess(_A, t, if b then (u1,v1) else (u0,v0));
    return b';
   }

}.

(* --------------------------------------------------------------------------- *)
(* Version of MLWE using a concrete hash function to derive the matrix         *)
(* --------------------------------------------------------------------------- *)
type seed.
op H : seed -> matrix.

(* --------------------------------------------------------------------------- *)
op [lossless] dseed : seed distr.

module type HAdv_T = {
   proc guess(sd : seed, t : vector, uv : vector * R) : bool
}.

module MLWE_H(Adv : HAdv_T) = {

  proc main(tr b : bool) : bool = {
    var sd, s, e, _A, u0, u1, t, e', v0, v1, b';
    
    sd <$ dseed;
    s <$ dshort;
    e <$ dshort;
    _A <- if tr then m_transpose (H sd) else H sd;
    u0 <- _A *^ s + e;
    u1 <$ duni;
    
    t <$ duni;
    e' <$ dshort_R;
    v0 <- (t `<*>` s) &+ e';
    v1 <$ duni_R;
    
    b' <@ Adv.guess(sd, t, if b then (u1,v1) else (u0,v0));
    return b';
   }

}.

(****************************************************************************)
(* Clearly the MLWE assumption and the H_MLWE assumption are the same when 
 *  one gets the matrix from from a random oracle.                          *)
(****************************************************************************)

theory MLWE_ROM.

clone import FullRO as RO with
  type in_t    = seed,
  type out_t   = matrix,
  op   dout    = fun (sd : seed) => duni_matrix, 
  type d_in_t  = bool,
  type d_out_t = bool.

module type POracle = { include RO [get] }.

module type ROAdv_T(O : POracle) = {
   proc guess(sd : seed, t : vector, uv : vector * R) : bool
}.

module MLWE_RO(Adv : ROAdv_T,O : RO) = {

  proc main(tr : bool, b : bool) : bool = {
    var sd, s, e, _A, u0, u1, t, e', v0, v1, b';
    
    O.init();
    sd <$ dseed;
    s <$ dshort;
    e <$ dshort;
    _A <@ O.get(sd);
    _A <- if tr then m_transpose _A else _A;
    u0 <- _A *^ s + e;
    u1 <$ duni;
    
    t <$ duni;
    e' <$ dshort_R;
    v0 <- (t `<*>` s) &+ e';
    v1 <$ duni_R;
    
    b' <@ Adv(O).guess(sd, t, if b then (u1,v1) else (u0,v0));
    return b';
   }

}.

theory MLWE_vs_MLWE_ROM.

module B(A : ROAdv_T, O : RO) : Adv_T = {
  var _sd : seed
  var __A : matrix

  module FakeRO  = {
      proc get(sd : seed) : matrix = {
           var _Ares;
           _Ares <- __A;
           if (sd <> _sd) {
              O.sample(sd);
              _Ares <@ O.get(sd);
           }
           return _Ares;
      }
  }
  
  proc guess(_A : matrix, t : vector, uv : vector * R) : bool = {
    var sd, b;
    sd <$ dseed;
    _sd <- sd;
    __A <- _A;
    O.init();
    b <@ A(FakeRO).guess(sd,t,uv);
    return b;
  }
}.

module Bt(A : ROAdv_T, O : RO) : Adv_T = {
  var _sd : seed
  var __A : matrix

  module FakeRO  = {
      proc get(sd : seed) : matrix = {
           var _Ares;
           _Ares <- __A;
           if (sd <> _sd) {
              O.sample(sd);
              _Ares <@ O.get(sd);
           }
           return _Ares;
      }
  }
  
  proc guess(_A : matrix, t : vector, uv : vector * R) : bool = {
    var sd, b;
    sd <$ dseed;
    _sd <- sd;
    __A <- m_transpose _A;
    O.init();
    b <@ A(FakeRO).guess(sd,t,uv);
    return b;
  }

}.

lemma MLWE_RO_equiv b &m (A <: ROAdv_T {-LRO,-B}):
  Pr[  MLWE_RO(A,LRO).main(false,b) @ &m : res ] =
  Pr[  MLWE(B(A,LRO)).main(b) @ &m : res].
proof.
byequiv => //.
proc; inline B(A,LRO).guess.
swap {2} 16 -15.
swap {2} 11 -8.
swap {2} 14 -13.
swap {2} [15..16] -10.
swap {1} 5 -2.

seq 3 6 : (#pre /\ ={b,_A,sd} /\ (RO.m{1}.[B._sd{2}] = Some B.__A{2}) /\ 
          B.__A{2} = _A{2} /\ B._sd{2} = sd{2} /\ 
          (forall x, x <> B._sd{2} => RO.m{1}.[x] = RO.m{2}.[x]));
 first by inline *; auto => />; smt(@FMap).
wp;call(: (RO.m{1}.[B._sd{2}] = Some B.__A{2}) /\ 
            forall x, x <> B._sd{2} => RO.m{1}.[x] = RO.m{2}.[x]).
proc;inline *.
case (sd{2} = B._sd{2}).
+ rcondf{1} 2; first by auto => /> /#.
  rcondf{2} 2; first by auto.
  by auto => />; smt(duni_matrix_ll).
+ rcondt{2} 2; first by auto.
  by auto => />;smt(get_setE).
by auto => />.
qed.

lemma MLWE_RO_equiv_t b &m (A <: ROAdv_T {-LRO,-Bt}):
  Pr[  MLWE_RO(A,LRO).main(true,b) @ &m : res ] =
  Pr[  MLWE(Bt(A,LRO)).main(b) @ &m : res].
proof.
byequiv => //.
proc; inline Bt(A,LRO).guess.
swap {2} 16 -15.
swap {2} 11 -8.
swap {2} 14 -13.
swap {2} [15..16] -10.
swap {1} 5 -2.
seq 3 6 : (#pre /\ ={b,sd} /\ _A{1} = m_transpose _A{2} /\ 
           RO.m{1}.[Bt._sd{2}] = Some Bt.__A{2} /\ 
           Bt.__A{2} = m_transpose _A{2} /\ Bt._sd{2} = sd{2} /\ 
           (forall x, x <> Bt._sd{2} => RO.m{1}.[x] = RO.m{2}.[x])).
+ inline *; wp; rnd (fun m => m_transpose m) (fun m => m_transpose m).
  by auto => />;   smt(@FMap trmxK duni_matrix_funi). 
wp;call(: (RO.m{1}.[Bt._sd{2}] = Some Bt.__A{2}) /\ 
            forall x, x <> Bt._sd{2} => RO.m{1}.[x] = RO.m{2}.[x]).
proc;inline *.
case (sd{2} = Bt._sd{2}).
+ rcondf{1} 2; first by auto => />/#.
  rcondf{2} 2; first by auto.
  by auto => />;smt(duni_matrix_ll).
+ rcondt{2} 2; first by auto.
  by auto => />;smt(get_setE).
by auto => />;smt(trmxK).
qed.

end MLWE_vs_MLWE_ROM.

end MLWE_ROM.
