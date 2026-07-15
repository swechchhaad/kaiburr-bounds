require import AllCore Distr List StdOrder PKE_ROM FMap.
require (****) LWE_PKE.
(*****) import IntOrder.

clone import LWE_PKE.LWE_PKE as LWE_PKE_.
import LWE_PKE_.DM.
import LWE_PKE_.LWE_.
import LWE_PKE_.LWE_.DM.
import LWE_PKE_.LWE_.Dmatrix_.

(* NOTE:matrix dimension ? *)
op noise_exp (_A s s' e e' e'': matrix) m =
    let _B = _A * s + e in
    let b' = s' * _A + e' in
    let v = s' * _B + e'' in
    let (c1, c2) = c_decode (c_encode (b',v + m_encode m)) in
        c2 - c1 * s - m_encode m.

op noise_exp_val (s s' e e' e'': matrix) = s' * e + e'' - e'* s.

op max_noise : R.
op under_noise_bound : matrix -> R -> bool.
op valid_plaintext: plaintext -> bool.

axiom good_c_decode c: c_decode (c_encode c) = c.
axiom good_m_decode m n :
  valid_plaintext m =>
  under_noise_bound n max_noise =>
  m_decode (m_encode m + n) = m.

hint simplify (good_c_decode).

module CorrectnessAdvNoise(A : PKEROM.CORR_ADV) = {
  proc main() = {
    var sd,s,s',e, e', e'', t, _A, pt, nu, pk, sk;
    LWE1.LWE_ROM.RO.LRO.init();
    sd <$ dseed;
    _A <@ LWE1.LWE_ROM.RO.LRO.get(sd);
    s  <$ dmatrix Chi n nb;
    s'  <$ dmatrix Chi mb m;
    e  <$ dmatrix Chi m nb;
    e'  <$ dmatrix Chi mb n;
    e''  <$ dmatrix Chi mb nb;
    t  <- _A * s + e;

    (pk, sk) <- (pk_encode (t, sd), sk_encode s);
    pt <@ A(LWE1.LWE_ROM.RO.LRO).find(pk, sk);
    nu <- noise_exp _A s s' e e' e'' pt;

    return !under_noise_bound nu max_noise;
  }
}.

module CorrectnessBound = {
  proc main() = {
    var s, s', e, e', e'', nu;
    s  <$ dmatrix Chi n nb;
    s'  <$ dmatrix Chi mb m;
    e  <$ dmatrix Chi m nb;
    e'  <$ dmatrix Chi mb n;
    e''  <$ dmatrix Chi mb nb;
    nu <- noise_exp_val s s' e e' e'';
    return !under_noise_bound nu max_noise;
  }
}.


(* correctness *)
section.
declare module A <: PKEROM.CORR_ADV {-PKEROM.RO.RO, -LWE1.LWE_ROM.RO.RO}.
declare axiom A_valid_guess:
  forall (O <: PKEROM.POracle),
  hoare[A(O).find: true ==> valid_plaintext res].

lemma correctness_noise &m:
  Pr[ PKEROM.Correctness_Adv(PKEROM.RO.LRO, LWE_PKE,A).main() @ &m : res]  <=
  Pr[ CorrectnessAdvNoise(A).main() @ &m : res].
proof.
byequiv => //.
proc. inline *.
swap {1} 19 -11;swap {1} [20..21] -10.
rcondt{1} 5; 1: by auto; smt(mem_empty).
rcondt{2} 5; 1: by auto; smt(mem_empty).
rcondf{1} 20.
+ auto => />.
  seq 13 : ((pk_decode pk).`2 \in PKEROM.RO.RO.m); 1: by auto;smt(pk_encodeK mem_set). 
  exlim (pk_decode pk).`2 => sd.
  call (: sd \in PKEROM.RO.RO.m); 1: by proc; auto; smt(mem_set).
  auto => />.
wp;rnd{1};wp => />.
seq 13 13: (
  ={glob A, sd, pk, sk, r, s, e, s', e', e''} /\
  PKEROM.RO.RO.m{1} = LWE1.LWE_ROM.RO.RO.m{2} /\
  sd{2} \in LWE1.LWE_ROM.RO.RO.m{2} /\
  pk{2} = pk_encode (r{2} * s{2} + e{2}, sd{2}) /\
  sk{2} = sk_encode s{2} /\
  r{2} = oget LWE1.LWE_ROM.RO.RO.m{2}.[sd{2}] /\
  _A{2} = r{2} /\
  rows s{2} = n /\ cols s{2} = nb /\
  rows s'{2} = mb /\ cols s'{2} = m /\
  rows e{2} = m /\ cols e{2} = nb /\
  rows e'{2} = mb /\ cols e'{2} = n /\
  rows e''{2} = mb /\ cols e''{2} = nb /\
  LWE1.LWE_ROM.RO.RO.m{2} = empty.[sd{2} <- r{2}]
).
+ auto => /> *.
  rewrite mem_set !get_setE /=.
  smt(supp_dmatrix gt0_m gt0_n gt0_mb gt0_nb).
exlim sd{2},r{2} => sd r.
call (_: ={glob A, sk, pk} /\ (glob PKEROM.RO.LRO){1} = (glob LWE1.LWE_ROM.RO.LRO){2} /\
  sd \in LWE1.LWE_ROM.RO.RO.m{2} /\
  LWE1.LWE_ROM.RO.RO.m{2} = empty.[sd <- r] /\
  oget LWE1.LWE_ROM.RO.RO.m{2}.[sd] = r
  ==> ={res} /\ (glob PKEROM.RO.LRO){1} = (glob LWE1.LWE_ROM.RO.LRO){2} /\
  sd \in LWE1.LWE_ROM.RO.RO.m{2} /\
  oget LWE1.LWE_ROM.RO.RO.m{2}.[sd] = r /\
    valid_plaintext res{1}
).
+ conseq (_: ={glob A, sk, pk} /\
  (glob PKEROM.RO.LRO){1} = (glob LWE1.LWE_ROM.RO.LRO){2} /\
  sd \in LWE1.LWE_ROM.RO.RO.m{2} /\
  LWE1.LWE_ROM.RO.RO.m{2} = empty.[sd <- r] /\
  oget LWE1.LWE_ROM.RO.RO.m{2}.[sd] = r
  ==> ={glob A, res} /\
  (glob PKEROM.RO.LRO){1} = (glob LWE1.LWE_ROM.RO.LRO){2} /\
  sd \in LWE1.LWE_ROM.RO.RO.m{2} /\
  oget LWE1.LWE_ROM.RO.RO.m{2}.[sd] = r
) (_:true ==> valid_plaintext res) (_: true ==> valid_plaintext res) => />.
+ apply (A_valid_guess PKEROM.RO.LRO).
+ apply (A_valid_guess LWE1.LWE_ROM.RO.LRO).
+ proc (PKEROM.RO.RO.m{1} = LWE1.LWE_ROM.RO.RO.m{2} /\
    sd \in LWE1.LWE_ROM.RO.RO.m{2} /\
    oget LWE1.LWE_ROM.RO.RO.m{2}.[sd] = r
); 1, 2: smt().
  + proc. auto => />.
    smt(mem_set get_setE).
auto => />.
move => &1 &2 ? ? ? ? ? ? ? ? ? ? ? ? ? ? h ? ? ?.
rewrite pk_encodeK sk_encodeK /= -h.
rewrite /noise_exp /= [_+m_encode _]addmC -addmA.
pose x := _ * (_ * s{1} + _) + _ - _.
apply Logic.contra.
rewrite [_+x-_]addmC addmA addNm m_encode_rows m_encode_cols.
have -> : zerom mb nb + x = x.
+ by rewrite lin_add0m; 1,2: smt(rows_addm rows_neg rows_mulmx cols_addm cols_neg cols_mulmx).
by apply good_m_decode.
qed.

lemma matrix_cancel (x y z: matrix): x = y => x + z = y + z.
proof. done. qed.

lemma correctness_bound &m:
  (forall (O <: PKEROM.POracle), islossless A(O).find) =>
  Pr[ CorrectnessAdvNoise(A).main() @ &m : res] =
  Pr[ CorrectnessBound.main() @ &m : res].
proof.
move => h.
byequiv => //.
proc; inline *.
wp; call{1}(:true ==> true); 1: by apply (h LWE1.LWE_ROM.RO.LRO).
rcondt{1} 5; 1: by auto; smt(mem_empty).
wp; do 5! rnd; auto => // />.
move => sd hsd r hr s hs s' hs' e he e' he' e'' he'' ?.
apply /congr1; congr.
rewrite get_setE /noise_exp/noise_exp_val /=.
rewrite -[(_ - _ - m_encode _)]addmA -oppmD mulmxDl mulmxDr mulmxA sub_eqm;
1,2: smt(rows_addm rows_neg rows_mulmx cols_addm cols_neg cols_mulmx supp_dmatrix gt0_m gt0_n gt0_mb gt0_nb m_encode_rows m_encode_cols).
pose x := s' * _ * s. rewrite -[x + _ + _]addmA.
pose y := s' * e + e''.
pose z := e' * s.
rewrite [(y-z)+_]addmC.
rewrite -[x+z+m_encode _] addmA.
rewrite [z+_]addmC.
rewrite [x+(_ + z)] addmA.
rewrite -[_+z+(y-z)] addmA.
rewrite [z+(y-z)] addmA.
rewrite [z+y] addmC.
rewrite -[y+z-z] addmA.
rewrite [_+(y+_)]addmA.
rewrite -[_+_+y]addmA.
rewrite [m_encode _+y]addmC.
rewrite [x+(y+_)]addmA.
by rewrite addmN lin_addm0;
1,2:smt(rows_addm rows_neg rows_mulmx cols_addm cols_neg cols_mulmx supp_dmatrix gt0_m gt0_n gt0_mb gt0_nb m_encode_rows m_encode_cols).
qed.

lemma correctness_theorem &m :
  (forall (O <: PKEROM.POracle), islossless A(O).find) =>
  Pr[PKEROM.Correctness_Adv(PKEROM.RO.LRO, LWE_PKE, A).main() @ &m: res] <=
  Pr[CorrectnessBound.main() @ &m : res].
proof.
move => *.
rewrite -correctness_bound 1://.
exact correctness_noise.
qed.

end section.
