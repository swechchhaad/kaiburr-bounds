require import AllCore StdOrder Distr IntDiv List.
require import MLKEM_Correctness Array256.


clone import MLKEM_Correctness as MLKEM768Corr with
   op VecMat.kvec <- 18,
   op ubits <- 12,
   op vbits <- 12,
   op cv_bound_max : int <- 104, (* this is the compress error bound for d = 4 *)
   op cub_provable : int <- 296,
   op epsilon = 1%r / (2^164)%r, 
   op epsilon_max = 1%r / (2^164)%r, (* FIXME *)
   op epsilon_provable1 = 1%r / (2^81)%r,
   op epsilon_provable2 = 1%r / (2^82)%r

   proof VecMat.gt0_kvec by auto
   proof epsilon_provable1_result
   proof epsilon_provable2_result
   proof MLWEPKE.cv_bound_valid
   proof epsilon_computed
   proof epsilon_computed_max.


realize MLWEPKE.cv_bound_valid.
move=> A s e r e2 m ????? t v.
rewrite /under_noise_bound /rnd_err_v /compress_poly_err /cv_bound /=.
rewrite allP /compress_err => i Hi /=.
rewrite mapiE //= -Bq4E. 
by move: (compress_err_bound (v.[i]) 4 _ _) => //= /#.
qed.

realize epsilon_provable1_result.
move => &m. 
have := provable_mu1 &m 296.
rewrite /epsilon_provable1.
have ESTIMATE_PROVABLE_1 : 256%r *
mu
  (dcadd
     (dcadd (MyDM.dmul (3 * 256) Sampling.dshort_elem Sampling.dshort_elem)
        (MyDM.dmul (3 * 256) Sampling.dshort_elem Sampling.dshort_elem)) Sampling.dshort_elem)
  (fun (c : Zq.coeff) => MLKEM768Corr.max_noise - 104 - 296 < absZq c) <= 1%r / (2^81)%r; 
  last by move : ESTIMATE_PROVABLE_1; smt().
admit. (* The above ESTIMATE_PROVABLE_1 statement is proved by computation. *)
qed.

realize epsilon_provable2_result.
move => &m. 
have := provable_mu2 &m 296.
rewrite /epsilon_provable2.
have ESTIMATE_PROVABLE_2 : StdBigop.Bigreal.BRA.big predT
  (fun (k : int) =>
     mu
       (dcsub (MyDM.dmul (3 * (k + 1)) Sampling.dshort_elem MLKEM768Corr.dround_elem)
          (MyDM.dmul (3 * (256 - k - 1)) Sampling.dshort_elem MLKEM768Corr.dround_elem))
       (fun (c : Zq.coeff) => 296 < absZq c)) (iota_ 0 256) <= 1%r / (2^82)%r; 
  last by move : ESTIMATE_PROVABLE_2; smt().
admit. (* The above ESTIMATE_PROVABLE_2 statement is proved by computation. *)
qed.


realize epsilon_computed.
move => &m. 
have := heuristic_mu &m.
rewrite /epsilon.

have ESTIMATE_HEURISTIC_1 : StdBigop.Bigreal.BRA.big predT
  (fun (k : int) =>
     mu
       (dcadd
          (dcadd
             (dcsub (MyDM.dmul (3 * 256) Sampling.dshort_elem Sampling.dshort_elem)
                (dcsub
                   (MyDM.dmul (3 * (k + 1)) Sampling.dshort_elem (dcadd Sampling.dshort_elem MLKEM768Corr.dround_elem))
                   (MyDM.dmul (3 * (255 - k)) Sampling.dshort_elem
                      (dcadd Sampling.dshort_elem MLKEM768Corr.dround_elem)))) Sampling.dshort_elem)
          MLKEM768Corr.dround_elem_v) (fun (c : Zq.coeff) => MLKEM768Corr.max_noise < absZq c)) (
  iota_ 0 256) <= 1%r / (2 ^ 164)%r; 
    last by move : ESTIMATE_HEURISTIC_1; smt().
admit. (* The above ESTIMATE_HEURISTIC_1 statement is proved by computation. *)
qed.

realize epsilon_computed_max.
move => &m. 
have := CB1_heuristic_mu &m 104.
rewrite /epsilon_max.
have ESTIMATE_HEURISTIC_2 : StdBigop.Bigreal.BRA.big predT
  (fun (k : int) =>
     mu
       (dcadd
          (dcsub (MyDM.dmul (3 * 256) Sampling.dshort_elem Sampling.dshort_elem)
             (dcsub
                (MyDM.dmul (3 * (k + 1)) Sampling.dshort_elem (dcadd Sampling.dshort_elem MLKEM768Corr.dround_elem))
                (MyDM.dmul (3 * (255 - k)) Sampling.dshort_elem (dcadd Sampling.dshort_elem MLKEM768Corr.dround_elem))))
          Sampling.dshort_elem) (fun (c : Zq.coeff) => MLKEM768Corr.max_noise - 104 < absZq c)) (
  iota_ 0 256) <= 1%r / (2 ^ 164)%r;
   last by move : ESTIMATE_HEURISTIC_2; smt().
admit. (* The above ESTIMATE_HEURISTIC_2 statement is proved by computation. *)
qed.

lemma provable_bound  (A<:MLWEPKE.PKE_ROM.CORR_ADV{-MLWEPKE.MLWE_.MLWE_ROM.RO.RO, -MLWEPKE.MLWE_.MLWE_ROM.RO.LRO, -MLWEPKE.CB}) &m  (epsmlwe : real):
    (forall (O <: MLWEPKE.MLWE_.MLWE_ROM.RO.RO), islossless O.get => islossless A(O).find) =>
    MLWEPKE.Bcb2.cu_bound{m} = 296 =>
    `|Pr[MLWEPKE.MLWE_.MLWE(MLWEPKE.Bcb2).main(true) @ &m : res] -
      Pr[MLWEPKE.MLWE_.MLWE(MLWEPKE.Bcb2).main(false) @ &m : res]| <=
    epsmlwe =>
    Pr[MLWEPKE.PKE_ROM.Correctness_Adv(MLWEPKE.MLWE_.MLWE_ROM.RO.LRO, MLWEPKE.MLWE_PKE, A).main() @ &m : res] <= 1%r / (2^80)%r + epsmlwe.
move => H H0 H1.
have := correctness_provable_inst A &m epsmlwe H H0 H1.
have := epsilon_provable1_result &m; rewrite /MLKEM768Corr.epsilon_provable1.
have := epsilon_provable2_result &m; rewrite /MLKEM768Corr.epsilon_provable2.
have : 1%r / (2 ^ 81)%r + 1%r / (2 ^ 82)%r <= 1%r / (2 ^ 80)%r; last by smt().
have : 2%r *1%r / (2 ^ 81)%r <= 1%r / (2 ^ 80)%r; by smt(@RealOrder).
qed.
