require import AllCore StdOrder Distr DistrExtra List IntDiv.
require import MLKEM_Correctness Array256.


clone import MLKEM_Correctness as MLKEM1024Corr with
   op VecMat.kvec <- 24,
   op ubits <- 12,
   op vbits <- 12,
   op cv_bound_max : int <- 52, (* this is the compress error bound for d = 5 *)
   op cub_provable : int <- 240,
   op epsilon = 1%r / (2^174)%r, 
   op epsilon_max = 1%r / (2^158)%r, 
   op epsilon_provable1 = 1%r / (2^96)%r,
   op epsilon_provable2 = 1%r / (2^97)%r

   proof VecMat.gt0_kvec by auto
   proof epsilon_provable1_result
   proof epsilon_provable2_result
   proof MLWEPKE.cv_bound_valid
   proof epsilon_computed
   proof epsilon_computed_max.
   (* proof *. *)


realize MLWEPKE.cv_bound_valid.
move=> A s e r e2 m ????? t v.
rewrite /under_noise_bound /rnd_err_v /compress_poly_err /cv_bound /=.
rewrite allP /compress_err => i Hi /=.
rewrite mapiE //= -Bq5E. 
by move: (compress_err_bound (v.[i]) 5 _ _) => //= /#.
qed.

realize epsilon_provable1_result.
move => &m. 
have := provable_mu1 &m 240.
rewrite /epsilon_provable1.
have ESTIMATE_PROVABLE_1 : 256%r *
mu
  (dcadd
     (dcadd (MyDM.dmul (4 * 256) Sampling.dshort_elem Sampling.dshort_elem)
        (MyDM.dmul (4 * 256) Sampling.dshort_elem Sampling.dshort_elem)) Sampling.dshort_elem)
  (fun (c : Zq.coeff) => MLKEM1024Corr.max_noise - 52 - 240 < absZq c) <= 1%r / (2^96)%r; 
  last by move : ESTIMATE_PROVABLE_1; smt().
admit. (* The above ESTIMATE_PROVABLE_1 statement is proved by computation. *)
qed.

realize epsilon_provable2_result.
move => &m. 
have := provable_mu2 &m 240.
rewrite /epsilon_provable2.
have ESTIMATE_PROVABLE_2 : StdBigop.Bigreal.BRA.big predT
  (fun (k : int) =>
     mu
       (dcsub (MyDM.dmul (4 * (k + 1)) Sampling.dshort_elem MLKEM1024Corr.dround_elem)
          (MyDM.dmul (4 * (256 - k - 1)) Sampling.dshort_elem MLKEM1024Corr.dround_elem))
       (fun (c : Zq.coeff) => 240 < absZq c)) (iota_ 0 256) <= 1%r / (2^97)%r; 
  last by move : ESTIMATE_PROVABLE_2; smt().
admit. (* The above ESTIMATE_PROVABLE_2 statement is proved by computation. *)
qed.

realize epsilon_computed_max.
move => &m. 
have := CB1_heuristic_mu &m 52.

rewrite /epsilon_max.
have ESTIMATE_HEURISTIC_1 : StdBigop.Bigreal.BRA.big predT
  (fun (k : int) =>
     mu
       (dcadd
          (dcsub (MyDM.dmul (4 * 256) Sampling.dshort_elem Sampling.dshort_elem)
             (dcsub
                (MyDM.dmul (4 * (k + 1)) Sampling.dshort_elem (dcadd Sampling.dshort_elem MLKEM1024Corr.dround_elem))
                (MyDM.dmul (4 * (255 - k)) Sampling.dshort_elem (dcadd Sampling.dshort_elem MLKEM1024Corr.dround_elem))))
          Sampling.dshort_elem) (fun (c : Zq.coeff) => MLKEM1024Corr.max_noise - 52 < absZq c)) (
  iota_ 0 256) <= 1%r / (2^174)%r;
    last by move : ESTIMATE_HEURISTIC_1; smt().
admit. (* The above ESTIMATE_HEURISTIC_1 statement is proved by computation. *)
qed.

realize epsilon_computed.
move => &m. 
have := heuristic_mu &m.

rewrite /epsilon.
have ESTIMATE_HEURISTIC_2 :StdBigop.Bigreal.BRA.big predT
  (fun (k : int) =>
     mu
       (dcadd
          (dcadd
             (dcsub (MyDM.dmul (4 * 256) Sampling.dshort_elem Sampling.dshort_elem)
                (dcsub
                   (MyDM.dmul (4 * (k + 1)) Sampling.dshort_elem (dcadd Sampling.dshort_elem MLKEM1024Corr.dround_elem))
                   (MyDM.dmul (4 * (255 - k)) Sampling.dshort_elem
                      (dcadd Sampling.dshort_elem MLKEM1024Corr.dround_elem)))) Sampling.dshort_elem)
          MLKEM1024Corr.dround_elem_v) (fun (c : Zq.coeff) => MLKEM1024Corr.max_noise < absZq c)) (
  iota_ 0 256) <= 1%r / (2^174)%r; 
   last by move : ESTIMATE_HEURISTIC_2;smt().
admit. (* The above ESTIMATE_HEURISTIC_2 statement is proved by computation. *)
qed.

lemma provable_bound  (A<:MLWEPKE.PKE_ROM.CORR_ADV{-MLWEPKE.MLWE_.MLWE_ROM.RO.RO, -MLWEPKE.MLWE_.MLWE_ROM.RO.LRO, -MLWEPKE.CB}) &m  (epsmlwe : real):
    (forall (O <: MLWEPKE.MLWE_.MLWE_ROM.RO.RO), islossless O.get => islossless A(O).find) =>
    MLWEPKE.Bcb2.cu_bound{m} = 240 =>
    `|Pr[MLWEPKE.MLWE_.MLWE(MLWEPKE.Bcb2).main(true) @ &m : res] -
      Pr[MLWEPKE.MLWE_.MLWE(MLWEPKE.Bcb2).main(false) @ &m : res]| <=
    epsmlwe =>
    Pr[MLWEPKE.PKE_ROM.Correctness_Adv(MLWEPKE.MLWE_.MLWE_ROM.RO.LRO, MLWEPKE.MLWE_PKE, A).main() @ &m : res] <= 1%r / (2^95)%r + epsmlwe.
move => H H0 H1.
have := correctness_provable_inst A &m epsmlwe H H0 H1.
have := epsilon_provable1_result &m; rewrite /MLKEM1024Corr.epsilon_provable1.
have := epsilon_provable2_result &m; rewrite /MLKEM1024Corr.epsilon_provable2.
have : 1%r / (2 ^ 96)%r + 1%r / (2 ^ 97)%r <= 1%r / (2 ^ 95)%r; last by smt().
have : 2%r *1%r / (2 ^ 96)%r <= 1%r / (2 ^ 95)%r; by smt(@RealOrder).
qed.
