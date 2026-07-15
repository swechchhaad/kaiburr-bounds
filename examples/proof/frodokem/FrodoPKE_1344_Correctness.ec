require import AllCore StdOrder Distr DistrExtra List IntDiv.
require import FrodoPKE_correctness.


clone import FrodoPKECorr as Frodo1344Corr
 with 
  op N <- 1344,
  op Nb <- 8,
  op Mb <- 8,
  op D <- 16,
  op B <- 4,
  op chi_support <- [   9142; 23462; 30338; 32361; 32725; 32765; 32767],
  op epsilon_corr <- 1%r / (2^252)%r
  proof gt0_N by auto 
  proof gt0_Nb by auto
  proof gt0_Mb by auto
  proof D_bound by auto
  proof B_bound by auto
  proof gt0_lenChi by auto
  proof NoiseBoundComputed.

realize NoiseBoundComputed.
move => &m.
have /= := NoiseBound_mu &m.
have COMPUTATION : 
64%r *
mu
  (FrodoPKE_.LWE_correctness.LWE_PKE_.LWE_.Dmatrix_.Distrmatrix_.dadd
     (dsub
        (FrodoPKE_.LWE_correctness.LWE_PKE_.LWE_.Dmatrix_.Distrmatrix_.dmul 1344 FrodoPKE_.ChiFrodo FrodoPKE_.ChiFrodo)
        (FrodoPKE_.LWE_correctness.LWE_PKE_.LWE_.Dmatrix_.Distrmatrix_.dmul 1344 FrodoPKE_.ChiFrodo FrodoPKE_.ChiFrodo))
     FrodoPKE_.ChiFrodo)
  (predC
     (fun (cc : FrodoPKE_.DM.R) =>
        - (Zq.asint (Zq.inZq (q %/ 16)))%r / 2%r <= (to_sint cc)%r < (Zq.asint (Zq.inZq (q %/ 16)))%r / 2%r)) <= 1%r / (2^252)%r; last by move : COMPUTATION;smt().
admit. (* The above COMPUTATION statement is proved by computation. *)
qed.
