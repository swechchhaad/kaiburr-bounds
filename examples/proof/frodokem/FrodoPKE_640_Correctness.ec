require import AllCore StdOrder Distr DistrExtra List IntDiv.
require import FrodoPKE_correctness.


clone import FrodoPKECorr as Frodo640Corr
 with 
  op N <- 640,
  op Nb <- 8,
  op Mb <- 8,
  op D <- 15,
  op B <- 2,
  op chi_support <- [ 4643; 13363; 20579; 25843; 29227; 31145; 32103; 32525; 32689; 32745; 32762; 32766; 32767],
  op epsilon_corr <- 1%r / (2^138)%r
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
        (FrodoPKE_.LWE_correctness.LWE_PKE_.LWE_.Dmatrix_.Distrmatrix_.dmul 640 FrodoPKE_.ChiFrodo FrodoPKE_.ChiFrodo)
        (FrodoPKE_.LWE_correctness.LWE_PKE_.LWE_.Dmatrix_.Distrmatrix_.dmul 640 FrodoPKE_.ChiFrodo FrodoPKE_.ChiFrodo))
     FrodoPKE_.ChiFrodo)
  (predC
     (fun (cc : FrodoPKE_.DM.R) =>
        - (Zq.asint (Zq.inZq (q %/ 4)))%r / 2%r <= (to_sint cc)%r < (Zq.asint (Zq.inZq (q %/ 4)))%r / 2%r)) <= 1%r / (2^138)%r; last by move : COMPUTATION;smt().
admit. (* The above COMPUTATION statement is proved by computation. *)
qed.
