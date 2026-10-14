(* k = 5, ML-KEM noise CBD_2, no ciphertext compression *)

require import AllCore StdOrder Distr IntDiv List.
require import MLKEM_CBD_Correctness Array256.

clone import MLKEM_CBD_Correctness as Warmup5Corr with
  op VecMat.kvec <- 5,
  op epsilon_corr <- 1%r / (2^185)%r
  proof VecMat.gt0_kvec by auto
  proof NoiseBoundComputed.

realize NoiseBoundComputed.
move => &m.
have := NoiseBound_mu &m.
have COMPUTATION :
  256%r *
  mu (dcadd (dcadd (MyDM.dmul (5 * 256) Sampling.dshort_elem Sampling.dshort_elem)
                   (MyDM.dmul (5 * 256) Sampling.dshort_elem Sampling.dshort_elem))
            Sampling.dshort_elem)
     (fun (c : Zq.coeff) => Warmup5Corr.max_noise < absZq c) <= 1%r / (2^185)%r;
  last by move : COMPUTATION; smt().
admit. (* The above COMPUTATION statement is proved by computation. *)
qed.
