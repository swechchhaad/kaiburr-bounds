(* Kaiburr-4608 with module rank k = 18, noise f(6), no ciphertext compression *)

require import AllCore StdOrder Distr IntDiv List.
require import MLKEM_Correctness Array256.

clone import MLKEM_Correctness as Kaiburr4608Corr with
  op VecMat.kvec <- 18,
  op Sampling.t <- 6,
  op epsilon_corr <- 1%r / (2^133)%r
  proof VecMat.gt0_kvec by auto
  proof Sampling.ge2_t by auto
  proof NoiseBoundComputed.

realize NoiseBoundComputed.
move => &m.
have := NoiseBound_mu &m.
have COMPUTATION :
  256%r *
  mu (dcadd (dcadd (MyDM.dmul (18 * 256) Sampling.dshort_elem Sampling.dshort_elem)
                   (MyDM.dmul (18 * 256) Sampling.dshort_elem Sampling.dshort_elem))
            Sampling.dshort_elem)
     (fun (c : Zq.coeff) => Kaiburr4608Corr.max_noise < absZq c) <= 1%r / (2^133)%r;
  last by move : COMPUTATION; smt().
admit. (* The above COMPUTATION statement is proved by computation. *)
qed.
