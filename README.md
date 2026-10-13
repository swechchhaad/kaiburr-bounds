# Formally-verified decryption failure bounds for Kaiburr

This artifact accompanies Section 6 of the paper "Kaiburr: ML-KEM at (much) higher security."
For each Kaiburr parameter set, it does the following:

1. machine-checks in [EasyCrypt](https://github.com/EasyCrypt/easycrypt) that the
   IND-CPA public-key encryption scheme in Kaiburr is $\delta$-correct, and
2. computes the numeric tail probability that the
   proof relies on with an OCaml bound calculator, and checks that it is below the bound $\delta$ admitted in the proof.

We derived it from the artifact of
> M. Barbosa, M. J. Kannwischer, T.-H. Lim, P. Schwabe, P.-Y. Strub.
> *Formally Verified Correctness Bounds for Lattice-Based Cryptography.* ACM CCS 2025.

We refer to it as [BKL+25]. Their ML-KEM development is kept and modified in
three places (noise distribution, ciphertext compression, module rank) as the rest of the paper does. We remove their FrodoKEM development, but the structure of its correctness proof is the
one we follow.


## What is proved

| Parameter set | $k$ | $t$ | Machine-checked: $\delta \le$ | Computed tail |
|---|---|---|---|---|
| Kaiburr-1792 | 7  | 4 | $2^{-133}$ | $2^{-133.34}$ |
| Kaiburr-4608 | 18 | 6 | $2^{-133}$ | $2^{-133.81}$ |
| Kaiburr-6144 | 24 | 8 | $2^{-139}$ | $2^{-139.58}$ |

For each parameter set, `Kaiburr<n>Corr.kaiburr_correctness` states that for every
(lossless, otherwise unbounded) adversary that receives the secret key and chooses the
message, the probability that decryption fails is at most `epsilon_corr` ($\delta$ above). This is the notion of correctness used in the Fujisaki–Okamoto bound. There is no MLWE term and no heuristic assumption on the distribution of ciphertexts.

## Quick start

With the toolchain installed (see [Setup](#one-time-setup)):

```
make check
```

This checks every proof from scratch, runs the calculator, and checks the admitted
bounds. The individual steps are `make proofs`, `make bounds` and `make check-bounds`;
`make help` lists all targets. Here is the expected output:

```
[✓] [0017/0017] [ 1:29.7] mlkem/MLKEM_Correctness.ec      # 17 files, all ✓
...
[kaiburr-1792]: failure probability <= 2^-1.333422019e+02
[kaiburr-4608]: failure probability <= 2^-1.338110681e+02
[kaiburr-6144]: failure probability <= 2^-1.395814583e+02
...
parameter set    k  t   admitted    computed  result
kaiburr-1792     7  4     2^-133  2^-133.3422  ok
kaiburr-4608    18  6     2^-133  2^-133.8111  ok
kaiburr-6144    24  8     2^-139  2^-139.5815  ok
all admitted bounds are backed by the calculator
```

(The calculator prints log2 values in scientific notation, for example `-1.333422019e+02` is $-133.34$.)


## One-time setup

Everything below installs into your home directory. The steps should be run in order.

**1. opam**

```bash
mkdir -p ~/bin
curl -fL -o ~/bin/opam https://github.com/ocaml/opam/releases/download/2.3.0/opam-2.3.0-x86_64-linux
chmod +x ~/bin/opam
export PATH=$HOME/bin:$PATH OPAMYES=true OPAMJOBS=8
opam init --bare --disable-sandboxing --no-setup
```

**2. OCaml 4.14.2**

```bash
opam switch create ec ocaml-base-compiler.4.14.2
eval $(opam env --switch=ec)
```

**3. MPFR ≥ 4.2.1** (skip if your system already has it)

```bash
mkdir -p ~/src && cd ~/src
curl -fLO https://www.mpfr.org/mpfr-4.2.1/mpfr-4.2.1.tar.xz
tar xJf mpfr-4.2.1.tar.xz && cd mpfr-4.2.1
./configure --prefix=$HOME/.local
make -j8 && make check -j8 && make install
cd ~
export CPATH=$HOME/.local/include${CPATH:+:$CPATH}
export LIBRARY_PATH=$HOME/.local/lib${LIBRARY_PATH:+:$LIBRARY_PATH}
export LD_LIBRARY_PATH=$HOME/.local/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}
```

**4. EasyCrypt and the calculator's libraries**

```bash
opam pin add -n easycrypt https://github.com/EasyCrypt/easycrypt.git#r2025.02
opam install easycrypt dune batteries yojson mlmpfr
easycrypt config | head -1
```

**5. CVC4 1.8 and Z3 4.8.17**

```bash
T=$(mktemp -d) && cd ~/bin
curl -fL -o cvc4-1.8 https://github.com/CVC4/CVC4-archived/releases/download/1.8/cvc4-1.8-x86_64-linux-opt
curl -fL -o $T/z3.zip https://github.com/Z3Prover/z3/releases/download/z3-4.8.17/z3-4.8.17-x64-glibc-2.31.zip
unzip -p $T/z3.zip z3-4.8.17-x64-glibc-2.31/bin/z3 > z3-4.8.17
chmod +x cvc4-1.8 z3-4.8.17 && rm -rf $T && cd ~
```

**6. Alt-Ergo 2.4.2**, in its own switch so its dependencies do not affect EasyCrypt's

```bash
opam switch create --no-switch alt-ergo-2.4.2 ocaml-base-compiler.4.14.2
opam install --switch=alt-ergo-2.4.2 alt-ergo.2.4.2
printf '#!/bin/bash\nexec opam exec --switch="$(basename "$0")" alt-ergo -- "$@"\n' > ~/bin/run-alt-ergo
chmod +x ~/bin/run-alt-ergo
ln -sf run-alt-ergo ~/bin/alt-ergo-2.4.2
```

**7. Register the provers with EasyCrypt**

```bash
easycrypt why3config
easycrypt config | grep "known provers"
```

The list must include `Alt-Ergo@2.4.2`, `CVC4@1.8.0` and `Z3@4.8.17`.

This next step is needed in every new shell, before running `make`:

```bash
export PATH=$HOME/bin:$PATH && eval $(opam env --switch=ec)
```

and, if MPFR was installed in step 3, pass its prefix to `make`:

```bash
make check MPFR_PREFIX=$HOME/.local
```


## Repository layout

```
Makefile                              entry points: check, proofs, bounds, check-bounds
scripts/check-bounds.py               checks the admitted bounds against the calculator
examples/proof/
  easycrypt.project, tests.config     prover versions and test scenarios
  eclib/                              generic libraries           (unchanged)
  mlkem/MLWE.ec, mlkem/MLWE_PKE.ec    MLWE-based PKE and its correctness games  (unchanged)
  mlkem/Array*.ec                     array types                               (unchanged)
  mlkem/MLKEM_Correctness.ec          ring, noise f(t), distributions, Kaiburr correctness proof
  mlkem/Kaiburr_1792_Correctness.ec   parameter set k = 7,  t = 4
  mlkem/Kaiburr_4608_Correctness.ec   parameter set k = 18, t = 6
  mlkem/Kaiburr_6144_Correctness.ec   parameter set k = 24, t = 8
examples/bound-calculator/
  distr.ml                            distribution library        (unchanged)
  kyber.ml                            Kaiburr bound calculator
```

The Docker files, `Makefile.root`, `MANIFEST`, `scripts/distribution`,
`scripts/install-sh` and `examples.tar.gz` are inherited from the original paper and are not used
directly for our paper. We keep them for reference.
