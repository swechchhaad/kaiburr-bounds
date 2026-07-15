# Formally Verified Correctness Bounds for Lattice-Based Cryptography

## Submission to CCS2025

### Setup

We provide a Docker [1] image that contains a ready to use EasyCrypt
installation along with a copy of the EasyCrypt formal
development. The Docker image has been tested on a X64_64 Linux & on
Apple M1 system (with Rosetta [2] configured so that X64_86 SMT provers
can be used).

[1] https://docs.docker.com/get-docker/
[2] https://en.wikipedia.org/wiki/Rosetta_(software)

To build the Docker image, run:

```shell
make build
```

Some distributions do not activate Docker builtkit (e.g. Arch
linux). In that case, you have to export the `DOCKER_BUILDKIT`
environment variable:

```shell
export DOCKER_BUILDKIT=1
```

Please, ensure that your Docker installation allocates at least 2 cores
and 8GB of memory to the Docker instance.

Once done, you can remove the image & local volume by issuing the
following commands:

```shell
docker rmi ecbounds
docker volume rm ecbounds-data
```

### EasyCrypt development

You can then run EasyCrypt on the formal develoment by running:

```shell
make run-proofs
```

To speed up the checking time, you can run several EasyCrypt instances
in parallel by running:

```shell
make JOBS=$n run-proofs
```

where $n is the number of parallel jobs. In that case, be sure that
you allocate enough resources to the Docker instance.


### Bound calculator

#### Kyber

You can run the bound calculator for Kyber by running:

```shell
make run-kyber
```

This will create a file named `kyber-768.json` and `kyber-1024.json`
in the current directory.

You can extract the relevant information from the file using the
following command:

```shell
make run-extract-kyber
```

It can happen that is ignored by `run-kyber`. If you need to force
stop the Docker container, you can run the following command from
another terminal:

```shell
make kill-docker
```

This will only stop the Docker containers that relate to this
submission.

#### FrodoKEM

You can run the bound calculator for FrodoKEM by running:

```shell
make run-frodokem
```

This will create a file named `frodokem.json`in the current directory.

You can extract the relevant information from the file using the
following command:

```shell
make run-extract-frodokem
```

It can happen that is ignored by `run-frodokem`. If you need to force
stop the Docker container, you can run the following command from
another terminal:

```shell
make kill-docker
```

This will only stop the Docker containers that relate to this
submission.

### Source code

The source code can be found in the `examples.tar.gz` archive.

- The EasyCrypt development can be found in folder `proof` of the
  archive.  It contains two subfolders, one containing the results
  for ML-KEM and another one for FrodoKEM.

  Here is a short description of the contents (files not referred here
  are just boilerplate):

  * `proof/mlkem`

     + `MLWE.ec`: Definitions of the MLWE problem

     + `MLWE_PKE.ec`: Definition and proofs for an abstract PKE based
        on MLWE

     + `MLKEM_Correctness.ec`: Instantiation of the previous file with
        ML-KEM algebraic structure and other definitions that apply to
        all variants. The main proofs about error distributions are here.

     + `MLKEM_768_Correctness.ec`: Refinement and final results for
        ML-KEM-768 parameters

     + `MLKEM_1024_Correctness.ec`: Refinement and final results for
        ML-KEM-1024 parameters

   * `proof/frodokem`

     + `LWE.ec`: Definitions of the LWE problem variants and their
        relations

     + `LWE_PKE.ec`: Definition and security proof for an abstract PKE
        based on LWE

     + `LWE_correctness.ec`: Correctness proof for the abstract PKE
        based on LWE

     + `FrodoPKE_correctness.ec`: Instantiation of the previous file
        with FrodoKEM algebraic structure and other definitions that
        apply to all variants. The main proofs about error
        distributions are here.

     + `FrodoPKE_640_Correctness.ec`: Refinement and final results for
        FrodoKEM-640 parameters

     + `FrodoPKE_976_Correctness.ec`: Refinement and final results for
        FrodoKEM-976 parameters

     + `FrodoPKE_1344_Correctness.ec`: Refinement and final results
        for FrodoKEM-1344 parameters

- The OCaml development can be found in folder `bound-calculator` of
  the archive.
