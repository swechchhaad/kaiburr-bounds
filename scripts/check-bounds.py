#!/usr/bin/env python3
import argparse, json, pathlib, re, sys

def one(pattern, text, what):
    m = re.findall(pattern, text)
    if len(set(m)) != 1:
        raise ValueError(f"expected exactly one value for {what}, found {sorted(set(m))}")
    return int(m[0])

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", required=True, help="directory with kaiburr-*.json and warmup-k*.json")
    ap.add_argument("--proofs", required=True, help="directory with Kaiburr_*_Correctness.ec and Warmup_k*_Correctness.ec")
    ap.add_argument("--calculator", required=True, help="path to kyber.ml")
    a = ap.parse_args()

    calc = pathlib.Path(a.calculator).read_text()
    # name -> (k, noise label) as defined in the calculator
    sets = {name: (int(k), f"f({t})") for name, k, t in
            re.findall(r'name = "(kaiburr-\d+)"; k = (\d+);\s*b = noise_f (\d+);', calc)}
    sets.update({name: (int(k), "CBD2") for name, k in
                 re.findall(r'name = "(warmup-k\d+)"; k = (\d+);\s*b = cbd2;', calc)})
    proofs = pathlib.Path(a.proofs)
    kaiburr = sorted(proofs.glob("Kaiburr_*_Correctness.ec"))
    warmup = sorted(proofs.glob("Warmup_k*_Correctness.ec"),
                    key=lambda f: int(re.search(r"Warmup_k(\d+)_", f.name).group(1)))
    if not kaiburr:
        sys.exit(f"no Kaiburr_*_Correctness.ec in {a.proofs}")

    ok = True
    print(f"{'parameter set':<14} {'k':>3} {'noise':>5}  {'admitted':>9}  {'computed':>10}  result")
    for f in kaiburr + warmup:
        s, errs = f.read_text(), []
        is_warmup = f.name.startswith("Warmup_")
        try:
            k = one(r"op VecMat\.kvec <- (\d+)", s, "k")
            if is_warmup:
                n = int(re.search(r"Warmup_k(\d+)_Correctness", f.name).group(1))
                name, noise = f"warmup-k{n}", "CBD2"
                if n != k:
                    errs.append(f"name says k = {n} but kvec = {k}")
                if "require import MLKEM_CBD_Correctness" not in s:
                    errs.append("does not use the CBD_2 theory MLKEM_CBD_Correctness")
            else:
                n = int(re.search(r"Kaiburr_(\d+)_Correctness", f.name).group(1))
                name = f"kaiburr-{n}"
                t = one(r"op Sampling\.t <- (\d+)", s, "t")
                noise = f"f({t})"
                if n != 256 * k:
                    errs.append(f"name says dimension {n} but k = {k}")
            e = one(r"op epsilon_corr <- 1%r / \(2\^(\d+)\)%r", s, "epsilon")
            if one(r"MyDM\.dmul \((\d+) \* 256\)", s, "k in COMPUTATION") != k:
                errs.append("COMPUTATION uses a different k")
            if one(r"<= 1%r / \(2\^(\d+)\)%r;", s, "epsilon in COMPUTATION") != e:
                errs.append("COMPUTATION uses a different epsilon")
        except ValueError as ex:
            print(f"{f.name}: {ex}"); ok = False; continue
        if sets.get(name) != (k, noise):
            errs.append(f"calculator has {sets.get(name)} for {name}, proof has (k, noise) = ({k}, {noise})")
        out = pathlib.Path(a.out) / f"{name}.json"
        if not out.exists():
            print(f"{name:<14} {k:>3} {noise:>5}  {'2^-'+str(e):>9}  {'missing':>10}  FAIL ({out} not found; run make bounds)")
            ok = False; continue
        lg = float(json.loads(out.read_text())["failure"])
        if lg > -e:
            errs.append(f"computed 2^{lg:.4f} exceeds admitted 2^-{e}")
        print(f"{name:<14} {k:>3} {noise:>5}  {'2^-'+str(e):>9}  {'2^'+format(lg, '.4f'):>10}  "
              + ("ok" if not errs else "FAIL: " + "; ".join(errs)))
        ok &= not errs
    print("all admitted bounds are backed by the calculator" if ok else "CHECK FAILED")
    sys.exit(0 if ok else 1)

if __name__ == "__main__":
    main()
