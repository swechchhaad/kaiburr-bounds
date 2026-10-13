#!/usr/bin/env python3
import argparse, json, pathlib, re, sys

def one(pattern, text, what):
    m = re.findall(pattern, text)
    if len(set(m)) != 1:
        raise ValueError(f"expected exactly one value for {what}, found {sorted(set(m))}")
    return int(m[0])

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", required=True, help="directory with kaiburr-*.json")
    ap.add_argument("--proofs", required=True, help="directory with Kaiburr_*_Correctness.ec")
    ap.add_argument("--calculator", required=True, help="path to kyber.ml")
    a = ap.parse_args()

    calc = pathlib.Path(a.calculator).read_text()
    sets = {name: (int(k), int(t)) for name, k, t in
            re.findall(r'name = "(kaiburr-\d+)"; k = (\d+);\s*b = noise_f (\d+);', calc)}
    files = sorted(pathlib.Path(a.proofs).glob("Kaiburr_*_Correctness.ec"))
    if not files:
        sys.exit(f"no Kaiburr_*_Correctness.ec in {a.proofs}")

    ok = True
    print(f"{'parameter set':<14} {'k':>3} {'t':>2}  {'admitted':>9}  {'computed':>10}  result")
    for f in files:
        n = int(re.search(r"Kaiburr_(\d+)_Correctness", f.name).group(1))
        name, s, errs = f"kaiburr-{n}", f.read_text(), []
        try:
            k = one(r"op VecMat\.kvec <- (\d+)", s, "k")
            t = one(r"op Sampling\.t <- (\d+)", s, "t")
            e = one(r"op epsilon_corr <- 1%r / \(2\^(\d+)\)%r", s, "epsilon")
            if one(r"MyDM\.dmul \((\d+) \* 256\)", s, "k in COMPUTATION") != k:
                errs.append("COMPUTATION uses a different k")
            if one(r"<= 1%r / \(2\^(\d+)\)%r;", s, "epsilon in COMPUTATION") != e:
                errs.append("COMPUTATION uses a different epsilon")
        except ValueError as ex:
            print(f"{name:<14} {f.name}: {ex}"); ok = False; continue
        if n != 256 * k:
            errs.append(f"name says dimension {n} but k = {k}")
        if sets.get(name) != (k, t):
            errs.append(f"calculator has {sets.get(name)} for {name}, proof has (k, t) = ({k}, {t})")
        out = pathlib.Path(a.out) / f"{name}.json"
        if not out.exists():
            print(f"{name:<14} {k:>3} {t:>2}  {'2^-'+str(e):>9}  {'missing':>10}  FAIL ({out} not found; run make bounds)")
            ok = False; continue
        lg = float(json.loads(out.read_text())["failure"])
        if lg > -e:
            errs.append(f"computed 2^{lg:.4f} exceeds admitted 2^-{e}")
        print(f"{name:<14} {k:>3} {t:>2}  {'2^-'+str(e):>9}  {'2^'+format(lg, '.4f'):>10}  "
              + ("ok" if not errs else "FAIL: " + "; ".join(errs)))
        ok &= not errs
    print("all admitted bounds are backed by the calculator" if ok else "CHECK FAILED")
    sys.exit(0 if ok else 1)

if __name__ == "__main__":
    main()
