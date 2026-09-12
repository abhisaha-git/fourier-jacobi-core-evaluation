"""Generate polynomial certificates for the eight-term Weyl sum.

SymPy constructs expressions; every equality is subsequently proved by Lean.
No CAS result is imported as an axiom. Requires SymPy 1.14.0 for regeneration only.
"""
from pathlib import Path
import json, runpy
import sympy as S

ROOT = Path(__file__).resolve().parent.parent
helper = runpy.run_path(str(ROOT / "scripts/generate-region-algebra.py"))
lean, vec = helper["lean"], helper["vec"]
t, d, U, V, P, N, E, F, G = [helper[s] for s in ("t","d","U","V","P","N","E","F","G")]
a,b=S.symbols("a b")


def main():
    rows=json.loads((ROOT/"data/region-expressions.json").read_text(encoding="utf-8"))
    exprs=[S.sympify(row["expression"],locals=helper["VARIABLES"]) for row in rows]
    common=d**2*P*N*E*F*G
    nums=[S.cancel(common*x) for x in exprs]
    sub={P:1-d*V*t,N:1-V*t/d,E:1-V**2*t**2,F:1-U*t**2,G:1-U*t**4}
    total=S.Poly(0,t,d,U,V)
    for num in nums:
        total += S.Poly(S.cancel(num.subs(sub)),t,d,U,V)
    H=S.cancel(total.as_expr()/((1-V**2*t**2)*(1-U*t**2)*(1-U*t**4)))
    R=(a-1)*(a-b)*(b-1)*(a*b-1)
    roots=[(b/a,1/b,1/(a*b),1/a),(a/b,1/a,1/(a*b),1/b),
           (1/(a*b),b,b/a,1/a),(a*b,1/a,b/a,b),
           (1/(a*b),a,a/b,1/b),(a*b,1/b,a/b,a),
           (b/a,a,a*b,b),(a/b,b,a*b,a)]
    rf=lambda x:(1-t*t*x)/(1-x)
    An=[S.factor(S.cancel(R*S.prod(rf(x) for x in row))) for row in roots]
    Us=[a*b,a*b,a/b,a/b,b/a,b/a,1/(a*b),1/(a*b)]
    Vs=[a,b,a,1/b,b,1/a,1/b,1/a]
    scale=[1,1,1,b**2,1,a**2,b**2,a**2]
    factors=[1-a*d*t, a-d*t, 1-b*d*t, b-d*t,
             d-a*t, a*d-t, d-b*t, b*d-t]
    omitted=[(0,4),(2,6),(0,4),(3,7),(2,6),(1,5),(3,7),(1,5)]
    Hs=[S.cancel(a*a*b*b*scale[i]*H.subs({U:Us[i],V:Vs[i]})) for i in range(8)]
    assert all(S.denom(x)==1 for x in Hs)
    remaining=[S.prod(v for j,v in enumerate(factors) if j not in omitted[i]) for i in range(8)]
    cleared=[An[i]*Hs[i]*remaining[i] for i in range(8)]
    target=R*d**5*(1+a)**2*(1+b)**2*(1-t*t)*(
        (1-a*t*t)*(a-t*t)*(1-b*t*t)*(b-t*t))*(
        (1-a*b*t*t)*(b-a*t*t)*(a-b*t*t)*(a*b-t*t))
    assert sum((S.Poly(x,t,a,b,d) for x in cleared),S.Poly(0,t,a,b,d)) == S.Poly(target,t,a,b,d)
    target_coefficient=S.Mul(*(x for x in target.args if x != d**5))
    assert S.expand(target-target_coefficient*d**5)==0
    hc=[[S.factor(S.Poly(x,d).nth(j)) for j in range(5)] for x in Hs]
    rc=[[S.factor(S.Poly(x,d).nth(j)) for j in range(7)] for x in remaining]
    proof=[]
    reduce_fin="Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val, Fin.reduceFinMk, Fin.val_zero, Fin.val_succ"
    proof += [
        "def evalCoefficients {n : ℕ} (x : K) (c : Fin n → K) : K := ∑ k, c k * x ^ (k : ℕ)",
        "def weylTargetCoefficient (t a b : K) : K := "+lean(target_coefficient),
        "",
    ]
    for i in range(8):
        for j in range(5):
            proof.append(f"@[irreducible] def wh{i}_{j} (t a b : K) : K := {lean(hc[i][j])}")
        for j in range(7):
            proof.append(f"@[irreducible] def wr{i}_{j} (t a b : K) : K := {lean(rc[i][j])}")
        for k in range(11):
            products=[f"(wh{i}_{j} t a b * wr{i}_{k-j} t a b)" for j in range(5) if 0<=k-j<7]
            proof.append(f"def wc{i}_{k} (t a b : K) : K := weylWeightNumerators t a b {i} * ("+" + ".join(products)+")")
        for letter,length in (("h",5),("r",7),("c",11)):
            proof.append(f"def w{letter}Coeffs{i} (t a b : K) : Fin {length} → K := !["+
                ", ".join(f"w{letter}{i}_{j} t a b" for j in range(length))+"]")
        proof += [
            f"theorem heightExpansion{i} (t a b d : K) :",
            f"    weylHeight{i} t a b d = evalCoefficients d (whCoeffs{i} t a b) := by",
            f"  simp only [evalCoefficients, whCoeffs{i}, {reduce_fin}]",
            "  unfold "+f"weylHeight{i} "+" ".join(f"wh{i}_{j}" for j in range(5)),
            "  norm_num",
            "  all_goals grind only",
            f"theorem remainingExpansion{i} (t a b d : K) :",
            f"    weylRemainingFactors t a b d {i} = evalCoefficients d (wrCoeffs{i} t a b) := by",
            f"  simp only [weylRemainingFactors, evalCoefficients, wrCoeffs{i}, {reduce_fin}]",
            "  unfold "+" ".join(f"wr{i}_{j}" for j in range(7)),
            "  norm_num",
            "  all_goals grind only",
            f"theorem clearedExpansion{i} (t a b d : K) :",
            f"    weylClearedTerms t a b d {i} = evalCoefficients d (wcCoeffs{i} t a b) := by",
            "  unfold weylClearedTerms",
            "  simp only [weylHeightNumerators, Matrix.cons_val_zero, Matrix.cons_val_succ]",
            f"  rw [heightExpansion{i}, remainingExpansion{i}]",
            f"  simp only [evalCoefficients, whCoeffs{i}, wrCoeffs{i}, wcCoeffs{i}, {reduce_fin}]",
            "  unfold "+" ".join(f"wc{i}_{j}" for j in range(11)),
            "  norm_num",
            "  all_goals grind only",
            "",
        ]
    data_proof=proof
    coefficient_proofs=[]
    for k in range(11):
        lhs=" + ".join(f"wc{i}_{k} t a b" for i in range(8))
        rhs="weylTargetCoefficient t a b" if k==5 else "0"
        coefficient_proofs.append([
            f"theorem coefficientIdentity{k} (t a b : K) : {lhs} = {rhs} := by",
            "  unfold "+" ".join(f"wc{i}_{k}" for i in range(8)),
            "  simp only [weylWeightNumerators, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val, Fin.reduceFinMk]",
            "  simp only ["+", ".join([f"wh{i}_{j}" for i in range(8) for j in range(5)]+
                [f"wr{i}_{j}" for i in range(8) for j in range(7)]+["weylTargetCoefficient"])+"]",
            "  norm_num",
            "  all_goals ring",
            "",
        ])
    proof=[]
    proof += [
        "def allWeylCoefficients (t a b : K) : Fin 8 → Fin 11 → K := !["+
            ", ".join(f"wcCoeffs{i} t a b" for i in range(8))+"]",
        "theorem clearedExpansion (t a b d : K) (i : Fin 8) :",
        "    weylClearedTerms t a b d i = evalCoefficients d (allWeylCoefficients t a b i) := by",
        "  fin_cases i",
        *[f"  · exact clearedExpansion{i} t a b d" for i in range(8)],
        "theorem coefficientIdentity (t a b : K) (k : Fin 11) :",
        "    (∑ i : Fin 8, allWeylCoefficients t a b i k) =",
        "      if k = 5 then weylTargetCoefficient t a b else 0 := by",
        "  fin_cases k",
    ]
    for k in range(11):
        proof += [
            f"  · simpa only [allWeylCoefficients, {reduce_fin}, "+
                ", ".join(f"wcCoeffs{i}" for i in range(8))+
                ", ite_true, ite_false, Fin.reduceEq, add_zero, add_assoc] using coefficientIdentity"+str(k)+" t a b",
        ]
    proof += [
        "theorem weyl_polynomial_identity (t a b d : K) :",
        "    (∑ i : Fin 8, weylClearedTerms t a b d i) = weylTargetNumerator t a b d := by",
        "  simp_rw [clearedExpansion, evalCoefficients]",
        "  rw [Finset.sum_comm]",
        "  simp_rw [← Finset.sum_mul, coefficientIdentity]",
        "  have ht : weylTargetNumerator t a b d = weylTargetCoefficient t a b * d ^ 5 := by",
        "    unfold weylTargetNumerator weylTargetCoefficient",
        "    ac_rfl",
        "  rw [ht]",
        "  norm_num [Fin.sum_univ_succ]",
        "",
    ]
    out=[
        "import FourierJacobi.Algebra.RegionSum",
        "import FourierJacobi.Algebra.EulerFactors",
        "",
        "/-!",
        "# The eight Weyl terms on the regular parameter locus",
        "",
        "The root lists, L and M values follow Proposition 2.10 of the manuscript.",
        "The generated polynomial certificate is proved by Lean ring normalization.",
        "No assertions about integrals or continuation across Weyl walls occur here.",
        "-/",
        "",
        "namespace FourierJacobi",
        "namespace Algebra",
        "variable {K : Type*} [Field K]",
        "set_option maxHeartbeats 4000000",
        "set_option maxRecDepth 4096",
        "-- Generated coefficient interfaces deliberately have uniform argument lists.",
        "set_option linter.unusedVariables false",
        "set_option linter.unusedSimpArgs false",
        "set_option linter.unusedTactic false",
        "set_option linter.unreachableTactic false",
        "",
        "def weylWall (a b : K) : K := (a - 1) * (a - b) * (b - 1) * (a * b - 1)",
        "",
        "def rootFactor (t z : K) : K := (1 - t ^ 2 * z) / (1 - z)",
        "",
        "def weylWeights (t a b : K) : Fin 8 → K :=",
        "  !["+",\n    ".join(" * ".join(f"rootFactor t {lean(z)}" for z in row) for row in roots)+"]",
        "",
        "def weylU (a b : K) : Fin 8 → K := "+vec(Us),
        "def weylV (a b : K) : Fin 8 → K := "+vec(Vs),
        "",
        "def weylTerms (t a b d : K) (i : Fin 8) : K :=",
        "  weylWeights t a b i * regionKernel t d (weylU a b i) (weylV a b i)",
        "",
        "@[irreducible] def weylWeightNumerators (t a b : K) : Fin 8 → K := "+vec(An),
        *[f"def weylHeight{i} (t a b d : K) : K := {lean(h)}" for i,h in enumerate(Hs)],
        "def weylHeightNumerators (t a b d : K) : Fin 8 → K := !["+
            ", ".join(f"weylHeight{i} t a b d" for i in range(8))+"]",
        "def weylRemainingFactors (t a b d : K) : Fin 8 → K := "+vec(remaining),
        "",
        "def weylClearedTerms (t a b d : K) (i : Fin 8) : K :=",
        "  weylWeightNumerators t a b i * weylHeightNumerators t a b d i *",
        "    weylRemainingFactors t a b d i",
        "",
        "def weylCommonDenominator (t a b d : K) : K :=",
        "  weylWall a b * a ^ 2 * b ^ 2 * d * "+lean(S.prod(factors)),
        "",
        "def weylTargetNumerator (t a b d : K) : K := "+lean(target),
        "",
        *data_proof,
        "",
        "end Algebra",
        "end FourierJacobi",
        "",
    ]
    destination=ROOT/"FourierJacobi/Algebra"
    (destination/"WeylData.lean").write_text("\n".join(out),encoding="utf-8")
    preamble=out[out.index("namespace FourierJacobi"):out.index("def weylWall (a b : K) : K := (a - 1) * (a - b) * (b - 1) * (a * b - 1)")]
    ending=["","end Algebra","end FourierJacobi",""]
    # Chain the coefficient modules so Lake does not launch all large proofs together.
    for k,certificate in enumerate(coefficient_proofs):
        previous="WeylData" if k==0 else f"WeylCoefficient{k-1}"
        contents=[f"import FourierJacobi.Algebra.{previous}","",
            f"/-! Generated certificate for coefficient {k} in d. -/","",
            *preamble,*certificate,*ending]
        (destination/f"WeylCoefficient{k}.lean").write_text("\n".join(contents),encoding="utf-8")
    contents=["import FourierJacobi.Algebra.WeylCoefficient10","",
        "/-! Assemble the separately checked coefficient identities. -/","",
        *preamble,*proof,*ending]
    (destination/"WeylSum.lean").write_text("\n".join(contents),encoding="utf-8")
    print("Generated the eight Weyl terms and their polynomial certificate.",flush=True)


if __name__=="__main__":
    main()
