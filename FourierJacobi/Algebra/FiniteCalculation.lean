import FourierJacobi.Algebra.WeylEvaluation

/-!
# The complete finite algebraic calculation

This file combines the fifty region expressions, eight Weyl terms, and Euler
normalization. Its input is an explicit finite rational expression. It is not
the Fourier--Jacobi period and no equality with that period is assumed here.
-/

namespace FourierJacobi
namespace Algebra
variable {K : Type*} [Field K]

/-- Precisely the nonzero denominators used by the fifty-region calculation. -/
structure RegionRegular (t d U V : K) : Prop where
  p : 1 - d * V * t ≠ 0
  n : 1 - V * t / d ≠ 0
  e : 1 - V ^ 2 * t ^ 2 ≠ 0
  f : 1 - U * t ^ 2 ≠ 0
  g : 1 - U * t ^ 4 ≠ 0

/-- Regularity conditions for the finite Weyl expression, without any integral assumption. -/
structure FiniteRegular (t a b d : K) : Prop where
  a_ne_zero : a ≠ 0
  b_ne_zero : b ≠ 0
  d_ne_zero : d ≠ 0
  a_ne_one : a - 1 ≠ 0
  b_ne_one : b - 1 ≠ 0
  a_ne_b : a - b ≠ 0
  ab_ne_one : a * b - 1 ≠ 0
  common : weylCommonDenominator t a b d ≠ 0
  rows : ∀ i, RegionRegular t d (weylU a b i) (weylV a b i)

def finiteCore (t a b d : K) : K :=
  (∑ i : Fin 8, weylWeights t a b i *
    (∑ j : Fin 50, regionTerms t d (weylU a b i) (weylV a b i) j)) / poincare t

theorem finiteCore_eq_closedCore (t a b d : K) (h : FiniteRegular t a b d) :
    finiteCore t a b d = closedCore t a b d := by
  have hterm (i : Fin 8) :
      weylWeights t a b i *
        (∑ j : Fin 50, regionTerms t d (weylU a b i) (weylV a b i) j) =
        weylTerms t a b d i := by
    rw [fifty_region_sum t d (weylU a b i) (weylV a b i)
      h.d_ne_zero (h.rows i).p (h.rows i).n (h.rows i).e (h.rows i).f (h.rows i).g]
    rfl
  have hD (i : Fin 8) : weylKernelDenominator t a b d i ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero 2 h.d_ne_zero) (h.rows i).p) (h.rows i).n
  calc
    finiteCore t a b d = (∑ i : Fin 8, weylTerms t a b d i) / poincare t := by
      unfold finiteCore
      congr 1
      exact Finset.sum_congr rfl (fun i _ => hterm i)
    _ = closedCore t a b d := by
      rw [eight_weyl_sum_closed t a b d h.a_ne_zero h.b_ne_zero h.d_ne_zero
        h.a_ne_one h.b_ne_one h.a_ne_b h.ab_ne_one hD h.common]
      exact weylClosed_div_poincare t a b d

theorem finite_sum_principal_formula (q t a b d : K)
    (h : FiniteRegular t a b d)
    (hc : poincare t ≠ 0) (hn₁ : n₁ t a b ≠ 0) (hn₂ : n₂ t a b ≠ 0)
    (hd₁ : d₁ t a b d ≠ 0) (hd₂ : d₂ t a b d ≠ 0)
    (ht : 1 - t ^ 2 ≠ 0)
    (hm : 1 - d * t ≠ 0) (hp : 1 + d * t ≠ 0)
    (him : 1 - t / d ≠ 0) (hip : 1 + t / d ≠ 0) :
    (2 / (q + 1) * finiteCore t a b d) * principalNormalizer t a b d =
      2 / (q + 1) * (a + 2 + a⁻¹) * (b + 2 + b⁻¹) /
        ((1 + d * t) * (1 + t / d)) := by
  rw [finiteCore_eq_closedCore t a b d h, mul_assoc,
    normalized_closedCore_principal t a b d hc hn₁ hn₂ hd₁ hd₂ ht hm hp him hip,
    satakeNumerator_eq a b h.a_ne_zero h.b_ne_zero]
  ring

theorem finite_sum_special_negative_formula (q t a b : K)
    (h : FiniteRegular t a b (-t))
    (ht₀ : t ≠ 0) (hc : poincare t ≠ 0) (hp : satakeNumerator a b ≠ 0)
    (hn₁ : n₁ t a b ≠ 0) (hn₂ : n₂ t a b ≠ 0)
    (hf : fourFactors a b (-t ^ 2) ≠ 0)
    (ht : 1 - t ^ 2 ≠ 0) (ht₄ : 1 - t ^ 4 ≠ 0) :
    (2 / (q + 1) * finiteCore t a b (-t)) * specialNormalizer t a b (-1) =
      2 / (q + 1) := by
  rw [finiteCore_eq_closedCore t a b (-t) h, mul_assoc,
    normalized_closedCore_special_negative t a b ht₀ h.a_ne_zero h.b_ne_zero
      hc hp hn₁ hn₂ hf ht ht₄, mul_one]

theorem finite_sum_special_positive_formula (q t a b : K) :
    ((1 - (1 : K)) / (q + 1) * finiteCore t a b t) * specialNormalizer t a b 1 = 0 := by
  simp

end Algebra
end FourierJacobi
