import FourierJacobi.Algebra.WeylSum

/-!
# Denominator-safe evaluation of the Weyl expression

This connects the explicit root factors and kernel to the polynomial certificate.
The nonvanishing assumptions describe the regular locus of these rational
expressions; this file does not extend an integral across the excluded parameters.
-/

namespace FourierJacobi
namespace Algebra
variable {K : Type*} [Field K]

set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

def weylScale (a b : K) : Fin 8 → K := ![1, 1, 1, b ^ 2, 1, a ^ 2, b ^ 2, a ^ 2]

def weylKernelDenominator (t a b d : K) (i : Fin 8) : K :=
  d ^ 2 * (1 - d * weylV a b i * t) * (1 - weylV a b i * t / d)

theorem weyl_weights_cleared (t a b : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (ha₁ : a - 1 ≠ 0) (hb₁ : b - 1 ≠ 0) (hab : a - b ≠ 0)
    (hab₁ : a * b - 1 ≠ 0) (i : Fin 8) :
    weylWall a b * weylWeights t a b i = weylWeightNumerators t a b i := by
  have ha₁' : 1 - a ≠ 0 := sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp ha₁))
  have hb₁' : 1 - b ≠ 0 := sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp hb₁))
  have hab' : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp hab))
  have hab₁' : 1 - a * b ≠ 0 := sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp hab₁))
  fin_cases i <;>
    simp [weylWall, weylWeights, weylWeightNumerators, rootFactor] <;>
    field_simp <;> ring

theorem weyl_height_cleared (t a b d : K) (ha : a ≠ 0) (hb : b ≠ 0) (i : Fin 8) :
    (a ^ 2 * b ^ 2 * weylScale a b i) *
      kernelNumerator t d (weylU a b i) (weylV a b i) =
      weylHeightNumerators t a b d i := by
  fin_cases i <;>
    simp [weylScale, weylU, weylV, kernelNumerator, weylHeightNumerators,
      weylHeight0, weylHeight1, weylHeight2, weylHeight3,
      weylHeight4, weylHeight5, weylHeight6, weylHeight7] <;>
    field_simp <;> ring

theorem weyl_denominator_factorization (t a b d : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hd : d ≠ 0) (i : Fin 8) :
    weylCommonDenominator t a b d =
      weylWall a b * weylKernelDenominator t a b d i *
        (a ^ 2 * b ^ 2 * weylScale a b i) * weylRemainingFactors t a b d i := by
  fin_cases i <;>
    simp [weylCommonDenominator, weylKernelDenominator, weylV,
      weylScale, weylRemainingFactors] <;> field_simp <;> ring

private theorem clear_weighted_kernel (R A An S H Hn D B : K) (hD : D ≠ 0)
    (hA : R * A = An) (hH : S * H = Hn) :
    (R * D * S * B) * (A * (H / D)) = An * Hn * B := by
  calc
    _ = (R * A) * (S * H) * B := by field_simp
    _ = _ := by rw [hA, hH]

theorem weyl_term_cleared (t a b d : K) (ha : a ≠ 0) (hb : b ≠ 0) (hd : d ≠ 0)
    (ha₁ : a - 1 ≠ 0) (hb₁ : b - 1 ≠ 0) (hab : a - b ≠ 0) (hab₁ : a * b - 1 ≠ 0)
    (i : Fin 8) (hD : weylKernelDenominator t a b d i ≠ 0) :
    weylCommonDenominator t a b d * weylTerms t a b d i =
      weylClearedTerms t a b d i := by
  rw [weyl_denominator_factorization t a b d ha hb hd i]
  exact clear_weighted_kernel _ _ _ _ _ _ _ _ hD
    (weyl_weights_cleared t a b ha hb ha₁ hb₁ hab hab₁ i)
    (weyl_height_cleared t a b d ha hb i)

/-- The full finite Weyl identity, with its common denominator left explicit. -/
theorem eight_weyl_sum (t a b d : K) (ha : a ≠ 0) (hb : b ≠ 0) (hd : d ≠ 0)
    (ha₁ : a - 1 ≠ 0) (hb₁ : b - 1 ≠ 0) (hab : a - b ≠ 0) (hab₁ : a * b - 1 ≠ 0)
    (hD : ∀ i, weylKernelDenominator t a b d i ≠ 0)
    (hW : weylCommonDenominator t a b d ≠ 0) :
    (∑ i : Fin 8, weylTerms t a b d i) =
      weylTargetNumerator t a b d / weylCommonDenominator t a b d := by
  apply (eq_div_iff hW).mpr
  rw [mul_comm, Finset.mul_sum]
  simp_rw [weyl_term_cleared t a b d ha hb hd ha₁ hb₁ hab hab₁ _ (hD _)]
  exact weyl_polynomial_identity t a b d

def tensorDenominatorPolynomial (t a b d : K) : K :=
  (1 - a * d * t) * (a - d * t) * (1 - b * d * t) * (b - d * t) *
    (d - a * t) * (a * d - t) * (d - b * t) * (b * d - t)

theorem tensor_denominator_cleared (t a b d : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hd : d ≠ 0) :
    (a ^ 2 * b ^ 2 * d ^ 4) * (d₁ t a b d * d₂ t a b d) =
      tensorDenominatorPolynomial t a b d := by
  unfold d₁ d₂ fourFactors tensorDenominatorPolynomial
  field_simp

theorem weyl_common_euler_factorization (t a b d : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hd : d ≠ 0) :
    weylCommonDenominator t a b d =
      (weylWall a b * a ^ 2 * b ^ 2 * d * (a ^ 2 * b ^ 2 * d ^ 4)) *
        (d₁ t a b d * d₂ t a b d) := by
  calc
    _ = (weylWall a b * a ^ 2 * b ^ 2 * d) *
        tensorDenominatorPolynomial t a b d := by
      unfold weylCommonDenominator tensorDenominatorPolynomial
      ring
    _ = _ := by rw [← tensor_denominator_cleared t a b d ha hb hd]; ring

def weylClosedExpression (t a b d : K) : K :=
  satakeNumerator a b * (1 - t ^ 2) * n₁ t a b * n₂ t a b /
    (d₁ t a b d * d₂ t a b d)

theorem weyl_target_numerator_eq (t a b d : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    weylTargetNumerator t a b d =
      (weylWall a b * a ^ 2 * b ^ 2 * d * (a ^ 2 * b ^ 2 * d ^ 4)) *
        (satakeNumerator a b * (1 - t ^ 2) * n₁ t a b * n₂ t a b) := by
  unfold weylTargetNumerator weylWall satakeNumerator n₁ n₂ fourFactors
  field_simp
  ring

theorem weyl_target_cleared (t a b d : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hd : d ≠ 0)
    (hD : d₁ t a b d * d₂ t a b d ≠ 0) :
    weylCommonDenominator t a b d * weylClosedExpression t a b d =
      weylTargetNumerator t a b d := by
  rw [weyl_common_euler_factorization t a b d ha hb hd, weyl_target_numerator_eq t a b d ha hb]
  unfold weylClosedExpression
  generalize (d₁ t a b d * d₂ t a b d) = D at *
  field_simp

theorem eight_weyl_sum_closed (t a b d : K) (ha : a ≠ 0) (hb : b ≠ 0) (hd : d ≠ 0)
    (ha₁ : a - 1 ≠ 0) (hb₁ : b - 1 ≠ 0) (hab : a - b ≠ 0) (hab₁ : a * b - 1 ≠ 0)
    (hD : ∀ i, weylKernelDenominator t a b d i ≠ 0)
    (hW : weylCommonDenominator t a b d ≠ 0) :
    (∑ i : Fin 8, weylTerms t a b d i) = weylClosedExpression t a b d := by
  have he := hW
  rw [weyl_common_euler_factorization t a b d ha hb hd] at he
  have he' := (mul_ne_zero_iff.mp he).2
  rw [eight_weyl_sum t a b d ha hb hd ha₁ hb₁ hab hab₁ hD hW]
  exact ((eq_div_iff hW).mpr (by
    simpa [mul_comm] using weyl_target_cleared t a b d ha hb hd he')).symm

theorem weylClosed_div_poincare (t a b d : K) :
    weylClosedExpression t a b d / poincare t = closedCore t a b d := by
  unfold weylClosedExpression closedCore
  rw [div_div]
  congr 1
  ring

def weylL (a b : K) : Fin 8 → K := ![a * b, a * b, a, a, b, b, 1, 1]

theorem gamma_substitution (a b gamma : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (hgamma : a * b * gamma ^ 2 = 1) (i : Fin 8) :
    gamma ^ 2 * weylL a b i ^ 2 = weylU a b i := by
  have hg : gamma ^ 2 = (a * b)⁻¹ := by
    rw [← one_div]
    apply (eq_div_iff (mul_ne_zero ha hb)).mpr
    simpa [mul_comm] using hgamma
  rw [hg]
  fin_cases i <;> simp [weylL, weylU] <;> field_simp

end Algebra
end FourierJacobi
