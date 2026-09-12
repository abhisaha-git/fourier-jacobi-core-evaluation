import FourierJacobi.Algebra.UnitaryFinite
import FourierJacobi.Analysis.ValuationSeries

/-! Natural convergence bounds and the independently transcribed expression E_q. -/

noncomputable section

namespace FourierJacobi.Analysis

open FourierJacobi.Algebra

/-- The tuple keeps multiplicities, including at exceptional Satake parameters. -/
def satakeTuple (a b : ℂ) : Fin 4 → ℂ := ![a, a⁻¹, b, b⁻¹]

def paperC (q : ℝ) : ℂ :=
  1 + 2 * (q : ℂ)⁻¹ + 2 * ((q : ℂ)⁻¹) ^ 2 +
    2 * ((q : ℂ)⁻¹) ^ 3 + ((q : ℂ)⁻¹) ^ 4

def paperN1 (q : ℝ) (a b : ℂ) : ℂ :=
  ∏ i : Fin 4, (1 - satakeTuple a b i * (q : ℂ)⁻¹)

def paperN2 (q : ℝ) (a b : ℂ) : ℂ :=
  (1 - a * b * (q : ℂ)⁻¹) * (1 - a⁻¹ * b * (q : ℂ)⁻¹) *
    (1 - a * b⁻¹ * (q : ℂ)⁻¹) * (1 - a⁻¹ * b⁻¹ * (q : ℂ)⁻¹)

def paperD1 (q : ℝ) (a b d : ℂ) : ℂ :=
  ∏ i : Fin 4, (1 - satakeTuple a b i * d * (inverseSqrt q : ℂ))

def paperD2 (q : ℝ) (a b d : ℂ) : ℂ :=
  ∏ i : Fin 4, (1 - satakeTuple a b i * d⁻¹ * (inverseSqrt q : ℂ))

/-- Exactly E_q in the brief; meaningful as a quotient when its denominator is nonzero. -/
def paperE (q : ℝ) (a b d : ℂ) : ℂ :=
  (((1 + a) ^ 2 * (1 + b) ^ 2 / (a * b)) * (1 - (q : ℂ)⁻¹) *
    paperN1 q a b * paperN2 q a b) /
      (paperC q * paperD1 q a b d * paperD2 q a b d)

theorem inverseSqrt_coe_sq (q : ℝ) (hq : 0 ≤ q) :
    (inverseSqrt q : ℂ) ^ 2 = (q : ℂ)⁻¹ := by
  exact_mod_cast inverseSqrt_sq hq

theorem paperC_eq_poincare (q : ℝ) (hq : 0 ≤ q) :
    paperC q = poincare (inverseSqrt q : ℂ) := by
  have h := inverseSqrt_coe_sq q hq
  unfold paperC poincare
  rw [← h]
  ring

theorem paperE_eq_closedCore (q : ℝ) (hq : 0 ≤ q) (a b d : ℂ) :
    paperE q a b d = closedCore (inverseSqrt q : ℂ) a b d := by
  unfold paperE closedCore satakeNumerator n₁ n₂ d₁ d₂ fourFactors
  rw [← paperC_eq_poincare q hq, inverseSqrt_coe_sq q hq]
  simp only [paperN1, paperN2, paperD1, paperD2, satakeTuple,
    Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, mul_one, div_eq_mul_inv, mul_inv_rev]
  ring

/-- Strict modulus bounds, not just nonzero geometric denominators. -/
structure GeometricRange (t d U V T : ℂ) : Prop where
  t2 : ‖t ^ 2‖ < 1
  p : ‖d * T * V * t‖ < 1
  n : ‖T * V * t / d‖ < 1
  e : ‖(T * V) ^ 2 * t ^ 2‖ < 1
  f : ‖T * U * t ^ 2‖ < 1
  g : ‖T * U * t ^ 4‖ < 1

theorem norm_one_sub_ne_zero {z : ℂ} (h : ‖z‖ < 1) : 1 - z ≠ 0 := by
  intro he
  have hz := congrArg norm (sub_eq_zero.mp he)
  rw [norm_one] at hz
  linarith

theorem GeometricRange.regionRegular {t d U V T : ℂ}
    (h : GeometricRange t d U V T) : RegionRegular t d (T * U) (T * V) := by
  refine ⟨?_, norm_one_sub_ne_zero h.n, norm_one_sub_ne_zero h.e,
    norm_one_sub_ne_zero h.f, norm_one_sub_ne_zero h.g⟩
  apply norm_one_sub_ne_zero
  simpa only [mul_assoc] using h.p

theorem geometricRange_of_bounds {t T : ℝ} {d U V : ℂ}
    (ht₀ : 0 < t) (ht₁ : t < 1) (hT₀ : 0 ≤ T) (hT₁ : T ≤ 1)
    (hd₀ : t ≤ ‖d‖) (hd₁ : ‖d‖ ≤ 1) (hstrict : T * t < ‖d‖)
    (hU : ‖U‖ = 1) (hV : ‖V‖ = 1) :
    GeometricRange (t : ℂ) d U V (T : ℂ) := by
  have ht : ‖(t : ℂ)‖ = t := by simp [abs_of_pos ht₀]
  have hT : ‖(T : ℂ)‖ = T := by simp [abs_of_nonneg hT₀]
  have hdpos : 0 < ‖d‖ := lt_of_lt_of_le ht₀ hd₀
  have ht2 : t ^ 2 < 1 := pow_lt_one₀ (le_of_lt ht₀) ht₁ (by decide)
  have ht4 : t ^ 4 < 1 := pow_lt_one₀ (le_of_lt ht₀) ht₁ (by decide)
  have hT2 : T ^ 2 ≤ 1 := pow_le_one₀ hT₀ hT₁
  have hprod : ‖d‖ * T ≤ 1 := by nlinarith [norm_nonneg d]
  constructor
  · simpa only [norm_pow, ht] using ht2
  · simp only [norm_mul, ht, hT, hV, mul_one]
    nlinarith
  · simp only [norm_div, norm_mul, ht, hT, hV, mul_one]
    exact (div_lt_one hdpos).mpr hstrict
  · simp only [norm_mul, norm_pow, ht, hT, hV, mul_one]
    nlinarith [sq_nonneg t]
  · simp only [norm_mul, norm_pow, ht, hT, hU, mul_one]
    nlinarith [sq_nonneg t]
  · simp only [norm_mul, norm_pow, ht, hT, hU, mul_one]
    nlinarith [sq_nonneg (t ^ 2)]

theorem geometricRange_damped {t T : ℝ} {d U V : ℂ}
    (ht₀ : 0 < t) (ht₁ : t < 1) (hT₀ : 0 < T) (hT₁ : T < 1)
    (hd₀ : t ≤ ‖d‖) (hd₁ : ‖d‖ ≤ 1)
    (hU : ‖U‖ = 1) (hV : ‖V‖ = 1) :
    GeometricRange (t : ℂ) d U V (T : ℂ) := by
  apply geometricRange_of_bounds ht₀ ht₁ hT₀.le hT₁.le hd₀ hd₁ ?_ hU hV
  nlinarith

theorem geometricRange_undamped {t : ℝ} {d U V : ℂ}
    (ht₀ : 0 < t) (ht₁ : t < 1) (hd₀ : t < ‖d‖) (hd₁ : ‖d‖ ≤ 1)
    (hU : ‖U‖ = 1) (hV : ‖V‖ = 1) :
    GeometricRange (t : ℂ) d U V 1 := by
  simpa only [Complex.ofReal_one] using
    geometricRange_of_bounds ht₀ ht₁ (by norm_num : (0 : ℝ) ≤ 1)
      (by norm_num : (1 : ℝ) ≤ 1) hd₀.le hd₁ (by simpa using hd₀) hU hV

theorem inverseSqrt_coe_mul (q : ℝ) (hq : 1 < q) :
    (q : ℂ) * (inverseSqrt q : ℂ) ^ 2 = 1 := by
  rw [inverseSqrt_coe_sq q (by linarith)]
  apply mul_inv_cancel₀
  exact_mod_cast (ne_of_gt (show 0 < q by linarith))

theorem residue_inverse_norm_lt_one (q : ℝ) (hq : 1 < q) :
    ‖(q : ℂ)⁻¹‖ < 1 := by
  rw [norm_inv]
  have hqn : ‖(q : ℂ)‖ = q := by simp [abs_of_pos (show 0 < q by linarith)]
  rw [hqn]
  exact (inv_lt_one₀ (by linarith : 0 < q)).mpr hq

theorem finiteRegular_interior {t : ℝ} {a b d : ℂ}
    (ht₀ : 0 < t) (ht₁ : t < 1) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hdlo : t < ‖d‖) (hdhi : ‖d‖ ≤ 1)
    (ha₁ : a ≠ 1) (hb₁ : b ≠ 1) (hab : a ≠ b) (hab₁ : a * b ≠ 1) :
    FiniteRegular (t : ℂ) a b d := by
  have ha₀ := unit_ne_zero ha
  have hb₀ := unit_ne_zero hb
  have hdpos : 0 < ‖d‖ := lt_trans ht₀ hdlo
  have hd₀ : d ≠ 0 := norm_pos_iff.mp hdpos
  have htn : ‖(t : ℂ)‖ = t := by simp [abs_of_pos ht₀]
  have hdt : ‖d * (t : ℂ)‖ < 1 := by
    rw [norm_mul, htn]
    nlinarith
  have htd : ‖(t : ℂ) / d‖ < 1 := by
    rw [norm_div, htn]
    exact (div_lt_one hdpos).mpr hdlo
  have hD₁ : d₁ (t : ℂ) a b d ≠ 0 := fourFactors_ne_zero ha hb hdt
  have hD₂ : d₂ (t : ℂ) a b d ≠ 0 := fourFactors_ne_zero ha hb htd
  have hWall : weylWall a b ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr ha₁)
      (sub_ne_zero.mpr hab)) (sub_ne_zero.mpr hb₁)) (sub_ne_zero.mpr hab₁)
  refine ⟨ha₀, hb₀, hd₀, sub_ne_zero.mpr ha₁, sub_ne_zero.mpr hb₁,
    sub_ne_zero.mpr hab, sub_ne_zero.mpr hab₁, ?_, ?_⟩
  · rw [weyl_common_euler_factorization (t : ℂ) a b d ha₀ hb₀ hd₀]
    exact mul_ne_zero
      (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hWall
        (pow_ne_zero 2 ha₀)) (pow_ne_zero 2 hb₀)) hd₀)
        (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 ha₀) (pow_ne_zero 2 hb₀))
          (pow_ne_zero 4 hd₀)))
      (mul_ne_zero hD₁ hD₂)
  · intro i
    have hr := (geometricRange_undamped ht₀ ht₁ hdlo hdhi
      (weylU_unitary ha hb i) (weylV_unitary ha hb i)).regionRegular
    simpa only [one_mul] using hr

end FourierJacobi.Analysis
