import FourierJacobi.Algebra.EulerFactors
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Nonvanishing and the real interpretation of the principal answer

The assumptions here are exactly norm-one Satake parameters and 0 < t < 1.
In particular, the final denominator does not require any Weyl regularity.
-/

namespace FourierJacobi
namespace Algebra

theorem unit_ne_zero {z : ℂ} (hz : ‖z‖ = 1) : z ≠ 0 := by
  intro h
  simp [h] at hz

theorem one_sub_mul_ne_zero_of_norm_lt_one {z x : ℂ}
    (hz : ‖z‖ = 1) (hx : ‖x‖ < 1) : 1 - z * x ≠ 0 := by
  intro he
  have hh := congrArg norm (sub_eq_zero.mp he)
  simp only [norm_one, norm_mul, hz, one_mul] at hh
  linarith

theorem one_add_mul_ne_zero_of_norm_lt_one {z x : ℂ}
    (hz : ‖z‖ = 1) (hx : ‖x‖ < 1) : 1 + z * x ≠ 0 := by
  have hn : ‖-z‖ = 1 := by simpa using hz
  simpa using one_sub_mul_ne_zero_of_norm_lt_one hn hx

theorem coe_norm_lt_one {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t < 1) :
    ‖(t : ℂ)‖ < 1 := by
  simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht₀] using ht₁

theorem principal_final_denominator_ne_zero {t : ℝ} {d : ℂ}
    (ht₀ : 0 ≤ t) (ht₁ : t < 1) (hd : ‖d‖ = 1) :
    (1 + d * (t : ℂ)) * (1 + (t : ℂ) / d) ≠ 0 := by
  have hx := coe_norm_lt_one ht₀ ht₁
  have hi : ‖d⁻¹‖ = 1 := by simp [hd]
  exact mul_ne_zero (one_add_mul_ne_zero_of_norm_lt_one hd hx)
    (by simpa [div_eq_mul_inv, mul_comm] using
      one_add_mul_ne_zero_of_norm_lt_one hi hx)

theorem fourFactors_ne_zero {a b x : ℂ}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hx : ‖x‖ < 1) :
    fourFactors a b x ≠ 0 := by
  have hai : ‖a⁻¹‖ = 1 := by simp [ha]
  have hbi : ‖b⁻¹‖ = 1 := by simp [hb]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero
    (one_sub_mul_ne_zero_of_norm_lt_one ha hx)
    (one_sub_mul_ne_zero_of_norm_lt_one hai hx))
    (one_sub_mul_ne_zero_of_norm_lt_one hb hx))
    (one_sub_mul_ne_zero_of_norm_lt_one hbi hx)

theorem unit_satake_real {a : ℂ} (ha : ‖a‖ = 1) :
    a + 2 + a⁻¹ = ((2 + 2 * a.re : ℝ) : ℂ) := by
  rw [Complex.inv_eq_conj ha]
  apply Complex.ext <;> simp
  ring

theorem principal_final_denominator_normSq {t : ℝ} {d : ℂ} (hd : ‖d‖ = 1) :
    (1 + d * (t : ℂ)) * (1 + (t : ℂ) / d) =
      (Complex.normSq (1 + d * (t : ℂ)) : ℂ) := by
  rw [← Complex.mul_conj]
  congr 1
  simp [div_eq_mul_inv, Complex.inv_eq_conj hd, mul_comm]

/-- The branch of the square root used by the paper. -/
noncomputable def inverseSqrt (q : ℝ) : ℝ := (Real.sqrt q)⁻¹

theorem inverseSqrt_pos {q : ℝ} (hq : 1 < q) : 0 < inverseSqrt q := by
  exact inv_pos.mpr (Real.sqrt_pos.mpr (by linarith))

theorem inverseSqrt_lt_one {q : ℝ} (hq : 1 < q) : inverseSqrt q < 1 := by
  have hs : 1 < Real.sqrt q := by
    have h := Real.sq_sqrt (show 0 ≤ q by linarith)
    have hnon := Real.sqrt_nonneg q
    nlinarith
  exact (inv_lt_one₀ (by linarith : 0 < Real.sqrt q)).mpr hs

theorem inverseSqrt_sq {q : ℝ} (hq : 0 ≤ q) : inverseSqrt q ^ 2 = q⁻¹ := by
  rw [inverseSqrt, inv_pow, Real.sq_sqrt hq]

end Algebra
end FourierJacobi
