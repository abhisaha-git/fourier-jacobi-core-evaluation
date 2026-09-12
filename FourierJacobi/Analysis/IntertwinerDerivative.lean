import FourierJacobi.Algebra.Intertwiner
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# The normalized derivative at the special endpoint

This verifies the analytic derivative of the displayed two-by-two matrix.
The construction and invariance of the representation-theoretic pairing from
this derivative remain separate from this finite-dimensional calculation.
-/

namespace FourierJacobi
namespace Analysis

noncomputable def inducingPower (q s : ℝ) : ℝ :=
  Real.exp ((-2 * Real.log q) * s)

theorem inducingPower_endpoint (q : ℝ) (hq : 0 < q) :
    inducingPower q (1 / 2) = q⁻¹ := by
  unfold inducingPower
  rw [show (-2 * Real.log q) * (1 / 2) = -Real.log q by ring,
    Real.exp_neg, Real.exp_log hq]

theorem hasDerivAt_inducingPower (q : ℝ) (hq : 0 < q) :
    HasDerivAt (inducingPower q) (-2 * Real.log q / q) (1 / 2) := by
  have h := ((hasDerivAt_id (1 / 2 : ℝ)).const_mul (-2 * Real.log q)).exp
  convert h using 1
  · rfl
  · dsimp
    rw [show (-2 * Real.log q) * (1 / 2) = -Real.log q by ring,
      Real.exp_neg, Real.exp_log hq]
    ring

noncomputable def intertwinerFamily (q s : ℝ) :=
  intertwinerMatrix q (inducingPower q s)

theorem intertwiner_entry_derivative (q : ℝ) (hq : 1 < q) (i j : Fin 2) :
    HasDerivAt (fun s => intertwinerFamily q s i j)
      ((-2 * Real.log q / (q - 1)) * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j) (1 / 2) := by
  have hq₀ : 0 < q := by linarith
  have hqne : q ≠ 0 := ne_of_gt hq₀
  have hq₁ : q - 1 ≠ 0 := by linarith
  have hr : inducingPower q (1 / 2) = q⁻¹ := inducingPower_endpoint q hq₀
  have hden : 1 - inducingPower q (1 / 2) ≠ 0 := by
    rw [hr]
    exact sub_ne_zero.mpr (Ne.symm (inv_ne_one.mpr (by linarith)))
  have hp := hasDerivAt_inducingPower q hq₀
  have hb := hp.const_sub 1
  have hc := hasDerivAt_const (1 / 2 : ℝ) (1 - q⁻¹)
  have h00 := (hc.mul hp).div hb hden
  have h11 := hc.div hb hden
  simp only [Pi.mul_apply, hr, zero_mul, zero_add, zero_sub] at h00 h11
  clear hp hb hc hden hr
  fin_cases i <;> fin_cases j
  · convert h00 using 1 <;> first | rfl | (norm_num; field_simp; ring)
  · simpa [intertwinerFamily, intertwinerMatrix] using hasDerivAt_const (1 / 2 : ℝ) (1 : ℝ)
  · simpa [intertwinerFamily, intertwinerMatrix] using hasDerivAt_const (1 / 2 : ℝ) q⁻¹
  · convert h11 using 1 <;> first | rfl | (norm_num; field_simp)

theorem normalized_intertwiner_derivative (q : ℝ) (hq : 1 < q) :
    (fun i j => -(q - 1) / (2 * Real.log q) *
      deriv (fun s => intertwinerFamily q s i j) (1 / 2)) =
      (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  have hq₁ : q - 1 ≠ 0 := by linarith
  have hl : Real.log q ≠ 0 := ne_of_gt (Real.log_pos hq)
  ext i j
  rw [(intertwiner_entry_derivative q hq i j).deriv]
  field_simp

end Analysis
end FourierJacobi
