import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Complex.Basic

/-!
# Removing a bounded height damping factor

This is the general dominated-convergence step required at the special endpoint.
Its integrability hypothesis must be proved for the original period integrand.
It is not an assertion that the separately unfolded endpoint integrals converge.
-/

namespace FourierJacobi
namespace Analysis

open MeasureTheory Filter
open scoped Topology

theorem polynomial_geometric_summable (k : ℕ) {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r < 1) :
    Summable (fun n : ℕ => (n : ℝ) ^ k * r ^ n) := by
  exact summable_pow_mul_geometric_of_norm_lt_one k
    (by simpa [Real.norm_eq_abs, abs_of_nonneg hr₀] using hr₁)

theorem height_damping_tendsto_integral
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : X → ℂ} (hf : Integrable f μ)
    {height : X → ℕ} (hh : Measurable height)
    {T : ℕ → ℝ} (hT₀ : ∀ n, 0 ≤ T n) (hT₁ : ∀ n, T n ≤ 1)
    (hTlim : Tendsto T atTop (𝓝 1)) :
    Tendsto (fun n => ∫ x, (T n ^ height x) • f x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => ‖f x‖)
  · intro n
    exact (hh.const_pow (T n)).aestronglyMeasurable.smul hf.aestronglyMeasurable
  · exact hf.norm
  · intro n
    filter_upwards [] with x
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hT₀ n) _)]
    exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (hT₀ n) (hT₁ n))
  · filter_upwards [] with x
    simpa using (hTlim.pow (height x)).smul_const (f x)

end Analysis
end FourierJacobi
