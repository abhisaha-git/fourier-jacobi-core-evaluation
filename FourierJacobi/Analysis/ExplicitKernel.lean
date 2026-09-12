import FourierJacobi.Valuations.KernelIndices
import FourierJacobi.Algebra.UnitaryFinite

/-!
# An explicit measurable Weyl kernel on the actual local-field matrices

The matrix indices in this definition are extracted from the actual entry and
two-by-two-minor valuation minima. The norm bound is a finite triangle inequality;
it uses no spherical coefficient estimate and assumes no integral identity.
The rational Weyl weights represent the intended formula on their regular locus.
-/

noncomputable section
set_option maxHeartbeats 1000000

namespace FourierJacobi.Analysis
open FourierJacobi.Algebra FourierJacobi.Valuations

/-- Integer-indexed Weyl formula, using integer powers throughout. -/
@[irreducible] def weylKernelAtIndices (t a b : ℂ) (n B : ℤ) : ℂ :=
  (poincare t)⁻¹ * ∑ i : Fin 8,
    weylWeights t a b i * t ^ (6 * n + 4 * B) *
      (weylU a b i) ^ n * (weylV a b i) ^ B

theorem weylKernelAtIndices_norm_le (t a b : ℂ) (n B : ℤ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    ‖weylKernelAtIndices t a b n B‖ ≤
      ((∑ i : Fin 8, ‖weylWeights t a b i‖) / ‖poincare t‖) *
        ‖t‖ ^ (6 * n + 4 * B) := by
  unfold weylKernelAtIndices
  rw [norm_mul, norm_inv]
  calc
    _ ≤ ‖poincare t‖⁻¹ * ∑ i : Fin 8,
        ‖weylWeights t a b i * t ^ (6*n+4*B) *
          (weylU a b i) ^ n * (weylV a b i) ^ B‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr (norm_nonneg _))
    _ = _ := by
      simp_rw [norm_mul, norm_zpow, weylU_unitary ha hb, weylV_unitary ha hb,
        one_zpow, mul_one]
      rw [← Finset.sum_mul]
      ring

theorem poincare_coe_norm (t : ℝ) : ‖poincare (t : ℂ)‖ = poincare t := by
  have hp : 0 < poincare t := by unfold poincare; positivity
  have hc : poincare (t : ℂ) = ((poincare t : ℝ) : ℂ) := by simp [poincare]
  rw [hc]
  simpa using abs_of_pos hp

theorem weylKernelAtIndices_damping (t a b T : ℂ) (n B : ℤ) (hT : T ≠ 0) :
    T ^ (n+B) * weylKernelAtIndices t a b n B =
      (poincare t)⁻¹ * ∑ i : Fin 8,
        weylWeights t a b i * t ^ (6*n+4*B) *
          (T * weylU a b i) ^ n * (T * weylV a b i) ^ B := by
  unfold weylKernelAtIndices
  calc
    _ = (poincare t)⁻¹ * ∑ i : Fin 8,
        T ^ (n+B) * (weylWeights t a b i * t ^ (6*n+4*B) *
          (weylU a b i) ^ n * (weylV a b i) ^ B) := by
      rw [← Finset.mul_sum]
      ring
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [zpow_add₀ hT]
      simp only [mul_zpow]
      ring

section LocalField
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The explicit kernel on the actual core matrices, independent of any integral. -/
def explicitWeylKernel (t a b : ℂ) (p : KernelPoint K) : ℂ :=
  ((fun nb : ℤ × ℤ => weylKernelAtIndices t a b nb.1 nb.2) ∘
    (fun s : KernelPoint K => (kernelN K s, kernelB K s))) p

theorem explicitWeylKernel_formula (t a b : ℂ) (p : KernelPoint K) :
    explicitWeylKernel K t a b p =
      (poincare t)⁻¹ * ∑ i : Fin 8,
        weylWeights t a b i * t ^ (3 * kernelEll K p + 4 * kernelB K p) *
          (weylU a b i) ^ (kernelEll K p / 2) *
            (weylV a b i) ^ (kernelB K p) := by
  rw [kernel_half_ell]
  unfold explicitWeylKernel weylKernelAtIndices kernelEll
  simp only [Function.comp_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 3
  ring

/-- The elementary regular-parameter majorant in the brief, in t coordinates. -/
theorem explicitWeylKernel_norm_le (t : ℝ) (a b : ℂ) (p : KernelPoint K)
    (ht : 0 ≤ t) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    ‖explicitWeylKernel K (t : ℂ) a b p‖ ≤
      ((∑ i : Fin 8, ‖weylWeights (t : ℂ) a b i‖) / poincare t) *
        t ^ (3 * kernelEll K p + 4 * kernelB K p) := by
  have hn := weylKernelAtIndices_norm_le (t : ℂ) a b (kernelN K p) (kernelB K p) ha hb
  have he : 6 * kernelN K p + 4 * kernelB K p =
      3 * kernelEll K p + 4 * kernelB K p := by unfold kernelEll; ring
  simpa only [explicitWeylKernel, Function.comp_apply, poincare_coe_norm, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg ht, he] using hn

theorem explicitWeylKernel_damping (t a b T : ℂ) (p : KernelPoint K) (hT : T ≠ 0) :
    T ^ (kernelHeight K p) * explicitWeylKernel K t a b p =
      (poincare t)⁻¹ * ∑ i : Fin 8,
        weylWeights t a b i * t ^ (6 * kernelN K p + 4 * kernelB K p) *
          (T * weylU a b i) ^ (kernelN K p) *
            (T * weylV a b i) ^ (kernelB K p) :=
  weylKernelAtIndices_damping t a b T (kernelN K p) (kernelB K p) hT

section Measurability
variable [MeasurableSpace K] [BorelSpace K]

theorem explicitWeylKernel_measurable (t a b : ℂ) :
    Measurable (explicitWeylKernel K t a b) := by
  have hi : Measurable (fun p : ℤ × ℤ => weylKernelAtIndices t a b p.1 p.2) :=
    measurable_of_countable _
  exact hi.comp ((kernelN_measurable K).prodMk (kernelB_measurable K))

theorem damped_explicitWeylKernel_measurable (t a b T : ℂ) :
    Measurable (fun p : KernelPoint K =>
      T ^ (kernelHeight K p) * explicitWeylKernel K t a b p) :=
  ((measurable_of_countable (fun n : ℤ => T ^ n)).comp
    (kernelHeight_measurable K)).mul (explicitWeylKernel_measurable K t a b)

end Measurability
end LocalField
end FourierJacobi.Analysis
