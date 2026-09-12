import FourierJacobi.Measure.MultiplicativeHaar

/-!
# The source's multiplicative Haar normalization

The source uses d×a = |a|⁻¹ da, so the volume of O_K^× is
1-q⁻¹. The auxiliary `multiplicativeHaar` has unit volume one; the
measure here restores the source normalization exactly once.
-/

noncomputable section

open MeasureTheory ValuativeRel
open scoped ENNReal

namespace FourierJacobi.Measure

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

theorem paperMultiplicativeFactor_pos : 0 < 1 - (residueCardinality K : ℝ)⁻¹ := by
  have hq : (1 : ℝ) < residueCardinality K := by exact_mod_cast residueCardinality_one_lt K
  exact sub_pos.mpr ((inv_lt_one₀ (lt_trans zero_lt_one hq)).mpr hq)

variable [MeasurableSpace Kˣ] [BorelSpace Kˣ]

/-- The paper's multiplicative measure: unit-shell mass 1-q⁻¹. -/
def paperMultiplicativeHaar : MeasureTheory.Measure Kˣ :=
  ENNReal.ofReal (1 - (residueCardinality K : ℝ)⁻¹) • multiplicativeHaar K

instance paperMultiplicativeHaar_isHaarMeasure : (paperMultiplicativeHaar K).IsHaarMeasure := by
  unfold paperMultiplicativeHaar
  exact Measure.IsHaarMeasure.smul (multiplicativeHaar K)
    (ENNReal.ofReal_pos.mpr (paperMultiplicativeFactor_pos K)).ne'
    ENNReal.ofReal_ne_top

instance paperMultiplicativeHaar_sigmaFinite : SigmaFinite (paperMultiplicativeHaar K) := by
  change SigmaFinite (Real.toNNReal (1 - (residueCardinality K : ℝ)⁻¹) • multiplicativeHaar K)
  infer_instance

theorem paperMultiplicativeHaar_valuationRingUnits :
    paperMultiplicativeHaar K (valuationRingUnits K : Set Kˣ) =
      ENNReal.ofReal (1 - (residueCardinality K : ℝ)⁻¹) := by
  simp only [paperMultiplicativeHaar, Measure.smul_apply,
    multiplicativeHaar_valuationRingUnits, smul_eq_mul, mul_one]

theorem paperMultiplicativeHaar_unitValuationShell (n : ℤ) :
    paperMultiplicativeHaar K (unitValuationShell K n) =
      ENNReal.ofReal (1 - (residueCardinality K : ℝ)⁻¹) := by
  simp only [paperMultiplicativeHaar, Measure.smul_apply,
    multiplicativeHaar_unitValuationShell, smul_eq_mul, mul_one]

theorem paperMultiplicativeHaar_real_unitValuationShell (n : ℤ) :
    (paperMultiplicativeHaar K).real (unitValuationShell K n) =
      1 - (residueCardinality K : ℝ)⁻¹ := by
  rw [Measure.real, paperMultiplicativeHaar_unitValuationShell,
    ENNReal.toReal_ofReal (paperMultiplicativeFactor_pos K).le]

end FourierJacobi.Measure
