import FourierJacobi.Analysis.HaarCellValue
import FourierJacobi.Analysis.HaarCellMass

/-!
The normalization identity joining an actual Haar cell's volume and constant
integrand value to the independently defined master summand. The only scalar
calculations are integer powers, the real absolute-value power, and the three
source prefactors. No summed region fraction is used.
-/

noncomputable section
namespace FourierJacobi.Analysis
open FourierJacobi.Algebra FourierJacobi.Valuations
set_option maxHeartbeats 2000000

def haarCellScalarMass (q : ℝ) (r : ℤ) (i : LatticeIndex) : ℂ :=
  (1 - (q : ℂ)⁻¹) ^ 3 * ((q : ℂ) ^ (-i.2.1) * (q : ℂ) ^ (-i.2.2.1)) *
    collisionWeight (q : ℂ) r i.2.1 i.2.2.1 i.2.2.2

theorem prefactor_cellScalarMass_haarCellValue (q : ℝ) (hq : 1 < q)
    (a b d : ℂ) (T : ℝ) (hT : T ≠ 0) (r : Fin 3) (i : LatticeIndex) :
    coreIntegralPrefactor q r * haarCellScalarMass q (r.val : ℤ) i *
        haarCellValue q a b d T (r.val : ℤ) i =
      ∑ w : Fin 8, (weylWeights (inverseSqrt q : ℂ) a b w / paperC q) *
        masterTerm (q : ℂ) (inverseSqrt q : ℂ) d (weylU a b w) (weylV a b w)
          (T : ℂ) (r.val : ℤ) i := by
  have hq₀ : 0 < q := by linarith
  have ht : (inverseSqrt q : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (inverseSqrt_pos hq)
  unfold haarCellScalarMass
  calc
    _ = (coreIntegralPrefactor q r * (1 - (q : ℂ)⁻¹) ^ 3) *
        (((q : ℂ) ^ (-i.2.1) * (q : ℂ) ^ (-i.2.2.1)) *
          collisionWeight (q : ℂ) (r.val : ℤ) i.2.1 i.2.2.1 i.2.2.2 *
          haarCellValue q a b d T (r.val : ℤ) i) := by ring
    _ = (shellCoeff (q : ℂ) (r.val : ℤ) * (1 - (q : ℂ)⁻¹) ^ 2) *
        (((q : ℂ) ^ (-i.2.1) * (q : ℂ) ^ (-i.2.2.1)) *
          collisionWeight (q : ℂ) (r.val : ℤ) i.2.1 i.2.2.1 i.2.2.2 *
          haarCellValue q a b d T (r.val : ℤ) i) := by
      rw [coreIntegralPrefactor_mul_shell_volume q hq r]
    _ = _ := by
      rw [haarCellValue_expanded q hq₀ a b d T hT (r.val : ℤ) i,
        haar_shell_zpow_coe q hq₀.le i.2.1, haar_shell_zpow_coe q hq₀.le i.2.2.1,
        paperC_eq_poincare q hq₀.le, ← inverseSqrt_coe_sq q hq₀.le]
      simp only [mul_assoc, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      unfold masterTerm shellMonomial
      dsimp
      simp only [zpow_add₀ ht, div_eq_mul_inv]
      ring

section LocalField
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K]

/-- The scalar normalization uses the actual source-normalized Haar cell mass. -/
theorem haarLatticeCell_prefactor_value
    (hq : 1 < (FourierJacobi.Measure.residueCardinality K : ℝ))
    (a b d : ℂ) (T : ℝ) (hT : T ≠ 0) (r : Fin 3) (z : K)
    (hz : CentralRepresentative K (r.val : ℤ) z) (i : LatticeIndex) :
    coreIntegralPrefactor (FourierJacobi.Measure.residueCardinality K : ℝ) r *
        (((paperCoreMeasure K).real (haarLatticeCell K (r.val : ℤ) z i) : ℝ) : ℂ) *
        haarCellValue (FourierJacobi.Measure.residueCardinality K : ℝ) a b d T
          (r.val : ℤ) i =
      ∑ w : Fin 8,
        (weylWeights (inverseSqrt (FourierJacobi.Measure.residueCardinality K : ℝ) : ℂ)
          a b w / paperC (FourierJacobi.Measure.residueCardinality K : ℝ)) *
        masterTerm (FourierJacobi.Measure.residueCardinality K : ℂ)
          (inverseSqrt (FourierJacobi.Measure.residueCardinality K : ℝ) : ℂ)
          d (weylU a b w) (weylV a b w) (T : ℂ) (r.val : ℤ) i := by
  rw [haarLatticeCell_complex_mass K (r.val : ℤ) z hz i]
  simpa only [haarCellScalarMass, Complex.ofReal_natCast] using
    prefactor_cellScalarMass_haarCellValue (FourierJacobi.Measure.residueCardinality K : ℝ)
      hq a b d T hT r i

end LocalField
end FourierJacobi.Analysis
