import FourierJacobi.Analysis.HaarLatticePartition
import FourierJacobi.Analysis.CoreParameters

/-!
Actual values of the explicit Haar integrand on its valuation/depth cells.
The scalar is defined by integer minima and the literal real power in the
integrand. No region fraction or integration identity enters its definition.
-/

noncomputable section
namespace FourierJacobi.Analysis
open FourierJacobi.Algebra FourierJacobi.Valuations
set_option maxHeartbeats 2000000

def haarCellValue (q : ℝ) (a b d : ℂ) (T : ℝ) (r : ℤ) (i : LatticeIndex) : ℂ :=
  d ^ i.1 * (Real.rpow (q ^ (-i.1)) (3 / 2) : ℂ) *
    (T : ℂ) ^ (-entryMinimum r i.1 i.2.1 i.2.2.1) *
      weylKernelAtIndices (inverseSqrt q : ℂ) a b
        ((cartanIndices r i.1 i.2.1 i.2.2.1 i.2.2.2).1 / 2)
        (cartanIndices r i.1 i.2.1 i.2.2.1 i.2.2.2).2

theorem haar_scale_rpow (q : ℝ) (hq : 0 < q) (k : ℤ) :
    Real.rpow (q ^ (-k)) (3 / 2) = inverseSqrt q ^ (3 * k) := by
  have ht : 0 ≤ inverseSqrt q := inv_nonneg.mpr (Real.sqrt_nonneg q)
  rw [← inverseSqrt_even_zpow q hq.le k]
  calc
    Real.rpow (inverseSqrt q ^ (2 * k)) (3 / 2) =
        inverseSqrt q ^ (((2 * k : ℤ) : ℝ) * (3 / 2 : ℝ)) := by
      simpa only [Real.rpow_eq_pow, Real.rpow_intCast] using
        (Real.rpow_mul ht (((2 * k : ℤ) : ℝ)) (3 / 2 : ℝ)).symm
    _ = inverseSqrt q ^ (3 * k) := by
      have he : ((2 * k : ℤ) : ℝ) * (3 / 2 : ℝ) = ((3 * k : ℤ) : ℝ) := by
        push_cast
        ring
      rw [he, Real.rpow_intCast]

theorem haar_scale_rpow_coe (q : ℝ) (hq : 0 < q) (k : ℤ) :
    (Real.rpow (q ^ (-k)) (3 / 2) : ℂ) = (inverseSqrt q : ℂ) ^ (3 * k) := by
  rw [haar_scale_rpow q hq]
  exact Complex.ofReal_zpow _ _

theorem haar_shell_zpow_coe (q : ℝ) (hq : 0 ≤ q) (j : ℤ) :
    (q : ℂ) ^ (-j) = (inverseSqrt q : ℂ) ^ (2 * j) := by
  exact_mod_cast (inverseSqrt_even_zpow q hq j).symm

section LocalField
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The independently defined integrand is exactly constant on each actual cell. -/
theorem explicitCoreIntegrand_eq_haarCellValue (q : ℝ) (a b d : ℂ) (T : ℝ)
    (r : ℤ) (z : K) (hz : CentralRepresentative K r z) (i : LatticeIndex)
    (p : HaarPoint K) (hp : p ∈ haarLatticeCell K r z i) :
    explicitCoreIntegrand K q a b d T z p = haarCellValue q a b d T r i := by
  have hk : coreScaleExponent K p.1 = i.1 := by
    apply WithTop.coe_injective
    exact (coreScaleExponent_coe K p.1).trans hp.1
  obtain ⟨_, _, _, hn, hb, _, hH⟩ :=
    haarLatticeCell_kernelCoordinates K r z hz i p hp
  unfold explicitCoreIntegrand coreLocalAbs explicitWeylKernel haarCellValue
  simp only [Function.comp_apply, hk, hn, hb, hH]

end LocalField

theorem haarCellValue_expanded (q : ℝ) (hq : 0 < q) (a b d : ℂ)
    (T : ℝ) (hT : T ≠ 0) (r : ℤ) (i : LatticeIndex) :
    haarCellValue q a b d T r i =
      d ^ i.1 * (inverseSqrt q : ℂ) ^ (3 * i.1) *
        ((poincare (inverseSqrt q : ℂ))⁻¹ * ∑ w : Fin 8,
          weylWeights (inverseSqrt q : ℂ) a b w *
            (inverseSqrt q : ℂ) ^
              (3 * (cartanIndices r i.1 i.2.1 i.2.2.1 i.2.2.2).1 +
                4 * (cartanIndices r i.1 i.2.1 i.2.2.1 i.2.2.2).2) *
            ((T : ℂ) * weylU a b w) ^
              ((cartanIndices r i.1 i.2.1 i.2.2.1 i.2.2.2).1 / 2) *
            ((T : ℂ) * weylV a b w) ^
              (cartanIndices r i.1 i.2.1 i.2.2.1 i.2.2.2).2) := by
  have hT' : (T : ℂ) ≠ 0 := by exact_mod_cast hT
  have hH := (shell_height_eq r i.1 i.2.1 i.2.2.1 i.2.2.2).symm
  have he : 6 * ((cartanIndices r i.1 i.2.1 i.2.2.1 i.2.2.2).1 / 2) =
      3 * (cartanIndices r i.1 i.2.1 i.2.2.1 i.2.2.2).1 := by
    unfold cartanIndices
    dsimp
    omega
  unfold haarCellValue
  rw [haar_scale_rpow_coe q hq, hH, mul_assoc]
  rw [weylKernelAtIndices_damping _ _ _ _ _ _ hT']
  rw [he]

theorem coreIntegralPrefactor_mul_shell_volume (q : ℝ) (hq : 1 < q) (r : Fin 3) :
    coreIntegralPrefactor q r * (1 - (q : ℂ)⁻¹) ^ 3 =
      shellCoeff (q : ℂ) (r.val : ℤ) * (1 - (q : ℂ)⁻¹) ^ 2 := by
  have hR : 1 - (q : ℂ)⁻¹ ≠ 0 :=
    norm_one_sub_ne_zero (residue_inverse_norm_lt_one q hq)
  fin_cases r
  · change (1 - (q : ℂ)⁻¹)⁻¹ * (1 - (q : ℂ)⁻¹) ^ 3 =
      (1 : ℂ) * (1 - (q : ℂ)⁻¹) ^ 2
    field_simp
  · change (q : ℂ) * (1 - (q : ℂ)⁻¹) ^ 3 =
      ((q : ℂ) * (1 - (q : ℂ)⁻¹)) * (1 - (q : ℂ)⁻¹) ^ 2
    ring
  · change (-(q : ℂ) / (1 - (q : ℂ)⁻¹)) * (1 - (q : ℂ)⁻¹) ^ 3 =
      -(q : ℂ) * (1 - (q : ℂ)⁻¹) ^ 2
    field_simp

end FourierJacobi.Analysis
