import FourierJacobi.Measure.MultiplicativeHaar

/-! The actual additive Haar scaling character of every nonzero local-field scalar. -/

noncomputable section

open MeasureTheory ValuativeRel FourierJacobi.Valuations
open scoped ENNReal NNReal Pointwise

namespace FourierJacobi.Measure

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

local instance unitScaling_t2Space : T2Space K := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  let := isUniformAddGroup_of_addCommGroup (G := K)
  infer_instance

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem valuationRingUnits_smul_integers (u : Kˣ) (hu : u ∈ valuationRingUnits K) :
    u • (𝒪[K] : Set K) = (𝒪[K] : Set K) := by
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  constructor
  · intro hx
    have h := (𝒪[K]).mul_mem hu.1 hx
    change (u : K) * (((u⁻¹ : Kˣ) : K) * x) ∈ 𝒪[K] at h
    simpa only [SetLike.mem_coe, ← mul_assoc, Units.mul_inv, one_mul] using h
  · intro hx
    exact (𝒪[K]).mul_mem hu.2 hx

variable [MeasurableSpace K] [BorelSpace K]

local instance unitScaling_additiveHaar_regular : (additiveHaar K).Regular := by
  unfold additiveHaar
  infer_instance

theorem distribHaarChar_valuationRingUnits (u : Kˣ) (hu : u ∈ valuationRingUnits K) :
    distribHaarChar K u = 1 := by
  have h := distribHaarChar_mul (additiveHaar K) u (𝒪[K] : Set K)
  rw [valuationRingUnits_smul_integers K u hu, additiveHaar_integers, mul_one] at h
  exact ENNReal.coe_injective h

/-- The additive Haar scaling character is derived for every actual scalar,
using its canonical integer valuation; no scaling law is assumed. -/
theorem distribHaarChar_eq_of_canonicalValuation (u : Kˣ) (n : ℤ)
    (hu : localFieldValuation K (u : K) = (n : WithTop ℤ)) :
    distribHaarChar K u = ((residueCardinality K : ℝ≥0)⁻¹) ^ n := by
  obtain ⟨π, hπ⟩ := exists_integral_canonical_uniformizer K
  have hs : u ∈ unitValuationShell K n := hu
  rw [unitValuationShell_eq_uniformizer_smul K π hπ n] at hs
  obtain ⟨v, hv, rfl⟩ := Set.mem_smul_set.mp hs
  simp only [smul_eq_mul, map_mul, map_zpow,
    canonicalUniformizer_distribHaarChar K π hπ,
    distribHaarChar_valuationRingUnits K v hv, mul_one]

theorem additiveHaar_smul_of_canonicalValuation (u : Kˣ) (n : ℤ)
    (hu : localFieldValuation K (u : K) = (n : WithTop ℤ)) (s : Set K) :
    additiveHaar K (u • s) =
      (↑(((residueCardinality K : ℝ≥0)⁻¹) ^ n) : ℝ≥0∞) * additiveHaar K s := by
  rw [← distribHaarChar_mul, distribHaarChar_eq_of_canonicalValuation K u n hu]

theorem additiveHaar_smul_valuationRingUnits (u : Kˣ)
    (hu : u ∈ valuationRingUnits K) (s : Set K) :
    additiveHaar K (u • s) = additiveHaar K s := by
  rw [← distribHaarChar_mul, distribHaarChar_valuationRingUnits K u hu]
  simp only [ENNReal.coe_one, one_mul]

theorem additiveHaar_real_smul_of_canonicalValuation (u : Kˣ) (n : ℤ)
    (hu : localFieldValuation K (u : K) = (n : WithTop ℤ)) (s : Set K) :
    (additiveHaar K).real (u • s) =
      (residueCardinality K : ℝ) ^ (-n) * (additiveHaar K).real s := by
  rw [Measure.real, additiveHaar_smul_of_canonicalValuation K u n hu,
    ENNReal.toReal_mul, ENNReal.coe_toReal]
  simp only [NNReal.coe_zpow, NNReal.coe_inv, NNReal.coe_natCast, inv_zpow, zpow_neg]
  rfl

end FourierJacobi.Measure
