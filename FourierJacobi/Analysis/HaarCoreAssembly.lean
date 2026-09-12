import FourierJacobi.Analysis.CentralWeylSeries
import FourierJacobi.Analysis.FiberIntegration
import FourierJacobi.Analysis.HaarCellMaster

/-! Evaluation of actual Haar integrals by the independently norm-summable
master family. Every partition, cell mass and cell value is proved from the
field and matrix definitions in the imported modules. -/

noncomputable section
namespace FourierJacobi.Analysis
open MeasureTheory FourierJacobi.Algebra FourierJacobi.Valuations FourierJacobi.Measure

theorem coreIntegralPrefactor_ne_zero (q : ℝ) (hq : 1 < q) (r : Fin 3) :
    coreIntegralPrefactor q r ≠ 0 := by
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (lt_trans zero_lt_one hq)
  have hSC : 1 - (q : ℂ)⁻¹ ≠ 0 := by
    rw [sub_ne_zero, ne_eq, eq_comm, inv_eq_one]
    exact_mod_cast ne_of_gt hq
  fin_cases r <;> simp [coreIntegralPrefactor, hqC, hSC]

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K]

local notation "qK" => (residueCardinality K : ℝ)
local instance : T2Space K := kernelField_t2Space K
local instance : SecondCountableTopology K := kernelField_secondCountable K
local instance : BorelSpace Kˣ := coreUnits_borelSpace K

/-- The source prefactor times each actual Haar integrand is integrable, and
its ordinary integral is the corresponding independent central lattice sum. -/
theorem integrable_prefactor_core_eq_centralLatticeCore
    (a b d : ℂ) (T : ℝ) (hq : 2 < qK) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hT₀ : 0 < T) (hT₁ : T ≤ 1) (hd₀ : inverseSqrt qK ≤ ‖d‖) (hd₁ : ‖d‖ ≤ 1)
    (hstrict : T * inverseSqrt qK < ‖d‖) (r : Fin 3) (z : K)
    (hz : CentralRepresentative K (r.val : ℤ) z) :
    Integrable (fun p => coreIntegralPrefactor qK r *
      explicitCoreIntegrand K qK a b d T z p) (paperCoreMeasure K) ∧
    (∫ p, coreIntegralPrefactor qK r * explicitCoreIntegrand K qK a b d T z p
      ∂paperCoreMeasure K) = centralLatticeCore qK a b d T r := by
  let s := haarLatticeCell K (r.val : ℤ) z
  let F := fun i : LatticeIndex => coreIntegralPrefactor qK r *
    haarCellValue qK a b d T (r.val : ℤ) i
  have he (i : LatticeIndex) : ((paperCoreMeasure K).real (s i) : ℂ) * F i =
      centralWeightedTerm qK a b d T r i := by
    dsimp [s, F]
    rw [mul_left_comm]
    simpa only [centralWeightedTerm, weightedLatticeTerm, Complex.ofReal_natCast,
      mul_assoc] using haarLatticeCell_prefactor_value K (by linarith) a b d T
        (ne_of_gt hT₀) r z hz i
  have hcover : (⋃ i, s i) =ᵐ[paperCoreMeasure K] Set.univ := by
    have hc := haarLatticeCell_exhaustive_ae K (additiveHaar K)
      (paperMultiplicativeHaar K) (r.val : ℤ) z hz
    filter_upwards [hc] with p hp
    apply propext
    exact ⟨fun _ => True.intro, fun _ => Set.mem_iUnion.mpr hp.exists⟩
  have hn : Summable (fun i => (paperCoreMeasure K).real (s i) * ‖F i‖) := by
    apply Summable.of_nonneg_of_le
      (fun i => mul_nonneg measureReal_nonneg (norm_nonneg _))
      (fun i => ?_)
      (summable_central_norm_majorant qK T a b d hq ha hb hT₀.le hT₁ hd₀ hd₁ hstrict r)
    calc
      _ = ‖((paperCoreMeasure K).real (s i) : ℂ) * F i‖ := by
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg measureReal_nonneg]
      _ = ‖centralWeightedTerm qK a b d T r i‖ := congrArg norm (he i)
      _ ≤ _ := norm_sum_le _ _
  have hi := integrable_hasSum_of_countable_fibers (paperCoreMeasure K) s
    (fun p => coreIntegralPrefactor qK r * explicitCoreIntegrand K qK a b d T z p) F
    (haarLatticeCell_measurableSet K (r.val : ℤ) z)
    (haarLatticeCell_measure_ne_top K (r.val : ℤ) z)
    (fun _ _ hij => haarLatticeCell_disjoint K (r.val : ℤ) z hij) hcover
    (fun i p hp => congrArg (coreIntegralPrefactor qK r * ·)
      (explicitCoreIntegrand_eq_haarCellValue K qK a b d T (r.val : ℤ) z hz i p hp)) hn
  refine ⟨hi.1, ?_⟩
  have hh : HasSum (centralWeightedTerm qK a b d T r)
      (∫ p, coreIntegralPrefactor qK r * explicitCoreIntegrand K qK a b d T z p
        ∂paperCoreMeasure K) := by
    simpa only [he] using hi.2
  exact hh.unique (hasSum_centralWeightedTerm qK T a b d hq ha hb hT₀.le hT₁ hd₀ hd₁ hstrict r)

/-- Ordinary (unprefactored) integrability is proved as well. -/
theorem explicitCoreIntegrand_integrable
    (a b d : ℂ) (T : ℝ) (hq : 2 < qK) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hT₀ : 0 < T) (hT₁ : T ≤ 1) (hd₀ : inverseSqrt qK ≤ ‖d‖) (hd₁ : ‖d‖ ≤ 1)
    (hstrict : T * inverseSqrt qK < ‖d‖) (r : Fin 3) (z : K)
    (hz : CentralRepresentative K (r.val : ℤ) z) :
    Integrable (explicitCoreIntegrand K qK a b d T z) (paperCoreMeasure K) := by
  have hi := (integrable_prefactor_core_eq_centralLatticeCore K a b d T hq ha hb
    hT₀ hT₁ hd₀ hd₁ hstrict r z hz).1
  exact (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr
    (coreIntegralPrefactor_ne_zero qK (by linarith) r)) _).mp hi

theorem explicitHaarCoreShell_eq_centralLatticeCore
    (a b d : ℂ) (T : ℝ) (hq : 2 < qK) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hT₀ : 0 < T) (hT₁ : T ≤ 1) (hd₀ : inverseSqrt qK ≤ ‖d‖) (hd₁ : ‖d‖ ≤ 1)
    (hstrict : T * inverseSqrt qK < ‖d‖) (π : Kˣ)
    (hπ : localFieldValuation K (π : K) = (1 : WithTop ℤ)) (r : Fin 3) :
    explicitHaarCoreShell K (additiveHaar K) (paperMultiplicativeHaar K)
      qK a b d T π r = centralLatticeCore qK a b d T r := by
  have he := (integrable_prefactor_core_eq_centralLatticeCore K a b d T hq ha hb
    hT₀ hT₁ hd₀ hd₁ hstrict r (coreCentral K π r)
    (centralRepresentative_coreCentral K π hπ r)).2
  simpa only [explicitHaarCoreShell, paperCoreMeasure, integral_const_mul] using he

/-- The actual three independently defined Haar integrals equal the independent
master series. No integral-to-series identity or integrability is assumed. -/
theorem paperExplicitHaarCore_eq_latticeCore
    (a b d : ℂ) (T : ℝ) (hq : 2 < qK) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hT₀ : 0 < T) (hT₁ : T ≤ 1) (hd₀ : inverseSqrt qK ≤ ‖d‖) (hd₁ : ‖d‖ ≤ 1)
    (hstrict : T * inverseSqrt qK < ‖d‖) (π : Kˣ)
    (hπ : localFieldValuation K (π : K) = (1 : WithTop ℤ)) :
    paperExplicitHaarCore K a b d T π = latticeCore qK a b d T := by
  unfold paperExplicitHaarCore explicitHaarCore
  simp_rw [explicitHaarCoreShell_eq_centralLatticeCore K a b d T hq ha hb
    hT₀ hT₁ hd₀ hd₁ hstrict π hπ]
  exact centralLatticeCore_sum qK a b d T

end FourierJacobi.Analysis
