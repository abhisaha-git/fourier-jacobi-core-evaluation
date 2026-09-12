import FourierJacobi.Measure.LocalHaar
import FourierJacobi.Valuations.LocalField
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

/-!
# Actual local-field additive Haar volumes at every integer valuation

The normalized valuation is the independently defined canonical valuation
from `Valuations.LocalField`; the measure is the actual Haar construction
from `Measure.LocalHaar`. Scaling is derived using Haar's distributive
character, with its normalization computed from the maximal ideal.
-/

noncomputable section

open MeasureTheory ValuativeRel FourierJacobi.Valuations
open scoped ENNReal NNReal Pointwise WithZero

namespace FourierJacobi.Measure

set_option maxHeartbeats 2000000

theorem extendedNegLog_eq_coe_iff (z : ℤᵐ⁰) (n : ℤ) :
    extendedNegLog z = (n : WithTop ℤ) ↔ z = WithZero.exp (-n) := by
  induction z using WithZero.expRecOn with
  | zero =>
    constructor
    · intro h
      exact False.elim (WithTop.top_ne_coe h)
    · intro h
      exact False.elim (WithZero.exp_ne_zero h.symm)
  | exp a =>
    simp only [extendedNegLog_exp, WithTop.coe_inj, WithZero.exp_inj]
    omega

theorem intValue_lt_one_iff_le_exp_neg_one (z : ℤᵐ⁰) :
    z < 1 ↔ z ≤ WithZero.exp (-1 : ℤ) := by
  induction z using WithZero.expRecOn with
  | zero => simp
  | exp a =>
    change WithZero.exp a < WithZero.exp (0 : ℤ) ↔
      WithZero.exp a ≤ WithZero.exp (-1 : ℤ)
    rw [WithZero.exp_lt_exp, WithZero.exp_le_exp]
    omega

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

local instance integerShells_t2Space : T2Space K := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  let := isUniformAddGroup_of_addCommGroup (G := K)
  infer_instance

theorem canonicalValuation_eq_coe_iff (x : K) (n : ℤ) :
    localFieldValuation K x = (n : WithTop ℤ) ↔
      discreteValuation K x = WithZero.exp (-n) :=
  extendedNegLog_eq_coe_iff (discreteValuation K x) n

theorem exists_integral_canonical_uniformizer :
    ∃ π : 𝒪[K], localFieldValuation K (π : K) = 1 := by
  obtain ⟨x, hx⟩ := localFieldValuation_surjective K (1 : WithTop ℤ)
  have hint : x ∈ 𝒪[K] := (localFieldValuation_nonnegative_iff K x).mp (by rw [hx]; norm_num)
  exact ⟨⟨x, hint⟩, hx⟩

theorem canonical_uniformizer_ne_zero (π : 𝒪[K])
    (hπ : localFieldValuation K (π : K) = 1) : (π : K) ≠ 0 := by
  intro he
  rw [he, localFieldValuation_zero] at hπ
  exact WithTop.top_ne_coe hπ

/-- Canonical additive valuation one implies generation of the actual maximal
ideal. Generation is proved here, not assumed as an extra local-field datum. -/
theorem canonical_uniformizer_generates (π : 𝒪[K])
    (hπ : localFieldValuation K (π : K) = 1) : 𝓂[K] = Ideal.span {π} := by
  have hdπ : discreteValuation K (π : K) = WithZero.exp (-1 : ℤ) :=
    (canonicalValuation_eq_coe_iff K (π : K) 1).mp hπ
  ext x
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    Valuation.Integer.not_isUnit_iff_valuation_lt_one]
  change valuation K (x : K) < 1 ↔ x ∈ (Ideal.span {π} : Set 𝒪[K])
  rw [Valuation.integer.coe_span_singleton_eq_setOfPred_le_v_coe]
  change valuation K (x : K) < 1 ↔ valuation K (x : K) ≤ valuation K (π : K)
  have hlt : valuation K (x : K) < 1 ↔ discreteValuation K (x : K) < 1 := by
    change valuation K (x : K) < 1 ↔
      IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K (valuation K (x : K)) < 1
    rw [← map_one (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)]
    exact (map_lt_map_iff (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)).symm
  have hle : valuation K (x : K) ≤ valuation K (π : K) ↔
      discreteValuation K (x : K) ≤ discreteValuation K (π : K) :=
    (map_le_map_iff (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)).symm
  rw [hlt, hle, hdπ]
  exact intValue_lt_one_iff_le_exp_neg_one _

theorem canonical_uniformizer_zpow (π : 𝒪[K])
    (hπ : localFieldValuation K (π : K) = 1) (n : ℤ) :
    localFieldValuation K ((π : K) ^ n) = (n : WithTop ℤ) := by
  rw [canonicalValuation_eq_coe_iff, map_zpow₀,
    (canonicalValuation_eq_coe_iff K (π : K) 1).mp hπ, ← WithZero.exp_zsmul]
  congr 1
  simp

/-- Closed valuation balls, including zero, indexed by all integers. -/
def integerBall (n : ℤ) : Set K := {x | (n : WithTop ℤ) ≤ localFieldValuation K x}

/-- Finite-valuation shells; zero belongs to none of them. -/
def integerShell (n : ℤ) : Set K := {x | localFieldValuation K x = (n : WithTop ℤ)}

theorem integerShell_eq_sdiff (n : ℤ) :
    integerShell K n = integerBall K n \ integerBall K (n + 1) := by
  ext x
  simp only [integerShell, integerBall, Set.mem_ofPred_eq, Set.mem_sdiff]
  generalize localFieldValuation K x = v
  induction v using WithTop.recTopCoe with
  | top => simp
  | coe m =>
    simp only [WithTop.coe_inj, WithTop.coe_le_coe]
    omega

theorem integerBall_succ_subset (n : ℤ) : integerBall K (n + 1) ⊆ integerBall K n := by
  intro x hx
  change ((n + 1 : ℤ) : WithTop ℤ) ≤ localFieldValuation K x at hx
  change (n : WithTop ℤ) ≤ localFieldValuation K x
  exact le_trans (by exact_mod_cast (show n ≤ n + 1 by omega)) hx

theorem integerShell_unique (x : K) (m n : ℤ)
    (hm : x ∈ integerShell K m) (hn : x ∈ integerShell K n) : m = n :=
  WithTop.coe_injective (hm.symm.trans hn)

theorem exists_integerShell_iff_ne_zero (x : K) :
    (∃ n : ℤ, x ∈ integerShell K n) ↔ x ≠ 0 := by
  have hfinite (v : WithTop ℤ) : (∃ n : ℤ, v = (n : WithTop ℤ)) ↔ v ≠ ⊤ := by
    induction v using WithTop.recTopCoe with
    | top => simp
    | coe m => simp
  exact (hfinite (localFieldValuation K x)).trans (localFieldValuation_ne_top K x)

theorem existsUnique_integerShell (x : K) (hx : x ≠ 0) :
    ∃! n : ℤ, x ∈ integerShell K n := by
  obtain ⟨n, hn⟩ := (exists_integerShell_iff_ne_zero K x).mpr hx
  exact ⟨n, hn, fun m hm => integerShell_unique K x m n hm hn⟩

theorem integerShell_pairwiseDisjoint :
    Pairwise (fun m n : ℤ => Disjoint (integerShell K m) (integerShell K n)) := by
  intro m n hmn
  apply Set.disjoint_left.mpr
  intro x hm hn
  exact hmn (integerShell_unique K x m n hm hn)

theorem iUnion_integerShell_eq : (⋃ n : ℤ, integerShell K n) = ({0} : Set K)ᶜ := by
  ext x
  simpa only [Set.mem_iUnion, Set.mem_compl_iff, Set.mem_singleton_iff] using
    exists_integerShell_iff_ne_zero K x

/-- The chosen canonical uniformizer viewed as a nonzero field unit. -/
def canonicalUniformizerUnit (π : 𝒪[K])
    (hπ : localFieldValuation K (π : K) = 1) : Kˣ :=
  Units.mk0 (π : K) (canonical_uniformizer_ne_zero K π hπ)

theorem canonicalValuation_uniformizer_smul (π : 𝒪[K])
    (hπ : localFieldValuation K (π : K) = 1) (n : ℤ) (x : K) :
    localFieldValuation K ((canonicalUniformizerUnit K π hπ ^ n) • x) =
      (n : WithTop ℤ) + localFieldValuation K x := by
  change localFieldValuation K (((canonicalUniformizerUnit K π hπ ^ n : Kˣ) : K) * x) = _
  rw [Units.val_zpow_eq_zpow_val]
  change localFieldValuation K ((π : K) ^ n * x) = _
  rw [(localFieldValuation K).map_mul, canonical_uniformizer_zpow K π hπ n]

theorem coe_le_iff_neg_add_nonnegative (n : ℤ) (v : WithTop ℤ) :
    (n : WithTop ℤ) ≤ v ↔ 0 ≤ ((-n : ℤ) : WithTop ℤ) + v := by
  induction v using WithTop.recTopCoe with
  | top => simp
  | coe m =>
    rw [← WithTop.coe_add]
    change (n : WithTop ℤ) ≤ (m : WithTop ℤ) ↔
      ((0 : ℤ) : WithTop ℤ) ≤ ((-n + m : ℤ) : WithTop ℤ)
    simp only [WithTop.coe_le_coe]
    omega

theorem integerBall_eq_uniformizer_smul (π : 𝒪[K])
    (hπ : localFieldValuation K (π : K) = 1) (n : ℤ) :
    integerBall K n = (canonicalUniformizerUnit K π hπ ^ n) • (𝒪[K] : Set K) := by
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  change (n : WithTop ℤ) ≤ localFieldValuation K x ↔
    (canonicalUniformizerUnit K π hπ ^ n)⁻¹ • x ∈ (valuation K).integer
  rw [← localFieldValuation_nonnegative_iff, ← zpow_neg,
    canonicalValuation_uniformizer_smul]
  exact coe_le_iff_neg_add_nonnegative n _

theorem integerBall_isOpen (n : ℤ) : IsOpen (integerBall K n) := by
  obtain ⟨π, hπ⟩ := exists_integral_canonical_uniformizer K
  rw [integerBall_eq_uniformizer_smul K π hπ n]
  exact (valuation K).isOpen_integer.smul _

variable [MeasurableSpace K] [BorelSpace K]

local instance integerShells_additiveHaar_regular : (additiveHaar K).Regular := by
  unfold additiveHaar
  infer_instance

theorem integerBall_measurableSet (n : ℤ) : MeasurableSet (integerBall K n) :=
  (integerBall_isOpen K n).measurableSet

theorem integerShell_measurableSet (n : ℤ) : MeasurableSet (integerShell K n) := by
  rw [integerShell_eq_sdiff]
  exact (integerBall_measurableSet K n).diff (integerBall_measurableSet K (n + 1))

/-- The Haar scaling factor of the canonical uniformizer is obtained from the
actual maximal-ideal volume, which was proved by finite additive index. -/
theorem canonicalUniformizer_distribHaarChar (π : 𝒪[K])
    (hπ : localFieldValuation K (π : K) = 1) :
    distribHaarChar K (canonicalUniformizerUnit K π hπ) =
      (residueCardinality K : ℝ≥0)⁻¹ := by
  have heq : canonicalUniformizerUnit K π hπ • (𝒪[K] : Set K) =
      (fun u : 𝒪[K] => (π : K) ^ 1 * (u : K)) '' Set.univ := by
    ext x
    constructor
    · rintro ⟨a, ha, hax⟩
      refine ⟨⟨a, ha⟩, Set.mem_univ _, ?_⟩
      simpa only [canonicalUniformizerUnit, Units.smul_def, Units.val_mk0, pow_one, smul_eq_mul] using hax
    · rintro ⟨a, _, hax⟩
      refine ⟨(a : K), a.property, ?_⟩
      simpa only [canonicalUniformizerUnit, Units.smul_def, Units.val_mk0, pow_one, smul_eq_mul] using hax
  have hm := additiveHaar_uniformizer_pow K π (canonical_uniformizer_generates K π hπ) 1
  have hc := distribHaarChar_mul (additiveHaar K) (canonicalUniformizerUnit K π hπ)
    (𝒪[K] : Set K)
  rw [additiveHaar_integers, mul_one, heq, hm, pow_one] at hc
  apply ENNReal.coe_injective
  rw [ENNReal.coe_inv (by exact_mod_cast (residueCardinality_pos K).ne')]
  simpa only [ENNReal.coe_natCast] using hc

/-- All integer balls have the expected finite, positive Haar measure.
The proof includes negative integers, using the group-homomorphism law for
the genuine Haar scaling character. -/
theorem additiveHaar_integerBall (n : ℤ) :
    additiveHaar K (integerBall K n) =
      (((residueCardinality K : ℝ≥0)⁻¹) ^ n : ℝ≥0) := by
  obtain ⟨π, hπ⟩ := exists_integral_canonical_uniformizer K
  rw [integerBall_eq_uniformizer_smul K π hπ n, ← distribHaarChar_mul,
    additiveHaar_integers, mul_one, map_zpow, canonicalUniformizer_distribHaarChar K π hπ]

theorem additiveHaar_integerBall_ne_top (n : ℤ) :
    additiveHaar K (integerBall K n) ≠ ⊤ := by
  rw [additiveHaar_integerBall]
  exact ENNReal.coe_ne_top

theorem additiveHaar_real_integerBall (n : ℤ) :
    (additiveHaar K).real (integerBall K n) = (residueCardinality K : ℝ) ^ (-n) := by
  simp [measureReal_def, additiveHaar_integerBall, zpow_neg]

/-- The canonical finite-valuation shell measure, for every integer depth,
with exactly the manuscript's additive Haar normalization. -/
theorem additiveHaar_real_integerShell (n : ℤ) :
    (additiveHaar K).real (integerShell K n) =
      (1 - (residueCardinality K : ℝ)⁻¹) * (residueCardinality K : ℝ) ^ (-n) := by
  rw [integerShell_eq_sdiff, measureReal_sdiff (integerBall_succ_subset K n)
    (integerBall_measurableSet K (n + 1)) (additiveHaar_integerBall_ne_top K n),
    additiveHaar_real_integerBall, additiveHaar_real_integerBall]
  have hq : (residueCardinality K : ℝ) ≠ 0 := by
    exact_mod_cast (residueCardinality_pos K).ne'
  rw [show -(n + 1) = -n + -1 by omega, zpow_add₀ hq, zpow_neg_one]
  ring

theorem additiveHaar_real_integerShell_pos (n : ℤ) :
    0 < (additiveHaar K).real (integerShell K n) := by
  have hq : (1 : ℝ) < residueCardinality K := by exact_mod_cast residueCardinality_one_lt K
  have hq0 : (0 : ℝ) < residueCardinality K := lt_trans zero_lt_one hq
  rw [additiveHaar_real_integerShell]
  exact mul_pos (sub_pos.mpr ((inv_lt_one₀ hq0).mpr hq)) (zpow_pos hq0 _)

theorem additiveHaar_integerShell_ne_top (n : ℤ) :
    additiveHaar K (integerShell K n) ≠ ⊤ := by
  rw [integerShell_eq_sdiff]
  exact measure_ne_top_of_subset Set.sdiff_subset (additiveHaar_integerBall_ne_top K n)

/-- The same shell-volume formula as an equality in the measure's native
extended nonnegative real codomain. -/
theorem additiveHaar_integerShell (n : ℤ) :
    additiveHaar K (integerShell K n) =
      ENNReal.ofReal ((1 - (residueCardinality K : ℝ)⁻¹) *
        (residueCardinality K : ℝ) ^ (-n)) := by
  calc
    _ = ENNReal.ofReal ((additiveHaar K).real (integerShell K n)) :=
      (ENNReal.ofReal_toReal (additiveHaar_integerShell_ne_top K n)).symm
    _ = _ := congrArg ENNReal.ofReal (additiveHaar_real_integerShell K n)

/-- The canonical extended integer valuation is measurable, including its
infinite value at zero. No arbitrary finite value is assigned at zero. -/
theorem canonicalValuation_measurable [MeasurableSpace (WithTop ℤ)] :
    Measurable (localFieldValuation K) := by
  apply measurable_to_countable'
  intro v
  induction v using WithTop.recTopCoe with
  | top =>
    have heq : (localFieldValuation K) ⁻¹' {⊤} = {0} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact not_iff_not.mp (localFieldValuation_ne_top K x)
    rw [heq]
    exact measurableSet_singleton 0
  | coe n =>
    exact integerShell_measurableSet K n

end FourierJacobi.Measure
