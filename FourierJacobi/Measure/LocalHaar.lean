import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.MeasureTheory.Measure.Real
import FourierJacobi.Measure.NullSets

/-!
# Concrete normalized local-field Haar measure

The field is an arbitrary nonarchimedean local field in mathlib's sense.
The residue cardinality is the cardinality of its actual residue field.
No primality, characteristic-zero, or oddness restriction is needed here.

The measure is constructed by Haar's theorem, normalized on the actual
valuation ring. Ideal-power volumes are deduced from finite additive indices;
they are not supplied as assumptions. These are ingredients of `exp:haar-shells`
and `expanded:collision` in the expanded Section 2.
-/

noncomputable section

open MeasureTheory ValuativeRel
open scoped ENNReal NNReal

namespace FourierJacobi.Measure

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

local instance localField_t2Space : T2Space K := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  let := isUniformAddGroup_of_addCommGroup (G := K)
  infer_instance

variable [MeasurableSpace K] [BorelSpace K]

/-- The compact open valuation ring, as a normalization set for Haar measure. -/
def integersCompact : TopologicalSpace.PositiveCompacts K :=
  ⟨⟨𝒪[K], IsNonarchimedeanLocalField.isCompact_closedBall K 1⟩,
    by
      rw [(valuation K).isOpen_integer.interior_eq]
      exact ⟨0, by simp⟩⟩

/-- Additive Haar measure on the local field, with valuation-ring volume one. -/
def additiveHaar : MeasureTheory.Measure K :=
  MeasureTheory.Measure.addHaarMeasure (integersCompact K)

instance additiveHaar_isAddHaarMeasure : (additiveHaar K).IsAddHaarMeasure := by
  unfold additiveHaar
  infer_instance

theorem additiveHaar_integers : additiveHaar K (𝒪[K] : Set K) = 1 :=
  MeasureTheory.Measure.addHaarMeasure_self

/-- The actual cardinality of the residue field; it is not assumed prime. -/
def residueCardinality : ℕ := Nat.card 𝓀[K]

omit [MeasurableSpace K] [BorelSpace K] in
theorem residueCardinality_pos : 0 < residueCardinality K := Nat.card_pos

omit [MeasurableSpace K] [BorelSpace K] in
theorem residueCardinality_isPrimePow : IsPrimePow (residueCardinality K) := by
  let := Fintype.ofFinite 𝓀[K]
  simpa [residueCardinality, Nat.card_eq_fintype_card] using
    (FiniteField.isPrimePow_card (K := 𝓀[K]))

omit [MeasurableSpace K] [BorelSpace K] in
theorem residueCardinality_one_lt : 1 < residueCardinality K := by
  have h := (residueCardinality_isPrimePow K).two_le
  omega

theorem integers_measurableEmbedding :
    MeasurableEmbedding (fun x : 𝒪[K] => (x : K)) :=
  MeasurableEmbedding.subtype_coe (valuation K).isOpen_integer.measurableSet

/-- The pullback of ambient additive Haar measure to its compact valuation ring. -/
def integersHaar : MeasureTheory.Measure 𝒪[K] :=
  (additiveHaar K).comap (fun x : 𝒪[K] => (x : K))

instance integersHaar_isAddLeftInvariant : (integersHaar K).IsAddLeftInvariant :=
  MeasureTheory.Measure.IsAddLeftInvariant.comap (additiveHaar K)
    (f := (𝒪[K]).subtype.toAddMonoidHom) (integers_measurableEmbedding K)

theorem integersHaar_apply (s : Set 𝒪[K]) :
    integersHaar K s = additiveHaar K ((fun x : 𝒪[K] => (x : K)) '' s) :=
  (integers_measurableEmbedding K).comap_apply (additiveHaar K) s

theorem integersHaar_univ : integersHaar K Set.univ = 1 := by
  rw [integersHaar_apply]
  simpa using additiveHaar_integers K

instance integersHaar_isProbabilityMeasure : IsProbabilityMeasure (integersHaar K) :=
  ⟨integersHaar_univ K⟩

omit [MeasurableSpace K] [BorelSpace K] in
theorem maximalIdeal_ne_bot : 𝓂[K] ≠ ⊥ :=
  IsDiscreteValuationRing.not_a_field 𝒪[K]

omit [MeasurableSpace K] [BorelSpace K] in
/-- The finite additive index of the nth maximal-ideal power is q^n. -/
theorem maximalIdeal_pow_index (n : ℕ) :
    (𝓂[K] ^ n).toAddSubgroup.index = residueCardinality K ^ n := by
  exact cardQuot_pow_of_prime (maximalIdeal_ne_bot K)

instance maximalIdeal_pow_finiteIndex (n : ℕ) : (𝓂[K] ^ n).toAddSubgroup.FiniteIndex :=
  ⟨by rw [maximalIdeal_pow_index]; exact pow_ne_zero n (residueCardinality_pos K).ne'⟩

/-- Every nonnegative valuation ball has its expected volume, using actual Haar measure. -/
theorem integersHaar_maximalIdeal_pow (n : ℕ) :
    integersHaar K ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K]) = (residueCardinality K : ℝ≥0∞)⁻¹ ^ n := by
  have h := (𝓂[K] ^ n).toAddSubgroup.index_mul_measure
    (IsNoetherianRing.isClosed_ideal (𝓂[K] ^ n)).measurableSet (integersHaar K)
  rw [maximalIdeal_pow_index, integersHaar_univ, Nat.cast_pow] at h
  rw [← ENNReal.inv_pow, ← one_div]
  exact (ENNReal.eq_div_iff (pow_ne_zero n (by exact_mod_cast
    (residueCardinality_pos K).ne')) (by finiteness)).mpr h

/-- Ambient local-field volume of the image of the nth maximal-ideal power. -/
theorem additiveHaar_maximalIdeal_pow (n : ℕ) :
    additiveHaar K ((fun x : 𝒪[K] => (x : K)) '' ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K])) =
      (residueCardinality K : ℝ≥0∞)⁻¹ ^ n := by
  rw [← integersHaar_apply, integersHaar_maximalIdeal_pow]

omit [MeasurableSpace K] [BorelSpace K] in
/-- A chosen generator of the maximal ideal realizes its powers as actual valuation balls.
This includes zero, whose multiplicative valuation is zero (additive valuation infinity). -/
theorem mem_maximalIdeal_pow_iff_valuation_le (π : 𝒪[K])
    (hπ : 𝓂[K] = Ideal.span {π}) (n : ℕ) (x : 𝒪[K]) :
    x ∈ 𝓂[K] ^ n ↔ valuation K (x : K) ≤ valuation K (π : K) ^ n := by
  rw [hπ, Ideal.span_singleton_pow]
  change x ∈ (Ideal.span {π ^ n} : Set 𝒪[K]) ↔ _
  rw [Valuation.integer.coe_span_singleton_eq_setOfPred_le_v_coe]
  simp

/-- Nonnegative uniformizer balls in the ambient field have volume q^-n. -/
theorem additiveHaar_uniformizer_pow (π : 𝒪[K])
    (hπ : 𝓂[K] = Ideal.span {π}) (n : ℕ) :
    additiveHaar K ((fun u : 𝒪[K] => (π : K) ^ n * (u : K)) '' Set.univ) =
      (residueCardinality K : ℝ≥0∞)⁻¹ ^ n := by
  have heq : (fun u : 𝒪[K] => (π : K) ^ n * (u : K)) '' Set.univ =
      (fun x : 𝒪[K] => (x : K)) '' ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K]) := by
    rw [hπ, Ideal.span_singleton_pow]
    ext x
    constructor
    · rintro ⟨u, _, rfl⟩
      exact ⟨π ^ n * u, Ideal.mem_span_singleton.mpr ⟨u, rfl⟩, by simp⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton.mp hy
      exact ⟨u, Set.mem_univ _, by simp⟩
  rw [heq, additiveHaar_maximalIdeal_pow]

/-- Unit elements inside the valuation ring, kept as a measurable subset of the ring. -/
def integralUnits : Set 𝒪[K] := (𝓂[K] : Set 𝒪[K])ᶜ

omit [MeasurableSpace K] [BorelSpace K] in
theorem mem_integralUnits_iff (x : 𝒪[K]) : x ∈ integralUnits K ↔ IsUnit x := by
  simp [integralUnits, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]

theorem integralUnits_measurableSet : MeasurableSet (integralUnits K) :=
  (IsNoetherianRing.isClosed_ideal 𝓂[K]).measurableSet.compl

/-- Additive volume of the units, with precisely the manuscript's normalization. -/
theorem integersHaar_integralUnits :
    integersHaar K (integralUnits K) = 1 - (residueCardinality K : ℝ≥0∞)⁻¹ := by
  rw [integralUnits, measure_compl (IsNoetherianRing.isClosed_ideal 𝓂[K]).measurableSet
    (measure_ne_top _ _)]
  simpa using congrArg (fun x : ℝ≥0∞ => 1 - x) (integersHaar_maximalIdeal_pow K 1)

/-- The additive valuation shell of depth n in the valuation ring. -/
def integralShell (n : ℕ) : Set 𝒪[K] :=
  ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K]) \ ((𝓂[K] ^ (n + 1) : Ideal 𝒪[K]) : Set 𝒪[K])

theorem integersHaar_integralShell (n : ℕ) :
    integersHaar K (integralShell K n) =
      (residueCardinality K : ℝ≥0∞)⁻¹ ^ n -
        (residueCardinality K : ℝ≥0∞)⁻¹ ^ (n + 1) := by
  rw [integralShell, measure_sdiff
    (show ((𝓂[K] ^ (n + 1) : Ideal 𝒪[K]) : Set 𝒪[K]) ⊆ ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K]) from
      Ideal.pow_le_pow_right (Nat.le_succ n))
    (IsNoetherianRing.isClosed_ideal (𝓂[K] ^ (n + 1))).measurableSet.nullMeasurableSet
    (measure_ne_top _ _), integersHaar_maximalIdeal_pow, integersHaar_maximalIdeal_pow]

/-- The event that a unit differs from one by an element of the nth ideal power.
The definition itself is on the whole valuation ring; for positive n the event
is proved to consist of units. The point one is retained at every finite depth. -/
def collisionTail (n : ℕ) : Set 𝒪[K] :=
  (fun x : 𝒪[K] => x - 1) ⁻¹' ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K])

theorem collisionTail_measurableSet (n : ℕ) : MeasurableSet (collisionTail K n) :=
  (IsNoetherianRing.isClosed_ideal (𝓂[K] ^ n)).measurableSet.preimage
    (by fun_prop)

omit [MeasurableSpace K] [BorelSpace K] in
theorem collisionTail_succ_subset (n : ℕ) :
    collisionTail K (n + 1) ⊆ collisionTail K n :=
  Set.preimage_mono (Ideal.pow_le_pow_right (Nat.le_succ n))

omit [MeasurableSpace K] [BorelSpace K] in
theorem collisionTail_subset_units {n : ℕ} (hn : 0 < n) :
    collisionTail K n ⊆ integralUnits K := by
  intro x hx
  have hm : x - 1 ∈ 𝓂[K] :=
    (show 𝓂[K] ^ n ≤ 𝓂[K] from by simpa using
      (Ideal.pow_le_pow_right (I := 𝓂[K]) hn)) hx
  intro hx'
  have h1 := (𝓂[K]).sub_mem hx' hm
  simp only [sub_sub_cancel] at h1
  exact Ideal.one_notMem 𝓂[K] h1

theorem integersHaar_collisionTail (n : ℕ) :
    integersHaar K (collisionTail K n) = (residueCardinality K : ℝ≥0∞)⁻¹ ^ n := by
  simp only [collisionTail, sub_eq_add_neg, measure_preimage_add_right]
  exact integersHaar_maximalIdeal_pow K n

theorem integersHaar_real_maximalIdeal_pow (n : ℕ) :
    (integersHaar K).real ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K]) =
      (residueCardinality K : ℝ)⁻¹ ^ n := by
  simp [measureReal_def, integersHaar_maximalIdeal_pow]

/-- The ordinary real-valued shell volume in product form. -/
theorem integersHaar_real_integralShell (n : ℕ) :
    (integersHaar K).real (integralShell K n) =
      (1 - (residueCardinality K : ℝ)⁻¹) * (residueCardinality K : ℝ)⁻¹ ^ n := by
  rw [integralShell, measureReal_sdiff
    (show ((𝓂[K] ^ (n + 1) : Ideal 𝒪[K]) : Set 𝒪[K]) ⊆
      ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K]) from
      Ideal.pow_le_pow_right (Nat.le_succ n))
    (IsNoetherianRing.isClosed_ideal (𝓂[K] ^ (n + 1))).measurableSet,
    integersHaar_real_maximalIdeal_pow, integersHaar_real_maximalIdeal_pow, pow_succ]
  ring

theorem integersHaar_real_collisionTail (n : ℕ) :
    (integersHaar K).real (collisionTail K n) = (residueCardinality K : ℝ)⁻¹ ^ n := by
  simp [measureReal_def, integersHaar_collisionTail]

theorem integersHaar_real_integralUnits :
    (integersHaar K).real (integralUnits K) = 1 - (residueCardinality K : ℝ)⁻¹ := by
  rw [integralUnits, measureReal_compl
    (IsNoetherianRing.isClosed_ideal 𝓂[K]).measurableSet]
  simpa using congrArg (fun x : ℝ => 1 - x) (integersHaar_real_maximalIdeal_pow K 1)

/-- The conditional Haar mass of a measurable event, conditioned on being a unit.
This is a ratio of actual Haar measures, not a stipulated distribution. -/
def unitConditionalMass (s : Set 𝒪[K]) : ℝ :=
  (integersHaar K).real (s ∩ integralUnits K) /
    (integersHaar K).real (integralUnits K)

theorem unitConditionalMass_of_subset (s : Set 𝒪[K]) (hs : s ⊆ integralUnits K) :
    unitConditionalMass K s = (integersHaar K).real s /
      (1 - (residueCardinality K : ℝ)⁻¹) := by
  rw [unitConditionalMass, Set.inter_eq_self_of_subset_left hs,
    integersHaar_real_integralUnits]

/-- Cancellation tail law: depth at least n+1 has probability q^-n/(q-1). -/
theorem unitConditionalMass_collisionTail (n : ℕ) :
    unitConditionalMass K (collisionTail K (n + 1)) =
      (residueCardinality K : ℝ)⁻¹ ^ n / (residueCardinality K - 1) := by
  have hq : (1 : ℝ) < residueCardinality K := by
    exact_mod_cast residueCardinality_one_lt K
  rw [unitConditionalMass_of_subset _ _ (collisionTail_subset_units K (Nat.succ_pos n)),
    integersHaar_real_collisionTail, pow_succ]
  field_simp

/-- Cancellation mass at positive depth: the difference of successive actual tails. -/
theorem unitConditionalMass_collisionDepth (n : ℕ) :
    unitConditionalMass K (collisionTail K (n + 1) \ collisionTail K (n + 2)) =
      (residueCardinality K : ℝ)⁻¹ ^ (n + 1) := by
  have hq : (1 : ℝ) < residueCardinality K := by
    exact_mod_cast residueCardinality_one_lt K
  rw [unitConditionalMass_of_subset _ _
    (Set.Subset.trans Set.sdiff_subset (collisionTail_subset_units K (Nat.succ_pos n))),
    measureReal_sdiff (collisionTail_succ_subset K (n + 1))
      (collisionTail_measurableSet K (n + 2)),
    integersHaar_real_collisionTail, integersHaar_real_collisionTail]
  rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
  have hd : 1 - (residueCardinality K : ℝ)⁻¹ ≠ 0 := by
    have hq0 : (residueCardinality K : ℝ) ≠ 0 := (lt_trans zero_lt_one hq).ne'
    have heq : 1 - (residueCardinality K : ℝ)⁻¹ =
        (residueCardinality K - 1) / residueCardinality K := by field_simp
    rw [heq]
    exact div_ne_zero (sub_ne_zero.mpr hq.ne') hq0
  calc
    _ = (residueCardinality K : ℝ)⁻¹ ^ (n + 1) *
        (1 - (residueCardinality K : ℝ)⁻¹) /
        (1 - (residueCardinality K : ℝ)⁻¹) := by congr 1; ring
    _ = _ := mul_div_cancel_right₀ _ hd

/-- Cancellation mass at depth zero, inside the unit group. -/
theorem unitConditionalMass_collisionDepth_zero :
    unitConditionalMass K (integralUnits K \ collisionTail K 1) =
      (residueCardinality K - 2) / (residueCardinality K - 1) := by
  have hq : (1 : ℝ) < residueCardinality K := by
    exact_mod_cast residueCardinality_one_lt K
  rw [unitConditionalMass_of_subset _ _ Set.sdiff_subset,
    measureReal_sdiff (collisionTail_subset_units K (by omega))
      (collisionTail_measurableSet K 1),
    integersHaar_real_collisionTail, integersHaar_real_integralUnits, pow_one]
  field_simp
  ring

/-- The corresponding congruence ball centered at an arbitrary integral unit. -/
def unitCenteredTail (a : 𝒪[K]ˣ) (n : ℕ) : Set 𝒪[K] :=
  (fun x : 𝒪[K] => x - (a : 𝒪[K])) ⁻¹'
    ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K])

omit [MeasurableSpace K] [BorelSpace K] in
theorem unitCenteredTail_subset_units (a : 𝒪[K]ˣ) {n : ℕ} (hn : 0 < n) :
    unitCenteredTail K a n ⊆ integralUnits K := by
  intro x hx hx'
  have hm : x - (a : 𝒪[K]) ∈ 𝓂[K] :=
    (show 𝓂[K] ^ n ≤ 𝓂[K] from by simpa using
      (Ideal.pow_le_pow_right (I := 𝓂[K]) hn)) hx
  have ha : (a : 𝒪[K]) ∈ integralUnits K :=
    (mem_integralUnits_iff K _).mpr a.isUnit
  apply ha
  simpa using (𝓂[K]).sub_mem hx' hm

theorem integersHaar_unitCenteredTail (a : 𝒪[K]ˣ) (n : ℕ) :
    integersHaar K (unitCenteredTail K a n) = (residueCardinality K : ℝ≥0∞)⁻¹ ^ n := by
  simp only [unitCenteredTail, sub_eq_add_neg, measure_preimage_add_right]
  exact integersHaar_maximalIdeal_pow K n

theorem unitConditionalMass_unitCenteredTail (a : 𝒪[K]ˣ) (n : ℕ) :
    unitConditionalMass K (unitCenteredTail K a (n + 1)) =
      (residueCardinality K : ℝ)⁻¹ ^ n / (residueCardinality K - 1) := by
  have hq : (1 : ℝ) < residueCardinality K := by
    exact_mod_cast residueCardinality_one_lt K
  rw [unitConditionalMass_of_subset _ _
    (unitCenteredTail_subset_units K a (Nat.succ_pos n))]
  have hv : (integersHaar K).real (unitCenteredTail K a (n + 1)) =
      (residueCardinality K : ℝ)⁻¹ ^ (n + 1) := by
    simp [measureReal_def, integersHaar_unitCenteredTail]
  rw [hv, pow_succ]
  field_simp

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [MeasurableSpace K] [BorelSpace K] in
/-- For an integral unit denominator, the ratio's cancellation depth is the depth
of the difference. This is the key elementary step for a fixed unit numerator. -/
theorem valuation_ratio_sub_one (a x : 𝒪[K]) (hx : IsUnit x) :
    valuation K ((a : K) / (x : K) - 1) = valuation K ((x : K) - (a : K)) := by
  have hvx : valuation K (x : K) = 1 := by
    change valuation K ((algebraMap 𝒪[K] K) x) = 1
    exact (Valuation.integer.integers (valuation K)).isUnit_iff_valuation_eq_one.mp hx
  have hx0 : (x : K) ≠ 0 := by
    intro h
    simp [h] at hvx
  have heq : (a : K) / (x : K) - 1 = ((a : K) - (x : K)) / (x : K) := by
    field_simp
  rw [heq, map_div₀, hvx, div_one, (valuation K).map_sub_swap]

/-- Actual ratio-cancellation tails for a unit numerator and Haar-uniform integral
units. The valuation inequality includes the infinite-depth point, with no
incorrect finite value assigned to it. -/
theorem unitConditionalMass_ratio_tail (π : 𝒪[K]) (hπ : 𝓂[K] = Ideal.span {π})
    (a : 𝒪[K]ˣ) (n : ℕ) :
    unitConditionalMass K {x : 𝒪[K] | x ∈ integralUnits K ∧
      valuation K (((a : 𝒪[K]) : K) / (x : K) - 1) ≤
        valuation K (π : K) ^ (n + 1)} =
      (residueCardinality K : ℝ)⁻¹ ^ n / (residueCardinality K - 1) := by
  have heq : {x : 𝒪[K] | x ∈ integralUnits K ∧
      valuation K (((a : 𝒪[K]) : K) / (x : K) - 1) ≤
        valuation K (π : K) ^ (n + 1)} = unitCenteredTail K a (n + 1) := by
    ext x
    constructor
    · rintro ⟨hx, hv⟩
      rw [valuation_ratio_sub_one K _ _ ((mem_integralUnits_iff K _).mp hx)] at hv
      exact (mem_maximalIdeal_pow_iff_valuation_le K π hπ _ (x - a)).mpr hv
    · intro hx
      have hu := unitCenteredTail_subset_units K a (Nat.succ_pos n) hx
      refine ⟨hu, ?_⟩
      rw [valuation_ratio_sub_one K _ _ ((mem_integralUnits_iff K _).mp hu)]
      exact (mem_maximalIdeal_pow_iff_valuation_le K π hπ _ (x - a)).mp hx
  rw [heq, unitConditionalMass_unitCenteredTail]

/-- Ambient additive Haar has no atoms, by the separately proved local-field
non-isolation theorem; atomlessness is not an extra hypothesis. -/
instance additiveHaar_nullSingletonClass : NullSingletonClass (additiveHaar K) :=
  localField_haar_nullSingletonClass K (additiveHaar K)

/-- In particular every point of the valuation ring has zero pulled-back Haar mass. -/
theorem integersHaar_singleton (x : 𝒪[K]) : integersHaar K {x} = 0 := by
  rw [integersHaar_apply]
  simp

/-- The infinite-cancellation point has no extra probability mass. -/
theorem unitConditionalMass_singleton (x : 𝒪[K]) : unitConditionalMass K {x} = 0 := by
  have h : integersHaar K ({x} ∩ integralUnits K) = 0 :=
    measure_mono_null Set.inter_subset_left (integersHaar_singleton K x)
  simp [unitConditionalMass, measureReal_def, h]

end FourierJacobi.Measure



