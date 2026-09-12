import FourierJacobi.Measure.ShellCollision
import FourierJacobi.Valuations.KernelIndices

/-! Actual product-Haar masses of the collision-depth shells for y²-xz. -/

noncomputable section

open MeasureTheory ValuativeRel FourierJacobi.Valuations

namespace FourierJacobi.Measure

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

local instance jointCollision_t2Space : T2Space K := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  let := isUniformAddGroup_of_addCommGroup (G := K)
  infer_instance

theorem shellCollisionDepth_mem_iff (a x : K) (n : ℤ) (c : ℕ) :
    x ∈ shellCollisionDepth K a n c ↔
      localFieldValuation K x = (n : WithTop ℤ) ∧
        localFieldValuation K (x - a) = ((n + (c : ℤ) : ℤ) : WithTop ℤ) := by
  simp only [shellCollisionDepth, shellCollisionTail, integerShell, integerBall,
    Set.mem_sdiff, Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq]
  by_cases hx : localFieldValuation K x = (n : WithTop ℤ)
  · simp only [hx, true_and]
    generalize localFieldValuation K (x - a) = v
    induction v using WithTop.recTopCoe with
    | top => simp only [le_top, not_true_eq_false, and_false, WithTop.top_ne_coe]
    | coe m =>
      simp only [WithTop.coe_inj, WithTop.coe_le_coe]
      omega
  · simp only [hx, false_and, not_false_eq_true, and_true]

theorem coe_add_eq_coe_add_iff (s n : ℤ) (v : WithTop ℤ) :
    (s : WithTop ℤ) + v = ((s + n : ℤ) : WithTop ℤ) ↔ v = (n : WithTop ℤ) := by
  induction v using WithTop.recTopCoe with
  | top => simp only [WithTop.add_top, WithTop.top_ne_coe]
  | coe m => simp only [← WithTop.coe_add, WithTop.coe_inj, add_right_inj]

theorem collision_center_valuation (y z : K) (h j s : ℤ)
    (hy : localFieldValuation K y = (h : WithTop ℤ))
    (hz : localFieldValuation K z = (s : WithTop ℤ)) (hlocus : 2 * h = j + s) :
    localFieldValuation K (y ^ 2 / z) = (j : WithTop ℤ) := by
  rw [(localFieldValuation K).map_div, (localFieldValuation K).map_pow, hy, hz, two_nsmul]
  change ((h + h - s : ℤ) : WithTop ℤ) = (j : WithTop ℤ)
  congr 1
  omega

theorem determinant_valuation_at_center (x y z : K) (s : ℤ)
    (hz : localFieldValuation K z = (s : WithTop ℤ)) :
    localFieldValuation K (y ^ 2 - x * z) =
      (s : WithTop ℤ) + localFieldValuation K (x - y ^ 2 / z) := by
  have hz0 : z ≠ 0 := (localFieldValuation_ne_top K z).mp (by rw [hz]; simp)
  have he : y ^ 2 - x * z = (-z) * (x - y ^ 2 / z) := by
    field_simp
    ring
  rw [he, (localFieldValuation K).map_mul, (localFieldValuation K).map_neg, hz]

/-- Coordinates are ordered (y,x), so the constant-center section is the
inner integral of the actual product Haar measure. -/
def jointCollisionDepth (z : K) (j h s : ℤ) (c : ℕ) : Set (K × K) :=
  {p | localFieldValuation K p.1 = (h : WithTop ℤ) ∧
    localFieldValuation K p.2 = (j : WithTop ℤ) ∧
    localFieldValuation K (p.1 ^ 2 - p.2 * z) =
      ((j + s + (c : ℤ) : ℤ) : WithTop ℤ)}

theorem jointCollisionDepth_section (y z : K) (j h s : ℤ) (c : ℕ)
    (hz : localFieldValuation K z = (s : WithTop ℤ)) :
    Prod.mk y ⁻¹' jointCollisionDepth K z j h s c =
      if localFieldValuation K y = (h : WithTop ℤ)
      then shellCollisionDepth K (y ^ 2 / z) j c else ∅ := by
  split_ifs with hy
  · ext x
    simp only [jointCollisionDepth, Set.mem_preimage, Set.mem_ofPred_eq, hy, true_and,
      shellCollisionDepth_mem_iff, determinant_valuation_at_center K x y z s hz]
    rw [show j + s + (c : ℤ) = s + (j + c) by omega, coe_add_eq_coe_add_iff]
  · ext x
    simp only [jointCollisionDepth, Set.mem_preimage, Set.mem_ofPred_eq, hy,
      false_and, Set.mem_empty_iff_false]

theorem collision_ratio_valuation_iff (x y z : K) (j s : ℤ) (c : ℕ)
    (hx : localFieldValuation K x = (j : WithTop ℤ))
    (hz : localFieldValuation K z = (s : WithTop ℤ)) :
    localFieldValuation K (y ^ 2 / (x * z) - 1) = ((c : ℤ) : WithTop ℤ) ↔
      localFieldValuation K (y ^ 2 - x * z) = ((j + s + (c : ℤ) : ℤ) : WithTop ℤ) := by
  have hx0 : x ≠ 0 := (localFieldValuation_ne_top K x).mp (by rw [hx]; simp)
  have hz0 : z ≠ 0 := (localFieldValuation_ne_top K z).mp (by rw [hz]; simp)
  have he : y ^ 2 / (x * z) - 1 = (y ^ 2 - x * z) / (x * z) := by
    field_simp
  rw [he, (localFieldValuation K).map_div, (localFieldValuation K).map_mul, hx, hz,
    ← WithTop.coe_add]
  generalize localFieldValuation K (y ^ 2 - x * z) = v
  induction v using WithTop.recTopCoe with
  | top =>
    change ((⊤ : WithTop ℤ) = ((c : ℤ) : WithTop ℤ)) ↔
      ((⊤ : WithTop ℤ) = ((j + s + (c : ℤ) : ℤ) : WithTop ℤ))
    simp only [WithTop.top_ne_coe]
  | coe d =>
    change ((d - (j + s) : ℤ) : WithTop ℤ) = ((c : ℤ) : WithTop ℤ) ↔
      (d : WithTop ℤ) = ((j + s + (c : ℤ) : ℤ) : WithTop ℤ)
    simp only [WithTop.coe_inj]
    omega

/-- The source ratio form, now in coordinates (x,y). -/
def sourceJointCollisionDepth (z : K) (j h : ℤ) (c : ℕ) : Set (K × K) :=
  {p | localFieldValuation K p.1 = (j : WithTop ℤ) ∧
    localFieldValuation K p.2 = (h : WithTop ℤ) ∧
    localFieldValuation K (p.2 ^ 2 / (p.1 * z) - 1) = ((c : ℤ) : WithTop ℤ)}

theorem sourceJointCollisionDepth_eq_swap (z : K) (j h s : ℤ) (c : ℕ)
    (hz : localFieldValuation K z = (s : WithTop ℤ)) :
    sourceJointCollisionDepth K z j h c =
      Prod.swap ⁻¹' jointCollisionDepth K z j h s c := by
  ext p
  simp only [sourceJointCollisionDepth, jointCollisionDepth, Set.mem_preimage,
    Set.mem_ofPred_eq, Prod.swap]
  by_cases hx : localFieldValuation K p.1 = (j : WithTop ℤ)
  · rw [collision_ratio_valuation_iff K p.1 p.2 z j s c hx hz]
    tauto
  · tauto

/-- The source's cancellation law, with no stipulated measure identity. -/
def shellCollisionProbability (c : ℕ) : ℝ :=
  if c = 0 then (residueCardinality K - 2) / (residueCardinality K - 1)
  else (residueCardinality K : ℝ) ^ (-(c : ℤ))

theorem shellCollisionProbability_nonneg (c : ℕ) : 0 ≤ shellCollisionProbability K c := by
  have hq : (2 : ℝ) ≤ residueCardinality K := by
    exact_mod_cast (show 2 ≤ residueCardinality K by have := residueCardinality_one_lt K; omega)
  unfold shellCollisionProbability
  split_ifs
  · exact div_nonneg (sub_nonneg.mpr hq) (by linarith)
  · exact zpow_nonneg (by linarith) _

variable [MeasurableSpace K] [BorelSpace K]

local instance jointCollision_secondCountable : SecondCountableTopology K :=
  FourierJacobi.Valuations.kernelField_secondCountable K

local instance jointCollision_additiveHaar_sigmaFinite : SigmaFinite (additiveHaar K) := by
  unfold additiveHaar
  infer_instance

theorem shellConditionalMass_collisionDepth (a : K) (n : ℤ) (c : ℕ)
    (ha : localFieldValuation K a = (n : WithTop ℤ)) :
    shellConditionalMass K n (shellCollisionDepth K a n c) = shellCollisionProbability K c := by
  by_cases hc : c = 0
  · subst c
    exact shellConditionalMass_collisionDepth_zero K a n ha
  · simpa only [shellCollisionProbability, if_neg hc] using
      shellConditionalMass_collisionDepth_pos K a n c ha (Nat.pos_of_ne_zero hc)

theorem additiveHaar_real_shellCollisionDepth (a : K) (n : ℤ) (c : ℕ)
    (ha : localFieldValuation K a = (n : WithTop ℤ)) :
    (additiveHaar K).real (shellCollisionDepth K a n c) =
      shellCollisionProbability K c * (additiveHaar K).real (integerShell K n) := by
  have he := shellConditionalMass_collisionDepth K a n c ha
  rw [shellConditionalMass,
    Set.inter_eq_self_of_subset_left (shellCollisionDepth_subset K a n c)] at he
  exact (div_eq_iff (additiveHaar_real_integerShell_pos K n).ne').mp he

theorem additiveHaar_shellCollisionDepth (a : K) (n : ℤ) (c : ℕ)
    (ha : localFieldValuation K a = (n : WithTop ℤ)) :
    additiveHaar K (shellCollisionDepth K a n c) =
      ENNReal.ofReal (shellCollisionProbability K c *
        (additiveHaar K).real (integerShell K n)) := by
  rw [← additiveHaar_real_shellCollisionDepth K a n c ha]
  exact (ENNReal.ofReal_toReal (measure_ne_top_of_subset
    (shellCollisionDepth_subset K a n c) (additiveHaar_integerShell_ne_top K n))).symm

theorem jointCollisionDepth_measurableSet (z : K) (j h s : ℤ) (c : ℕ) :
    MeasurableSet (jointCollisionDepth K z j h s c) := by
  have h1 := (integerShell_measurableSet K h).preimage
    (show Measurable (fun p : K × K => p.1) from measurable_fst)
  have h2 := (integerShell_measurableSet K j).preimage
    (show Measurable (fun p : K × K => p.2) from measurable_snd)
  have h3 := (integerShell_measurableSet K (j + s + (c : ℤ))).preimage
    (show Measurable (fun p : K × K => p.1 ^ 2 - p.2 * z) by fun_prop)
  exact h1.inter (h2.inter h3)

/-- The actual two-variable collision shell mass, using product Haar and
the determinant polynomial. -/
theorem additiveHaar_prod_jointCollisionDepth (z : K) (j h s : ℤ) (c : ℕ)
    (hz : localFieldValuation K z = (s : WithTop ℤ)) (hlocus : 2 * h = j + s) :
    ((additiveHaar K).prod (additiveHaar K)) (jointCollisionDepth K z j h s c) =
      ENNReal.ofReal (shellCollisionProbability K c *
        (additiveHaar K).real (integerShell K j)) * additiveHaar K (integerShell K h) := by
  rw [Measure.prod_apply (jointCollisionDepth_measurableSet K z j h s c)]
  have he : (fun y => additiveHaar K (Prod.mk y ⁻¹' jointCollisionDepth K z j h s c)) =
      (integerShell K h).indicator (fun _ => ENNReal.ofReal (shellCollisionProbability K c *
        (additiveHaar K).real (integerShell K j))) := by
    funext y
    rw [jointCollisionDepth_section K y z j h s c hz]
    by_cases hy : localFieldValuation K y = (h : WithTop ℤ)
    · rw [if_pos hy, Set.indicator_of_mem (show y ∈ integerShell K h from hy),
        additiveHaar_shellCollisionDepth K (y ^ 2 / z) j c
          (collision_center_valuation K y z h j s hy hz hlocus)]
    · rw [if_neg hy, Set.indicator_of_notMem (show y ∉ integerShell K h from hy), measure_empty]
  rw [he, lintegral_indicator_const (integerShell_measurableSet K h)]

theorem additiveHaar_real_prod_jointCollisionDepth (z : K) (j h s : ℤ) (c : ℕ)
    (hz : localFieldValuation K z = (s : WithTop ℤ)) (hlocus : 2 * h = j + s) :
    ((additiveHaar K).prod (additiveHaar K)).real (jointCollisionDepth K z j h s c) =
      shellCollisionProbability K c *
        ((1 - (residueCardinality K : ℝ)⁻¹) ^ 2 *
          ((residueCardinality K : ℝ) ^ (-j) * (residueCardinality K : ℝ) ^ (-h))) := by
  rw [Measure.real, additiveHaar_prod_jointCollisionDepth K z j h s c hz hlocus,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal
      (mul_nonneg (shellCollisionProbability_nonneg K c) measureReal_nonneg)]
  change shellCollisionProbability K c * (additiveHaar K).real (integerShell K j) *
    (additiveHaar K).real (integerShell K h) = _
  rw [additiveHaar_real_integerShell, additiveHaar_real_integerShell]
  ring

theorem sourceJointCollisionDepth_measurableSet (z : K) (j h s : ℤ) (c : ℕ)
    (hz : localFieldValuation K z = (s : WithTop ℤ)) :
    MeasurableSet (sourceJointCollisionDepth K z j h c) := by
  rw [sourceJointCollisionDepth_eq_swap K z j h s c hz]
  exact (jointCollisionDepth_measurableSet K z j h s c).preimage measurable_swap

theorem additiveHaar_prod_sourceJointCollisionDepth (z : K) (j h s : ℤ) (c : ℕ)
    (hz : localFieldValuation K z = (s : WithTop ℤ)) (hlocus : 2 * h = j + s) :
    ((additiveHaar K).prod (additiveHaar K)) (sourceJointCollisionDepth K z j h c) =
      ENNReal.ofReal (shellCollisionProbability K c *
        (additiveHaar K).real (integerShell K j)) * additiveHaar K (integerShell K h) := by
  rw [sourceJointCollisionDepth_eq_swap K z j h s c hz,
    ← Measure.map_apply measurable_swap (jointCollisionDepth_measurableSet K z j h s c),
    Measure.prod_swap]
  exact additiveHaar_prod_jointCollisionDepth K z j h s c hz hlocus

/-- The exact source collision ratio has joint mass S² q^(-j-h) p_c.
The factors q^(-j) and q^(-h) retain integer powers throughout. -/
theorem additiveHaar_real_prod_sourceJointCollisionDepth (z : K) (j h s : ℤ) (c : ℕ)
    (hz : localFieldValuation K z = (s : WithTop ℤ)) (hlocus : 2 * h = j + s) :
    ((additiveHaar K).prod (additiveHaar K)).real (sourceJointCollisionDepth K z j h c) =
      (1 - (residueCardinality K : ℝ)⁻¹) ^ 2 *
        ((residueCardinality K : ℝ) ^ (-j) * (residueCardinality K : ℝ) ^ (-h)) *
          shellCollisionProbability K c := by
  rw [Measure.real, sourceJointCollisionDepth_eq_swap K z j h s c hz,
    ← Measure.map_apply measurable_swap (jointCollisionDepth_measurableSet K z j h s c),
    Measure.prod_swap]
  change ((additiveHaar K).prod (additiveHaar K)).real (jointCollisionDepth K z j h s c) = _
  rw [additiveHaar_real_prod_jointCollisionDepth K z j h s c hz hlocus]
  ring

end FourierJacobi.Measure
