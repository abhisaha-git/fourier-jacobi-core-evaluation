import FourierJacobi.Measure.IntegerShells

/-!
# Actual cancellation-depth distribution in every additive valuation shell

The center and the integration variable lie in the same fixed integer
valuation shell. Every tail, exact-depth event, and conditional mass is
defined from the actual local-field valuation and actual additive Haar.
-/

noncomputable section

open MeasureTheory ValuativeRel FourierJacobi.Valuations

namespace FourierJacobi.Measure

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

local instance shellCollision_t2Space : T2Space K := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  let := isUniformAddGroup_of_addCommGroup (G := K)
  infer_instance

/-- Depth at least c, in the prescribed shell; the exact-cancellation point
x=a is retained at every finite depth. -/
def shellCollisionTail (a : K) (n : ℤ) (c : ℕ) : Set K :=
  integerShell K n ∩ ((fun x : K => x - a) ⁻¹' integerBall K (n + c))

/-- Exact finite cancellation depth. -/
def shellCollisionDepth (a : K) (n : ℤ) (c : ℕ) : Set K :=
  shellCollisionTail K a n c \ shellCollisionTail K a n (c + 1)

theorem shellCollisionTail_zero_eq (a : K) (n : ℤ)
    (ha : localFieldValuation K a = (n : WithTop ℤ)) :
    shellCollisionTail K a n 0 = integerShell K n := by
  apply Set.inter_eq_self_of_subset_left
  intro x hx
  change (n + (0 : ℕ) : ℤ) ≤ localFieldValuation K (x - a)
  simp only [Nat.cast_zero, add_zero]
  exact (localFieldValuation K).map_le_sub (le_of_eq hx.symm) (le_of_eq ha.symm)

theorem shellCollisionTail_eq_preimage (a : K) (n : ℤ) (c : ℕ)
    (ha : localFieldValuation K a = (n : WithTop ℤ)) (hc : 0 < c) :
    shellCollisionTail K a n c =
      (fun x : K => x - a) ⁻¹' integerBall K (n + c) := by
  apply Set.inter_eq_self_of_subset_right
  intro x hx
  change localFieldValuation K x = (n : WithTop ℤ)
  have hlt : localFieldValuation K a < localFieldValuation K (x - a) := by
    rw [ha]
    exact lt_of_lt_of_le (by exact_mod_cast (show n < n + (c : ℤ) by omega)) hx
  simpa only [sub_add_cancel, ha] using
    (localFieldValuation K).map_add_eq_of_lt_right hlt

theorem shellCollisionTail_succ_subset (a : K) (n : ℤ) (c : ℕ) :
    shellCollisionTail K a n (c + 1) ⊆ shellCollisionTail K a n c := by
  intro x hx
  refine ⟨hx.1, ?_⟩
  change ((n + (c : ℤ) : ℤ) : WithTop ℤ) ≤ localFieldValuation K (x - a)
  have hx' : ((n + ((c + 1 : ℕ) : ℤ) : ℤ) : WithTop ℤ) ≤
      localFieldValuation K (x - a) := hx.2
  apply le_trans ?_ hx'
  exact_mod_cast (show n + (c : ℤ) ≤ n + ((c + 1 : ℕ) : ℤ) by omega)

theorem shellCollisionDepth_subset (a : K) (n : ℤ) (c : ℕ) :
    shellCollisionDepth K a n c ⊆ integerShell K n :=
  Set.Subset.trans Set.sdiff_subset Set.inter_subset_left

theorem shellCollisionDepth_eq_preimage (a : K) (n : ℤ) (c : ℕ)
    (ha : localFieldValuation K a = (n : WithTop ℤ)) (hc : 0 < c) :
    shellCollisionDepth K a n c =
      (fun x : K => x - a) ⁻¹' integerShell K (n + c) := by
  rw [shellCollisionDepth, shellCollisionTail_eq_preimage K a n c ha hc,
    shellCollisionTail_eq_preimage K a n (c + 1) ha (Nat.succ_pos c),
    ← Set.preimage_sdiff, integerShell_eq_sdiff]
  simp only [Nat.cast_add, Nat.cast_one, add_assoc]

variable [MeasurableSpace K] [BorelSpace K]

theorem shellCollisionTail_measurableSet (a : K) (n : ℤ) (c : ℕ) :
    MeasurableSet (shellCollisionTail K a n c) :=
  (integerShell_measurableSet K n).inter
    ((integerBall_measurableSet K (n + c)).preimage (by fun_prop))

theorem shellCollisionDepth_measurableSet (a : K) (n : ℤ) (c : ℕ) :
    MeasurableSet (shellCollisionDepth K a n c) :=
  (shellCollisionTail_measurableSet K a n c).diff
    (shellCollisionTail_measurableSet K a n (c + 1))

theorem additiveHaar_real_shellCollisionTail (a : K) (n : ℤ) (c : ℕ)
    (ha : localFieldValuation K a = (n : WithTop ℤ)) (hc : 0 < c) :
    (additiveHaar K).real (shellCollisionTail K a n c) =
      (residueCardinality K : ℝ) ^ (-(n + (c : ℤ))) := by
  rw [shellCollisionTail_eq_preimage K a n c ha hc]
  simpa only [Measure.real, sub_eq_add_neg, measure_preimage_add_right] using
    additiveHaar_real_integerBall K (n + c)

theorem additiveHaar_real_shellCollisionDepth_pos (a : K) (n : ℤ) (c : ℕ)
    (ha : localFieldValuation K a = (n : WithTop ℤ)) (hc : 0 < c) :
    (additiveHaar K).real (shellCollisionDepth K a n c) =
      (1 - (residueCardinality K : ℝ)⁻¹) *
        (residueCardinality K : ℝ) ^ (-(n + (c : ℤ))) := by
  rw [shellCollisionDepth_eq_preimage K a n c ha hc]
  simpa only [Measure.real, sub_eq_add_neg, measure_preimage_add_right] using
    additiveHaar_real_integerShell K (n + c)

/-- Actual conditional additive Haar mass in the integer shell. The divisor
is separately proved finite and strictly positive. -/
def shellConditionalMass (n : ℤ) (s : Set K) : ℝ :=
  (additiveHaar K).real (s ∩ integerShell K n) /
    (additiveHaar K).real (integerShell K n)

theorem shellConditionalMass_of_subset (n : ℤ) (s : Set K)
    (hs : s ⊆ integerShell K n) :
    shellConditionalMass K n s =
      (additiveHaar K).real s /
        ((1 - (residueCardinality K : ℝ)⁻¹) * (residueCardinality K : ℝ) ^ (-n)) := by
  rw [shellConditionalMass, Set.inter_eq_self_of_subset_left hs, additiveHaar_real_integerShell]

/-- Every positive exact cancellation depth has the paper's mass q^(-c),
on every actual integer shell and for every fixed center in that shell. -/
theorem shellConditionalMass_collisionDepth_pos (a : K) (n : ℤ) (c : ℕ)
    (ha : localFieldValuation K a = (n : WithTop ℤ)) (hc : 0 < c) :
    shellConditionalMass K n (shellCollisionDepth K a n c) =
      (residueCardinality K : ℝ) ^ (-(c : ℤ)) := by
  have hq : (1 : ℝ) < residueCardinality K := by exact_mod_cast residueCardinality_one_lt K
  have hq0 : (0 : ℝ) < residueCardinality K := lt_trans zero_lt_one hq
  have hs : 1 - (residueCardinality K : ℝ)⁻¹ ≠ 0 :=
    (sub_pos.mpr ((inv_lt_one₀ hq0).mpr hq)).ne'
  rw [shellConditionalMass_of_subset K n _ (shellCollisionDepth_subset K a n c),
    additiveHaar_real_shellCollisionDepth_pos K a n c ha hc,
    neg_add, zpow_add₀ hq0.ne']
  field_simp [sub_ne_zero.mpr hq.ne']

/-- The depth-zero collision mass is (q-2)/(q-1), including all integer shells. -/
theorem shellConditionalMass_collisionDepth_zero (a : K) (n : ℤ)
    (ha : localFieldValuation K a = (n : WithTop ℤ)) :
    shellConditionalMass K n (shellCollisionDepth K a n 0) =
      (residueCardinality K - 2) / (residueCardinality K - 1) := by
  have hq : (1 : ℝ) < residueCardinality K := by exact_mod_cast residueCardinality_one_lt K
  have hq0 : (0 : ℝ) < residueCardinality K := lt_trans zero_lt_one hq
  have hs : 1 - (residueCardinality K : ℝ)⁻¹ ≠ 0 :=
    (sub_pos.mpr ((inv_lt_one₀ hq0).mpr hq)).ne'
  rw [shellConditionalMass_of_subset K n _ (shellCollisionDepth_subset K a n 0),
    shellCollisionDepth,
    measureReal_sdiff (shellCollisionTail_succ_subset K a n 0)
      (shellCollisionTail_measurableSet K a n 1)
      (measure_ne_top_of_subset Set.inter_subset_left (additiveHaar_integerShell_ne_top K n)),
    shellCollisionTail_zero_eq K a n ha, additiveHaar_real_integerShell,
    additiveHaar_real_shellCollisionTail K a n 1 ha (by decide)]
  rw [Nat.cast_one, show -(n + 1) = -n + -1 by omega, zpow_add₀ hq0.ne', zpow_neg_one]
  field_simp
  ring

theorem shellConditionalMass_singleton (a : K) (n : ℤ) :
    shellConditionalMass K n {a} = 0 := by
  have h : additiveHaar K ({a} ∩ integerShell K n) = 0 :=
    measure_mono_null Set.inter_subset_left (measure_singleton a)
  simp only [shellConditionalMass, Measure.real, h, ENNReal.toReal_zero, zero_div]

end FourierJacobi.Measure
