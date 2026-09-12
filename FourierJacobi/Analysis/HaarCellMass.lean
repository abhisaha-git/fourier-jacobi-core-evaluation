import FourierJacobi.Analysis.HaarLatticePartition
import FourierJacobi.Measure.JointCollision

/-! Actual finite Haar mass of every independently defined master lattice cell. -/

noncomputable section

open MeasureTheory

namespace FourierJacobi.Analysis

open FourierJacobi.Measure FourierJacobi.Valuations

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

theorem haarLatticeCell_eq_off (r : ℤ) (z : K) (k j h : ℤ) (c : ℕ)
    (he : r = 0 ∨ 2 * h ≠ j - r) :
    haarLatticeCell K r z (k,j,h,c) =
      if c = 0 then unitValuationShell K k ×ˢ (integerShell K j ×ˢ integerShell K h)
      else ∅ := by
  ext p
  simp only [haarLatticeCell, unitValuationShell, integerShell,
    Set.mem_ofPred_eq, he, if_true]
  split_ifs <;> simp_all

theorem haarLatticeCell_eq_collision (r : ℤ) (z : K) (k j h : ℤ) (c : ℕ)
    (he : ¬(r = 0 ∨ 2 * h ≠ j - r)) :
    haarLatticeCell K r z (k,j,h,c) =
      unitValuationShell K k ×ˢ sourceJointCollisionDepth K z j h c := by
  ext p
  simp only [haarLatticeCell, unitValuationShell, sourceJointCollisionDepth,
    Set.mem_ofPred_eq, Set.mem_prod, he, if_false]

theorem haarLatticeCell_subset_product (r : ℤ) (z : K) (k j h : ℤ) (c : ℕ) :
    haarLatticeCell K r z (k,j,h,c) ⊆
      unitValuationShell K k ×ˢ (integerShell K j ×ˢ integerShell K h) := by
  intro p hp
  exact ⟨hp.1, hp.2.1, hp.2.2.1⟩

/-- A real-valued transcription of the actual collision weight. -/
def haarCellWeight (r j h : ℤ) (c : ℕ) : ℝ :=
  if r = 0 ∨ 2 * h ≠ j - r then (if c = 0 then 1 else 0)
  else shellCollisionProbability K c

theorem haarCellWeight_coe (r j h : ℤ) (c : ℕ) :
    (haarCellWeight K r j h c : ℂ) = collisionWeight (residueCardinality K : ℂ) r j h c := by
  unfold haarCellWeight collisionWeight shellCollisionProbability collisionProbability
  split_ifs <;> push_cast <;> rfl

variable [MeasurableSpace K] [BorelSpace K]

local instance haarCellMass_t2Space : T2Space K := kernelField_t2Space K
local instance haarCellMass_secondCountable : SecondCountableTopology K := kernelField_secondCountable K
local instance haarCellMass_unitsBorel : BorelSpace Kˣ := coreUnits_borelSpace K
local instance haarCellMass_additiveSigmaFinite : SigmaFinite (additiveHaar K) := by
  unfold additiveHaar
  infer_instance

/-- The actual source-normalized product measure on the three field coordinates. -/
def paperCoreMeasure : MeasureTheory.Measure (HaarPoint K) :=
  (paperMultiplicativeHaar K).prod ((additiveHaar K).prod (additiveHaar K))

theorem haarLatticeCell_measure_ne_top (r : ℤ) (z : K) (i : LatticeIndex) :
    paperCoreMeasure K (haarLatticeCell K r z i) ≠ ⊤ := by
  rcases i with ⟨k,j,h,c⟩
  apply measure_ne_top_of_subset (haarLatticeCell_subset_product K r z k j h c)
  simp only [paperCoreMeasure, Measure.prod_prod, paperMultiplicativeHaar_unitValuationShell]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.mul_ne_top (additiveHaar_integerShell_ne_top K j) (additiveHaar_integerShell_ne_top K h))

/-- Every actual lattice cell has the expected source-normalized real volume. -/
theorem haarLatticeCell_real_mass (r : ℤ) (z : K) (hz : CentralRepresentative K r z)
    (i : LatticeIndex) :
    (paperCoreMeasure K).real (haarLatticeCell K r z i) =
      (1 - (residueCardinality K : ℝ)⁻¹) ^ 3 *
        ((residueCardinality K : ℝ) ^ (-i.2.1) *
          (residueCardinality K : ℝ) ^ (-i.2.2.1)) *
            haarCellWeight K r i.2.1 i.2.2.1 i.2.2.2 := by
  rcases i with ⟨k,j,h,c⟩
  by_cases he : r = 0 ∨ 2 * h ≠ j - r
  · rw [haarLatticeCell_eq_off K r z k j h c he]
    by_cases hc : c = 0
    · rw [if_pos hc]
      simp only [paperCoreMeasure, measureReal_prod_prod, paperMultiplicativeHaar_real_unitValuationShell,
        additiveHaar_real_integerShell, haarCellWeight, he, if_true, hc, mul_one]
      ring
    · simp only [measureReal_empty, haarCellWeight, he, if_true, hc,
        if_false, mul_zero]
  · have hr : r ≠ 0 := fun hr => he (Or.inl hr)
    have hlocus : 2 * h = j + (-r) := by
      have hh : 2 * h = j - r := Classical.not_not.mp (fun hh => he (Or.inr hh))
      omega
    have hzr : localFieldValuation K z = ((-r : ℤ) : WithTop ℤ) := by
      rcases hz with ⟨hr',_⟩ | ⟨_,hz'⟩
      · exact (hr hr').elim
      · exact hz'
    rw [haarLatticeCell_eq_collision K r z k j h c he]
    simp only [paperCoreMeasure, measureReal_prod_prod, paperMultiplicativeHaar_real_unitValuationShell]
    rw [additiveHaar_real_prod_sourceJointCollisionDepth K z j h (-r) c hzr hlocus]
    simp only [haarCellWeight, he, if_false]
    ring

theorem haarLatticeCell_mass (r : ℤ) (z : K) (hz : CentralRepresentative K r z)
    (i : LatticeIndex) :
    paperCoreMeasure K (haarLatticeCell K r z i) =
      ENNReal.ofReal ((1 - (residueCardinality K : ℝ)⁻¹) ^ 3 *
        ((residueCardinality K : ℝ) ^ (-i.2.1) *
          (residueCardinality K : ℝ) ^ (-i.2.2.1)) *
            haarCellWeight K r i.2.1 i.2.2.1 i.2.2.2) := by
  rw [← haarLatticeCell_real_mass K r z hz i]
  exact (ENNReal.ofReal_toReal (haarLatticeCell_measure_ne_top K r z i)).symm

/-- The convenient complex-coercion interface matches the actual measure
with the independently defined master family's collision weight. -/
theorem haarLatticeCell_complex_mass (r : ℤ) (z : K) (hz : CentralRepresentative K r z)
    (i : LatticeIndex) :
    (((paperCoreMeasure K).real (haarLatticeCell K r z i) : ℝ) : ℂ) =
      (1 - (residueCardinality K : ℂ)⁻¹) ^ 3 *
        ((residueCardinality K : ℂ) ^ (-i.2.1) *
          (residueCardinality K : ℂ) ^ (-i.2.2.1)) *
            collisionWeight (residueCardinality K : ℂ) r i.2.1 i.2.2.1 i.2.2.2 := by
  rw [haarLatticeCell_real_mass K r z hz i]
  push_cast
  rw [haarCellWeight_coe]

end FourierJacobi.Analysis
