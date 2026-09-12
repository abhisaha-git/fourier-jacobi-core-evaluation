import FourierJacobi.Analysis.I2Assembly
import Mathlib.Data.Fintype.Fin

/-! The full independent I2 integer/depth family, summed before rearrangement. -/

noncomputable section

namespace FourierJacobi.Analysis

open scoped Classical

set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
set_option linter.unusedVariables false

def i2Offset (ν : Fin 25) : Fin 50 := ⟨25 + ν.val, by omega⟩

theorem i2RegionTerm_eq_regionTerms (t d U V : ℂ) (ν : Fin 25) :
    i2RegionTerm ν t d U V = Algebra.regionTerms t d U V (i2Offset ν) := by
  fin_cases ν <;> rfl

def i2SpaceLatticeEquiv (ν : Fin 25) : (I2SpatialRow ν × ℕ) ≃
    {p : LatticeIndex // i2SpatialPredicate ν (p.1,p.2.1,p.2.2.1)} where
  toFun p := ⟨(p.1.val.1,p.1.val.2.1,p.1.val.2.2,p.2),p.1.property⟩
  invFun p := (⟨(p.val.1,p.val.2.1,p.val.2.2.1),p.property⟩,p.val.2.2.2)
  left_inv p := by
    rcases p with ⟨⟨⟨k,j,h⟩,hp⟩,c⟩
    rfl
  right_inv p := by
    rcases p with ⟨⟨k,j,h,c⟩,hp⟩
    rfl

def i2RowTerm (q t d U V T : ℂ) (ν : Fin 25) (p : LatticeIndex) : ℂ := by
  classical
  exact if i2SpatialPredicate ν (p.1,p.2.1,p.2.2.1) ∧ i2DepthPredicate ν p.2.2.2
    then masterTerm q t d U V T 2 p else 0

theorem hasSum_i2_rowTerm (q t d U V T : ℂ) (ν : Fin 25)
    (hq₀ : q ≠ 0) (hq₁ : q - 1 ≠ 0) (hq₂ : q - 2 ≠ 0) (hq : ‖q⁻¹‖ < 1)
    (hqt : q * t ^ 2 = 1) (hd : d ≠ 0) (h : GeometricRange t d U V T) :
    HasSum (i2RowTerm q t d U V T ν) (i2RegionTerm ν t d (T * U) (T * V)) := by
  classical
  let s : Set LatticeIndex := {p | i2SpatialPredicate ν (p.1,p.2.1,p.2.2.1)}
  let f : LatticeIndex → ℂ := fun p => if i2DepthPredicate ν p.2.2.2 then
    masterTerm q t d U V T 2 p else 0
  have hs : HasSum (fun p : s => f p.val) (i2RegionTerm ν t d (T * U) (T * V)) := by
    apply (i2SpaceLatticeEquiv ν).hasSum_iff.mp
    exact hasSum_i2_rowFamily q t d U V T ν hq₀ hq₁ hq₂ hq hqt hd h
  have hi := (hasSum_subtype_iff_indicator (s := s) (f := f)).mp hs
  convert hi using 1
  funext p
  simp only [i2RowTerm, Set.indicator, Set.mem_ofPred_eq, s, f]
  split_ifs <;> simp_all

theorem summable_norm_i2_rowTerm (q t d U V T : ℂ) (ν : Fin 25)
    (hq₀ : q ≠ 0) (hq₁ : q - 1 ≠ 0) (hq₂ : q - 2 ≠ 0) (hq : ‖q⁻¹‖ < 1)
    (h : GeometricRange t d U V T) :
    Summable (fun p => ‖i2RowTerm q t d U V T ν p‖) := by
  classical
  let s : Set LatticeIndex := {p | i2SpatialPredicate ν (p.1,p.2.1,p.2.2.1)}
  let f : LatticeIndex → ℂ := fun p => if i2DepthPredicate ν p.2.2.2 then
    masterTerm q t d U V T 2 p else 0
  have hs : Summable (fun p : s => ‖f p.val‖) := by
    apply (i2SpaceLatticeEquiv ν).summable_iff.mp
    exact summable_norm_i2_rowFamily q t d U V T ν hq₀ hq₁ hq₂ hq h
  have hi := (summable_subtype_iff_indicator (s := s) (f := fun p => ‖f p‖)).mp hs
  convert hi using 1
  funext p
  simp only [i2RowTerm, Set.indicator, Set.mem_ofPred_eq, s, f]
  split_ifs <;> simp_all


end FourierJacobi.Analysis
