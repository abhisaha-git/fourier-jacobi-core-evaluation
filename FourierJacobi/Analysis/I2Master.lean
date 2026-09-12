import FourierJacobi.Analysis.I2Ambient
import FourierJacobi.Analysis.I2Partition

noncomputable section

namespace FourierJacobi.Analysis

open scoped Classical

set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
set_option linter.unusedVariables false

theorem i2_partition_sum {M : Type*} [AddCommMonoid M] (k j h : ℤ) (c : ℕ) (v : M) :
    (∑ ν : Fin 25, if i2SpatialPredicate ν (k,j,h) ∧ i2DepthPredicate ν c then v else 0) = v := by
  classical
  obtain ⟨ν,hν,huniq⟩ := i2_rows_partition k j h c
  rw [Finset.sum_eq_single ν]
  · simp [hν]
  · intro μ hμ hμν
    have hn : ¬(i2SpatialPredicate μ (k,j,h) ∧ i2DepthPredicate μ c) := by
      intro hm
      exact hμν (huniq μ hm)
    simp [hn]
  · intro hνnot
    exact False.elim (hνnot (Finset.mem_univ ν))

theorem i2RowTerm_sum (q t d U V T : ℂ) (p : LatticeIndex) :
    (∑ ν : Fin 25, i2RowTerm q t d U V T ν p) = masterTerm q t d U V T 2 p := by
  classical
  exact i2_partition_sum p.1 p.2.1 p.2.2.1 p.2.2.2 (masterTerm q t d U V T 2 p)

theorem i2RowTerm_norm_sum (q t d U V T : ℂ) (p : LatticeIndex) :
    (∑ ν : Fin 25, ‖i2RowTerm q t d U V T ν p‖) = ‖masterTerm q t d U V T 2 p‖ := by
  classical
  simpa only [i2RowTerm, apply_ite, norm_zero] using
    i2_partition_sum p.1 p.2.1 p.2.2.1 p.2.2.2 ‖masterTerm q t d U V T 2 p‖

theorem i2_inv_norm_bound (q t : ℂ) (ht : t ≠ 0) (hqt : q * t ^ 2 = 1)
    (h : ‖t ^ 2‖ < 1) : ‖q⁻¹‖ < 1 := by
  have he : q = (t ^ 2)⁻¹ := by
    calc
      q = q * (t ^ 2 * (t ^ 2)⁻¹) := by rw [mul_inv_cancel₀ (pow_ne_zero 2 ht),mul_one]
      _ = (t ^ 2)⁻¹ := by rw [← mul_assoc,hqt,one_mul]
  simpa [he] using h

/-- Absolute summability of the actual original four-coordinate I2 family. -/
theorem summable_norm_i2_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hq₀ : q ≠ 0) (hq₁ : q - 1 ≠ 0) (hq₂ : q - 2 ≠ 0)
    (hqt : q * t ^ 2 = 1) (h : GeometricRange t d U V T) :
    Summable (fun p : LatticeIndex => ‖masterTerm q t d U V T 2 p‖) := by
  have hq := i2_inv_norm_bound q t ht hqt h.t2
  have hs := summable_sum (s := Finset.univ) (fun ν _ =>
    summable_norm_i2_rowTerm q t d U V T ν hq₀ hq₁ hq₂ hq h)
  simpa only [i2RowTerm_norm_sum] using hs

/-- All twenty-five actual I2 lattice rows, with cancellation depths restored once. -/
theorem hasSum_i2_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hq₀ : q ≠ 0) (hq₁ : q - 1 ≠ 0) (hq₂ : q - 2 ≠ 0)
    (hqt : q * t ^ 2 = 1) (h : GeometricRange t d U V T) :
    HasSum (masterTerm q t d U V T 2)
      (∑ ν : Fin 25, Algebra.regionTerms t d (T * U) (T * V) (i2Offset ν)) := by
  have hq := i2_inv_norm_bound q t ht hqt h.t2
  have hs := hasSum_sum (s := Finset.univ) (fun ν _ =>
    hasSum_i2_rowTerm q t d U V T ν hq₀ hq₁ hq₂ hq hqt hd h)
  simpa only [i2RowTerm_sum, i2RegionTerm_eq_regionTerms] using hs

end FourierJacobi.Analysis
