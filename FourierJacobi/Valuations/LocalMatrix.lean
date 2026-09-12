import FourierJacobi.Valuations.MatrixBridge
import FourierJacobi.Measure.NullSets

/-!
# Actual local-field matrices on the almost-everywhere integer-table locus

This assembles the canonical valuation, Haar-null-set removal and intrinsic
matrix minima. No Cartan double-coset assertion is assumed. The conclusions
are exact minima of the actual entries and actual two-by-two minors.
-/

noncomputable section
open MeasureTheory Filter FourierJacobi.LocalMatrix

namespace FourierJacobi.Valuations

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K]
  (μ : MeasureTheory.Measure K) [μ.IsAddHaarMeasure]

/-- For a fixed nonzero a and a central coordinate of valuation -r, r≠0,
the actual matrix entry/minor minima are the integer-table minima almost
everywhere. The nonnegative collision depth is constructed from the actual
field ratio when the two terms have equal valuation, and is zero otherwise. -/
theorem localField_matrix_minima_ae (a z : K) (ha : a ≠ 0)
    (r : ℤ) (hr : r ≠ 0) (hz : localFieldValuation K z = ((-r : ℤ) : WithTop ℤ)) :
    ∀ᵐ p : K × K ∂μ.prod μ, ∃ k j h c : ℤ,
      0 ≤ c ∧ localFieldValuation K a = (k : WithTop ℤ) ∧
      localFieldValuation K p.1 = (j : WithTop ℤ) ∧
      localFieldValuation K p.2 = (h : WithTop ℤ) ∧
      (2 * h = j - r → localFieldValuation K (p.2 ^ 2 / (p.1 * z) - 1) =
        (c : WithTop ℤ)) ∧
      matrixMinimum (localFieldValuation K) (g a p.1 p.2 z) =
        (entryMinimum r k j h : WithTop ℤ) ∧
      matrixMinimum (localFieldValuation K) (secondCompound (g a p.1 p.2 z)) =
        (minorMinimum r k j h c : WithTop ℤ) := by
  let v := localFieldValuation K
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp ((localFieldValuation_ne_top K a).mpr ha)
  have hk' : v a = (k : WithTop ℤ) := hk.symm
  filter_upwards [Measure.localField_coordinates_determinant_ae K μ z] with p hp
  obtain ⟨j, hj⟩ := WithTop.ne_top_iff_exists.mp ((localFieldValuation_ne_top K p.1).mpr hp.1)
  obtain ⟨h, hh⟩ := WithTop.ne_top_iff_exists.mp ((localFieldValuation_ne_top K p.2).mpr hp.2.1)
  have hj' : v p.1 = (j : WithTop ℤ) := hj.symm
  have hh' : v p.2 = (h : WithTop ℤ) := hh.symm
  have hz0 : z ≠ 0 := nonzero_of_integer_valuation v z (-r) hz
  have hratio : p.2 ^ 2 / (p.1 * z) - 1 ≠ 0 := by
    intro he
    apply hp.2.2
    apply sub_eq_zero.mpr
    exact (div_eq_one_iff_eq (mul_ne_zero hp.1 hz0)).mp (sub_eq_zero.mp he)
  by_cases heq : 2 * h = j - r
  · obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.mp (v.ne_top_iff.mpr hratio)
    have hc' : v (p.2 ^ 2 / (p.1 * z) - 1) = (c : WithTop ℤ) := hc.symm
    have hn := actual_cancellation_depth_nonnegative v p.1 p.2 z r j h c
      hj' hh' hz heq hc'
    obtain ⟨he, hm⟩ := actual_minima_integer_nonzero v a p.1 p.2 z r k j h c hr
      hk' hj' hh' hz (fun _ => hc')
    exact ⟨k, j, h, c, hn, hk', hj', hh', (fun _ => hc'), he, hm⟩
  · obtain ⟨he, hm⟩ := actual_minima_integer_nonzero v a p.1 p.2 z r k j h 0 hr
      hk' hj' hh' hz (fun h => (heq h).elim)
    exact ⟨k, j, h, 0, le_rfl, hk', hj', hh', (fun h => (heq h).elim), he, hm⟩

end FourierJacobi.Valuations
