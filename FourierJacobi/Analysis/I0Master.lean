import FourierJacobi.Analysis.I0Complete
import FourierJacobi.Analysis.MasterSeries
import FourierJacobi.Analysis.CoreParameters

noncomputable section
namespace FourierJacobi.Analysis
set_option maxHeartbeats 2000000

/-- Regrouping the independent lattice coordinates; both inverse laws are definitional. -/
def latticeDepthEquiv : ((ℤ × ℤ × ℤ) × ℕ) ≃ LatticeIndex where
  toFun p := (p.1.1, p.1.2.1, p.1.2.2, p.2)
  invFun p := ((p.1, p.2.1, p.2.2.1), p.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem summable_norm_i0_master (q t d U V T : ℂ) (h : GeometricRange t d U V T) :
    Summable (fun p : LatticeIndex => ‖masterTerm q t d U V T 0 p‖) := by
  apply latticeDepthEquiv.summable_iff.mp
  have hs := summable_norm_i0_full t d U V T h.t2 h.p h.n h.e h.f h.g
  have hd : Summable (fun c : ℕ => ‖if c = 0 then (1 : ℂ) else 0‖) := by
    simpa only [apply_ite, norm_one, norm_zero] using
      (hasSum_ite_eq (α := ℝ) (β := ℕ) 0 1).summable
  convert hs.mul_norm hd using 1
  funext p
  simp only [masterTerm_zero, latticeDepthEquiv, Equiv.coe_fn_mk]
  split_ifs with hp <;> simp [hp]

theorem hasSum_i0_master (q t d U V T : ℂ) (h : GeometricRange t d U V T) :
    HasSum (masterTerm q t d U V T 0)
      (∑ i : Fin 10, Algebra.regionTerms t d (T * U) (T * V) (i.castLE (by decide))) := by
  have hs := (summable_norm_i0_master q t d U V T h).of_norm
  have hs' : Summable (fun p : (ℤ × ℤ × ℤ) × ℕ =>
      masterTerm q t d U V T 0 (latticeDepthEquiv p)) :=
    latticeDepthEquiv.summable_iff.mpr hs
  apply latticeDepthEquiv.hasSum_iff.mp
  have he : (∑' p : (ℤ × ℤ × ℤ) × ℕ,
      masterTerm q t d U V T 0 (latticeDepthEquiv p)) =
        ∑ i : Fin 10, Algebra.regionTerms t d (T * U) (T * V) (i.castLE (by decide)) := by
    rw [hs'.tsum_prod]
    simp only [masterTerm_zero, latticeDepthEquiv, Equiv.coe_fn_mk,
      tsum_ite_eq, tsum_i0_full t d U V T h.t2 h.p h.n h.e h.f h.g]
  exact he ▸ hs'.hasSum

end FourierJacobi.Analysis
