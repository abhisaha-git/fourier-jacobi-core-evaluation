import FourierJacobi.Analysis.MasterSeries
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic.FunProp

noncomputable section
namespace FourierJacobi.Analysis
open FourierJacobi.Valuations Filter
open scoped Topology

def shellHeight (r : ℤ) (p : ℤ × ℤ × ℤ) : ℕ :=
  (-entryMinimum r p.1 p.2.1 p.2.2).toNat

theorem shellHeight_eq (r : ℤ) (p : ℤ × ℤ × ℤ) (c : ℕ) :
    shellHeight r p = ((cartanIndices r p.1 p.2.1 p.2.2 c).1 / 2).toNat +
      (cartanIndices r p.1 p.2.1 p.2.2 c).2.toNat := by
  have hh := shell_height_eq r p.1 p.2.1 p.2.2 c
  have hn := shell_exponents_nonnegative r p.1 p.2.1 p.2.2 c
  unfold shellHeight
  omega

theorem shellMonomial_damping (t d U V T : ℂ) (r : ℤ)
    (p : ℤ × ℤ × ℤ) (c : ℕ) :
    shellMonomial t d U V T r p c =
      T ^ shellHeight r p * shellMonomial t d U V 1 r p c := by
  have hn := shell_exponents_nonnegative r p.1 p.2.1 p.2.2 c
  have hn' := Int.toNat_of_nonneg hn.1
  have hb' := Int.toNat_of_nonneg hn.2
  rw [shellHeight_eq r p c]
  unfold shellMonomial
  dsimp
  rw [← hn', ← hb']
  simp only [zpow_natCast, Int.toNat_natCast, one_mul, mul_pow, pow_add]
  ring

theorem masterTerm_damping (q t d U V T : ℂ) (r : ℤ) (p : LatticeIndex) :
    masterTerm q t d U V T r p =
      T ^ shellHeight r (p.1, p.2.1, p.2.2.1) * masterTerm q t d U V 1 r p := by
  unfold masterTerm
  rw [shellMonomial_damping]
  ring

theorem masterTerm_norm_le_undamped (q t d U V : ℂ) (r : ℤ)
    (p : LatticeIndex) {T : ℝ} (hT₀ : 0 ≤ T) (hT₁ : T ≤ 1) :
    ‖masterTerm q t d U V (T : ℂ) r p‖ ≤ ‖masterTerm q t d U V 1 r p‖ := by
  rw [masterTerm_damping, norm_mul, norm_pow]
  have ht : ‖(T : ℂ)‖ = T := by simp [abs_of_nonneg hT₀]
  rw [ht]
  exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hT₀ hT₁)

theorem tendsto_masterTerm (q t d U V : ℂ) (r : ℤ) (p : LatticeIndex) :
    Tendsto (fun T : ℝ => masterTerm q t d U V (T : ℂ) r p)
      (𝓝[Set.Ioo 0 1] 1) (𝓝 (masterTerm q t d U V 1 r p)) := by
  have he : (fun T : ℝ => masterTerm q t d U V (T : ℂ) r p) =
      (fun T : ℝ => (T : ℂ) ^ shellHeight r (p.1, p.2.1, p.2.2.1) *
        masterTerm q t d U V 1 r p) := by
    funext T
    exact masterTerm_damping q t d U V (T : ℂ) r p
  rw [he]
  have hc : ContinuousAt (fun T : ℝ =>
      (T : ℂ) ^ shellHeight r (p.1, p.2.1, p.2.2.1) *
        masterTerm q t d U V 1 r p) 1 := by fun_prop
  simpa using hc.tendsto.mono_left nhdsWithin_le_nhds

/-- Dominated convergence on the actual master family. The summability
input is deliberately visible and is discharged by the region assembly. -/
theorem tendsto_master_sum_of_summable (q t d U V : ℂ) (r : ℤ)
    (hs : Summable (fun p : LatticeIndex => ‖masterTerm q t d U V 1 r p‖)) :
    Tendsto (fun T : ℝ => ∑' p : LatticeIndex, masterTerm q t d U V (T : ℂ) r p)
      (𝓝[Set.Ioo 0 1] 1) (𝓝 (∑' p : LatticeIndex, masterTerm q t d U V 1 r p)) := by
  apply tendsto_tsum_of_dominated_convergence hs (tendsto_masterTerm q t d U V r)
  filter_upwards [self_mem_nhdsWithin] with T hT
  intro p
  exact masterTerm_norm_le_undamped q t d U V r p hT.1.le hT.2.le

end FourierJacobi.Analysis
