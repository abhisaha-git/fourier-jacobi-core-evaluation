import FourierJacobi.Analysis.ValuationSeries
import FourierJacobi.Algebra.WeylSum

/-!
The independent integer-shell family of section 4 of the corrected brief.
The central index zero means z=0.  Only a genuine collision carries a
nontrivial depth distribution.  No sum is defined by its proposed value.
-/

noncomputable section

namespace FourierJacobi.Analysis

open FourierJacobi.Valuations

abbrev LatticeIndex := ℤ × ℤ × ℤ × ℕ

def shellCoeff (q : ℂ) (r : ℤ) : ℂ :=
  if r = 0 then 1 else if r = 1 then q * (1 - q⁻¹) else -q

def collisionProbability (q : ℂ) (c : ℕ) : ℂ :=
  if c = 0 then (q - 2) / (q - 1) else q ^ (-(c : ℤ))

def collisionWeight (q : ℂ) (r j h : ℤ) (c : ℕ) : ℂ :=
  if r = 0 ∨ 2 * h ≠ j - r then (if c = 0 then 1 else 0)
  else collisionProbability q c

def shellMonomial (t d U V T : ℂ) (r : ℤ) (p : ℤ × ℤ × ℤ) (c : ℕ) : ℂ :=
  let ell := (cartanIndices r p.1 p.2.1 p.2.2 c).1
  let b := (cartanIndices r p.1 p.2.1 p.2.2 c).2
  (1 - t ^ 2) ^ 2 * d ^ p.1 *
    t ^ (3 * p.1 + 2 * p.2.1 + 2 * p.2.2 + 3 * ell + 4 * b) *
    (T * U) ^ (ell / 2) * (T * V) ^ b

def masterTerm (q t d U V T : ℂ) (r : ℤ) (p : LatticeIndex) : ℂ :=
  shellCoeff q r * shellMonomial t d U V T r (p.1, p.2.1, p.2.2.1) p.2.2.2 *
    collisionWeight q r p.2.1 p.2.2.1 p.2.2.2

theorem half_cartan_eq (r k j h c : ℤ) :
    (cartanIndices r k j h c).1 / 2 =
      entryMinimum r k j h - minorMinimum r k j h c := by
  unfold cartanIndices
  dsimp
  omega

theorem shell_exponents_nonnegative (r k j h : ℤ) (c : ℕ) :
    0 ≤ (cartanIndices r k j h c).1 / 2 ∧
    0 ≤ (cartanIndices r k j h c).2 := by
  have hc := cartanIndices_nonnegative r k j h c (by omega)
  constructor
  · omega
  · exact hc.2

theorem shell_height_eq (r k j h c : ℤ) :
    (cartanIndices r k j h c).1 / 2 + (cartanIndices r k j h c).2 =
      -entryMinimum r k j h := by
  rw [half_cartan_eq]
  unfold cartanIndices
  dsimp
  ring

@[simp] theorem shellMonomial_zero (t d U V T : ℂ) (p : ℤ × ℤ × ℤ) (c : ℕ) :
    shellMonomial t d U V T 0 p c = i0Shell t d U V T p := by
  rfl

@[simp] theorem masterTerm_zero (q t d U V T : ℂ) (p : LatticeIndex) :
    masterTerm q t d U V T 0 p =
      if p.2.2.2 = 0 then i0Shell t d U V T (p.1, p.2.1, p.2.2.1) else 0 := by
  simp only [masterTerm, shellCoeff, collisionWeight, true_or, if_true,
    shellMonomial_zero, one_mul]
  split_ifs <;> simp

theorem collisionProbability_succ (q : ℂ) (c : ℕ) :
    collisionProbability q (c + 1) = q⁻¹ * (q⁻¹) ^ c := by
  unfold collisionProbability
  rw [if_neg (by omega), zpow_neg, zpow_natCast]
  simp only [pow_succ, mul_inv_rev, inv_pow]

theorem hasSum_collisionProbability_tail (q : ℂ) (m : ℕ)
    (hq : ‖q⁻¹‖ < 1) :
    HasSum (fun c : ℕ => collisionProbability q (c + m + 1))
      ((q⁻¹) ^ (m + 1) * (1 - q⁻¹)⁻¹) := by
  have hg : HasSum (fun c : ℕ => (q⁻¹) ^ c) (1 - q⁻¹)⁻¹ :=
    hasSum_geometric_of_norm_lt_one hq
  have he : (fun c : ℕ => collisionProbability q (c + m + 1)) =
      (fun c : ℕ => (q⁻¹) ^ (m + 1) * (q⁻¹) ^ c) := by
    funext c
    rw [collisionProbability_succ]
    simp only [pow_add, pow_one]
    ring
  rw [he]
  exact hg.mul_left _

theorem hasSum_collisionProbability (q : ℂ) (hq₀ : q ≠ 0)
    (hq₁ : q - 1 ≠ 0) (hq : ‖q⁻¹‖ < 1) :
    HasSum (collisionProbability q) 1 := by
  have h := hasSum_collisionProbability_tail q 0 hq
  have he : (q⁻¹) ^ (0 + 1) * (1 - q⁻¹)⁻¹ = 1 - collisionProbability q 0 := by
    simp only [collisionProbability, if_true]
    field_simp [hq₀, hq₁]
    ring_nf
    simp [hq₀]
  rw [he] at h
  apply (hasSum_nat_add_iff' 1).mp
  simpa only [Nat.add_zero, Finset.sum_range_one] using h

theorem summable_norm_collisionProbability (q : ℂ) (hq : ‖q⁻¹‖ < 1) :
    Summable (fun c : ℕ => ‖collisionProbability q c‖) := by
  rw [← summable_nat_add_iff 1]
  simpa only [collisionProbability_succ, norm_mul, norm_pow] using
    (geometric_norm_summable q⁻¹ hq).mul_left ‖q⁻¹‖

theorem hasSum_collisionWeight (q : ℂ) (r j h : ℤ)
    (hq₀ : q ≠ 0) (hq₁ : q - 1 ≠ 0) (hq : ‖q⁻¹‖ < 1) :
    HasSum (collisionWeight q r j h) 1 := by
  unfold collisionWeight
  split_ifs
  · exact hasSum_ite_eq 0 1
  · exact hasSum_collisionProbability q hq₀ hq₁ hq

theorem summable_norm_collisionWeight (q : ℂ) (r j h : ℤ)
    (hq : ‖q⁻¹‖ < 1) :
    Summable (fun c : ℕ => ‖collisionWeight q r j h c‖) := by
  unfold collisionWeight
  split_ifs
  · simpa only [apply_ite, norm_one, norm_zero] using
      (hasSum_ite_eq (α := ℝ) (β := ℕ) 0 1).summable
  · exact summable_norm_collisionProbability q hq

/-- Uniformly summable depth majorant, valid even for complex q in the geometric range. -/
def depthMajorant (q : ℂ) (c : ℕ) : ℝ :=
  (if c = 0 then 1 else 0) + ‖collisionProbability q c‖

theorem depthMajorant_nonneg (q : ℂ) (c : ℕ) : 0 ≤ depthMajorant q c := by
  unfold depthMajorant
  positivity

theorem summable_depthMajorant (q : ℂ) (hq : ‖q⁻¹‖ < 1) :
    Summable (depthMajorant q) :=
  (hasSum_ite_eq (α := ℝ) (β := ℕ) 0 1).summable.add
    (summable_norm_collisionProbability q hq)

theorem collisionWeight_norm_le (q : ℂ) (r j h : ℤ) (c : ℕ) :
    ‖collisionWeight q r j h c‖ ≤ depthMajorant q c := by
  unfold collisionWeight depthMajorant
  split_ifs <;> simp

theorem summable_norm_weighted_collision {ι : Type*} (q : ℂ) (r : ℤ)
    (j h : ι → ℤ) (f : ι → ℂ) (hq : ‖q⁻¹‖ < 1)
    (hf : Summable (fun p => ‖f p‖)) :
    Summable (fun p : ι × ℕ => ‖f p.1 * collisionWeight q r (j p.1) (h p.1) p.2‖) := by
  have hm := hf.mul_of_nonneg (summable_depthMajorant q hq)
    (fun p => norm_nonneg (f p)) (depthMajorant_nonneg q)
  apply hm.of_norm_bounded
  intro p
  simp only [norm_norm, norm_mul]
  exact mul_le_mul_of_nonneg_left (collisionWeight_norm_le q r (j p.1) (h p.1) p.2)
    (norm_nonneg _)

theorem hasSum_weighted_collision {ι : Type*} (q : ℂ) (r : ℤ)
    (j h : ι → ℤ) (f : ι → ℂ) (s : ℂ)
    (hq₀ : q ≠ 0) (hq₁ : q - 1 ≠ 0) (hq : ‖q⁻¹‖ < 1)
    (hf : HasSum f s) (hfn : Summable (fun p => ‖f p‖)) :
    HasSum (fun p : ι × ℕ => f p.1 * collisionWeight q r (j p.1) (h p.1) p.2) s := by
  have hs := (summable_norm_weighted_collision q r j h f hq hfn).of_norm
  have he : (∑' p : ι × ℕ, f p.1 * collisionWeight q r (j p.1) (h p.1) p.2) = s := by
    rw [hs.tsum_prod]
    simp only [tsum_mul_left, (hasSum_collisionWeight q r _ _ hq₀ hq₁ hq).tsum_eq,
      mul_one, hf.tsum_eq]
  exact he ▸ hs.hasSum

end FourierJacobi.Analysis
