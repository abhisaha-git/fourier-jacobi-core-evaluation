import FourierJacobi.Algebra.RegionSum
import FourierJacobi.Valuations.Cartan
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Complex.Basic

/-!
# Damped sums over actual integer valuation regions

The domains below are the simultaneous integer inequalities of `I0eq3` in
the expanded Section 2. The summand is `expanded:master-row`, with the
entry/minor Cartan indices already checked in `Valuations.Cartan` and with
damping retained. These are infinite-series theorems. Identification of this
shell summand with an independently defined Haar integral is still separate.

The four completed cases are 1, 2, 6 and 7 of `I0eq3` (zero-based rational
rows 0, 1, 5 and 6). Each proof first constructs a bijection from the original
integer domain to `ℕ × ℕ × ℕ`, then substitutes the existing integer Cartan
table into the master monomial. Absolute summability is proved on this product
index type before the sum is evaluated and transported back to the original
domain. The final `regionTerm` theorems identify the result with the existing
fifty-row data under `U ↦ T*U`, `V ↦ T*V`.

The norm hypotheses are genuine convergence conditions. In particular,
`‖T*V*t/d‖ < 1` fails at the undamped special endpoint when `‖V‖=1` and
`d=±t`, even when the corresponding rational denominator is nonzero.
The parameters are abstract complex numbers; integer powers use Lean's
totalized inverse. Restrict to nonzero Laurent parameters for the ordinary
mathematical interpretation. No local field, Haar integral, representation,
or identification with a Fourier--Jacobi period is assumed in these statements.
-/

noncomputable section

namespace FourierJacobi.Analysis

open FourierJacobi.Valuations

set_option maxHeartbeats 2000000

/-- The full shell monomial for `I₀`, with `t=q^(-1/2)` and the common Weyl
factor `Aᵢ/Cq` omitted. All exponents use integer valuation conventions. -/
def i0Shell (t d U V T : ℂ) (p : ℤ × ℤ × ℤ) : ℂ :=
  let ell := (cartanIndices 0 p.1 p.2.1 p.2.2 0).1
  let b := (cartanIndices 0 p.1 p.2.1 p.2.2 0).2
  (1 - t ^ 2) ^ 2 * d ^ p.1 *
    t ^ (3 * p.1 + 2 * p.2.1 + 2 * p.2.2 + 3 * ell + 4 * b) *
    (T * U) ^ (ell / 2) * (T * V) ^ b

/-- Cases 1 (`tail=false`) and 2 (`tail=true`) of `I0eq3`.
These are the original inequalities, before a geometric-series substitution. -/
abbrev I0PositiveRow (tail : Bool) :=
  {p : ℤ × ℤ × ℤ // 0 ≤ p.1 ∧ -2 * p.1 ≤ p.2.1 ∧
    if tail then p.2.2 < -p.1 else -p.1 ≤ p.2.2}

/-- A bijection between the actual valuation region and three free
nonnegative integers. The last coordinate measures depth below, or above,
the boundary `h=-k`. -/
def i0PositiveRowEquiv (tail : Bool) : (ℕ × ℕ × ℕ) ≃ I0PositiveRow tail where
  toFun n := ⟨((n.1 : ℤ), (n.2.1 : ℤ) - 2 * n.1,
    if tail then -(n.1 : ℤ) - n.2.2 - 1 else (n.2.2 : ℤ) - n.1), by
      cases tail <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega⟩
  invFun p := (p.val.1.toNat, (p.val.2.1 + 2 * p.val.1).toNat,
    (if tail then -p.val.1 - p.val.2.2 - 1 else p.val.2.2 + p.val.1).toNat)
  left_inv n := by
    rcases n with ⟨k, j, h⟩
    cases tail <;> simp only [Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq]
    all_goals omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k, j, h⟩, hk, hj, hh⟩
    change 0 ≤ k at hk
    change -2 * k ≤ j at hj
    change (if tail then h < -k else -k ≤ h) at hh
    cases tail
    · change ((k.toNat : ℤ), ((j + 2 * k).toNat : ℤ) - 2 * k.toNat,
        ((h + k).toNat : ℤ) - k.toNat) = (k, j, h)
      simp only [Bool.false_eq_true, ↓reduceIte] at hh
      simp only [Prod.mk.injEq]
      omega
    · change ((k.toNat : ℤ), ((j + 2 * k).toNat : ℤ) - 2 * k.toNat,
        -(k.toNat : ℤ) - (-k - h - 1).toNat - 1) = (k, j, h)
      simp only [↓reduceIte] at hh
      simp only [Prod.mk.injEq]
      omega

@[simp] theorem i0PositiveRowEquiv_val (tail : Bool) (n : ℕ × ℕ × ℕ) :
    (i0PositiveRowEquiv tail n).val = ((n.1 : ℤ), (n.2.1 : ℤ) - 2 * n.1,
      if tail then -(n.1 : ℤ) - n.2.2 - 1 else (n.2.2 : ℤ) - n.1) := rfl

theorem i0PositiveRow_cartan (tail : Bool) (n : ℕ × ℕ × ℕ) :
    cartanIndices 0 (i0PositiveRowEquiv tail n).val.1
      (i0PositiveRowEquiv tail n).val.2.1
      (i0PositiveRowEquiv tail n).val.2.2 0 =
      (if tail then (2 * (n.2.2 : ℤ) + 2, (n.1 : ℤ)) else (0, (n.1 : ℤ))) := by
  rw [← tableZero_correct]
  have hk : 0 ≤ (n.1 : ℤ) := by omega
  have hj : -2 * (n.1 : ℤ) ≤ (n.2.1 : ℤ) - 2 * n.1 := by omega
  cases tail
  · change tableZero (n.1 : ℤ) ((n.2.1 : ℤ) - 2 * n.1)
      ((n.2.2 : ℤ) - n.1) = (0, (n.1 : ℤ))
    have hh : -(n.1 : ℤ) ≤ (n.2.2 : ℤ) - n.1 := by omega
    rw [tableZero, if_pos hk, if_pos hj, if_pos hh]
  · change tableZero (n.1 : ℤ) ((n.2.1 : ℤ) - 2 * n.1)
      (-(n.1 : ℤ) - n.2.2 - 1) = (2 * (n.2.2 : ℤ) + 2, (n.1 : ℤ))
    have hh : ¬ -(n.1 : ℤ) ≤ -(n.1 : ℤ) - n.2.2 - 1 := by omega
    rw [tableZero, if_pos hk, if_pos hj, if_neg hh]
    simp only [Prod.mk.injEq]
    exact ⟨by ring, trivial⟩

theorem i0_case1_reindexed (t d U V T : ℂ) (n : ℕ × ℕ × ℕ) :
    i0Shell t d U V T (i0PositiveRowEquiv false n).val =
      (1 - t ^ 2) ^ 2 * (d * T * V * t) ^ n.1 *
        (t ^ 2) ^ n.2.1 * (t ^ 2) ^ n.2.2 := by
  unfold i0Shell
  rw [i0PositiveRow_cartan]
  simp only [Bool.false_eq_true, ↓reduceIte, i0PositiveRowEquiv_val]
  have he : 3 * (n.1 : ℤ) + 2 * ((n.2.1 : ℤ) - 2 * n.1) +
      2 * ((n.2.2 : ℤ) - n.1) + 3 * 0 + 4 * n.1 =
      ((n.1 + 2 * n.2.1 + 2 * n.2.2 : ℕ) : ℤ) := by omega
  rw [he]
  simp only [zpow_natCast, pow_add, pow_mul, mul_pow]
  simp
  ring

theorem i0_case2_reindexed (t d U V T : ℂ) (n : ℕ × ℕ × ℕ) :
    i0Shell t d U V T (i0PositiveRowEquiv true n).val =
      ((1 - t ^ 2) ^ 2 * (T * U * t ^ 4)) *
        (d * T * V * t) ^ n.1 * (t ^ 2) ^ n.2.1 *
          (T * U * t ^ 4) ^ n.2.2 := by
  unfold i0Shell
  rw [i0PositiveRow_cartan]
  simp only [↓reduceIte, i0PositiveRowEquiv_val]
  have he : 3 * (n.1 : ℤ) + 2 * ((n.2.1 : ℤ) - 2 * n.1) +
      2 * (-(n.1 : ℤ) - n.2.2 - 1) + 3 * (2 * n.2.2 + 2) + 4 * n.1 =
      ((n.1 + 2 * n.2.1 + 4 * (n.2.2 + 1) : ℕ) : ℤ) := by omega
  have hl : (2 * (n.2.2 : ℤ) + 2) / 2 = ((n.2.2 + 1 : ℕ) : ℤ) := by omega
  rw [he, hl]
  simp only [zpow_natCast, pow_add, pow_mul, mul_pow, pow_one]
  ring

/-- Norm summability is proved from the real geometric series directly. -/
theorem geometric_norm_summable (z : ℂ) (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ => ‖z ^ n‖) := by
  have hz' : ‖(‖z‖ : ℝ)‖ < 1 := by simpa using hz
  simpa only [norm_pow] using (hasSum_geometric_of_norm_lt_one hz').summable

/-- Absolute convergence of a product indexed by three free nonnegative
integers, proved without changing the order of conditionally convergent sums. -/
theorem summable_norm_three_geometric (C a b c : ℂ)
    (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) (hc : ‖c‖ < 1) :
    Summable (fun n : ℕ × ℕ × ℕ => ‖C * a ^ n.1 * b ^ n.2.1 * c ^ n.2.2‖) := by
  have hBC := (geometric_norm_summable b hb).mul_norm (geometric_norm_summable c hc)
  have hABC := (geometric_norm_summable a ha).mul_norm hBC
  simpa only [norm_mul, mul_assoc] using hABC.mul_left ‖C‖

/-- An absolutely convergent product of three geometric families, indexed
by an unordered product type rather than an iterated, potentially conditional,
sum. This is the analysis used after the explicit domain bijections. -/
theorem hasSum_three_geometric (C a b c : ℂ)
    (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) (hc : ‖c‖ < 1) :
    HasSum (fun n : ℕ × ℕ × ℕ => C * a ^ n.1 * b ^ n.2.1 * c ^ n.2.2)
      (C * (1 - a)⁻¹ * (1 - b)⁻¹ * (1 - c)⁻¹) := by
  have hA : (∑' n : ℕ, a ^ n) = (1 - a)⁻¹ :=
    (hasSum_geometric_of_norm_lt_one ha).tsum_eq
  have hB : (∑' n : ℕ, b ^ n) = (1 - b)⁻¹ :=
    (hasSum_geometric_of_norm_lt_one hb).tsum_eq
  have hC : (∑' n : ℕ, c ^ n) = (1 - c)⁻¹ :=
    (hasSum_geometric_of_norm_lt_one hc).tsum_eq
  have hsBC : Summable (fun n : ℕ × ℕ => b ^ n.1 * c ^ n.2) :=
    summable_mul_of_summable_norm (f := fun n : ℕ => b ^ n)
      (g := fun n : ℕ => c ^ n) (geometric_norm_summable b hb) (geometric_norm_summable c hc)
  have hBC : (∑' n : ℕ × ℕ, b ^ n.1 * c ^ n.2) =
      (1 - b)⁻¹ * (1 - c)⁻¹ := by
    rw [hsBC.tsum_prod]
    simp only [tsum_mul_left, hC, tsum_mul_right, hB]
  have hs : Summable (fun n : ℕ × ℕ × ℕ =>
      C * a ^ n.1 * b ^ n.2.1 * c ^ n.2.2) :=
    (summable_norm_three_geometric C a b c ha hb hc).of_norm
  have he : (∑' n : ℕ × ℕ × ℕ, C * a ^ n.1 * b ^ n.2.1 * c ^ n.2.2) =
      C * (1 - a)⁻¹ * (1 - b)⁻¹ * (1 - c)⁻¹ := by
    rw [hs.tsum_prod]
    simp only [mul_assoc, tsum_mul_left, hBC, tsum_mul_right, hA]
  exact he ▸ hs.hasSum

/-- The first infinite valuation sum of `I0eq3`, equal to the damped
version of `I0eqq1`. Its hypotheses prove convergence, not merely that
the displayed denominator is nonzero. -/
theorem hasSum_i0_case1 (t d U V T : ℂ)
    (ht : ‖t ^ 2‖ < 1) (hP : ‖d * T * V * t‖ < 1) :
    HasSum (fun p : I0PositiveRow false => i0Shell t d U V T p.val)
      (1 - d * T * V * t)⁻¹ := by
  have h := hasSum_three_geometric ((1 - t ^ 2) ^ 2)
    (d * T * V * t) (t ^ 2) (t ^ 2) hP ht ht
  have hn : 1 - t ^ 2 ≠ 0 := sub_ne_zero.mpr (by
    intro he
    rw [← he, norm_one] at ht
    exact (lt_irrefl (1 : ℝ)) ht)
  have he : (1 - t ^ 2) ^ 2 * (1 - d * T * V * t)⁻¹ *
      (1 - t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹ = (1 - d * T * V * t)⁻¹ := by
    calc
      _ = (1 - d * T * V * t)⁻¹ *
          ((1 - t ^ 2) * (1 - t ^ 2)⁻¹) *
          ((1 - t ^ 2) * (1 - t ^ 2)⁻¹) := by ring
      _ = _ := by rw [mul_inv_cancel₀ hn]; simp
  rw [he] at h
  apply (i0PositiveRowEquiv false).hasSum_iff.mp
  convert h using 1
  exact funext fun n => i0_case1_reindexed t d U V T n

/-- The second infinite valuation sum of `I0eq3`, equal to the damped
version of `I0eqq2`, with both geometric-ratio bounds explicit. -/
theorem hasSum_i0_case2 (t d U V T : ℂ)
    (ht : ‖t ^ 2‖ < 1) (hP : ‖d * T * V * t‖ < 1)
    (hG : ‖T * U * t ^ 4‖ < 1) :
    HasSum (fun p : I0PositiveRow true => i0Shell t d U V T p.val)
      ((T * U * t ^ 4 * (1 - t ^ 2)) /
        ((1 - T * U * t ^ 4) * (1 - d * T * V * t))) := by
  have h := hasSum_three_geometric ((1 - t ^ 2) ^ 2 * (T * U * t ^ 4))
    (d * T * V * t) (t ^ 2) (T * U * t ^ 4) hP ht hG
  have hn : 1 - t ^ 2 ≠ 0 := sub_ne_zero.mpr (by
    intro he
    rw [← he, norm_one] at ht
    exact (lt_irrefl (1 : ℝ)) ht)
  have he : (1 - t ^ 2) ^ 2 * (T * U * t ^ 4) *
      (1 - d * T * V * t)⁻¹ * (1 - t ^ 2)⁻¹ * (1 - T * U * t ^ 4)⁻¹ =
      (T * U * t ^ 4 * (1 - t ^ 2)) /
        ((1 - T * U * t ^ 4) * (1 - d * T * V * t)) := by
    calc
      _ = ((T * U * t ^ 4 * (1 - t ^ 2)) /
          ((1 - T * U * t ^ 4) * (1 - d * T * V * t))) *
          ((1 - t ^ 2) * (1 - t ^ 2)⁻¹) := by
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      _ = _ := by rw [mul_inv_cancel₀ hn, mul_one]
  rw [he] at h
  apply (i0PositiveRowEquiv true).hasSum_iff.mp
  convert h using 1
  exact funext fun n => i0_case2_reindexed t d U V T n

/-- Cases 6 and 7 of `I0eq3`, retaining the strict condition `k<0`. -/
abbrev I0NegativeRow (tail : Bool) :=
  {p : ℤ × ℤ × ℤ // p.1 < 0 ∧ 0 ≤ p.2.1 ∧
    if tail then p.2.2 < 0 else 0 ≤ p.2.2}

def i0NegativeRowEquiv (tail : Bool) : (ℕ × ℕ × ℕ) ≃ I0NegativeRow tail where
  toFun n := ⟨(-(n.1 : ℤ) - 1, (n.2.1 : ℤ),
    if tail then -(n.2.2 : ℤ) - 1 else (n.2.2 : ℤ)), by
      cases tail <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega⟩
  invFun p := ((-p.val.1 - 1).toNat, p.val.2.1.toNat,
    (if tail then -p.val.2.2 - 1 else p.val.2.2).toNat)
  left_inv n := by
    rcases n with ⟨k, j, h⟩
    cases tail <;> simp only [Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq]
    all_goals omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k, j, h⟩, hk, hj, hh⟩
    change k < 0 at hk
    change 0 ≤ j at hj
    change (if tail then h < 0 else 0 ≤ h) at hh
    cases tail
    · change (-((-k - 1).toNat : ℤ) - 1, (j.toNat : ℤ), (h.toNat : ℤ)) = (k, j, h)
      simp only [Bool.false_eq_true, ↓reduceIte] at hh
      simp only [Prod.mk.injEq]
      omega
    · change (-((-k - 1).toNat : ℤ) - 1, (j.toNat : ℤ),
        -((-h - 1).toNat : ℤ) - 1) = (k, j, h)
      simp only [↓reduceIte] at hh
      simp only [Prod.mk.injEq]
      omega

@[simp] theorem i0NegativeRowEquiv_val (tail : Bool) (n : ℕ × ℕ × ℕ) :
    (i0NegativeRowEquiv tail n).val = (-(n.1 : ℤ) - 1, (n.2.1 : ℤ),
      if tail then -(n.2.2 : ℤ) - 1 else (n.2.2 : ℤ)) := rfl

theorem i0NegativeRow_cartan (tail : Bool) (n : ℕ × ℕ × ℕ) :
    cartanIndices 0 (i0NegativeRowEquiv tail n).val.1
      (i0NegativeRowEquiv tail n).val.2.1
      (i0NegativeRowEquiv tail n).val.2.2 0 =
      (if tail then (2 * (n.2.2 : ℤ) + 2, (n.1 : ℤ) + 1)
        else (0, (n.1 : ℤ) + 1)) := by
  rw [← tableZero_correct]
  have hk : ¬ 0 ≤ -(n.1 : ℤ) - 1 := by omega
  have hj : 0 ≤ (n.2.1 : ℤ) := by omega
  cases tail
  · change tableZero (-(n.1 : ℤ) - 1) (n.2.1 : ℤ) (n.2.2 : ℤ) =
      (0, (n.1 : ℤ) + 1)
    have hh : 0 ≤ (n.2.2 : ℤ) := by omega
    rw [tableZero, if_neg hk, if_pos hj, if_pos hh]
    simp only [Prod.mk.injEq]
    exact ⟨trivial, by ring⟩
  · change tableZero (-(n.1 : ℤ) - 1) (n.2.1 : ℤ) (-(n.2.2 : ℤ) - 1) =
      (2 * (n.2.2 : ℤ) + 2, (n.1 : ℤ) + 1)
    have hh : ¬ 0 ≤ -(n.2.2 : ℤ) - 1 := by omega
    rw [tableZero, if_neg hk, if_pos hj, if_neg hh]
    simp only [Prod.mk.injEq]
    omega

theorem i0_case6_reindexed (t d U V T : ℂ) (n : ℕ × ℕ × ℕ) :
    i0Shell t d U V T (i0NegativeRowEquiv false n).val =
      ((1 - t ^ 2) ^ 2 * (T * V * t / d)) *
        (T * V * t / d) ^ n.1 * (t ^ 2) ^ n.2.1 * (t ^ 2) ^ n.2.2 := by
  unfold i0Shell
  rw [i0NegativeRow_cartan]
  simp only [Bool.false_eq_true, ↓reduceIte, i0NegativeRowEquiv_val]
  have he : 3 * (-(n.1 : ℤ) - 1) + 2 * n.2.1 + 2 * n.2.2 +
      3 * 0 + 4 * (n.1 + 1) =
      ((n.1 + 1 + 2 * n.2.1 + 2 * n.2.2 : ℕ) : ℤ) := by omega
  have hk : -(n.1 : ℤ) - 1 = -((n.1 + 1 : ℕ) : ℤ) := by omega
  have hb : (n.1 : ℤ) + 1 = ((n.1 + 1 : ℕ) : ℤ) := by omega
  rw [he, hk, hb]
  simp only [zpow_neg, zpow_natCast, pow_add, pow_mul, mul_pow, pow_one,
    mul_inv_rev, div_eq_mul_inv, inv_pow]
  simp
  ring

theorem i0_case7_reindexed (t d U V T : ℂ) (n : ℕ × ℕ × ℕ) :
    i0Shell t d U V T (i0NegativeRowEquiv true n).val =
      ((1 - t ^ 2) ^ 2 * (T * V * t / d) * (T * U * t ^ 4)) *
        (T * V * t / d) ^ n.1 * (t ^ 2) ^ n.2.1 *
          (T * U * t ^ 4) ^ n.2.2 := by
  unfold i0Shell
  rw [i0NegativeRow_cartan]
  simp only [↓reduceIte, i0NegativeRowEquiv_val]
  have he : 3 * (-(n.1 : ℤ) - 1) + 2 * n.2.1 +
      2 * (-(n.2.2 : ℤ) - 1) + 3 * (2 * n.2.2 + 2) + 4 * (n.1 + 1) =
      ((n.1 + 1 + 2 * n.2.1 + 4 * (n.2.2 + 1) : ℕ) : ℤ) := by omega
  have hk : -(n.1 : ℤ) - 1 = -((n.1 + 1 : ℕ) : ℤ) := by omega
  have hb : (n.1 : ℤ) + 1 = ((n.1 + 1 : ℕ) : ℤ) := by omega
  have hl : (2 * (n.2.2 : ℤ) + 2) / 2 = ((n.2.2 + 1 : ℕ) : ℤ) := by omega
  rw [he, hk, hb, hl]
  simp only [zpow_neg, zpow_natCast, pow_add, pow_mul, mul_pow, pow_one,
    mul_inv_rev, div_eq_mul_inv, inv_pow]
  ring

/-- Case 6, including the first strictly negative valuation shell. -/
theorem hasSum_i0_case6 (t d U V T : ℂ)
    (ht : ‖t ^ 2‖ < 1) (hN : ‖T * V * t / d‖ < 1) :
    HasSum (fun p : I0NegativeRow false => i0Shell t d U V T p.val)
      ((T * V * t / d) / (1 - T * V * t / d)) := by
  have h := hasSum_three_geometric ((1 - t ^ 2) ^ 2 * (T * V * t / d))
    (T * V * t / d) (t ^ 2) (t ^ 2) hN ht ht
  have hn : 1 - t ^ 2 ≠ 0 := sub_ne_zero.mpr (by
    intro he
    rw [← he, norm_one] at ht
    exact (lt_irrefl (1 : ℝ)) ht)
  have he : (1 - t ^ 2) ^ 2 * (T * V * t / d) *
      (1 - T * V * t / d)⁻¹ * (1 - t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹ =
      (T * V * t / d) / (1 - T * V * t / d) := by
    calc
      _ = ((T * V * t / d) / (1 - T * V * t / d)) *
          ((1 - t ^ 2) * (1 - t ^ 2)⁻¹) *
          ((1 - t ^ 2) * (1 - t ^ 2)⁻¹) := by
        simp only [div_eq_mul_inv]
        ring
      _ = _ := by rw [mul_inv_cancel₀ hn]; simp
  rw [he] at h
  apply (i0NegativeRowEquiv false).hasSum_iff.mp
  convert h using 1
  exact funext fun n => i0_case6_reindexed t d U V T n

/-- Case 7, with damping present in both independent geometric ratios. -/
theorem hasSum_i0_case7 (t d U V T : ℂ)
    (ht : ‖t ^ 2‖ < 1) (hN : ‖T * V * t / d‖ < 1)
    (hG : ‖T * U * t ^ 4‖ < 1) :
    HasSum (fun p : I0NegativeRow true => i0Shell t d U V T p.val)
      (((T * V * t / d) * (T * U * t ^ 4) * (1 - t ^ 2)) /
        ((1 - T * U * t ^ 4) * (1 - T * V * t / d))) := by
  have h := hasSum_three_geometric
    ((1 - t ^ 2) ^ 2 * (T * V * t / d) * (T * U * t ^ 4))
    (T * V * t / d) (t ^ 2) (T * U * t ^ 4) hN ht hG
  have hn : 1 - t ^ 2 ≠ 0 := sub_ne_zero.mpr (by
    intro he
    rw [← he, norm_one] at ht
    exact (lt_irrefl (1 : ℝ)) ht)
  have he : (1 - t ^ 2) ^ 2 * (T * V * t / d) * (T * U * t ^ 4) *
      (1 - T * V * t / d)⁻¹ * (1 - t ^ 2)⁻¹ * (1 - T * U * t ^ 4)⁻¹ =
      ((T * V * t / d) * (T * U * t ^ 4) * (1 - t ^ 2)) /
        ((1 - T * U * t ^ 4) * (1 - T * V * t / d)) := by
    calc
      _ = (((T * V * t / d) * (T * U * t ^ 4) * (1 - t ^ 2)) /
          ((1 - T * U * t ^ 4) * (1 - T * V * t / d))) *
          ((1 - t ^ 2) * (1 - t ^ 2)⁻¹) := by
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      _ = _ := by rw [mul_inv_cancel₀ hn, mul_one]
  rw [he] at h
  apply (i0NegativeRowEquiv true).hasSum_iff.mp
  convert h using 1
  exact funext fun n => i0_case7_reindexed t d U V T n

/-- Direct identification with row 0 of the existing fifty-row expression,
under the expansion's damping substitution `U ↦ TU`, `V ↦ TV`. -/
theorem hasSum_i0_case1_regionTerm (t d U V T : ℂ)
    (ht : ‖t ^ 2‖ < 1) (hP : ‖d * T * V * t‖ < 1) :
    HasSum (fun p : I0PositiveRow false => i0Shell t d U V T p.val)
      (Algebra.regionTerm0 t d (T * U) (T * V)
        (1 - d * (T * V) * t) (1 - (T * V) * t / d)
        (1 - (T * V) ^ 2 * t ^ 2) (1 - (T * U) * t ^ 2)
        (1 - (T * U) * t ^ 4)) := by
  simpa only [Algebra.regionTerm0, pow_one, mul_assoc]
    using hasSum_i0_case1 t d U V T ht hP

/-- Direct identification with row 1 of the existing fifty-row expression. -/
theorem hasSum_i0_case2_regionTerm (t d U V T : ℂ)
    (ht : ‖t ^ 2‖ < 1) (hP : ‖d * T * V * t‖ < 1)
    (hG : ‖T * U * t ^ 4‖ < 1) :
    HasSum (fun p : I0PositiveRow true => i0Shell t d U V T p.val)
      (Algebra.regionTerm1 t d (T * U) (T * V)
        (1 - d * (T * V) * t) (1 - (T * V) * t / d)
        (1 - (T * V) ^ 2 * t ^ 2) (1 - (T * U) * t ^ 2)
        (1 - (T * U) * t ^ 4)) := by
  convert hasSum_i0_case2 t d U V T ht hP hG using 1
  simp only [Algebra.regionTerm1, pow_one, div_eq_mul_inv, mul_inv_rev, mul_assoc]
  ring

/-- Direct identification with row 5 of the existing fifty-row expression. -/
theorem hasSum_i0_case6_regionTerm (t d U V T : ℂ)
    (ht : ‖t ^ 2‖ < 1) (hN : ‖T * V * t / d‖ < 1) :
    HasSum (fun p : I0NegativeRow false => i0Shell t d U V T p.val)
      (Algebra.regionTerm5 t d (T * U) (T * V)
        (1 - d * (T * V) * t) (1 - (T * V) * t / d)
        (1 - (T * V) ^ 2 * t ^ 2) (1 - (T * U) * t ^ 2)
        (1 - (T * U) * t ^ 4)) := by
  convert hasSum_i0_case6 t d U V T ht hN using 1
  simp only [Algebra.regionTerm5, pow_one, div_eq_mul_inv, mul_assoc]
  ring

/-- Direct identification with row 6 of the existing fifty-row expression. -/
theorem hasSum_i0_case7_regionTerm (t d U V T : ℂ)
    (ht : ‖t ^ 2‖ < 1) (hN : ‖T * V * t / d‖ < 1)
    (hG : ‖T * U * t ^ 4‖ < 1) :
    HasSum (fun p : I0NegativeRow true => i0Shell t d U V T p.val)
      (Algebra.regionTerm6 t d (T * U) (T * V)
        (1 - d * (T * V) * t) (1 - (T * V) * t / d)
        (1 - (T * V) ^ 2 * t ^ 2) (1 - (T * U) * t ^ 2)
        (1 - (T * U) * t ^ 4)) := by
  convert hasSum_i0_case7 t d U V T ht hN hG using 1
  simp only [Algebra.regionTerm6, pow_one, div_eq_mul_inv, mul_inv_rev, mul_assoc]
  ring

/-- Absolute convergence of all four original-domain families. The shared
ratio conditions are kept explicit, including the damping variable. -/
theorem i0_four_rows_absolutelySummable (t d U V T : ℂ)
    (ht : ‖t ^ 2‖ < 1) (hP : ‖d * T * V * t‖ < 1)
    (hN : ‖T * V * t / d‖ < 1) (hG : ‖T * U * t ^ 4‖ < 1) :
    Summable (fun p : I0PositiveRow false => ‖i0Shell t d U V T p.val‖) ∧
    Summable (fun p : I0PositiveRow true => ‖i0Shell t d U V T p.val‖) ∧
    Summable (fun p : I0NegativeRow false => ‖i0Shell t d U V T p.val‖) ∧
    Summable (fun p : I0NegativeRow true => ‖i0Shell t d U V T p.val‖) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply (i0PositiveRowEquiv false).summable_iff.mp
    convert summable_norm_three_geometric ((1 - t ^ 2) ^ 2)
      (d * T * V * t) (t ^ 2) (t ^ 2) hP ht ht using 1
    exact funext fun n => congrArg norm (i0_case1_reindexed t d U V T n)
  · apply (i0PositiveRowEquiv true).summable_iff.mp
    convert summable_norm_three_geometric ((1 - t ^ 2) ^ 2 * (T * U * t ^ 4))
      (d * T * V * t) (t ^ 2) (T * U * t ^ 4) hP ht hG using 1
    exact funext fun n => congrArg norm (i0_case2_reindexed t d U V T n)
  · apply (i0NegativeRowEquiv false).summable_iff.mp
    convert summable_norm_three_geometric ((1 - t ^ 2) ^ 2 * (T * V * t / d))
      (T * V * t / d) (t ^ 2) (t ^ 2) hN ht ht using 1
    exact funext fun n => congrArg norm (i0_case6_reindexed t d U V T n)
  · apply (i0NegativeRowEquiv true).summable_iff.mp
    convert summable_norm_three_geometric
      ((1 - t ^ 2) ^ 2 * (T * V * t / d) * (T * U * t ^ 4))
      (T * V * t / d) (t ^ 2) (T * U * t ^ 4) hN ht hG using 1
    exact funext fun n => congrArg norm (i0_case7_reindexed t d U V T n)

end FourierJacobi.Analysis
