import FourierJacobi.Analysis.ValuationSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# The complete independent zero-central-coordinate valuation sum

The four `ValuationSeries` rows are inherited from the v2 snapshot. This file
supplies the remaining six rows, including the parity bijection, and assembles
the actual integer lattice. Every monomial retains damping before summation.
-/

noncomputable section

namespace FourierJacobi.Analysis

open FourierJacobi.Valuations

set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

/-- Rows 3 and 8: the upper half-plane beyond the second valuation cut. -/
abbrev I0UpperRow (neg : Bool) :=
  {p : ℤ × ℤ × ℤ // (if neg then p.1 < 0 else 0 ≤ p.1) ∧
    p.2.1 < (if neg then 0 else -2 * p.1) ∧
    (if neg then p.2.1 else p.1 + p.2.1) ≤ p.2.2 ∧ p.2.1 ≤ 2 * p.2.2}

/-- Rows 4 and 9: the intervening triangular region. -/
abbrev I0MiddleRow (neg : Bool) :=
  {p : ℤ × ℤ × ℤ // (if neg then p.1 < 0 else 0 ≤ p.1) ∧
    p.2.1 < (if neg then 0 else -2 * p.1) ∧
    (if neg then p.2.1 else p.1 + p.2.1) ≤ p.2.2 ∧ 2 * p.2.2 < p.2.1}

/-- Rows 5 and 10: the lower half-plane beyond the second valuation cut. -/
abbrev I0LowerRow (neg : Bool) :=
  {p : ℤ × ℤ × ℤ // (if neg then p.1 < 0 else 0 ≤ p.1) ∧
    p.2.1 < (if neg then 0 else -2 * p.1) ∧
    p.2.2 < (if neg then p.2.1 else p.1 + p.2.1)}

/-- All three free indices of a triangular row are genuinely independent. -/
def i0MiddleRowEquiv (neg : Bool) : (ℕ × ℕ × ℕ) ≃ I0MiddleRow neg where
  toFun n := ⟨(if neg then -(n.1 : ℤ) - 1 else n.1,
    -(if neg then 0 else 2 * (n.1 : ℤ)) - 2 * n.2.1 - n.2.2 - 1,
    -(if neg then 0 else (n.1 : ℤ)) - n.2.1 - n.2.2 - 1), by
      cases neg <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega⟩
  invFun p := ((if neg then -p.val.1 - 1 else p.val.1).toNat,
    (p.val.2.2 - p.val.2.1 - (if neg then 0 else p.val.1)).toNat,
    (p.val.2.1 - 2 * p.val.2.2 - 1).toNat)
  left_inv n := by
    rcases n with ⟨m, j, h⟩
    cases neg <;> simp only [Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq] <;> omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k, j, h⟩, hk, hj, hh, hc⟩
    change (if neg then k < 0 else 0 ≤ k) at hk
    change j < (if neg then 0 else -2 * k) at hj
    change (if neg then j else k + j) ≤ h at hh
    change 2 * h < j at hc
    cases neg
    · change 0 ≤ k at hk
      change j < -2 * k at hj
      change k + j ≤ h at hh
      change ((k.toNat : ℤ), -(2 * (k.toNat : ℤ)) - 2 * (h - j - k).toNat -
        (j - 2 * h - 1).toNat - 1,
        -(k.toNat : ℤ) - (h - j - k).toNat - (j - 2 * h - 1).toNat - 1) = (k, j, h)
      simp only [Prod.mk.injEq]
      omega
    · change k < 0 at hk
      change j < 0 at hj
      change j ≤ h at hh
      change (-((-k - 1).toNat : ℤ) - 1, -(0 : ℤ) - 2 * (h - j - 0).toNat -
        (j - 2 * h - 1).toNat - 1,
        -0 - ((h - j - 0).toNat : ℤ) - (j - 2 * h - 1).toNat - 1) = (k, j, h)
      simp only [Prod.mk.injEq]
      omega

/-- The lower row is also a free triple, with both lower bounds strict. -/
def i0LowerRowEquiv (neg : Bool) : (ℕ × ℕ × ℕ) ≃ I0LowerRow neg where
  toFun n := ⟨(if neg then -(n.1 : ℤ) - 1 else n.1,
    -(if neg then 0 else 2 * (n.1 : ℤ)) - n.2.1 - 1,
    -(if neg then 0 else (n.1 : ℤ)) - n.2.1 - n.2.2 - 2), by
      cases neg <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega⟩
  invFun p := ((if neg then -p.val.1 - 1 else p.val.1).toNat,
    (-p.val.2.1 - (if neg then 0 else 2 * p.val.1) - 1).toNat,
    ((if neg then 0 else p.val.1) + p.val.2.1 - p.val.2.2 - 1).toNat)
  left_inv n := by
    rcases n with ⟨m, j, h⟩
    cases neg <;> simp only [Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq] <;> omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k, j, h⟩, hk, hj, hh⟩
    change (if neg then k < 0 else 0 ≤ k) at hk
    change j < (if neg then 0 else -2 * k) at hj
    change h < (if neg then j else k + j) at hh
    cases neg
    · change 0 ≤ k at hk
      change j < -2 * k at hj
      change h < k + j at hh
      change ((k.toNat : ℤ), -(2 * (k.toNat : ℤ)) - (-j - 2 * k - 1).toNat - 1,
        -(k.toNat : ℤ) - (-j - 2 * k - 1).toNat - (k + j - h - 1).toNat - 2) = (k, j, h)
      simp only [Prod.mk.injEq]
      omega
    · change k < 0 at hk
      change j < 0 at hj
      change h < j at hh
      change (-((-k - 1).toNat : ℤ) - 1, -0 - ((-j - 0 - 1).toNat : ℤ) - 1,
        -0 - ((-j - 0 - 1).toNat : ℤ) - (0 + j - h - 1).toNat - 2) = (k, j, h)
      simp only [Prod.mk.injEq]
      omega

/-- Parity is retained as a finite index. Parity 0 means an odd negative
offset, and parity 1 means an even negative offset. -/
def i0UpperRowEquiv (neg : Bool) : (Fin 2 × ℕ × ℕ × ℕ) ≃ I0UpperRow neg where
  toFun n := ⟨(if neg then -(n.2.1 : ℤ) - 1 else n.2.1,
    -(if neg then 0 else 2 * (n.2.1 : ℤ)) - 2 * n.2.2.1 - n.1.val - 1,
    -(if neg then 0 else (n.2.1 : ℤ)) - n.2.2.1 - n.1.val + n.2.2.2), by
      have he := n.1.isLt
      cases neg <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega⟩
  invFun p :=
    let s := -p.val.2.1 - (if neg then 0 else 2 * p.val.1) - 1
    (⟨(s % 2).toNat, by omega⟩,
      (if neg then -p.val.1 - 1 else p.val.1).toNat,
      (s / 2).toNat,
      (p.val.2.2 + (if neg then 0 else p.val.1) + s / 2 + s % 2).toNat)
  left_inv n := by
    rcases n with ⟨e, m, j, h⟩
    have he := e.isLt
    cases neg <;> simp only [Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq, Fin.ext_iff]
    all_goals omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k, j, h⟩, hk, hj, hh, hc⟩
    change (if neg then k < 0 else 0 ≤ k) at hk
    change j < (if neg then 0 else -2 * k) at hj
    change (if neg then j else k + j) ≤ h at hh
    change j ≤ 2 * h at hc
    cases neg
    · change 0 ≤ k at hk
      change j < -2 * k at hj
      change k + j ≤ h at hh
      let s : ℤ := -j - 2 * k - 1
      change ((k.toNat : ℤ), -(2 * (k.toNat : ℤ)) - 2 * (s / 2).toNat -
        (s % 2).toNat - 1,
        -(k.toNat : ℤ) - (s / 2).toNat - (s % 2).toNat +
          (h + k + s / 2 + s % 2).toNat) = (k, j, h)
      simp only [Prod.mk.injEq]
      dsimp [s]
      omega
    · change k < 0 at hk
      change j < 0 at hj
      change j ≤ h at hh
      let s : ℤ := -j - 0 - 1
      change (-((-k - 1).toNat : ℤ) - 1, -(0 : ℤ) - 2 * (s / 2).toNat - (s % 2).toNat - 1,
        -0 - ((s / 2).toNat : ℤ) - (s % 2).toNat +
          (h + 0 + s / 2 + s % 2).toNat) = (k, j, h)
      simp only [Prod.mk.injEq]
      dsimp [s]
      omega

theorem i0MiddleRow_cartan (neg : Bool) (n : ℕ × ℕ × ℕ) :
    cartanIndices 0 (i0MiddleRowEquiv neg n).val.1
      (i0MiddleRowEquiv neg n).val.2.1 (i0MiddleRowEquiv neg n).val.2.2 0 =
      (2 * (n.2.2 : ℤ) + 2, (if neg then (n.1 : ℤ) + 1 else n.1) + 2 * n.2.1) := by
  rw [← tableZero_correct]
  cases neg <;> simp only [i0MiddleRowEquiv, Equiv.coe_fn_mk, Bool.false_eq_true, ↓reduceIte]
  all_goals unfold tableZero; split_ifs <;> simp only [Prod.mk.injEq, and_true, true_and] <;> omega

theorem i0LowerRow_cartan (neg : Bool) (n : ℕ × ℕ × ℕ) :
    cartanIndices 0 (i0LowerRowEquiv neg n).val.1
      (i0LowerRowEquiv neg n).val.2.1 (i0LowerRowEquiv neg n).val.2.2 0 =
      (2 * (n.2.1 : ℤ) + 2 * n.2.2 + 4, if neg then (n.1 : ℤ) + 1 else n.1) := by
  rw [← tableZero_correct]
  cases neg <;> simp only [i0LowerRowEquiv, Equiv.coe_fn_mk, Bool.false_eq_true, ↓reduceIte]
  all_goals unfold tableZero; split_ifs <;> simp only [Prod.mk.injEq, and_true, true_and] <;> omega

theorem i0UpperRow_cartan (neg : Bool) (e : Fin 2) (n : ℕ × ℕ × ℕ) :
    cartanIndices 0 (i0UpperRowEquiv neg (e, n)).val.1
      (i0UpperRowEquiv neg (e, n)).val.2.1 (i0UpperRowEquiv neg (e, n)).val.2.2 0 =
      (0, (if neg then (n.1 : ℤ) + 1 else n.1) + 2 * n.2.1 + e.val + 1) := by
  have he := e.isLt
  rw [← tableZero_correct]
  cases neg <;> simp only [i0UpperRowEquiv, Equiv.coe_fn_mk, Bool.false_eq_true, ↓reduceIte]
  all_goals unfold tableZero; split_ifs <;> simp only [Prod.mk.injEq, and_true, true_and] <;> omega

/-- The first valuation coordinate has a nonnegative geometric parameter,
with an extra first-shell factor on its strictly negative branch. -/
def i0KRatio (neg : Bool) (t d V T : ℂ) : ℂ :=
  if neg then T * V * t / d else d * T * V * t

def i0KInitial (neg : Bool) (t d V T : ℂ) : ℂ :=
  if neg then T * V * t / d else 1

theorem i0_middle_reindexed (neg : Bool) (t d U V T : ℂ) (n : ℕ × ℕ × ℕ) :
    i0Shell t d U V T (i0MiddleRowEquiv neg n).val =
      ((1 - t ^ 2) ^ 2 * i0KInitial neg t d V T * (T * U * t ^ 2)) *
        (i0KRatio neg t d V T) ^ n.1 * ((T * V) ^ 2 * t ^ 2) ^ n.2.1 *
        (T * U * t ^ 2) ^ n.2.2 := by
  unfold i0Shell
  rw [i0MiddleRow_cartan]
  cases neg <;> simp only [i0MiddleRowEquiv, Equiv.coe_fn_mk, i0KInitial,
    i0KRatio, Bool.false_eq_true, ↓reduceIte]
  · have he : 3 * (n.1 : ℤ) + 2 * (-(2 * (n.1 : ℤ)) - 2 * n.2.1 - n.2.2 - 1) +
        2 * (-(n.1 : ℤ) - n.2.1 - n.2.2 - 1) + 3 * (2 * n.2.2 + 2) +
        4 * (n.1 + 2 * n.2.1) = ((n.1 + 2 * n.2.1 + 2 * n.2.2 + 2 : ℕ) : ℤ) := by omega
    have hb : (n.1 : ℤ) + 2 * n.2.1 = ((n.1 + 2 * n.2.1 : ℕ) : ℤ) := by omega
    have hl : (2 * (n.2.2 : ℤ) + 2) / 2 = ((n.2.2 + 1 : ℕ) : ℤ) := by omega
    rw [he, hb, hl]
    simp only [zpow_natCast, pow_add, pow_mul, mul_pow, pow_one]
    ring
  · have he : 3 * (-(n.1 : ℤ) - 1) + 2 * (-0 - 2 * (n.2.1 : ℤ) - n.2.2 - 1) +
        2 * (-0 - (n.2.1 : ℤ) - n.2.2 - 1) + 3 * (2 * n.2.2 + 2) +
        4 * (n.1 + 1 + 2 * n.2.1) = ((n.1 + 1 + 2 * n.2.1 + 2 * n.2.2 + 2 : ℕ) : ℤ) := by omega
    have hb : (n.1 : ℤ) + 1 + 2 * n.2.1 = ((n.1 + 1 + 2 * n.2.1 : ℕ) : ℤ) := by omega
    have hl : (2 * (n.2.2 : ℤ) + 2) / 2 = ((n.2.2 + 1 : ℕ) : ℤ) := by omega
    have hk : -(n.1 : ℤ) - 1 = -((n.1 + 1 : ℕ) : ℤ) := by omega
    rw [he, hb, hl, hk]
    simp only [zpow_neg, zpow_natCast, pow_add, pow_mul, mul_pow, pow_one,
      mul_inv_rev, div_eq_mul_inv, inv_pow]
    ring

theorem i0_lower_reindexed (neg : Bool) (t d U V T : ℂ) (n : ℕ × ℕ × ℕ) :
    i0Shell t d U V T (i0LowerRowEquiv neg n).val =
      ((1 - t ^ 2) ^ 2 * i0KInitial neg t d V T * (T * U * t ^ 2) *
        (T * U * t ^ 4)) * (i0KRatio neg t d V T) ^ n.1 *
        (T * U * t ^ 2) ^ n.2.1 * (T * U * t ^ 4) ^ n.2.2 := by
  unfold i0Shell
  rw [i0LowerRow_cartan]
  cases neg <;> simp only [i0LowerRowEquiv, Equiv.coe_fn_mk, i0KInitial,
    i0KRatio, Bool.false_eq_true, ↓reduceIte]
  · have he : 3 * (n.1 : ℤ) + 2 * (-(2 * (n.1 : ℤ)) - n.2.1 - 1) +
        2 * (-(n.1 : ℤ) - n.2.1 - n.2.2 - 2) +
        3 * (2 * n.2.1 + 2 * n.2.2 + 4) + 4 * n.1 =
        ((n.1 + 2 * n.2.1 + 4 * n.2.2 + 6 : ℕ) : ℤ) := by omega
    have hl : (2 * (n.2.1 : ℤ) + 2 * n.2.2 + 4) / 2 =
        ((n.2.1 + n.2.2 + 2 : ℕ) : ℤ) := by omega
    rw [he, hl]
    simp only [zpow_natCast, pow_add, pow_mul, mul_pow, pow_one]
    ring
  · have he : 3 * (-(n.1 : ℤ) - 1) + 2 * (-0 - (n.2.1 : ℤ) - 1) +
        2 * (-0 - (n.2.1 : ℤ) - n.2.2 - 2) +
        3 * (2 * n.2.1 + 2 * n.2.2 + 4) + 4 * (n.1 + 1) =
        ((n.1 + 1 + 2 * n.2.1 + 4 * n.2.2 + 6 : ℕ) : ℤ) := by omega
    have hl : (2 * (n.2.1 : ℤ) + 2 * n.2.2 + 4) / 2 =
        ((n.2.1 + n.2.2 + 2 : ℕ) : ℤ) := by omega
    have hb : (n.1 : ℤ) + 1 = ((n.1 + 1 : ℕ) : ℤ) := by omega
    have hk : -(n.1 : ℤ) - 1 = -((n.1 + 1 : ℕ) : ℤ) := by omega
    rw [he, hl, hb, hk]
    simp only [zpow_neg, zpow_natCast, pow_add, pow_mul, mul_pow, pow_one,
      mul_inv_rev, div_eq_mul_inv, inv_pow]
    ring

theorem i0_upper_reindexed (neg : Bool) (t d U V T : ℂ) (e : Fin 2) (n : ℕ × ℕ × ℕ) :
    i0Shell t d U V T (i0UpperRowEquiv neg (e, n)).val =
      ((1 - t ^ 2) ^ 2 * i0KInitial neg t d V T * (T * V) ^ (e.val + 1) * t ^ 2) *
        (i0KRatio neg t d V T) ^ n.1 * ((T * V) ^ 2 * t ^ 2) ^ n.2.1 *
        (t ^ 2) ^ n.2.2 := by
  unfold i0Shell
  rw [i0UpperRow_cartan]
  cases neg <;> simp only [i0UpperRowEquiv, Equiv.coe_fn_mk, i0KInitial,
    i0KRatio, Bool.false_eq_true, ↓reduceIte]
  · have he : 3 * (n.1 : ℤ) +
        2 * (-(2 * (n.1 : ℤ)) - 2 * n.2.1 - e.val - 1) +
        2 * (-(n.1 : ℤ) - n.2.1 - e.val + n.2.2) +
        3 * 0 + 4 * (n.1 + 2 * n.2.1 + e.val + 1) =
        ((n.1 + 2 * n.2.1 + 2 * n.2.2 + 2 : ℕ) : ℤ) := by omega
    have hb : (n.1 : ℤ) + 2 * n.2.1 + e.val + 1 =
        ((n.1 + 2 * n.2.1 + e.val + 1 : ℕ) : ℤ) := by omega
    rw [he, hb]
    simp only [zero_div, Int.zero_ediv, zpow_zero, pow_zero, mul_one, zpow_natCast, pow_add, pow_mul, mul_pow, pow_one]
    ring
  · have he : 3 * (-(n.1 : ℤ) - 1) +
        2 * (-0 - 2 * (n.2.1 : ℤ) - e.val - 1) +
        2 * (-0 - (n.2.1 : ℤ) - e.val + n.2.2) +
        3 * 0 + 4 * (n.1 + 1 + 2 * n.2.1 + e.val + 1) =
        ((n.1 + 1 + 2 * n.2.1 + 2 * n.2.2 + 2 : ℕ) : ℤ) := by omega
    have hb : (n.1 : ℤ) + 1 + 2 * n.2.1 + e.val + 1 =
        ((n.1 + 1 + 2 * n.2.1 + e.val + 1 : ℕ) : ℤ) := by omega
    have hk : -(n.1 : ℤ) - 1 = -((n.1 + 1 : ℕ) : ℤ) := by omega
    rw [he, hb, hk]
    simp only [zero_div, Int.zero_ediv, zpow_zero, pow_zero, mul_one, zpow_neg, zpow_natCast, pow_add,
      pow_mul, mul_pow, pow_one, mul_inv_rev, div_eq_mul_inv, inv_pow]
    ring

/-- A norm bound implies a genuine geometric denominator is nonzero. -/
theorem i0_one_sub_ne_zero {z : ℂ} (hz : ‖z‖ < 1) : 1 - z ≠ 0 := by
  intro he
  have hz1 : z = 1 := (sub_eq_zero.mp he).symm
  simp [hz1] at hz

theorem summable_norm_i0_middle (neg : Bool) (t d U V T : ℂ)
    (hK : ‖i0KRatio neg t d V T‖ < 1)
    (hE : ‖(T * V) ^ 2 * t ^ 2‖ < 1) (hF : ‖T * U * t ^ 2‖ < 1) :
    Summable (fun p : I0MiddleRow neg => ‖i0Shell t d U V T p.val‖) := by
  apply (i0MiddleRowEquiv neg).summable_iff.mp
  convert summable_norm_three_geometric
    ((1 - t ^ 2) ^ 2 * i0KInitial neg t d V T * (T * U * t ^ 2))
    (i0KRatio neg t d V T) ((T * V) ^ 2 * t ^ 2) (T * U * t ^ 2) hK hE hF using 1
  exact funext fun n => congrArg norm (i0_middle_reindexed neg t d U V T n)

theorem hasSum_i0_middle (neg : Bool) (t d U V T : ℂ)
    (hK : ‖i0KRatio neg t d V T‖ < 1)
    (hE : ‖(T * V) ^ 2 * t ^ 2‖ < 1) (hF : ‖T * U * t ^ 2‖ < 1) :
    HasSum (fun p : I0MiddleRow neg => i0Shell t d U V T p.val)
      (((1 - t ^ 2) ^ 2 * i0KInitial neg t d V T * (T * U * t ^ 2)) *
        (1 - i0KRatio neg t d V T)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ *
        (1 - T * U * t ^ 2)⁻¹) := by
  apply (i0MiddleRowEquiv neg).hasSum_iff.mp
  convert hasSum_three_geometric
    ((1 - t ^ 2) ^ 2 * i0KInitial neg t d V T * (T * U * t ^ 2))
    (i0KRatio neg t d V T) ((T * V) ^ 2 * t ^ 2) (T * U * t ^ 2) hK hE hF using 1
  exact funext fun n => i0_middle_reindexed neg t d U V T n

theorem summable_norm_i0_lower (neg : Bool) (t d U V T : ℂ)
    (hK : ‖i0KRatio neg t d V T‖ < 1)
    (hF : ‖T * U * t ^ 2‖ < 1) (hG : ‖T * U * t ^ 4‖ < 1) :
    Summable (fun p : I0LowerRow neg => ‖i0Shell t d U V T p.val‖) := by
  apply (i0LowerRowEquiv neg).summable_iff.mp
  convert summable_norm_three_geometric
    ((1 - t ^ 2) ^ 2 * i0KInitial neg t d V T * (T * U * t ^ 2) * (T * U * t ^ 4))
    (i0KRatio neg t d V T) (T * U * t ^ 2) (T * U * t ^ 4) hK hF hG using 1
  exact funext fun n => congrArg norm (i0_lower_reindexed neg t d U V T n)

theorem hasSum_i0_lower (neg : Bool) (t d U V T : ℂ)
    (hK : ‖i0KRatio neg t d V T‖ < 1)
    (hF : ‖T * U * t ^ 2‖ < 1) (hG : ‖T * U * t ^ 4‖ < 1) :
    HasSum (fun p : I0LowerRow neg => i0Shell t d U V T p.val)
      (((1 - t ^ 2) ^ 2 * i0KInitial neg t d V T * (T * U * t ^ 2) * (T * U * t ^ 4)) *
        (1 - i0KRatio neg t d V T)⁻¹ * (1 - T * U * t ^ 2)⁻¹ * (1 - T * U * t ^ 4)⁻¹) := by
  apply (i0LowerRowEquiv neg).hasSum_iff.mp
  convert hasSum_three_geometric
    ((1 - t ^ 2) ^ 2 * i0KInitial neg t d V T * (T * U * t ^ 2) * (T * U * t ^ 4))
    (i0KRatio neg t d V T) (T * U * t ^ 2) (T * U * t ^ 4) hK hF hG using 1
  exact funext fun n => i0_lower_reindexed neg t d U V T n

theorem summable_norm_i0_upper_reindexed (neg : Bool) (t d U V T : ℂ)
    (ht : ‖t ^ 2‖ < 1) (hK : ‖i0KRatio neg t d V T‖ < 1)
    (hE : ‖(T * V) ^ 2 * t ^ 2‖ < 1) :
    Summable (fun n : Fin 2 × ℕ × ℕ × ℕ =>
      ‖i0Shell t d U V T (i0UpperRowEquiv neg n).val‖) := by
  apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
  refine ⟨?_, (hasSum_fintype _).summable⟩
  intro e
  convert summable_norm_three_geometric
    ((1 - t ^ 2) ^ 2 * i0KInitial neg t d V T * (T * V) ^ (e.val + 1) * t ^ 2)
    (i0KRatio neg t d V T) ((T * V) ^ 2 * t ^ 2) (t ^ 2) hK hE ht using 1
  exact funext fun n => congrArg norm (i0_upper_reindexed neg t d U V T e n)

theorem summable_norm_i0_upper (neg : Bool) (t d U V T : ℂ)
    (ht : ‖t ^ 2‖ < 1) (hK : ‖i0KRatio neg t d V T‖ < 1)
    (hE : ‖(T * V) ^ 2 * t ^ 2‖ < 1) :
    Summable (fun p : I0UpperRow neg => ‖i0Shell t d U V T p.val‖) :=
  (i0UpperRowEquiv neg).summable_iff.mp
    (summable_norm_i0_upper_reindexed neg t d U V T ht hK hE)

theorem hasSum_i0_upper (neg : Bool) (t d U V T : ℂ)
    (ht : ‖t ^ 2‖ < 1) (hK : ‖i0KRatio neg t d V T‖ < 1)
    (hE : ‖(T * V) ^ 2 * t ^ 2‖ < 1) :
    HasSum (fun p : I0UpperRow neg => i0Shell t d U V T p.val)
      ((1 - t ^ 2) * i0KInitial neg t d V T * (T * V) * (1 + T * V) * t ^ 2 *
        (1 - i0KRatio neg t d V T)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹) := by
  have hs := (summable_norm_i0_upper_reindexed neg t d U V T ht hK hE).of_norm
  have hrow (e : Fin 2) :
      (∑' n : ℕ × ℕ × ℕ, i0Shell t d U V T (i0UpperRowEquiv neg (e, n)).val) =
      ((1 - t ^ 2) ^ 2 * i0KInitial neg t d V T * (T * V) ^ (e.val + 1) * t ^ 2) *
        (1 - i0KRatio neg t d V T)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹ := by
    simp_rw [i0_upper_reindexed]
    exact (hasSum_three_geometric _ _ _ _ hK hE ht).tsum_eq
  have he : (∑' n : Fin 2 × ℕ × ℕ × ℕ, i0Shell t d U V T (i0UpperRowEquiv neg n).val) =
      (1 - t ^ 2) * i0KInitial neg t d V T * (T * V) * (1 + T * V) * t ^ 2 *
        (1 - i0KRatio neg t d V T)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ := by
    rw [hs.tsum_prod]
    simp_rw [hrow]
    rw [tsum_fintype, Fin.sum_univ_two]
    norm_num only [Fin.val_zero, Fin.val_one, zero_add, one_add_one_eq_two, pow_one]
    have ht0 := i0_one_sub_ne_zero ht
    have hK0 := i0_one_sub_ne_zero hK
    have hE0 := i0_one_sub_ne_zero hE
    field_simp [ht0, hK0, hE0]
  apply (i0UpperRowEquiv neg).hasSum_iff.mp
  exact he ▸ hs.hasSum

theorem hasSum_i0_case3_regionTerm (t d U V T : ℂ)
    (ht : ‖t ^ 2‖ < 1) (hP : ‖d * T * V * t‖ < 1)
    (hE : ‖(T * V) ^ 2 * t ^ 2‖ < 1) :
    HasSum (fun p : I0UpperRow false => i0Shell t d U V T p.val)
      (Algebra.regionTerms t d (T * U) (T * V) 2) := by
  convert hasSum_i0_upper false t d U V T ht hP hE using 1
  change Algebra.regionTerm2 t d (T * U) (T * V)
    (1 - d * (T * V) * t) (1 - (T * V) * t / d)
    (1 - (T * V) ^ 2 * t ^ 2) (1 - (T * U) * t ^ 2)
    (1 - (T * U) * t ^ 4) = _
  simp only [Algebra.regionTerm2,
    Matrix.cons_val_zero, Matrix.cons_val_succ, i0KInitial, i0KRatio,
    Bool.false_eq_true, ↓reduceIte, pow_one, div_eq_mul_inv, mul_inv_rev, mul_assoc]
  ring

theorem hasSum_i0_case4_regionTerm (t d U V T : ℂ)
    (hP : ‖d * T * V * t‖ < 1) (hE : ‖(T * V) ^ 2 * t ^ 2‖ < 1)
    (hF : ‖T * U * t ^ 2‖ < 1) :
    HasSum (fun p : I0MiddleRow false => i0Shell t d U V T p.val)
      (Algebra.regionTerms t d (T * U) (T * V) 3) := by
  convert hasSum_i0_middle false t d U V T hP hE hF using 1
  change Algebra.regionTerm3 t d (T * U) (T * V)
    (1 - d * (T * V) * t) (1 - (T * V) * t / d)
    (1 - (T * V) ^ 2 * t ^ 2) (1 - (T * U) * t ^ 2)
    (1 - (T * U) * t ^ 4) = _
  simp only [Algebra.regionTerm3,
    Matrix.cons_val_zero, Matrix.cons_val_succ, i0KInitial, i0KRatio,
    Bool.false_eq_true, ↓reduceIte, pow_one, div_eq_mul_inv, mul_inv_rev, mul_assoc]
  ring

theorem hasSum_i0_case5_regionTerm (t d U V T : ℂ)
    (hP : ‖d * T * V * t‖ < 1) (hF : ‖T * U * t ^ 2‖ < 1)
    (hG : ‖T * U * t ^ 4‖ < 1) :
    HasSum (fun p : I0LowerRow false => i0Shell t d U V T p.val)
      (Algebra.regionTerms t d (T * U) (T * V) 4) := by
  convert hasSum_i0_lower false t d U V T hP hF hG using 1
  change Algebra.regionTerm4 t d (T * U) (T * V)
    (1 - d * (T * V) * t) (1 - (T * V) * t / d)
    (1 - (T * V) ^ 2 * t ^ 2) (1 - (T * U) * t ^ 2)
    (1 - (T * U) * t ^ 4) = _
  simp only [Algebra.regionTerm4,
    Matrix.cons_val_zero, Matrix.cons_val_succ, i0KInitial, i0KRatio,
    Bool.false_eq_true, ↓reduceIte, pow_one, div_eq_mul_inv, mul_inv_rev, mul_assoc]
  ring

theorem hasSum_i0_case8_regionTerm (t d U V T : ℂ)
    (ht : ‖t ^ 2‖ < 1) (hN : ‖T * V * t / d‖ < 1)
    (hE : ‖(T * V) ^ 2 * t ^ 2‖ < 1) :
    HasSum (fun p : I0UpperRow true => i0Shell t d U V T p.val)
      (Algebra.regionTerms t d (T * U) (T * V) 7) := by
  convert hasSum_i0_upper true t d U V T ht hN hE using 1
  change Algebra.regionTerm7 t d (T * U) (T * V)
    (1 - d * (T * V) * t) (1 - (T * V) * t / d)
    (1 - (T * V) ^ 2 * t ^ 2) (1 - (T * U) * t ^ 2)
    (1 - (T * U) * t ^ 4) = _
  simp only [Algebra.regionTerm7,
    Matrix.cons_val_zero, Matrix.cons_val_succ, i0KInitial, i0KRatio,
    ↓reduceIte, pow_one, div_eq_mul_inv, mul_inv_rev, mul_assoc]
  ring

theorem hasSum_i0_case9_regionTerm (t d U V T : ℂ)
    (hN : ‖T * V * t / d‖ < 1) (hE : ‖(T * V) ^ 2 * t ^ 2‖ < 1)
    (hF : ‖T * U * t ^ 2‖ < 1) :
    HasSum (fun p : I0MiddleRow true => i0Shell t d U V T p.val)
      (Algebra.regionTerms t d (T * U) (T * V) 8) := by
  convert hasSum_i0_middle true t d U V T hN hE hF using 1
  change Algebra.regionTerm8 t d (T * U) (T * V)
    (1 - d * (T * V) * t) (1 - (T * V) * t / d)
    (1 - (T * V) ^ 2 * t ^ 2) (1 - (T * U) * t ^ 2)
    (1 - (T * U) * t ^ 4) = _
  simp only [Algebra.regionTerm8,
    Matrix.cons_val_zero, Matrix.cons_val_succ, i0KInitial, i0KRatio,
    ↓reduceIte, pow_one, div_eq_mul_inv, mul_inv_rev, mul_assoc]
  ring

theorem hasSum_i0_case10_regionTerm (t d U V T : ℂ)
    (hN : ‖T * V * t / d‖ < 1) (hF : ‖T * U * t ^ 2‖ < 1)
    (hG : ‖T * U * t ^ 4‖ < 1) :
    HasSum (fun p : I0LowerRow true => i0Shell t d U V T p.val)
      (Algebra.regionTerms t d (T * U) (T * V) 9) := by
  convert hasSum_i0_lower true t d U V T hN hF hG using 1
  change Algebra.regionTerm9 t d (T * U) (T * V)
    (1 - d * (T * V) * t) (1 - (T * V) * t / d)
    (1 - (T * V) ^ 2 * t ^ 2) (1 - (T * U) * t ^ 2)
    (1 - (T * U) * t ^ 4) = _
  simp only [Algebra.regionTerm9,
    Matrix.cons_val_zero, Matrix.cons_val_succ, i0KInitial, i0KRatio,
    ↓reduceIte, pow_one, div_eq_mul_inv, mul_inv_rev, mul_assoc]
  ring

/-- The ten simultaneous integer conditions of `I0eq3`, in source order.
This is an actual partition of the entire lattice, without any cutoff. -/
def i0Region (i : Fin 10) : Set (ℤ × ℤ × ℤ) :=
  match i.val with
  | 0 => {p | 0 ≤ p.1 ∧ -2 * p.1 ≤ p.2.1 ∧ -p.1 ≤ p.2.2}
  | 1 => {p | 0 ≤ p.1 ∧ -2 * p.1 ≤ p.2.1 ∧ p.2.2 < -p.1}
  | 2 => {p | 0 ≤ p.1 ∧ p.2.1 < -2 * p.1 ∧ p.1 + p.2.1 ≤ p.2.2 ∧ p.2.1 ≤ 2 * p.2.2}
  | 3 => {p | 0 ≤ p.1 ∧ p.2.1 < -2 * p.1 ∧ p.1 + p.2.1 ≤ p.2.2 ∧ 2 * p.2.2 < p.2.1}
  | 4 => {p | 0 ≤ p.1 ∧ p.2.1 < -2 * p.1 ∧ p.2.2 < p.1 + p.2.1}
  | 5 => {p | p.1 < 0 ∧ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2}
  | 6 => {p | p.1 < 0 ∧ 0 ≤ p.2.1 ∧ p.2.2 < 0}
  | 7 => {p | p.1 < 0 ∧ p.2.1 < 0 ∧ p.2.1 ≤ p.2.2 ∧ p.2.1 ≤ 2 * p.2.2}
  | 8 => {p | p.1 < 0 ∧ p.2.1 < 0 ∧ p.2.1 ≤ p.2.2 ∧ 2 * p.2.2 < p.2.1}
  | _ => {p | p.1 < 0 ∧ p.2.1 < 0 ∧ p.2.2 < p.2.1}

def i0RegionIndex (p : ℤ × ℤ × ℤ) : Fin 10 :=
  if 0 ≤ p.1 then
    if -2 * p.1 ≤ p.2.1 then
      if -p.1 ≤ p.2.2 then 0 else 1
    else if p.2.2 < p.1 + p.2.1 then 4
    else if p.2.1 ≤ 2 * p.2.2 then 2 else 3
  else
    if 0 ≤ p.2.1 then
      if 0 ≤ p.2.2 then 5 else 6
    else if p.2.2 < p.2.1 then 9
    else if p.2.1 ≤ 2 * p.2.2 then 7 else 8

theorem i0RegionIndex_mem (p : ℤ × ℤ × ℤ) : p ∈ i0Region (i0RegionIndex p) := by
  unfold i0RegionIndex
  split_ifs <;> norm_num [i0Region] <;> omega

theorem i0Region_unique (p : ℤ × ℤ × ℤ) (i j : Fin 10)
    (hi : p ∈ i0Region i) (hj : p ∈ i0Region j) : i = j := by
  fin_cases i <;> fin_cases j <;>
    simp only [i0Region, Matrix.cons_val_zero, Matrix.cons_val_succ, Set.mem_ofPred_eq] at hi hj
  all_goals first | rfl | omega

theorem i0Region_partition (p : ℤ × ℤ × ℤ) : ∃! i : Fin 10, p ∈ i0Region i :=
  ⟨i0RegionIndex p, i0RegionIndex_mem p, fun i hi =>
    i0Region_unique p i (i0RegionIndex p) hi (i0RegionIndex_mem p)⟩

/-- Every source row equals its already-restored stored fraction. The inherited
four rows are reused verbatim, and the six others are proved above. -/
theorem hasSum_i0_region (t d U V T : ℂ)
    (ht : ‖t ^ 2‖ < 1) (hP : ‖d * T * V * t‖ < 1)
    (hN : ‖T * V * t / d‖ < 1) (hE : ‖(T * V) ^ 2 * t ^ 2‖ < 1)
    (hF : ‖T * U * t ^ 2‖ < 1) (hG : ‖T * U * t ^ 4‖ < 1) (i : Fin 10) :
    HasSum (fun p : i0Region i => i0Shell t d U V T p.val)
      (Algebra.regionTerms t d (T * U) (T * V) (i.castLE (by decide))) := by
  fin_cases i
  · exact hasSum_i0_case1_regionTerm t d U V T ht hP
  · exact hasSum_i0_case2_regionTerm t d U V T ht hP hG
  · exact hasSum_i0_case3_regionTerm t d U V T ht hP hE
  · exact hasSum_i0_case4_regionTerm t d U V T hP hE hF
  · exact hasSum_i0_case5_regionTerm t d U V T hP hF hG
  · exact hasSum_i0_case6_regionTerm t d U V T ht hN
  · exact hasSum_i0_case7_regionTerm t d U V T ht hN hG
  · exact hasSum_i0_case8_regionTerm t d U V T ht hN hE
  · exact hasSum_i0_case9_regionTerm t d U V T hN hE hF
  · exact hasSum_i0_case10_regionTerm t d U V T hN hF hG

/-- Absolute convergence is established on the full independent lattice
before the regions are combined. This statement is stronger than existence
of an iterated sum. -/
theorem summable_norm_i0_full (t d U V T : ℂ)
    (ht : ‖t ^ 2‖ < 1) (hP : ‖d * T * V * t‖ < 1)
    (hN : ‖T * V * t / d‖ < 1) (hE : ‖(T * V) ^ 2 * t ^ 2‖ < 1)
    (hF : ‖T * U * t ^ 2‖ < 1) (hG : ‖T * U * t ^ 4‖ < 1) :
    Summable (fun p : ℤ × ℤ × ℤ => ‖i0Shell t d U V T p‖) := by
  apply (summable_partition (fun _ => norm_nonneg _) i0Region_partition).mpr
  refine ⟨?_, (hasSum_fintype _).summable⟩
  intro i
  have h4 := i0_four_rows_absolutelySummable t d U V T ht hP hN hG
  fin_cases i
  · exact h4.1
  · exact h4.2.1
  · exact summable_norm_i0_upper false t d U V T ht hP hE
  · exact summable_norm_i0_middle false t d U V T hP hE hF
  · exact summable_norm_i0_lower false t d U V T hP hF hG
  · exact h4.2.2.1
  · exact h4.2.2.2
  · exact summable_norm_i0_upper true t d U V T ht hN hE
  · exact summable_norm_i0_middle true t d U V T hN hE hF
  · exact summable_norm_i0_lower true t d U V T hN hF hG

/-- Complete evaluation of the independently defined zero-central-coordinate
valuation series. The sum on the right is exactly rows 0--9 of the stored
fifty-row expression, with damping inserted in the unsummed monomial. -/
theorem hasSum_i0_full (t d U V T : ℂ)
    (ht : ‖t ^ 2‖ < 1) (hP : ‖d * T * V * t‖ < 1)
    (hN : ‖T * V * t / d‖ < 1) (hE : ‖(T * V) ^ 2 * t ^ 2‖ < 1)
    (hF : ‖T * U * t ^ 2‖ < 1) (hG : ‖T * U * t ^ 4‖ < 1) :
    HasSum (fun p : ℤ × ℤ × ℤ => i0Shell t d U V T p)
      (∑ i : Fin 10, Algebra.regionTerms t d (T * U) (T * V) (i.castLE (by decide))) := by
  let e := Set.sigmaEquiv i0Region i0Region_partition
  have hs := (summable_norm_i0_full t d U V T ht hP hN hE hF hG).of_norm
  have hs' : Summable (fun p : Σ i : Fin 10, i0Region i => i0Shell t d U V T p.2.val) :=
    e.summable_iff.mpr hs
  apply e.hasSum_iff.mp
  exact (hasSum_fintype _).sigma_of_hasSum
    (hasSum_i0_region t d U V T ht hP hN hE hF hG) hs'

theorem tsum_i0_full (t d U V T : ℂ)
    (ht : ‖t ^ 2‖ < 1) (hP : ‖d * T * V * t‖ < 1)
    (hN : ‖T * V * t / d‖ < 1) (hE : ‖(T * V) ^ 2 * t ^ 2‖ < 1)
    (hF : ‖T * U * t ^ 2‖ < 1) (hG : ‖T * U * t ^ 4‖ < 1) :
    (∑' p : ℤ × ℤ × ℤ, i0Shell t d U V T p) =
      ∑ i : Fin 10, Algebra.regionTerms t d (T * U) (T * V) (i.castLE (by decide)) :=
  (hasSum_i0_full t d U V T ht hP hN hE hF hG).tsum_eq

end FourierJacobi.Analysis





