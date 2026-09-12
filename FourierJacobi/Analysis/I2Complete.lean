import FourierJacobi.Analysis.I2Domains
import FourierJacobi.Analysis.I2Convergence

/-!
Independent infinite spatial sums for every I2 row. The unsummed terms use
the integer Cartan minima. Cancellation-depth masses are explicit; they are
the sum of the specified depth strata, not assumed geometric row fractions.
The separate depth bridge must identify these spatial sums with the full
four-coordinate master family before a complete I2 lattice theorem is claimed.
-/

noncomputable section

namespace FourierJacobi.Analysis

open FourierJacobi.Valuations

set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
-- Uniform generated proofs share simplifiers and arithmetic clearing tactics.
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

def i2DepthAt (ν : Fin 25) : ℕ :=
  if ν.val = 5 ∨ ν.val = 21 then 1
  else if ν.val = 6 ∨ ν.val = 22 then 2 else 0

def i2DepthMass (q : ℂ) (ν : Fin 25) : ℂ :=
  if ν.val = 4 ∨ ν.val = 20 then (q - 2) / (q - 1)
  else if ν.val = 5 ∨ ν.val = 21 then q⁻¹
  else if ν.val = 6 ∨ ν.val = 22 then q⁻¹ ^ 2 / (1 - q⁻¹) else 1

def i2SpatialTerm (q t d U V T : ℂ) (ν : Fin 25) (p : ℤ × ℤ × ℤ) : ℂ :=
  -q * shellMonomial t d U V T 2 p (i2DepthAt ν) * i2DepthMass q ν

def i2RegionTerm (ν : Fin 25) (t d U V : ℂ) : ℂ :=
  let P := 1 - d * V * t
  let N := 1 - V * t / d
  let E := 1 - V ^ 2 * t ^ 2
  let F := 1 - U * t ^ 2
  let G := 1 - U * t ^ 4
  match ν.val with
  | 0 => Algebra.regionTerm25 t d U V P N E F G
  | 1 => Algebra.regionTerm26 t d U V P N E F G
  | 2 => Algebra.regionTerm27 t d U V P N E F G
  | 3 => Algebra.regionTerm28 t d U V P N E F G
  | 4 => Algebra.regionTerm29 t d U V P N E F G
  | 5 => Algebra.regionTerm30 t d U V P N E F G
  | 6 => Algebra.regionTerm31 t d U V P N E F G
  | 7 => Algebra.regionTerm32 t d U V P N E F G
  | 8 => Algebra.regionTerm33 t d U V P N E F G
  | 9 => Algebra.regionTerm34 t d U V P N E F G
  | 10 => Algebra.regionTerm35 t d U V P N E F G
  | 11 => Algebra.regionTerm36 t d U V P N E F G
  | 12 => Algebra.regionTerm37 t d U V P N E F G
  | 13 => Algebra.regionTerm38 t d U V P N E F G
  | 14 => Algebra.regionTerm39 t d U V P N E F G
  | 15 => Algebra.regionTerm40 t d U V P N E F G
  | 16 => Algebra.regionTerm41 t d U V P N E F G
  | 17 => Algebra.regionTerm42 t d U V P N E F G
  | 18 => Algebra.regionTerm43 t d U V P N E F G
  | 19 => Algebra.regionTerm44 t d U V P N E F G
  | 20 => Algebra.regionTerm45 t d U V P N E F G
  | 21 => Algebra.regionTerm46 t d U V P N E F G
  | 22 => Algebra.regionTerm47 t d U V P N E F G
  | 23 => Algebra.regionTerm48 t d U V P N E F G
  | _ => Algebra.regionTerm49 t d U V P N E F G

@[simp] theorem i2DepthAt_row0 : i2DepthAt 0 = 0 := rfl
@[simp] theorem i2DepthMass_row0 (q : ℂ) : i2DepthMass q 0 = 1 := rfl
@[simp] theorem i2RegionTerm_row0 (t d U V : ℂ) :
    i2RegionTerm 0 t d U V = Algebra.regionTerm25 t d U V
      (1 - d * V * t) (1 - V * t / d) (1 - V ^ 2 * t ^ 2)
      (1 - U * t ^ 2) (1 - U * t ^ 4) := rfl

@[simp] theorem i2DepthAt_row1 : i2DepthAt 1 = 0 := rfl
@[simp] theorem i2DepthMass_row1 (q : ℂ) : i2DepthMass q 1 = 1 := rfl
@[simp] theorem i2RegionTerm_row1 (t d U V : ℂ) :
    i2RegionTerm 1 t d U V = Algebra.regionTerm26 t d U V
      (1 - d * V * t) (1 - V * t / d) (1 - V ^ 2 * t ^ 2)
      (1 - U * t ^ 2) (1 - U * t ^ 4) := rfl

@[simp] theorem i2DepthAt_row2 : i2DepthAt 2 = 0 := rfl
@[simp] theorem i2DepthMass_row2 (q : ℂ) : i2DepthMass q 2 = 1 := rfl
@[simp] theorem i2RegionTerm_row2 (t d U V : ℂ) :
    i2RegionTerm 2 t d U V = Algebra.regionTerm27 t d U V
      (1 - d * V * t) (1 - V * t / d) (1 - V ^ 2 * t ^ 2)
      (1 - U * t ^ 2) (1 - U * t ^ 4) := rfl

@[simp] theorem i2DepthAt_row3 : i2DepthAt 3 = 0 := rfl
@[simp] theorem i2DepthMass_row3 (q : ℂ) : i2DepthMass q 3 = 1 := rfl
@[simp] theorem i2RegionTerm_row3 (t d U V : ℂ) :
    i2RegionTerm 3 t d U V = Algebra.regionTerm28 t d U V
      (1 - d * V * t) (1 - V * t / d) (1 - V ^ 2 * t ^ 2)
      (1 - U * t ^ 2) (1 - U * t ^ 4) := rfl

@[simp] theorem i2DepthAt_row4 : i2DepthAt 4 = 0 := rfl
@[simp] theorem i2DepthMass_row4 (q : ℂ) : i2DepthMass q 4 = (q - 2) / (q - 1) := rfl
@[simp] theorem i2RegionTerm_row4 (t d U V : ℂ) :
    i2RegionTerm 4 t d U V = Algebra.regionTerm29 t d U V
      (1 - d * V * t) (1 - V * t / d) (1 - V ^ 2 * t ^ 2)
      (1 - U * t ^ 2) (1 - U * t ^ 4) := rfl

@[simp] theorem i2DepthAt_row5 : i2DepthAt 5 = 1 := rfl
@[simp] theorem i2DepthMass_row5 (q : ℂ) : i2DepthMass q 5 = q⁻¹ := rfl
@[simp] theorem i2RegionTerm_row5 (t d U V : ℂ) :
    i2RegionTerm 5 t d U V = Algebra.regionTerm30 t d U V
      (1 - d * V * t) (1 - V * t / d) (1 - V ^ 2 * t ^ 2)
      (1 - U * t ^ 2) (1 - U * t ^ 4) := rfl

@[simp] theorem i2DepthAt_row6 : i2DepthAt 6 = 2 := rfl
@[simp] theorem i2DepthMass_row6 (q : ℂ) : i2DepthMass q 6 = q⁻¹ ^ 2 / (1 - q⁻¹) := rfl
@[simp] theorem i2RegionTerm_row6 (t d U V : ℂ) :
    i2RegionTerm 6 t d U V = Algebra.regionTerm31 t d U V
      (1 - d * V * t) (1 - V * t / d) (1 - V ^ 2 * t ^ 2)
      (1 - U * t ^ 2) (1 - U * t ^ 4) := rfl

@[simp] theorem i2DepthAt_row7 : i2DepthAt 7 = 0 := rfl
@[simp] theorem i2DepthMass_row7 (q : ℂ) : i2DepthMass q 7 = 1 := rfl
@[simp] theorem i2RegionTerm_row7 (t d U V : ℂ) :
    i2RegionTerm 7 t d U V = Algebra.regionTerm32 t d U V
      (1 - d * V * t) (1 - V * t / d) (1 - V ^ 2 * t ^ 2)
      (1 - U * t ^ 2) (1 - U * t ^ 4) := rfl

@[simp] theorem i2DepthAt_row8 : i2DepthAt 8 = 0 := rfl
@[simp] theorem i2DepthMass_row8 (q : ℂ) : i2DepthMass q 8 = 1 := rfl
@[simp] theorem i2RegionTerm_row8 (t d U V : ℂ) :
    i2RegionTerm 8 t d U V = Algebra.regionTerm33 t d U V
      (1 - d * V * t) (1 - V * t / d) (1 - V ^ 2 * t ^ 2)
      (1 - U * t ^ 2) (1 - U * t ^ 4) := rfl

@[simp] theorem i2DepthAt_row9 : i2DepthAt 9 = 0 := rfl
@[simp] theorem i2DepthMass_row9 (q : ℂ) : i2DepthMass q 9 = 1 := rfl
@[simp] theorem i2RegionTerm_row9 (t d U V : ℂ) :
    i2RegionTerm 9 t d U V = Algebra.regionTerm34 t d U V
      (1 - d * V * t) (1 - V * t / d) (1 - V ^ 2 * t ^ 2)
      (1 - U * t ^ 2) (1 - U * t ^ 4) := rfl

@[simp] theorem i2DepthAt_row10 : i2DepthAt 10 = 0 := rfl
@[simp] theorem i2DepthMass_row10 (q : ℂ) : i2DepthMass q 10 = 1 := rfl
@[simp] theorem i2RegionTerm_row10 (t d U V : ℂ) :
    i2RegionTerm 10 t d U V = Algebra.regionTerm35 t d U V
      (1 - d * V * t) (1 - V * t / d) (1 - V ^ 2 * t ^ 2)
      (1 - U * t ^ 2) (1 - U * t ^ 4) := rfl

@[simp] theorem i2DepthAt_row11 : i2DepthAt 11 = 0 := rfl
@[simp] theorem i2DepthMass_row11 (q : ℂ) : i2DepthMass q 11 = 1 := rfl
@[simp] theorem i2RegionTerm_row11 (t d U V : ℂ) :
    i2RegionTerm 11 t d U V = Algebra.regionTerm36 t d U V
      (1 - d * V * t) (1 - V * t / d) (1 - V ^ 2 * t ^ 2)
      (1 - U * t ^ 2) (1 - U * t ^ 4) := rfl

@[simp] theorem i2DepthAt_row12 : i2DepthAt 12 = 0 := rfl
@[simp] theorem i2DepthMass_row12 (q : ℂ) : i2DepthMass q 12 = 1 := rfl
@[simp] theorem i2RegionTerm_row12 (t d U V : ℂ) :
    i2RegionTerm 12 t d U V = Algebra.regionTerm37 t d U V
      (1 - d * V * t) (1 - V * t / d) (1 - V ^ 2 * t ^ 2)
      (1 - U * t ^ 2) (1 - U * t ^ 4) := rfl

@[simp] theorem i2DepthAt_row13 : i2DepthAt 13 = 0 := rfl
@[simp] theorem i2DepthMass_row13 (q : ℂ) : i2DepthMass q 13 = 1 := rfl
@[simp] theorem i2RegionTerm_row13 (t d U V : ℂ) :
    i2RegionTerm 13 t d U V = Algebra.regionTerm38 t d U V
      (1 - d * V * t) (1 - V * t / d) (1 - V ^ 2 * t ^ 2)
      (1 - U * t ^ 2) (1 - U * t ^ 4) := rfl

@[simp] theorem i2DepthAt_row14 : i2DepthAt 14 = 0 := rfl
@[simp] theorem i2DepthMass_row14 (q : ℂ) : i2DepthMass q 14 = 1 := rfl
@[simp] theorem i2RegionTerm_row14 (t d U V : ℂ) :
    i2RegionTerm 14 t d U V = Algebra.regionTerm39 t d U V
      (1 - d * V * t) (1 - V * t / d) (1 - V ^ 2 * t ^ 2)
      (1 - U * t ^ 2) (1 - U * t ^ 4) := rfl

@[simp] theorem i2DepthAt_row15 : i2DepthAt 15 = 0 := rfl
@[simp] theorem i2DepthMass_row15 (q : ℂ) : i2DepthMass q 15 = 1 := rfl
@[simp] theorem i2RegionTerm_row15 (t d U V : ℂ) :
    i2RegionTerm 15 t d U V = Algebra.regionTerm40 t d U V
      (1 - d * V * t) (1 - V * t / d) (1 - V ^ 2 * t ^ 2)
      (1 - U * t ^ 2) (1 - U * t ^ 4) := rfl

@[simp] theorem i2DepthAt_row16 : i2DepthAt 16 = 0 := rfl
@[simp] theorem i2DepthMass_row16 (q : ℂ) : i2DepthMass q 16 = 1 := rfl
@[simp] theorem i2RegionTerm_row16 (t d U V : ℂ) :
    i2RegionTerm 16 t d U V = Algebra.regionTerm41 t d U V
      (1 - d * V * t) (1 - V * t / d) (1 - V ^ 2 * t ^ 2)
      (1 - U * t ^ 2) (1 - U * t ^ 4) := rfl

@[simp] theorem i2DepthAt_row17 : i2DepthAt 17 = 0 := rfl
@[simp] theorem i2DepthMass_row17 (q : ℂ) : i2DepthMass q 17 = 1 := rfl
@[simp] theorem i2RegionTerm_row17 (t d U V : ℂ) :
    i2RegionTerm 17 t d U V = Algebra.regionTerm42 t d U V
      (1 - d * V * t) (1 - V * t / d) (1 - V ^ 2 * t ^ 2)
      (1 - U * t ^ 2) (1 - U * t ^ 4) := rfl

@[simp] theorem i2DepthAt_row18 : i2DepthAt 18 = 0 := rfl
@[simp] theorem i2DepthMass_row18 (q : ℂ) : i2DepthMass q 18 = 1 := rfl
@[simp] theorem i2RegionTerm_row18 (t d U V : ℂ) :
    i2RegionTerm 18 t d U V = Algebra.regionTerm43 t d U V
      (1 - d * V * t) (1 - V * t / d) (1 - V ^ 2 * t ^ 2)
      (1 - U * t ^ 2) (1 - U * t ^ 4) := rfl

@[simp] theorem i2DepthAt_row19 : i2DepthAt 19 = 0 := rfl
@[simp] theorem i2DepthMass_row19 (q : ℂ) : i2DepthMass q 19 = 1 := rfl
@[simp] theorem i2RegionTerm_row19 (t d U V : ℂ) :
    i2RegionTerm 19 t d U V = Algebra.regionTerm44 t d U V
      (1 - d * V * t) (1 - V * t / d) (1 - V ^ 2 * t ^ 2)
      (1 - U * t ^ 2) (1 - U * t ^ 4) := rfl

@[simp] theorem i2DepthAt_row20 : i2DepthAt 20 = 0 := rfl
@[simp] theorem i2DepthMass_row20 (q : ℂ) : i2DepthMass q 20 = (q - 2) / (q - 1) := rfl
@[simp] theorem i2RegionTerm_row20 (t d U V : ℂ) :
    i2RegionTerm 20 t d U V = Algebra.regionTerm45 t d U V
      (1 - d * V * t) (1 - V * t / d) (1 - V ^ 2 * t ^ 2)
      (1 - U * t ^ 2) (1 - U * t ^ 4) := rfl

@[simp] theorem i2DepthAt_row21 : i2DepthAt 21 = 1 := rfl
@[simp] theorem i2DepthMass_row21 (q : ℂ) : i2DepthMass q 21 = q⁻¹ := rfl
@[simp] theorem i2RegionTerm_row21 (t d U V : ℂ) :
    i2RegionTerm 21 t d U V = Algebra.regionTerm46 t d U V
      (1 - d * V * t) (1 - V * t / d) (1 - V ^ 2 * t ^ 2)
      (1 - U * t ^ 2) (1 - U * t ^ 4) := rfl

@[simp] theorem i2DepthAt_row22 : i2DepthAt 22 = 2 := rfl
@[simp] theorem i2DepthMass_row22 (q : ℂ) : i2DepthMass q 22 = q⁻¹ ^ 2 / (1 - q⁻¹) := rfl
@[simp] theorem i2RegionTerm_row22 (t d U V : ℂ) :
    i2RegionTerm 22 t d U V = Algebra.regionTerm47 t d U V
      (1 - d * V * t) (1 - V * t / d) (1 - V ^ 2 * t ^ 2)
      (1 - U * t ^ 2) (1 - U * t ^ 4) := rfl

@[simp] theorem i2DepthAt_row23 : i2DepthAt 23 = 0 := rfl
@[simp] theorem i2DepthMass_row23 (q : ℂ) : i2DepthMass q 23 = 1 := rfl
@[simp] theorem i2RegionTerm_row23 (t d U V : ℂ) :
    i2RegionTerm 23 t d U V = Algebra.regionTerm48 t d U V
      (1 - d * V * t) (1 - V * t / d) (1 - V ^ 2 * t ^ 2)
      (1 - U * t ^ 2) (1 - U * t ^ 4) := rfl

@[simp] theorem i2DepthAt_row24 : i2DepthAt 24 = 0 := rfl
@[simp] theorem i2DepthMass_row24 (q : ℂ) : i2DepthMass q 24 = 1 := rfl
@[simp] theorem i2RegionTerm_row24 (t d U V : ℂ) :
    i2RegionTerm 24 t d U V = Algebra.regionTerm49 t d U V
      (1 - d * V * t) (1 - V * t / d) (1 - V ^ 2 * t ^ 2)
      (1 - U * t ^ 2) (1 - U * t ^ 4) := rfl

theorem i2_case1a_reindexed (q t d U V T : ℂ) (n : ℕ × ℕ × ℕ) :
    i2SpatialTerm q t d U V T 0 (i2Case1aEquiv n).val =
      (-q * (1 - t ^ 2) ^ 2 * (d ^ 2) * t ^ 6 * (T * U) ^ 2 * (T * V) ^ 0 * i2DepthMass q 0) * (d * T * V * t) ^ n.1 * (t ^ 2) ^ n.2.1 * (t ^ 2) ^ n.2.2 := by
  unfold i2SpatialTerm
  rw [i2DepthAt_row0]
  unfold shellMonomial
  rw [i2Case1a_cartan]
  simp only [i2Case1aEquiv_val]
  have he : 3 * ((n.1 : ℤ)+2) + 2 * ((n.2.1 : ℤ)-2*((n.1 : ℤ)+2)) + 2 * ((n.2.2 : ℤ)-((n.1 : ℤ)+2)) + 3 * (4) + 4 * (((n.1 : ℤ)+2)-2) = ((n.1 + 2 * n.2.1 + 2 * n.2.2 + 6 : ℕ) : ℤ) := by omega
  have hn : (4) / 2 = ((2 : ℕ) : ℤ) := by omega
  have hb : (((n.1 : ℤ)+2)-2) = ((n.1 : ℕ) : ℤ) := by omega
  have hk : (n.1 : ℤ)+2 = ((n.1 + 2 : ℕ) : ℤ) := by omega
  rw [he]
  try rw [hn]
  try rw [hb]
  try rw [hk]
  simp only [zpow_neg, zpow_natCast, pow_add, pow_mul, mul_pow, pow_zero, pow_one, inv_pow, div_eq_mul_inv]
  ring

theorem summable_norm_i2_case1a (q t d U V T : ℂ)
    (hQ : ‖t ^ 2‖ < 1)
    (hP : ‖d * T * V * t‖ < 1) :
    Summable (fun p : I2SpatialRow 0 => ‖i2SpatialTerm q t d U V T 0 p.val‖) := by
  apply i2Case1aEquiv.summable_iff.mp
  convert summable_norm_three_geometric (-q * (1 - t ^ 2) ^ 2 * (d ^ 2) * t ^ 6 * (T * U) ^ 2 * (T * V) ^ 0 * i2DepthMass q 0) (d * T * V * t) (t ^ 2) (t ^ 2) hP hQ hQ using 1
  exact funext fun n => congrArg norm (i2_case1a_reindexed q t d U V T n)

theorem hasSum_i2_case1a_regionTerm (q t d U V T : ℂ)
    (hq : q * t ^ 2 = 1) (hd : d ≠ 0)
    (hQ : ‖t ^ 2‖ < 1)
    (hP : ‖d * T * V * t‖ < 1)
    : HasSum (fun p : I2SpatialRow 0 => i2SpatialTerm q t d U V T 0 p.val)
      (i2RegionTerm 0 t d (T * U) (T * V)) := by
  have h := hasSum_three_geometric (-q * (1 - t ^ 2) ^ 2 * (d ^ 2) * t ^ 6 * (T * U) ^ 2 * (T * V) ^ 0 * i2DepthMass q 0) (d * T * V * t) (t ^ 2) (t ^ 2) hP hQ hQ
  apply i2Case1aEquiv.hasSum_iff.mp
  convert h using 1
  · exact funext fun n => i2_case1a_reindexed q t d U V T n
  · have ht : t ≠ 0 := by
      intro ht
      simp [ht] at hq
    have hqeq : q = (t ^ 2)⁻¹ := by
      calc
        q = q * (t ^ 2 * (t ^ 2)⁻¹) := by rw [mul_inv_cancel₀ (pow_ne_zero 2 ht), mul_one]
        _ = (t ^ 2)⁻¹ := by rw [← mul_assoc, hq, one_mul]
    have hnQ := i2_geometric_denominator_ne (t ^ 2) hQ
    have hnP := i2_geometric_denominator_ne (d * T * V * t) hP
    rw [i2RegionTerm_row0, i2DepthMass_row0, hqeq]
    unfold Algebra.regionTerm25
    try simp only [inv_inv, pow_one]
    field_simp
    <;> ring

theorem i2_case1b_reindexed (q t d U V T : ℂ) (n : ℕ × ℕ) :
    i2SpatialTerm q t d U V T 1 (i2Case1bEquiv n).val =
      (-q * (1 - t ^ 2) ^ 2 * (d ^ 1) * t ^ 7 * (T * U) ^ 1 * (T * V) ^ 1 * i2DepthMass q 1) * (t ^ 2) ^ n.1 * (t ^ 2) ^ n.2 := by
  unfold i2SpatialTerm
  rw [i2DepthAt_row1]
  unfold shellMonomial
  rw [i2Case1b_cartan]
  simp only [i2Case1bEquiv_val]
  have he : 3 * (1) + 2 * ((n.1 : ℤ)-2) + 2 * ((n.2 : ℤ)-1) + 3 * (2) + 4 * (1) = ((2 * n.1 + 2 * n.2 + 7 : ℕ) : ℤ) := by omega
  have hn : (2) / 2 = ((1 : ℕ) : ℤ) := by omega
  have hb : (1) = ((1 : ℕ) : ℤ) := by omega
  have hk : 1 = ((1 : ℕ) : ℤ) := by omega
  rw [he]
  try rw [hn]
  try rw [hb]
  try rw [hk]
  simp only [zpow_neg, zpow_natCast, pow_add, pow_mul, mul_pow, pow_zero, pow_one, inv_pow, div_eq_mul_inv]
  ring

theorem summable_norm_i2_case1b (q t d U V T : ℂ)
    (hQ : ‖t ^ 2‖ < 1) :
    Summable (fun p : I2SpatialRow 1 => ‖i2SpatialTerm q t d U V T 1 p.val‖) := by
  apply i2Case1bEquiv.summable_iff.mp
  convert i2_summable_norm_two_geometric (-q * (1 - t ^ 2) ^ 2 * (d ^ 1) * t ^ 7 * (T * U) ^ 1 * (T * V) ^ 1 * i2DepthMass q 1) (t ^ 2) (t ^ 2) hQ hQ using 1
  exact funext fun n => congrArg norm (i2_case1b_reindexed q t d U V T n)

theorem hasSum_i2_case1b_regionTerm (q t d U V T : ℂ)
    (hq : q * t ^ 2 = 1) (hd : d ≠ 0)
    (hQ : ‖t ^ 2‖ < 1)
    : HasSum (fun p : I2SpatialRow 1 => i2SpatialTerm q t d U V T 1 p.val)
      (i2RegionTerm 1 t d (T * U) (T * V)) := by
  have h := i2_hasSum_two_geometric (-q * (1 - t ^ 2) ^ 2 * (d ^ 1) * t ^ 7 * (T * U) ^ 1 * (T * V) ^ 1 * i2DepthMass q 1) (t ^ 2) (t ^ 2) hQ hQ
  apply i2Case1bEquiv.hasSum_iff.mp
  convert h using 1
  · exact funext fun n => i2_case1b_reindexed q t d U V T n
  · have ht : t ≠ 0 := by
      intro ht
      simp [ht] at hq
    have hqeq : q = (t ^ 2)⁻¹ := by
      calc
        q = q * (t ^ 2 * (t ^ 2)⁻¹) := by rw [mul_inv_cancel₀ (pow_ne_zero 2 ht), mul_one]
        _ = (t ^ 2)⁻¹ := by rw [← mul_assoc, hq, one_mul]
    have hnQ := i2_geometric_denominator_ne (t ^ 2) hQ
    rw [i2RegionTerm_row1, i2DepthMass_row1, hqeq]
    unfold Algebra.regionTerm26
    try simp only [inv_inv, pow_one]
    field_simp
    <;> ring

theorem i2_case2_reindexed (q t d U V T : ℂ) (n : ℕ × ℕ × ℕ) :
    i2SpatialTerm q t d U V T 2 (i2Case2Equiv n).val =
      (-q * (1 - t ^ 2) ^ 2 * (d ^ 1) * t ^ 5 * (T * U) ^ 1 * (T * V) ^ 1 * i2DepthMass q 2) * (d * T * V * t) ^ n.1 * (t ^ 2) ^ n.2.1 * (T * U * t ^ 4) ^ n.2.2 := by
  unfold i2SpatialTerm
  rw [i2DepthAt_row2]
  unfold shellMonomial
  rw [i2Case2_cartan]
  simp only [i2Case2Equiv_val]
  have he : 3 * ((n.1 : ℤ)+1) + 2 * ((n.2.1 : ℤ)-2*((n.1 : ℤ)+1)) + 2 * (-((n.1 : ℤ)+1)-(n.2.2 : ℤ)-1) + 3 * (-2*((n.1 : ℤ)+1)-2*(-((n.1 : ℤ)+1)-(n.2.2 : ℤ)-1)) + 4 * (((n.1 : ℤ)+1)) = ((n.1 + 2 * n.2.1 + 4 * n.2.2 + 5 : ℕ) : ℤ) := by omega
  have hn : (-2*((n.1 : ℤ)+1)-2*(-((n.1 : ℤ)+1)-(n.2.2 : ℤ)-1)) / 2 = ((n.2.2 + 1 : ℕ) : ℤ) := by omega
  have hb : (((n.1 : ℤ)+1)) = ((n.1 + 1 : ℕ) : ℤ) := by omega
  have hk : (n.1 : ℤ)+1 = ((n.1 + 1 : ℕ) : ℤ) := by omega
  rw [he]
  try rw [hn]
  try rw [hb]
  try rw [hk]
  simp only [zpow_neg, zpow_natCast, pow_add, pow_mul, mul_pow, pow_zero, pow_one, inv_pow, div_eq_mul_inv]
  ring

theorem summable_norm_i2_case2 (q t d U V T : ℂ)
    (hQ : ‖t ^ 2‖ < 1)
    (hP : ‖d * T * V * t‖ < 1)
    (hG : ‖T * U * t ^ 4‖ < 1) :
    Summable (fun p : I2SpatialRow 2 => ‖i2SpatialTerm q t d U V T 2 p.val‖) := by
  apply i2Case2Equiv.summable_iff.mp
  convert summable_norm_three_geometric (-q * (1 - t ^ 2) ^ 2 * (d ^ 1) * t ^ 5 * (T * U) ^ 1 * (T * V) ^ 1 * i2DepthMass q 2) (d * T * V * t) (t ^ 2) (T * U * t ^ 4) hP hQ hG using 1
  exact funext fun n => congrArg norm (i2_case2_reindexed q t d U V T n)

theorem hasSum_i2_case2_regionTerm (q t d U V T : ℂ)
    (hq : q * t ^ 2 = 1) (hd : d ≠ 0)
    (hQ : ‖t ^ 2‖ < 1)
    (hP : ‖d * T * V * t‖ < 1)
    (hG : ‖T * U * t ^ 4‖ < 1)
    : HasSum (fun p : I2SpatialRow 2 => i2SpatialTerm q t d U V T 2 p.val)
      (i2RegionTerm 2 t d (T * U) (T * V)) := by
  have h := hasSum_three_geometric (-q * (1 - t ^ 2) ^ 2 * (d ^ 1) * t ^ 5 * (T * U) ^ 1 * (T * V) ^ 1 * i2DepthMass q 2) (d * T * V * t) (t ^ 2) (T * U * t ^ 4) hP hQ hG
  apply i2Case2Equiv.hasSum_iff.mp
  convert h using 1
  · exact funext fun n => i2_case2_reindexed q t d U V T n
  · have ht : t ≠ 0 := by
      intro ht
      simp [ht] at hq
    have hqeq : q = (t ^ 2)⁻¹ := by
      calc
        q = q * (t ^ 2 * (t ^ 2)⁻¹) := by rw [mul_inv_cancel₀ (pow_ne_zero 2 ht), mul_one]
        _ = (t ^ 2)⁻¹ := by rw [← mul_assoc, hq, one_mul]
    have hnQ := i2_geometric_denominator_ne (t ^ 2) hQ
    have hnP := i2_geometric_denominator_ne (d * T * V * t) hP
    have hnG := i2_geometric_denominator_ne (T * U * t ^ 4) hG
    rw [i2RegionTerm_row2, i2DepthMass_row2, hqeq]
    unfold Algebra.regionTerm27
    try simp only [inv_inv, pow_one]
    field_simp
    <;> ring

theorem i2_case3a_reindexed (q t d U V T : ℂ) (n : Fin 2 × ℕ × ℕ × ℕ) :
    i2SpatialTerm q t d U V T 3 (i2Case3aEquiv n).val =
      (-q * (1 - t ^ 2) ^ 2 * (d ^ 1) * t ^ 5 * (T * U) ^ 2 * (T * V) ^ 0 * i2DepthMass q 3) * (T * V * t ^ 2) ^ n.1.val * (d * T * V * t) ^ n.2.1 * ((T * V) ^ 2 * t ^ 2) ^ n.2.2.1 * (t ^ 2) ^ n.2.2.2 := by
  unfold i2SpatialTerm
  rw [i2DepthAt_row3]
  unfold shellMonomial
  rw [i2Case3a_cartan]
  simp only [i2Case3aEquiv_val]
  have he : 3 * ((n.2.1 : ℤ)+1) + 2 * (-2*((n.2.1 : ℤ)+1)-2*(n.2.2.1 : ℤ)-(n.1.val : ℤ)-1) + 2 * (-((n.2.1 : ℤ)+1)-(n.2.2.1 : ℤ)-1+(n.2.2.2 : ℤ)) + 3 * (4) + 4 * (-((n.2.1 : ℤ)+1)-(-2*((n.2.1 : ℤ)+1)-2*(n.2.2.1 : ℤ)-(n.1.val : ℤ)-1)-2) = ((n.2.1 + 2 * n.2.2.1 + 2 * n.2.2.2 + 2 * n.1.val + 5 : ℕ) : ℤ) := by omega
  have hn : (4) / 2 = ((2 : ℕ) : ℤ) := by omega
  have hb : (-((n.2.1 : ℤ)+1)-(-2*((n.2.1 : ℤ)+1)-2*(n.2.2.1 : ℤ)-(n.1.val : ℤ)-1)-2) = ((n.2.1 + 2 * n.2.2.1 + n.1.val : ℕ) : ℤ) := by omega
  have hk : (n.2.1 : ℤ)+1 = ((n.2.1 + 1 : ℕ) : ℤ) := by omega
  rw [he]
  try rw [hn]
  try rw [hb]
  try rw [hk]
  simp only [zpow_neg, zpow_natCast, pow_add, pow_mul, mul_pow, pow_zero, pow_one, inv_pow, div_eq_mul_inv]
  ring

theorem summable_norm_i2_case3a (q t d U V T : ℂ)
    (hQ : ‖t ^ 2‖ < 1)
    (hP : ‖d * T * V * t‖ < 1)
    (hE : ‖(T * V) ^ 2 * t ^ 2‖ < 1) :
    Summable (fun p : I2SpatialRow 3 => ‖i2SpatialTerm q t d U V T 3 p.val‖) := by
  apply i2Case3aEquiv.summable_iff.mp
  convert i2_summable_norm_parity_geometric (-q * (1 - t ^ 2) ^ 2 * (d ^ 1) * t ^ 5 * (T * U) ^ 2 * (T * V) ^ 0 * i2DepthMass q 3) (T * V * t ^ 2) (d * T * V * t) ((T * V) ^ 2 * t ^ 2) (t ^ 2) hP hE hQ using 1
  exact funext fun n => congrArg norm (i2_case3a_reindexed q t d U V T n)

theorem hasSum_i2_case3a_regionTerm (q t d U V T : ℂ)
    (hq : q * t ^ 2 = 1) (hd : d ≠ 0)
    (hQ : ‖t ^ 2‖ < 1)
    (hP : ‖d * T * V * t‖ < 1)
    (hE : ‖(T * V) ^ 2 * t ^ 2‖ < 1)
    : HasSum (fun p : I2SpatialRow 3 => i2SpatialTerm q t d U V T 3 p.val)
      (i2RegionTerm 3 t d (T * U) (T * V)) := by
  have h := i2_hasSum_parity_geometric (-q * (1 - t ^ 2) ^ 2 * (d ^ 1) * t ^ 5 * (T * U) ^ 2 * (T * V) ^ 0 * i2DepthMass q 3) (T * V * t ^ 2) (d * T * V * t) ((T * V) ^ 2 * t ^ 2) (t ^ 2) hP hE hQ
  apply i2Case3aEquiv.hasSum_iff.mp
  convert h using 1
  · exact funext fun n => i2_case3a_reindexed q t d U V T n
  · have ht : t ≠ 0 := by
      intro ht
      simp [ht] at hq
    have hqeq : q = (t ^ 2)⁻¹ := by
      calc
        q = q * (t ^ 2 * (t ^ 2)⁻¹) := by rw [mul_inv_cancel₀ (pow_ne_zero 2 ht), mul_one]
        _ = (t ^ 2)⁻¹ := by rw [← mul_assoc, hq, one_mul]
    have hnQ := i2_geometric_denominator_ne (t ^ 2) hQ
    have hnP := i2_geometric_denominator_ne (d * T * V * t) hP
    have hnE := i2_geometric_denominator_ne ((T * V) ^ 2 * t ^ 2) hE
    rw [i2RegionTerm_row3, i2DepthMass_row3, hqeq]
    unfold Algebra.regionTerm28
    try simp only [inv_inv, pow_one]
    field_simp
    <;> ring

theorem i2_case3b_reindexed (q t d U V T : ℂ) (n : ℕ × ℕ) :
    i2SpatialTerm q t d U V T 4 (i2Case3bEquiv n).val =
      (-q * (1 - t ^ 2) ^ 2 * (d ^ 1) * t ^ 5 * (T * U) ^ 2 * (T * V) ^ 1 * i2DepthMass q 4) * (d * T * V * t) ^ n.1 * ((T * V) ^ 2 * t ^ 2) ^ n.2 := by
  unfold i2SpatialTerm
  rw [i2DepthAt_row4]
  unfold shellMonomial
  rw [i2Case3b_cartan _ _ (by omega)]
  simp only [i2Case3bEquiv_val]
  have he : 3 * ((n.1 : ℤ)+1) + 2 * (-2*((n.1 : ℤ)+1)-2*(n.2 : ℤ)-2) + 2 * (-((n.1 : ℤ)+1)-(n.2 : ℤ)-2) + 3 * (4) + 4 * (-((n.1 : ℤ)+1)-(-2*((n.1 : ℤ)+1)-2*(n.2 : ℤ)-2)-2) = ((n.1 + 2 * n.2 + 5 : ℕ) : ℤ) := by omega
  have hn : (4) / 2 = ((2 : ℕ) : ℤ) := by omega
  have hb : (-((n.1 : ℤ)+1)-(-2*((n.1 : ℤ)+1)-2*(n.2 : ℤ)-2)-2) = ((n.1 + 2 * n.2 + 1 : ℕ) : ℤ) := by omega
  have hk : (n.1 : ℤ)+1 = ((n.1 + 1 : ℕ) : ℤ) := by omega
  rw [he]
  try rw [hn]
  try rw [hb]
  try rw [hk]
  simp only [zpow_neg, zpow_natCast, pow_add, pow_mul, mul_pow, pow_zero, pow_one, inv_pow, div_eq_mul_inv]
  ring

theorem summable_norm_i2_case3b (q t d U V T : ℂ)
    (hP : ‖d * T * V * t‖ < 1)
    (hE : ‖(T * V) ^ 2 * t ^ 2‖ < 1) :
    Summable (fun p : I2SpatialRow 4 => ‖i2SpatialTerm q t d U V T 4 p.val‖) := by
  apply i2Case3bEquiv.summable_iff.mp
  convert i2_summable_norm_two_geometric (-q * (1 - t ^ 2) ^ 2 * (d ^ 1) * t ^ 5 * (T * U) ^ 2 * (T * V) ^ 1 * i2DepthMass q 4) (d * T * V * t) ((T * V) ^ 2 * t ^ 2) hP hE using 1
  exact funext fun n => congrArg norm (i2_case3b_reindexed q t d U V T n)

theorem hasSum_i2_case3b_regionTerm (q t d U V T : ℂ)
    (hq : q * t ^ 2 = 1) (hd : d ≠ 0)
    (hQ : ‖t ^ 2‖ < 1)
    (hP : ‖d * T * V * t‖ < 1)
    (hE : ‖(T * V) ^ 2 * t ^ 2‖ < 1)
    : HasSum (fun p : I2SpatialRow 4 => i2SpatialTerm q t d U V T 4 p.val)
      (i2RegionTerm 4 t d (T * U) (T * V)) := by
  have h := i2_hasSum_two_geometric (-q * (1 - t ^ 2) ^ 2 * (d ^ 1) * t ^ 5 * (T * U) ^ 2 * (T * V) ^ 1 * i2DepthMass q 4) (d * T * V * t) ((T * V) ^ 2 * t ^ 2) hP hE
  apply i2Case3bEquiv.hasSum_iff.mp
  convert h using 1
  · exact funext fun n => i2_case3b_reindexed q t d U V T n
  · have ht : t ≠ 0 := by
      intro ht
      simp [ht] at hq
    have hqeq : q = (t ^ 2)⁻¹ := by
      calc
        q = q * (t ^ 2 * (t ^ 2)⁻¹) := by rw [mul_inv_cancel₀ (pow_ne_zero 2 ht), mul_one]
        _ = (t ^ 2)⁻¹ := by rw [← mul_assoc, hq, one_mul]
    have hnQ := i2_geometric_denominator_ne (t ^ 2) hQ
    have hnP := i2_geometric_denominator_ne (d * T * V * t) hP
    have hnE := i2_geometric_denominator_ne ((T * V) ^ 2 * t ^ 2) hE
    rw [i2RegionTerm_row4, i2DepthMass_row4, hqeq]
    unfold Algebra.regionTerm29
    try simp only [inv_inv, pow_one]
    field_simp
    <;> ring

theorem i2_case3c_reindexed (q t d U V T : ℂ) (n : ℕ × ℕ) :
    i2SpatialTerm q t d U V T 5 (i2Case3cEquiv n).val =
      (-q * (1 - t ^ 2) ^ 2 * (d ^ 1) * t ^ 3 * (T * U) ^ 1 * (T * V) ^ 2 * i2DepthMass q 5) * (d * T * V * t) ^ n.1 * ((T * V) ^ 2 * t ^ 2) ^ n.2 := by
  unfold i2SpatialTerm
  rw [i2DepthAt_row5]
  unfold shellMonomial
  rw [i2Case3c_cartan _ _ (by omega)]
  simp only [i2Case3cEquiv_val]
  have he : 3 * ((n.1 : ℤ)+1) + 2 * (-2*((n.1 : ℤ)+1)-2*(n.2 : ℤ)-2) + 2 * (-((n.1 : ℤ)+1)-(n.2 : ℤ)-2) + 3 * (2) + 4 * (-((n.1 : ℤ)+1)-(-2*((n.1 : ℤ)+1)-2*(n.2 : ℤ)-2)-1) = ((n.1 + 2 * n.2 + 3 : ℕ) : ℤ) := by omega
  have hn : (2) / 2 = ((1 : ℕ) : ℤ) := by omega
  have hb : (-((n.1 : ℤ)+1)-(-2*((n.1 : ℤ)+1)-2*(n.2 : ℤ)-2)-1) = ((n.1 + 2 * n.2 + 2 : ℕ) : ℤ) := by omega
  have hk : (n.1 : ℤ)+1 = ((n.1 + 1 : ℕ) : ℤ) := by omega
  rw [he]
  try rw [hn]
  try rw [hb]
  try rw [hk]
  simp only [zpow_neg, zpow_natCast, pow_add, pow_mul, mul_pow, pow_zero, pow_one, inv_pow, div_eq_mul_inv]
  ring

theorem summable_norm_i2_case3c (q t d U V T : ℂ)
    (hP : ‖d * T * V * t‖ < 1)
    (hE : ‖(T * V) ^ 2 * t ^ 2‖ < 1) :
    Summable (fun p : I2SpatialRow 5 => ‖i2SpatialTerm q t d U V T 5 p.val‖) := by
  apply i2Case3cEquiv.summable_iff.mp
  convert i2_summable_norm_two_geometric (-q * (1 - t ^ 2) ^ 2 * (d ^ 1) * t ^ 3 * (T * U) ^ 1 * (T * V) ^ 2 * i2DepthMass q 5) (d * T * V * t) ((T * V) ^ 2 * t ^ 2) hP hE using 1
  exact funext fun n => congrArg norm (i2_case3c_reindexed q t d U V T n)

theorem hasSum_i2_case3c_regionTerm (q t d U V T : ℂ)
    (hq : q * t ^ 2 = 1) (hd : d ≠ 0)
    (hQ : ‖t ^ 2‖ < 1)
    (hP : ‖d * T * V * t‖ < 1)
    (hE : ‖(T * V) ^ 2 * t ^ 2‖ < 1)
    : HasSum (fun p : I2SpatialRow 5 => i2SpatialTerm q t d U V T 5 p.val)
      (i2RegionTerm 5 t d (T * U) (T * V)) := by
  have h := i2_hasSum_two_geometric (-q * (1 - t ^ 2) ^ 2 * (d ^ 1) * t ^ 3 * (T * U) ^ 1 * (T * V) ^ 2 * i2DepthMass q 5) (d * T * V * t) ((T * V) ^ 2 * t ^ 2) hP hE
  apply i2Case3cEquiv.hasSum_iff.mp
  convert h using 1
  · exact funext fun n => i2_case3c_reindexed q t d U V T n
  · have ht : t ≠ 0 := by
      intro ht
      simp [ht] at hq
    have hqeq : q = (t ^ 2)⁻¹ := by
      calc
        q = q * (t ^ 2 * (t ^ 2)⁻¹) := by rw [mul_inv_cancel₀ (pow_ne_zero 2 ht), mul_one]
        _ = (t ^ 2)⁻¹ := by rw [← mul_assoc, hq, one_mul]
    have hnQ := i2_geometric_denominator_ne (t ^ 2) hQ
    have hnP := i2_geometric_denominator_ne (d * T * V * t) hP
    have hnE := i2_geometric_denominator_ne ((T * V) ^ 2 * t ^ 2) hE
    rw [i2RegionTerm_row5, i2DepthMass_row5, hqeq]
    unfold Algebra.regionTerm30
    try simp only [inv_inv, pow_one]
    field_simp
    <;> ring

theorem i2_case3d_reindexed (q t d U V T : ℂ) (n : ℕ × ℕ) :
    i2SpatialTerm q t d U V T 6 (i2Case3dEquiv n).val =
      (-q * (1 - t ^ 2) ^ 2 * (d ^ 1) * t ^ 1 * (T * U) ^ 0 * (T * V) ^ 3 * i2DepthMass q 6) * (d * T * V * t) ^ n.1 * ((T * V) ^ 2 * t ^ 2) ^ n.2 := by
  unfold i2SpatialTerm
  rw [i2DepthAt_row6]
  unfold shellMonomial
  rw [i2Case3d_cartan _ _ (by omega)]
  simp only [i2Case3dEquiv_val]
  have he : 3 * ((n.1 : ℤ)+1) + 2 * (-2*((n.1 : ℤ)+1)-2*(n.2 : ℤ)-2) + 2 * (-((n.1 : ℤ)+1)-(n.2 : ℤ)-2) + 3 * (0) + 4 * (-((n.1 : ℤ)+1)-(-2*((n.1 : ℤ)+1)-2*(n.2 : ℤ)-2)) = ((n.1 + 2 * n.2 + 1 : ℕ) : ℤ) := by omega
  have hn : (0) / 2 = ((0 : ℕ) : ℤ) := by omega
  have hb : (-((n.1 : ℤ)+1)-(-2*((n.1 : ℤ)+1)-2*(n.2 : ℤ)-2)) = ((n.1 + 2 * n.2 + 3 : ℕ) : ℤ) := by omega
  have hk : (n.1 : ℤ)+1 = ((n.1 + 1 : ℕ) : ℤ) := by omega
  rw [he]
  try rw [hn]
  try rw [hb]
  try rw [hk]
  simp only [zpow_neg, zpow_natCast, pow_add, pow_mul, mul_pow, pow_zero, pow_one, inv_pow, div_eq_mul_inv]
  ring

theorem summable_norm_i2_case3d (q t d U V T : ℂ)
    (hP : ‖d * T * V * t‖ < 1)
    (hE : ‖(T * V) ^ 2 * t ^ 2‖ < 1) :
    Summable (fun p : I2SpatialRow 6 => ‖i2SpatialTerm q t d U V T 6 p.val‖) := by
  apply i2Case3dEquiv.summable_iff.mp
  convert i2_summable_norm_two_geometric (-q * (1 - t ^ 2) ^ 2 * (d ^ 1) * t ^ 1 * (T * U) ^ 0 * (T * V) ^ 3 * i2DepthMass q 6) (d * T * V * t) ((T * V) ^ 2 * t ^ 2) hP hE using 1
  exact funext fun n => congrArg norm (i2_case3d_reindexed q t d U V T n)

theorem hasSum_i2_case3d_regionTerm (q t d U V T : ℂ)
    (hq : q * t ^ 2 = 1) (hd : d ≠ 0)
    (hQ : ‖t ^ 2‖ < 1)
    (hP : ‖d * T * V * t‖ < 1)
    (hE : ‖(T * V) ^ 2 * t ^ 2‖ < 1)
    : HasSum (fun p : I2SpatialRow 6 => i2SpatialTerm q t d U V T 6 p.val)
      (i2RegionTerm 6 t d (T * U) (T * V)) := by
  have h := i2_hasSum_two_geometric (-q * (1 - t ^ 2) ^ 2 * (d ^ 1) * t ^ 1 * (T * U) ^ 0 * (T * V) ^ 3 * i2DepthMass q 6) (d * T * V * t) ((T * V) ^ 2 * t ^ 2) hP hE
  apply i2Case3dEquiv.hasSum_iff.mp
  convert h using 1
  · exact funext fun n => i2_case3d_reindexed q t d U V T n
  · have ht : t ≠ 0 := by
      intro ht
      simp [ht] at hq
    have hqeq : q = (t ^ 2)⁻¹ := by
      calc
        q = q * (t ^ 2 * (t ^ 2)⁻¹) := by rw [mul_inv_cancel₀ (pow_ne_zero 2 ht), mul_one]
        _ = (t ^ 2)⁻¹ := by rw [← mul_assoc, hq, one_mul]
    have hnQ := i2_geometric_denominator_ne (t ^ 2) hQ
    have hnP := i2_geometric_denominator_ne (d * T * V * t) hP
    have hnE := i2_geometric_denominator_ne ((T * V) ^ 2 * t ^ 2) hE
    rw [i2RegionTerm_row6, i2DepthMass_row6, hqeq]
    unfold Algebra.regionTerm31
    try simp only [inv_inv, pow_one]
    field_simp
    <;> ring

theorem i2_case4_reindexed (q t d U V T : ℂ) (n : ℕ × ℕ × ℕ) :
    i2SpatialTerm q t d U V T 7 (i2Case4Equiv n).val =
      (-q * (1 - t ^ 2) ^ 2 * (d ^ 1) * t ^ 7 * (T * U) ^ 3 * (T * V) ^ 1 * i2DepthMass q 7) * (d * T * V * t) ^ n.1 * ((T * V) ^ 2 * t ^ 2) ^ n.2.1 * (T * U * t ^ 2) ^ n.2.2 := by
  unfold i2SpatialTerm
  rw [i2DepthAt_row7]
  unfold shellMonomial
  rw [i2Case4_cartan]
  simp only [i2Case4Equiv_val]
  have he : 3 * ((n.1 : ℤ)+1) + 2 * (-2*((n.1 : ℤ)+1)-2*(n.2.1 : ℤ)-(n.2.2 : ℤ)-3) + 2 * (-((n.1 : ℤ)+1)-(n.2.1 : ℤ)-(n.2.2 : ℤ)-3) + 3 * (2*(-2*((n.1 : ℤ)+1)-2*(n.2.1 : ℤ)-(n.2.2 : ℤ)-3)-4*(-((n.1 : ℤ)+1)-(n.2.1 : ℤ)-(n.2.2 : ℤ)-3)) + 4 * (2*(-((n.1 : ℤ)+1)-(n.2.1 : ℤ)-(n.2.2 : ℤ)-3)-2*(-2*((n.1 : ℤ)+1)-2*(n.2.1 : ℤ)-(n.2.2 : ℤ)-3)-((n.1 : ℤ)+1)) = ((n.1 + 2 * n.2.1 + 2 * n.2.2 + 7 : ℕ) : ℤ) := by omega
  have hn : (2*(-2*((n.1 : ℤ)+1)-2*(n.2.1 : ℤ)-(n.2.2 : ℤ)-3)-4*(-((n.1 : ℤ)+1)-(n.2.1 : ℤ)-(n.2.2 : ℤ)-3)) / 2 = ((n.2.2 + 3 : ℕ) : ℤ) := by omega
  have hb : (2*(-((n.1 : ℤ)+1)-(n.2.1 : ℤ)-(n.2.2 : ℤ)-3)-2*(-2*((n.1 : ℤ)+1)-2*(n.2.1 : ℤ)-(n.2.2 : ℤ)-3)-((n.1 : ℤ)+1)) = ((n.1 + 2 * n.2.1 + 1 : ℕ) : ℤ) := by omega
  have hk : (n.1 : ℤ)+1 = ((n.1 + 1 : ℕ) : ℤ) := by omega
  rw [he]
  try rw [hn]
  try rw [hb]
  try rw [hk]
  simp only [zpow_neg, zpow_natCast, pow_add, pow_mul, mul_pow, pow_zero, pow_one, inv_pow, div_eq_mul_inv]
  ring

theorem summable_norm_i2_case4 (q t d U V T : ℂ)
    (hP : ‖d * T * V * t‖ < 1)
    (hE : ‖(T * V) ^ 2 * t ^ 2‖ < 1)
    (hF : ‖T * U * t ^ 2‖ < 1) :
    Summable (fun p : I2SpatialRow 7 => ‖i2SpatialTerm q t d U V T 7 p.val‖) := by
  apply i2Case4Equiv.summable_iff.mp
  convert summable_norm_three_geometric (-q * (1 - t ^ 2) ^ 2 * (d ^ 1) * t ^ 7 * (T * U) ^ 3 * (T * V) ^ 1 * i2DepthMass q 7) (d * T * V * t) ((T * V) ^ 2 * t ^ 2) (T * U * t ^ 2) hP hE hF using 1
  exact funext fun n => congrArg norm (i2_case4_reindexed q t d U V T n)

theorem hasSum_i2_case4_regionTerm (q t d U V T : ℂ)
    (hq : q * t ^ 2 = 1) (hd : d ≠ 0)
    (hQ : ‖t ^ 2‖ < 1)
    (hP : ‖d * T * V * t‖ < 1)
    (hE : ‖(T * V) ^ 2 * t ^ 2‖ < 1)
    (hF : ‖T * U * t ^ 2‖ < 1)
    : HasSum (fun p : I2SpatialRow 7 => i2SpatialTerm q t d U V T 7 p.val)
      (i2RegionTerm 7 t d (T * U) (T * V)) := by
  have h := hasSum_three_geometric (-q * (1 - t ^ 2) ^ 2 * (d ^ 1) * t ^ 7 * (T * U) ^ 3 * (T * V) ^ 1 * i2DepthMass q 7) (d * T * V * t) ((T * V) ^ 2 * t ^ 2) (T * U * t ^ 2) hP hE hF
  apply i2Case4Equiv.hasSum_iff.mp
  convert h using 1
  · exact funext fun n => i2_case4_reindexed q t d U V T n
  · have ht : t ≠ 0 := by
      intro ht
      simp [ht] at hq
    have hqeq : q = (t ^ 2)⁻¹ := by
      calc
        q = q * (t ^ 2 * (t ^ 2)⁻¹) := by rw [mul_inv_cancel₀ (pow_ne_zero 2 ht), mul_one]
        _ = (t ^ 2)⁻¹ := by rw [← mul_assoc, hq, one_mul]
    have hnQ := i2_geometric_denominator_ne (t ^ 2) hQ
    have hnP := i2_geometric_denominator_ne (d * T * V * t) hP
    have hnE := i2_geometric_denominator_ne ((T * V) ^ 2 * t ^ 2) hE
    have hnF := i2_geometric_denominator_ne (T * U * t ^ 2) hF
    rw [i2RegionTerm_row7, i2DepthMass_row7, hqeq]
    unfold Algebra.regionTerm32
    try simp only [inv_inv, pow_one]
    field_simp
    <;> ring

theorem i2_case5_reindexed (q t d U V T : ℂ) (n : ℕ × ℕ × ℕ) :
    i2SpatialTerm q t d U V T 8 (i2Case5Equiv n).val =
      (-q * (1 - t ^ 2) ^ 2 * (d ^ 1) * t ^ 7 * (T * U) ^ 2 * (T * V) ^ 1 * i2DepthMass q 8) * (d * T * V * t) ^ n.1 * (T * U * t ^ 2) ^ n.2.1 * (T * U * t ^ 4) ^ n.2.2 := by
  unfold i2SpatialTerm
  rw [i2DepthAt_row8]
  unfold shellMonomial
  rw [i2Case5_cartan]
  simp only [i2Case5Equiv_val]
  have he : 3 * ((n.1 : ℤ)+1) + 2 * (-2*((n.1 : ℤ)+1)-(n.2.1 : ℤ)-1) + 2 * (-((n.1 : ℤ)+1)-(n.2.1 : ℤ)-(n.2.2 : ℤ)-2) + 3 * (-2*((n.1 : ℤ)+1)-2*(-((n.1 : ℤ)+1)-(n.2.1 : ℤ)-(n.2.2 : ℤ)-2)) + 4 * (((n.1 : ℤ)+1)) = ((n.1 + 2 * n.2.1 + 4 * n.2.2 + 7 : ℕ) : ℤ) := by omega
  have hn : (-2*((n.1 : ℤ)+1)-2*(-((n.1 : ℤ)+1)-(n.2.1 : ℤ)-(n.2.2 : ℤ)-2)) / 2 = ((n.2.1 + n.2.2 + 2 : ℕ) : ℤ) := by omega
  have hb : (((n.1 : ℤ)+1)) = ((n.1 + 1 : ℕ) : ℤ) := by omega
  have hk : (n.1 : ℤ)+1 = ((n.1 + 1 : ℕ) : ℤ) := by omega
  rw [he]
  try rw [hn]
  try rw [hb]
  try rw [hk]
  simp only [zpow_neg, zpow_natCast, pow_add, pow_mul, mul_pow, pow_zero, pow_one, inv_pow, div_eq_mul_inv]
  ring

theorem summable_norm_i2_case5 (q t d U V T : ℂ)
    (hP : ‖d * T * V * t‖ < 1)
    (hF : ‖T * U * t ^ 2‖ < 1)
    (hG : ‖T * U * t ^ 4‖ < 1) :
    Summable (fun p : I2SpatialRow 8 => ‖i2SpatialTerm q t d U V T 8 p.val‖) := by
  apply i2Case5Equiv.summable_iff.mp
  convert summable_norm_three_geometric (-q * (1 - t ^ 2) ^ 2 * (d ^ 1) * t ^ 7 * (T * U) ^ 2 * (T * V) ^ 1 * i2DepthMass q 8) (d * T * V * t) (T * U * t ^ 2) (T * U * t ^ 4) hP hF hG using 1
  exact funext fun n => congrArg norm (i2_case5_reindexed q t d U V T n)

theorem hasSum_i2_case5_regionTerm (q t d U V T : ℂ)
    (hq : q * t ^ 2 = 1) (hd : d ≠ 0)
    (hQ : ‖t ^ 2‖ < 1)
    (hP : ‖d * T * V * t‖ < 1)
    (hF : ‖T * U * t ^ 2‖ < 1)
    (hG : ‖T * U * t ^ 4‖ < 1)
    : HasSum (fun p : I2SpatialRow 8 => i2SpatialTerm q t d U V T 8 p.val)
      (i2RegionTerm 8 t d (T * U) (T * V)) := by
  have h := hasSum_three_geometric (-q * (1 - t ^ 2) ^ 2 * (d ^ 1) * t ^ 7 * (T * U) ^ 2 * (T * V) ^ 1 * i2DepthMass q 8) (d * T * V * t) (T * U * t ^ 2) (T * U * t ^ 4) hP hF hG
  apply i2Case5Equiv.hasSum_iff.mp
  convert h using 1
  · exact funext fun n => i2_case5_reindexed q t d U V T n
  · have ht : t ≠ 0 := by
      intro ht
      simp [ht] at hq
    have hqeq : q = (t ^ 2)⁻¹ := by
      calc
        q = q * (t ^ 2 * (t ^ 2)⁻¹) := by rw [mul_inv_cancel₀ (pow_ne_zero 2 ht), mul_one]
        _ = (t ^ 2)⁻¹ := by rw [← mul_assoc, hq, one_mul]
    have hnQ := i2_geometric_denominator_ne (t ^ 2) hQ
    have hnP := i2_geometric_denominator_ne (d * T * V * t) hP
    have hnF := i2_geometric_denominator_ne (T * U * t ^ 2) hF
    have hnG := i2_geometric_denominator_ne (T * U * t ^ 4) hG
    rw [i2RegionTerm_row8, i2DepthMass_row8, hqeq]
    unfold Algebra.regionTerm33
    try simp only [inv_inv, pow_one]
    field_simp
    <;> ring

theorem i2_case6a_reindexed (q t d U V T : ℂ) (n : ℕ × ℕ) :
    i2SpatialTerm q t d U V T 9 (i2Case6aEquiv n).val =
      (-q * (1 - t ^ 2) ^ 2 * (d ^ 0) * t ^ 6 * (T * U) ^ 0 * (T * V) ^ 2 * i2DepthMass q 9) * (t ^ 2) ^ n.1 * (t ^ 2) ^ n.2 := by
  unfold i2SpatialTerm
  rw [i2DepthAt_row9]
  unfold shellMonomial
  rw [i2Case6a_cartan]
  simp only [i2Case6aEquiv_val]
  have he : 3 * (0) + 2 * ((n.1 : ℤ)) + 2 * ((n.2 : ℤ)-1) + 3 * (0) + 4 * (2) = ((2 * n.1 + 2 * n.2 + 6 : ℕ) : ℤ) := by omega
  have hn : (0) / 2 = ((0 : ℕ) : ℤ) := by omega
  have hb : (2) = ((2 : ℕ) : ℤ) := by omega
  have hk : 0 = ((0 : ℕ) : ℤ) := by omega
  rw [he]
  try rw [hn]
  try rw [hb]
  try rw [hk]
  simp only [zpow_neg, zpow_natCast, pow_add, pow_mul, mul_pow, pow_zero, pow_one, inv_pow, div_eq_mul_inv]
  ring

theorem summable_norm_i2_case6a (q t d U V T : ℂ)
    (hQ : ‖t ^ 2‖ < 1) :
    Summable (fun p : I2SpatialRow 9 => ‖i2SpatialTerm q t d U V T 9 p.val‖) := by
  apply i2Case6aEquiv.summable_iff.mp
  convert i2_summable_norm_two_geometric (-q * (1 - t ^ 2) ^ 2 * (d ^ 0) * t ^ 6 * (T * U) ^ 0 * (T * V) ^ 2 * i2DepthMass q 9) (t ^ 2) (t ^ 2) hQ hQ using 1
  exact funext fun n => congrArg norm (i2_case6a_reindexed q t d U V T n)

theorem hasSum_i2_case6a_regionTerm (q t d U V T : ℂ)
    (hq : q * t ^ 2 = 1) (hd : d ≠ 0)
    (hQ : ‖t ^ 2‖ < 1)
    : HasSum (fun p : I2SpatialRow 9 => i2SpatialTerm q t d U V T 9 p.val)
      (i2RegionTerm 9 t d (T * U) (T * V)) := by
  have h := i2_hasSum_two_geometric (-q * (1 - t ^ 2) ^ 2 * (d ^ 0) * t ^ 6 * (T * U) ^ 0 * (T * V) ^ 2 * i2DepthMass q 9) (t ^ 2) (t ^ 2) hQ hQ
  apply i2Case6aEquiv.hasSum_iff.mp
  convert h using 1
  · exact funext fun n => i2_case6a_reindexed q t d U V T n
  · have ht : t ≠ 0 := by
      intro ht
      simp [ht] at hq
    have hqeq : q = (t ^ 2)⁻¹ := by
      calc
        q = q * (t ^ 2 * (t ^ 2)⁻¹) := by rw [mul_inv_cancel₀ (pow_ne_zero 2 ht), mul_one]
        _ = (t ^ 2)⁻¹ := by rw [← mul_assoc, hq, one_mul]
    have hnQ := i2_geometric_denominator_ne (t ^ 2) hQ
    rw [i2RegionTerm_row9, i2DepthMass_row9, hqeq]
    unfold Algebra.regionTerm34
    try simp only [inv_inv, pow_one]
    field_simp
    <;> ring

theorem i2_case6aa_reindexed (q t d U V T : ℂ) (n : ℕ) :
    i2SpatialTerm q t d U V T 10 (i2Case6aaEquiv n).val =
      (-q * (1 - t ^ 2) ^ 2 * (d ^ 0) * t ^ 6 * (T * U) ^ 1 * (T * V) ^ 1 * i2DepthMass q 10) * (t ^ 2) ^ n := by
  unfold i2SpatialTerm
  rw [i2DepthAt_row10]
  unfold shellMonomial
  rw [i2Case6aa_cartan]
  simp only [i2Case6aaEquiv_val]
  have he : 3 * (0) + 2 * (-1) + 2 * ((n : ℤ)-1) + 3 * (2) + 4 * (1) = ((2 * n + 6 : ℕ) : ℤ) := by omega
  have hn : (2) / 2 = ((1 : ℕ) : ℤ) := by omega
  have hb : (1) = ((1 : ℕ) : ℤ) := by omega
  have hk : 0 = ((0 : ℕ) : ℤ) := by omega
  rw [he]
  try rw [hn]
  try rw [hb]
  try rw [hk]
  simp only [zpow_neg, zpow_natCast, pow_add, pow_mul, mul_pow, pow_zero, pow_one, inv_pow, div_eq_mul_inv]
  ring

theorem summable_norm_i2_case6aa (q t d U V T : ℂ)
    (hQ : ‖t ^ 2‖ < 1) :
    Summable (fun p : I2SpatialRow 10 => ‖i2SpatialTerm q t d U V T 10 p.val‖) := by
  apply i2Case6aaEquiv.summable_iff.mp
  convert i2_summable_norm_one_geometric (-q * (1 - t ^ 2) ^ 2 * (d ^ 0) * t ^ 6 * (T * U) ^ 1 * (T * V) ^ 1 * i2DepthMass q 10) (t ^ 2) hQ using 1
  exact funext fun n => congrArg norm (i2_case6aa_reindexed q t d U V T n)

theorem hasSum_i2_case6aa_regionTerm (q t d U V T : ℂ)
    (hq : q * t ^ 2 = 1) (hd : d ≠ 0)
    (hQ : ‖t ^ 2‖ < 1)
    : HasSum (fun p : I2SpatialRow 10 => i2SpatialTerm q t d U V T 10 p.val)
      (i2RegionTerm 10 t d (T * U) (T * V)) := by
  have h := i2_hasSum_one_geometric (-q * (1 - t ^ 2) ^ 2 * (d ^ 0) * t ^ 6 * (T * U) ^ 1 * (T * V) ^ 1 * i2DepthMass q 10) (t ^ 2) hQ
  apply i2Case6aaEquiv.hasSum_iff.mp
  convert h using 1
  · exact funext fun n => i2_case6aa_reindexed q t d U V T n
  · have ht : t ≠ 0 := by
      intro ht
      simp [ht] at hq
    have hqeq : q = (t ^ 2)⁻¹ := by
      calc
        q = q * (t ^ 2 * (t ^ 2)⁻¹) := by rw [mul_inv_cancel₀ (pow_ne_zero 2 ht), mul_one]
        _ = (t ^ 2)⁻¹ := by rw [← mul_assoc, hq, one_mul]
    have hnQ := i2_geometric_denominator_ne (t ^ 2) hQ
    rw [i2RegionTerm_row10, i2DepthMass_row10, hqeq]
    unfold Algebra.regionTerm35
    try simp only [inv_inv, pow_one]
    field_simp
    <;> ring

theorem i2_case6aaa_reindexed (q t d U V T : ℂ) (n : ℕ × ℕ) :
    i2SpatialTerm q t d U V T 11 (i2Case6aaaEquiv n).val =
      (-q * (1 - t ^ 2) ^ 2 * (d ^ 0) * t ^ 6 * (T * U) ^ 2 * (T * V) ^ 0 * i2DepthMass q 11) * (t ^ 2) ^ n.1 * (T * U * t ^ 4) ^ n.2 := by
  unfold i2SpatialTerm
  rw [i2DepthAt_row11]
  unfold shellMonomial
  rw [i2Case6aaa_cartan]
  simp only [i2Case6aaaEquiv_val]
  have he : 3 * (0) + 2 * ((n.1 : ℤ)-1) + 2 * (-(n.2 : ℤ)-2) + 3 * (-2*(-(n.2 : ℤ)-2)) + 4 * (0) = ((2 * n.1 + 4 * n.2 + 6 : ℕ) : ℤ) := by omega
  have hn : (-2*(-(n.2 : ℤ)-2)) / 2 = ((n.2 + 2 : ℕ) : ℤ) := by omega
  have hb : (0) = ((0 : ℕ) : ℤ) := by omega
  have hk : 0 = ((0 : ℕ) : ℤ) := by omega
  rw [he]
  try rw [hn]
  try rw [hb]
  try rw [hk]
  simp only [zpow_neg, zpow_natCast, pow_add, pow_mul, mul_pow, pow_zero, pow_one, inv_pow, div_eq_mul_inv]
  ring

theorem summable_norm_i2_case6aaa (q t d U V T : ℂ)
    (hQ : ‖t ^ 2‖ < 1)
    (hG : ‖T * U * t ^ 4‖ < 1) :
    Summable (fun p : I2SpatialRow 11 => ‖i2SpatialTerm q t d U V T 11 p.val‖) := by
  apply i2Case6aaaEquiv.summable_iff.mp
  convert i2_summable_norm_two_geometric (-q * (1 - t ^ 2) ^ 2 * (d ^ 0) * t ^ 6 * (T * U) ^ 2 * (T * V) ^ 0 * i2DepthMass q 11) (t ^ 2) (T * U * t ^ 4) hQ hG using 1
  exact funext fun n => congrArg norm (i2_case6aaa_reindexed q t d U V T n)

theorem hasSum_i2_case6aaa_regionTerm (q t d U V T : ℂ)
    (hq : q * t ^ 2 = 1) (hd : d ≠ 0)
    (hQ : ‖t ^ 2‖ < 1)
    (hG : ‖T * U * t ^ 4‖ < 1)
    : HasSum (fun p : I2SpatialRow 11 => i2SpatialTerm q t d U V T 11 p.val)
      (i2RegionTerm 11 t d (T * U) (T * V)) := by
  have h := i2_hasSum_two_geometric (-q * (1 - t ^ 2) ^ 2 * (d ^ 0) * t ^ 6 * (T * U) ^ 2 * (T * V) ^ 0 * i2DepthMass q 11) (t ^ 2) (T * U * t ^ 4) hQ hG
  apply i2Case6aaaEquiv.hasSum_iff.mp
  convert h using 1
  · exact funext fun n => i2_case6aaa_reindexed q t d U V T n
  · have ht : t ≠ 0 := by
      intro ht
      simp [ht] at hq
    have hqeq : q = (t ^ 2)⁻¹ := by
      calc
        q = q * (t ^ 2 * (t ^ 2)⁻¹) := by rw [mul_inv_cancel₀ (pow_ne_zero 2 ht), mul_one]
        _ = (t ^ 2)⁻¹ := by rw [← mul_assoc, hq, one_mul]
    have hnQ := i2_geometric_denominator_ne (t ^ 2) hQ
    have hnG := i2_geometric_denominator_ne (T * U * t ^ 4) hG
    rw [i2RegionTerm_row11, i2DepthMass_row11, hqeq]
    unfold Algebra.regionTerm36
    try simp only [inv_inv, pow_one]
    field_simp
    <;> ring

theorem i2_case6b_reindexed (q t d U V T : ℂ) (n : ℕ × ℕ) :
    i2SpatialTerm q t d U V T 12 (i2Case6bEquiv n).val =
      (-q * (1 - t ^ 2) ^ 2 * ((d⁻¹) ^ 1) * t ^ 7 * (T * U) ^ 1 * (T * V) ^ 1 * i2DepthMass q 12) * (t ^ 2) ^ n.1 * (t ^ 2) ^ n.2 := by
  unfold i2SpatialTerm
  rw [i2DepthAt_row12]
  unfold shellMonomial
  rw [i2Case6b_cartan]
  simp only [i2Case6bEquiv_val]
  have he : 3 * (-1) + 2 * ((n.1 : ℤ)) + 2 * ((n.2 : ℤ)) + 3 * (2) + 4 * (1) = ((2 * n.1 + 2 * n.2 + 7 : ℕ) : ℤ) := by omega
  have hn : (2) / 2 = ((1 : ℕ) : ℤ) := by omega
  have hb : (1) = ((1 : ℕ) : ℤ) := by omega
  have hk : -1 = -((1 : ℕ) : ℤ) := by omega
  rw [he]
  try rw [hn]
  try rw [hb]
  try rw [hk]
  simp only [zpow_neg, zpow_natCast, pow_add, pow_mul, mul_pow, pow_zero, pow_one, inv_pow, div_eq_mul_inv]
  ring

theorem summable_norm_i2_case6b (q t d U V T : ℂ)
    (hQ : ‖t ^ 2‖ < 1) :
    Summable (fun p : I2SpatialRow 12 => ‖i2SpatialTerm q t d U V T 12 p.val‖) := by
  apply i2Case6bEquiv.summable_iff.mp
  convert i2_summable_norm_two_geometric (-q * (1 - t ^ 2) ^ 2 * ((d⁻¹) ^ 1) * t ^ 7 * (T * U) ^ 1 * (T * V) ^ 1 * i2DepthMass q 12) (t ^ 2) (t ^ 2) hQ hQ using 1
  exact funext fun n => congrArg norm (i2_case6b_reindexed q t d U V T n)

theorem hasSum_i2_case6b_regionTerm (q t d U V T : ℂ)
    (hq : q * t ^ 2 = 1) (hd : d ≠ 0)
    (hQ : ‖t ^ 2‖ < 1)
    : HasSum (fun p : I2SpatialRow 12 => i2SpatialTerm q t d U V T 12 p.val)
      (i2RegionTerm 12 t d (T * U) (T * V)) := by
  have h := i2_hasSum_two_geometric (-q * (1 - t ^ 2) ^ 2 * ((d⁻¹) ^ 1) * t ^ 7 * (T * U) ^ 1 * (T * V) ^ 1 * i2DepthMass q 12) (t ^ 2) (t ^ 2) hQ hQ
  apply i2Case6bEquiv.hasSum_iff.mp
  convert h using 1
  · exact funext fun n => i2_case6b_reindexed q t d U V T n
  · have ht : t ≠ 0 := by
      intro ht
      simp [ht] at hq
    have hqeq : q = (t ^ 2)⁻¹ := by
      calc
        q = q * (t ^ 2 * (t ^ 2)⁻¹) := by rw [mul_inv_cancel₀ (pow_ne_zero 2 ht), mul_one]
        _ = (t ^ 2)⁻¹ := by rw [← mul_assoc, hq, one_mul]
    have hnQ := i2_geometric_denominator_ne (t ^ 2) hQ
    rw [i2RegionTerm_row12, i2DepthMass_row12, hqeq]
    unfold Algebra.regionTerm37
    try simp only [inv_inv, pow_one]
    field_simp
    <;> ring

theorem i2_case6bb_reindexed (q t d U V T : ℂ) (n : ℕ) :
    i2SpatialTerm q t d U V T 13 (i2Case6bbEquiv n).val =
      (-q * (1 - t ^ 2) ^ 2 * ((d⁻¹) ^ 1) * t ^ 5 * (T * U) ^ 2 * (T * V) ^ 0 * i2DepthMass q 13) * (t ^ 2) ^ n := by
  unfold i2SpatialTerm
  rw [i2DepthAt_row13]
  unfold shellMonomial
  rw [i2Case6bb_cartan]
  simp only [i2Case6bbEquiv_val]
  have he : 3 * (-1) + 2 * (-1) + 2 * ((n : ℤ)-1) + 3 * (4) + 4 * (0) = ((2 * n + 5 : ℕ) : ℤ) := by omega
  have hn : (4) / 2 = ((2 : ℕ) : ℤ) := by omega
  have hb : (0) = ((0 : ℕ) : ℤ) := by omega
  have hk : -1 = -((1 : ℕ) : ℤ) := by omega
  rw [he]
  try rw [hn]
  try rw [hb]
  try rw [hk]
  simp only [zpow_neg, zpow_natCast, pow_add, pow_mul, mul_pow, pow_zero, pow_one, inv_pow, div_eq_mul_inv]
  ring

theorem summable_norm_i2_case6bb (q t d U V T : ℂ)
    (hQ : ‖t ^ 2‖ < 1) :
    Summable (fun p : I2SpatialRow 13 => ‖i2SpatialTerm q t d U V T 13 p.val‖) := by
  apply i2Case6bbEquiv.summable_iff.mp
  convert i2_summable_norm_one_geometric (-q * (1 - t ^ 2) ^ 2 * ((d⁻¹) ^ 1) * t ^ 5 * (T * U) ^ 2 * (T * V) ^ 0 * i2DepthMass q 13) (t ^ 2) hQ using 1
  exact funext fun n => congrArg norm (i2_case6bb_reindexed q t d U V T n)

theorem hasSum_i2_case6bb_regionTerm (q t d U V T : ℂ)
    (hq : q * t ^ 2 = 1) (hd : d ≠ 0)
    (hQ : ‖t ^ 2‖ < 1)
    : HasSum (fun p : I2SpatialRow 13 => i2SpatialTerm q t d U V T 13 p.val)
      (i2RegionTerm 13 t d (T * U) (T * V)) := by
  have h := i2_hasSum_one_geometric (-q * (1 - t ^ 2) ^ 2 * ((d⁻¹) ^ 1) * t ^ 5 * (T * U) ^ 2 * (T * V) ^ 0 * i2DepthMass q 13) (t ^ 2) hQ
  apply i2Case6bbEquiv.hasSum_iff.mp
  convert h using 1
  · exact funext fun n => i2_case6bb_reindexed q t d U V T n
  · have ht : t ≠ 0 := by
      intro ht
      simp [ht] at hq
    have hqeq : q = (t ^ 2)⁻¹ := by
      calc
        q = q * (t ^ 2 * (t ^ 2)⁻¹) := by rw [mul_inv_cancel₀ (pow_ne_zero 2 ht), mul_one]
        _ = (t ^ 2)⁻¹ := by rw [← mul_assoc, hq, one_mul]
    have hnQ := i2_geometric_denominator_ne (t ^ 2) hQ
    rw [i2RegionTerm_row13, i2DepthMass_row13, hqeq]
    unfold Algebra.regionTerm38
    try simp only [inv_inv, pow_one]
    field_simp
    <;> ring

theorem i2_case6bbb_reindexed (q t d U V T : ℂ) (n : ℕ) :
    i2SpatialTerm q t d U V T 14 (i2Case6bbbEquiv n).val =
      (-q * (1 - t ^ 2) ^ 2 * ((d⁻¹) ^ 1) * t ^ 7 * (T * U) ^ 2 * (T * V) ^ 1 * i2DepthMass q 14) * (T * U * t ^ 4) ^ n := by
  unfold i2SpatialTerm
  rw [i2DepthAt_row14]
  unfold shellMonomial
  rw [i2Case6bbb_cartan]
  simp only [i2Case6bbbEquiv_val]
  have he : 3 * (-1) + 2 * (-1) + 2 * (-(n : ℤ)-2) + 3 * (-2*(-(n : ℤ)-2)) + 4 * (1) = ((4 * n + 7 : ℕ) : ℤ) := by omega
  have hn : (-2*(-(n : ℤ)-2)) / 2 = ((n + 2 : ℕ) : ℤ) := by omega
  have hb : (1) = ((1 : ℕ) : ℤ) := by omega
  have hk : -1 = -((1 : ℕ) : ℤ) := by omega
  rw [he]
  try rw [hn]
  try rw [hb]
  try rw [hk]
  simp only [zpow_neg, zpow_natCast, pow_add, pow_mul, mul_pow, pow_zero, pow_one, inv_pow, div_eq_mul_inv]
  ring

theorem summable_norm_i2_case6bbb (q t d U V T : ℂ)
    (hG : ‖T * U * t ^ 4‖ < 1) :
    Summable (fun p : I2SpatialRow 14 => ‖i2SpatialTerm q t d U V T 14 p.val‖) := by
  apply i2Case6bbbEquiv.summable_iff.mp
  convert i2_summable_norm_one_geometric (-q * (1 - t ^ 2) ^ 2 * ((d⁻¹) ^ 1) * t ^ 7 * (T * U) ^ 2 * (T * V) ^ 1 * i2DepthMass q 14) (T * U * t ^ 4) hG using 1
  exact funext fun n => congrArg norm (i2_case6bbb_reindexed q t d U V T n)

theorem hasSum_i2_case6bbb_regionTerm (q t d U V T : ℂ)
    (hq : q * t ^ 2 = 1) (hd : d ≠ 0)
    (hQ : ‖t ^ 2‖ < 1)
    (hG : ‖T * U * t ^ 4‖ < 1)
    : HasSum (fun p : I2SpatialRow 14 => i2SpatialTerm q t d U V T 14 p.val)
      (i2RegionTerm 14 t d (T * U) (T * V)) := by
  have h := i2_hasSum_one_geometric (-q * (1 - t ^ 2) ^ 2 * ((d⁻¹) ^ 1) * t ^ 7 * (T * U) ^ 2 * (T * V) ^ 1 * i2DepthMass q 14) (T * U * t ^ 4) hG
  apply i2Case6bbbEquiv.hasSum_iff.mp
  convert h using 1
  · exact funext fun n => i2_case6bbb_reindexed q t d U V T n
  · have ht : t ≠ 0 := by
      intro ht
      simp [ht] at hq
    have hqeq : q = (t ^ 2)⁻¹ := by
      calc
        q = q * (t ^ 2 * (t ^ 2)⁻¹) := by rw [mul_inv_cancel₀ (pow_ne_zero 2 ht), mul_one]
        _ = (t ^ 2)⁻¹ := by rw [← mul_assoc, hq, one_mul]
    have hnQ := i2_geometric_denominator_ne (t ^ 2) hQ
    have hnG := i2_geometric_denominator_ne (T * U * t ^ 4) hG
    rw [i2RegionTerm_row14, i2DepthMass_row14, hqeq]
    unfold Algebra.regionTerm39
    try simp only [inv_inv, pow_one]
    field_simp
    <;> ring

theorem i2_case6c_reindexed (q t d U V T : ℂ) (n : ℕ × ℕ × ℕ) :
    i2SpatialTerm q t d U V T 15 (i2Case6cEquiv n).val =
      (-q * (1 - t ^ 2) ^ 2 * ((d⁻¹) ^ 2) * t ^ 6 * (T * U) ^ 2 * (T * V) ^ 0 * i2DepthMass q 15) * (T * V * t / d) ^ n.1 * (t ^ 2) ^ n.2.1 * (t ^ 2) ^ n.2.2 := by
  unfold i2SpatialTerm
  rw [i2DepthAt_row15]
  unfold shellMonomial
  rw [i2Case6c_cartan]
  simp only [i2Case6cEquiv_val]
  have he : 3 * (-(n.1 : ℤ)-2) + 2 * ((n.2.1 : ℤ)) + 2 * ((n.2.2 : ℤ)) + 3 * (4) + 4 * (-(-(n.1 : ℤ)-2)-2) = ((n.1 + 2 * n.2.1 + 2 * n.2.2 + 6 : ℕ) : ℤ) := by omega
  have hn : (4) / 2 = ((2 : ℕ) : ℤ) := by omega
  have hb : (-(-(n.1 : ℤ)-2)-2) = ((n.1 : ℕ) : ℤ) := by omega
  have hk : -(n.1 : ℤ)-2 = -((n.1 + 2 : ℕ) : ℤ) := by omega
  rw [he]
  try rw [hn]
  try rw [hb]
  try rw [hk]
  simp only [zpow_neg, zpow_natCast, pow_add, pow_mul, mul_pow, pow_zero, pow_one, inv_pow, div_eq_mul_inv]
  ring

theorem summable_norm_i2_case6c (q t d U V T : ℂ)
    (hQ : ‖t ^ 2‖ < 1)
    (hN : ‖T * V * t / d‖ < 1) :
    Summable (fun p : I2SpatialRow 15 => ‖i2SpatialTerm q t d U V T 15 p.val‖) := by
  apply i2Case6cEquiv.summable_iff.mp
  convert summable_norm_three_geometric (-q * (1 - t ^ 2) ^ 2 * ((d⁻¹) ^ 2) * t ^ 6 * (T * U) ^ 2 * (T * V) ^ 0 * i2DepthMass q 15) (T * V * t / d) (t ^ 2) (t ^ 2) hN hQ hQ using 1
  exact funext fun n => congrArg norm (i2_case6c_reindexed q t d U V T n)

theorem hasSum_i2_case6c_regionTerm (q t d U V T : ℂ)
    (hq : q * t ^ 2 = 1) (hd : d ≠ 0)
    (hQ : ‖t ^ 2‖ < 1)
    (hN : ‖T * V * t / d‖ < 1)
    : HasSum (fun p : I2SpatialRow 15 => i2SpatialTerm q t d U V T 15 p.val)
      (i2RegionTerm 15 t d (T * U) (T * V)) := by
  have h := hasSum_three_geometric (-q * (1 - t ^ 2) ^ 2 * ((d⁻¹) ^ 2) * t ^ 6 * (T * U) ^ 2 * (T * V) ^ 0 * i2DepthMass q 15) (T * V * t / d) (t ^ 2) (t ^ 2) hN hQ hQ
  apply i2Case6cEquiv.hasSum_iff.mp
  convert h using 1
  · exact funext fun n => i2_case6c_reindexed q t d U V T n
  · have ht : t ≠ 0 := by
      intro ht
      simp [ht] at hq
    have hqeq : q = (t ^ 2)⁻¹ := by
      calc
        q = q * (t ^ 2 * (t ^ 2)⁻¹) := by rw [mul_inv_cancel₀ (pow_ne_zero 2 ht), mul_one]
        _ = (t ^ 2)⁻¹ := by rw [← mul_assoc, hq, one_mul]
    have hnQ := i2_geometric_denominator_ne (t ^ 2) hQ
    have hnN := i2_geometric_denominator_ne (T * V * t / d) hN
    rw [i2RegionTerm_row15, i2DepthMass_row15, hqeq]
    unfold Algebra.regionTerm40
    try simp only [inv_inv, pow_one]
    field_simp
    <;> ring

theorem i2_case6cc_reindexed (q t d U V T : ℂ) (n : ℕ × ℕ) :
    i2SpatialTerm q t d U V T 16 (i2Case6ccEquiv n).val =
      (-q * (1 - t ^ 2) ^ 2 * ((d⁻¹) ^ 2) * t ^ 6 * (T * U) ^ 2 * (T * V) ^ 1 * i2DepthMass q 16) * (T * V * t / d) ^ n.1 * (t ^ 2) ^ n.2 := by
  unfold i2SpatialTerm
  rw [i2DepthAt_row16]
  unfold shellMonomial
  rw [i2Case6cc_cartan]
  simp only [i2Case6ccEquiv_val]
  have he : 3 * (-(n.1 : ℤ)-2) + 2 * (-1) + 2 * ((n.2 : ℤ)-1) + 3 * (4) + 4 * (-(-(n.1 : ℤ)-2)-1) = ((n.1 + 2 * n.2 + 6 : ℕ) : ℤ) := by omega
  have hn : (4) / 2 = ((2 : ℕ) : ℤ) := by omega
  have hb : (-(-(n.1 : ℤ)-2)-1) = ((n.1 + 1 : ℕ) : ℤ) := by omega
  have hk : -(n.1 : ℤ)-2 = -((n.1 + 2 : ℕ) : ℤ) := by omega
  rw [he]
  try rw [hn]
  try rw [hb]
  try rw [hk]
  simp only [zpow_neg, zpow_natCast, pow_add, pow_mul, mul_pow, pow_zero, pow_one, inv_pow, div_eq_mul_inv]
  ring

theorem summable_norm_i2_case6cc (q t d U V T : ℂ)
    (hQ : ‖t ^ 2‖ < 1)
    (hN : ‖T * V * t / d‖ < 1) :
    Summable (fun p : I2SpatialRow 16 => ‖i2SpatialTerm q t d U V T 16 p.val‖) := by
  apply i2Case6ccEquiv.summable_iff.mp
  convert i2_summable_norm_two_geometric (-q * (1 - t ^ 2) ^ 2 * ((d⁻¹) ^ 2) * t ^ 6 * (T * U) ^ 2 * (T * V) ^ 1 * i2DepthMass q 16) (T * V * t / d) (t ^ 2) hN hQ using 1
  exact funext fun n => congrArg norm (i2_case6cc_reindexed q t d U V T n)

theorem hasSum_i2_case6cc_regionTerm (q t d U V T : ℂ)
    (hq : q * t ^ 2 = 1) (hd : d ≠ 0)
    (hQ : ‖t ^ 2‖ < 1)
    (hN : ‖T * V * t / d‖ < 1)
    : HasSum (fun p : I2SpatialRow 16 => i2SpatialTerm q t d U V T 16 p.val)
      (i2RegionTerm 16 t d (T * U) (T * V)) := by
  have h := i2_hasSum_two_geometric (-q * (1 - t ^ 2) ^ 2 * ((d⁻¹) ^ 2) * t ^ 6 * (T * U) ^ 2 * (T * V) ^ 1 * i2DepthMass q 16) (T * V * t / d) (t ^ 2) hN hQ
  apply i2Case6ccEquiv.hasSum_iff.mp
  convert h using 1
  · exact funext fun n => i2_case6cc_reindexed q t d U V T n
  · have ht : t ≠ 0 := by
      intro ht
      simp [ht] at hq
    have hqeq : q = (t ^ 2)⁻¹ := by
      calc
        q = q * (t ^ 2 * (t ^ 2)⁻¹) := by rw [mul_inv_cancel₀ (pow_ne_zero 2 ht), mul_one]
        _ = (t ^ 2)⁻¹ := by rw [← mul_assoc, hq, one_mul]
    have hnQ := i2_geometric_denominator_ne (t ^ 2) hQ
    have hnN := i2_geometric_denominator_ne (T * V * t / d) hN
    rw [i2RegionTerm_row16, i2DepthMass_row16, hqeq]
    unfold Algebra.regionTerm41
    try simp only [inv_inv, pow_one]
    field_simp
    <;> ring

theorem i2_case6ccc_reindexed (q t d U V T : ℂ) (n : ℕ × ℕ) :
    i2SpatialTerm q t d U V T 17 (i2Case6cccEquiv n).val =
      (-q * (1 - t ^ 2) ^ 2 * ((d⁻¹) ^ 2) * t ^ 8 * (T * U) ^ 2 * (T * V) ^ 2 * i2DepthMass q 17) * (T * V * t / d) ^ n.1 * (T * U * t ^ 4) ^ n.2 := by
  unfold i2SpatialTerm
  rw [i2DepthAt_row17]
  unfold shellMonomial
  rw [i2Case6ccc_cartan]
  simp only [i2Case6cccEquiv_val]
  have he : 3 * (-(n.1 : ℤ)-2) + 2 * (-1) + 2 * (-(n.2 : ℤ)-2) + 3 * (-2*(-(n.2 : ℤ)-2)) + 4 * (-(-(n.1 : ℤ)-2)) = ((n.1 + 4 * n.2 + 8 : ℕ) : ℤ) := by omega
  have hn : (-2*(-(n.2 : ℤ)-2)) / 2 = ((n.2 + 2 : ℕ) : ℤ) := by omega
  have hb : (-(-(n.1 : ℤ)-2)) = ((n.1 + 2 : ℕ) : ℤ) := by omega
  have hk : -(n.1 : ℤ)-2 = -((n.1 + 2 : ℕ) : ℤ) := by omega
  rw [he]
  try rw [hn]
  try rw [hb]
  try rw [hk]
  simp only [zpow_neg, zpow_natCast, pow_add, pow_mul, mul_pow, pow_zero, pow_one, inv_pow, div_eq_mul_inv]
  ring

theorem summable_norm_i2_case6ccc (q t d U V T : ℂ)
    (hN : ‖T * V * t / d‖ < 1)
    (hG : ‖T * U * t ^ 4‖ < 1) :
    Summable (fun p : I2SpatialRow 17 => ‖i2SpatialTerm q t d U V T 17 p.val‖) := by
  apply i2Case6cccEquiv.summable_iff.mp
  convert i2_summable_norm_two_geometric (-q * (1 - t ^ 2) ^ 2 * ((d⁻¹) ^ 2) * t ^ 8 * (T * U) ^ 2 * (T * V) ^ 2 * i2DepthMass q 17) (T * V * t / d) (T * U * t ^ 4) hN hG using 1
  exact funext fun n => congrArg norm (i2_case6ccc_reindexed q t d U V T n)

theorem hasSum_i2_case6ccc_regionTerm (q t d U V T : ℂ)
    (hq : q * t ^ 2 = 1) (hd : d ≠ 0)
    (hQ : ‖t ^ 2‖ < 1)
    (hN : ‖T * V * t / d‖ < 1)
    (hG : ‖T * U * t ^ 4‖ < 1)
    : HasSum (fun p : I2SpatialRow 17 => i2SpatialTerm q t d U V T 17 p.val)
      (i2RegionTerm 17 t d (T * U) (T * V)) := by
  have h := i2_hasSum_two_geometric (-q * (1 - t ^ 2) ^ 2 * ((d⁻¹) ^ 2) * t ^ 8 * (T * U) ^ 2 * (T * V) ^ 2 * i2DepthMass q 17) (T * V * t / d) (T * U * t ^ 4) hN hG
  apply i2Case6cccEquiv.hasSum_iff.mp
  convert h using 1
  · exact funext fun n => i2_case6ccc_reindexed q t d U V T n
  · have ht : t ≠ 0 := by
      intro ht
      simp [ht] at hq
    have hqeq : q = (t ^ 2)⁻¹ := by
      calc
        q = q * (t ^ 2 * (t ^ 2)⁻¹) := by rw [mul_inv_cancel₀ (pow_ne_zero 2 ht), mul_one]
        _ = (t ^ 2)⁻¹ := by rw [← mul_assoc, hq, one_mul]
    have hnQ := i2_geometric_denominator_ne (t ^ 2) hQ
    have hnN := i2_geometric_denominator_ne (T * V * t / d) hN
    have hnG := i2_geometric_denominator_ne (T * U * t ^ 4) hG
    rw [i2RegionTerm_row17, i2DepthMass_row17, hqeq]
    unfold Algebra.regionTerm42
    try simp only [inv_inv, pow_one]
    field_simp
    <;> ring

theorem i2_case7_reindexed (q t d U V T : ℂ) (n : ℕ × ℕ × ℕ) :
    i2SpatialTerm q t d U V T 18 (i2Case7Equiv n).val =
      (-q * (1 - t ^ 2) ^ 2 * ((d⁻¹) ^ 1) * t ^ 5 * (T * U) ^ 1 * (T * V) ^ 1 * i2DepthMass q 18) * (T * V * t / d) ^ n.1 * (t ^ 2) ^ n.2.1 * (T * U * t ^ 4) ^ n.2.2 := by
  unfold i2SpatialTerm
  rw [i2DepthAt_row18]
  unfold shellMonomial
  rw [i2Case7_cartan]
  simp only [i2Case7Equiv_val]
  have he : 3 * (-(n.1 : ℤ)-1) + 2 * ((n.2.1 : ℤ)) + 2 * (-(n.2.2 : ℤ)-1) + 3 * (-2*(-(n.2.2 : ℤ)-1)) + 4 * (-(-(n.1 : ℤ)-1)) = ((n.1 + 2 * n.2.1 + 4 * n.2.2 + 5 : ℕ) : ℤ) := by omega
  have hn : (-2*(-(n.2.2 : ℤ)-1)) / 2 = ((n.2.2 + 1 : ℕ) : ℤ) := by omega
  have hb : (-(-(n.1 : ℤ)-1)) = ((n.1 + 1 : ℕ) : ℤ) := by omega
  have hk : -(n.1 : ℤ)-1 = -((n.1 + 1 : ℕ) : ℤ) := by omega
  rw [he]
  try rw [hn]
  try rw [hb]
  try rw [hk]
  simp only [zpow_neg, zpow_natCast, pow_add, pow_mul, mul_pow, pow_zero, pow_one, inv_pow, div_eq_mul_inv]
  ring

theorem summable_norm_i2_case7 (q t d U V T : ℂ)
    (hQ : ‖t ^ 2‖ < 1)
    (hN : ‖T * V * t / d‖ < 1)
    (hG : ‖T * U * t ^ 4‖ < 1) :
    Summable (fun p : I2SpatialRow 18 => ‖i2SpatialTerm q t d U V T 18 p.val‖) := by
  apply i2Case7Equiv.summable_iff.mp
  convert summable_norm_three_geometric (-q * (1 - t ^ 2) ^ 2 * ((d⁻¹) ^ 1) * t ^ 5 * (T * U) ^ 1 * (T * V) ^ 1 * i2DepthMass q 18) (T * V * t / d) (t ^ 2) (T * U * t ^ 4) hN hQ hG using 1
  exact funext fun n => congrArg norm (i2_case7_reindexed q t d U V T n)

theorem hasSum_i2_case7_regionTerm (q t d U V T : ℂ)
    (hq : q * t ^ 2 = 1) (hd : d ≠ 0)
    (hQ : ‖t ^ 2‖ < 1)
    (hN : ‖T * V * t / d‖ < 1)
    (hG : ‖T * U * t ^ 4‖ < 1)
    : HasSum (fun p : I2SpatialRow 18 => i2SpatialTerm q t d U V T 18 p.val)
      (i2RegionTerm 18 t d (T * U) (T * V)) := by
  have h := hasSum_three_geometric (-q * (1 - t ^ 2) ^ 2 * ((d⁻¹) ^ 1) * t ^ 5 * (T * U) ^ 1 * (T * V) ^ 1 * i2DepthMass q 18) (T * V * t / d) (t ^ 2) (T * U * t ^ 4) hN hQ hG
  apply i2Case7Equiv.hasSum_iff.mp
  convert h using 1
  · exact funext fun n => i2_case7_reindexed q t d U V T n
  · have ht : t ≠ 0 := by
      intro ht
      simp [ht] at hq
    have hqeq : q = (t ^ 2)⁻¹ := by
      calc
        q = q * (t ^ 2 * (t ^ 2)⁻¹) := by rw [mul_inv_cancel₀ (pow_ne_zero 2 ht), mul_one]
        _ = (t ^ 2)⁻¹ := by rw [← mul_assoc, hq, one_mul]
    have hnQ := i2_geometric_denominator_ne (t ^ 2) hQ
    have hnN := i2_geometric_denominator_ne (T * V * t / d) hN
    have hnG := i2_geometric_denominator_ne (T * U * t ^ 4) hG
    rw [i2RegionTerm_row18, i2DepthMass_row18, hqeq]
    unfold Algebra.regionTerm43
    try simp only [inv_inv, pow_one]
    field_simp
    <;> ring

theorem i2_case8a_reindexed (q t d U V T : ℂ) (n : Fin 2 × ℕ × ℕ × ℕ) :
    i2SpatialTerm q t d U V T 19 (i2Case8aEquiv n).val =
      (-q * (1 - t ^ 2) ^ 2 * (d ^ 0) * t ^ 6 * (T * U) ^ 2 * (T * V) ^ 0 * i2DepthMass q 19) * (T * V) ^ n.1.val * (T * V * t / d) ^ n.2.1 * ((T * V) ^ 2 * t ^ 2) ^ n.2.2.1 * (t ^ 2) ^ n.2.2.2 := by
  unfold i2SpatialTerm
  rw [i2DepthAt_row19]
  unfold shellMonomial
  rw [i2Case8a_cartan]
  simp only [i2Case8aEquiv_val]
  have he : 3 * (-(n.2.1 : ℤ)) + 2 * (-2*(n.2.2.1 : ℤ)-(n.1.val : ℤ)-2) + 2 * (-(n.2.2.1 : ℤ)-(n.1.val : ℤ)-1+(n.2.2.2 : ℤ)) + 3 * (4) + 4 * (-(-(n.2.1 : ℤ))-(-2*(n.2.2.1 : ℤ)-(n.1.val : ℤ)-2)-2) = ((n.2.1 + 2 * n.2.2.1 + 2 * n.2.2.2 + 6 : ℕ) : ℤ) := by omega
  have hn : (4) / 2 = ((2 : ℕ) : ℤ) := by omega
  have hb : (-(-(n.2.1 : ℤ))-(-2*(n.2.2.1 : ℤ)-(n.1.val : ℤ)-2)-2) = ((n.2.1 + 2 * n.2.2.1 + n.1.val : ℕ) : ℤ) := by omega
  have hk : -(n.2.1 : ℤ) = -((n.2.1 : ℕ) : ℤ) := by omega
  rw [he]
  try rw [hn]
  try rw [hb]
  try rw [hk]
  simp only [zpow_neg, zpow_natCast, pow_add, pow_mul, mul_pow, pow_zero, pow_one, inv_pow, div_eq_mul_inv]
  ring

theorem summable_norm_i2_case8a (q t d U V T : ℂ)
    (hQ : ‖t ^ 2‖ < 1)
    (hN : ‖T * V * t / d‖ < 1)
    (hE : ‖(T * V) ^ 2 * t ^ 2‖ < 1) :
    Summable (fun p : I2SpatialRow 19 => ‖i2SpatialTerm q t d U V T 19 p.val‖) := by
  apply i2Case8aEquiv.summable_iff.mp
  convert i2_summable_norm_parity_geometric (-q * (1 - t ^ 2) ^ 2 * (d ^ 0) * t ^ 6 * (T * U) ^ 2 * (T * V) ^ 0 * i2DepthMass q 19) (T * V) (T * V * t / d) ((T * V) ^ 2 * t ^ 2) (t ^ 2) hN hE hQ using 1
  exact funext fun n => congrArg norm (i2_case8a_reindexed q t d U V T n)

theorem hasSum_i2_case8a_regionTerm (q t d U V T : ℂ)
    (hq : q * t ^ 2 = 1) (hd : d ≠ 0)
    (hQ : ‖t ^ 2‖ < 1)
    (hN : ‖T * V * t / d‖ < 1)
    (hE : ‖(T * V) ^ 2 * t ^ 2‖ < 1)
    : HasSum (fun p : I2SpatialRow 19 => i2SpatialTerm q t d U V T 19 p.val)
      (i2RegionTerm 19 t d (T * U) (T * V)) := by
  have h := i2_hasSum_parity_geometric (-q * (1 - t ^ 2) ^ 2 * (d ^ 0) * t ^ 6 * (T * U) ^ 2 * (T * V) ^ 0 * i2DepthMass q 19) (T * V) (T * V * t / d) ((T * V) ^ 2 * t ^ 2) (t ^ 2) hN hE hQ
  apply i2Case8aEquiv.hasSum_iff.mp
  convert h using 1
  · exact funext fun n => i2_case8a_reindexed q t d U V T n
  · have ht : t ≠ 0 := by
      intro ht
      simp [ht] at hq
    have hqeq : q = (t ^ 2)⁻¹ := by
      calc
        q = q * (t ^ 2 * (t ^ 2)⁻¹) := by rw [mul_inv_cancel₀ (pow_ne_zero 2 ht), mul_one]
        _ = (t ^ 2)⁻¹ := by rw [← mul_assoc, hq, one_mul]
    have hnQ := i2_geometric_denominator_ne (t ^ 2) hQ
    have hnN := i2_geometric_denominator_ne (T * V * t / d) hN
    have hnE := i2_geometric_denominator_ne ((T * V) ^ 2 * t ^ 2) hE
    rw [i2RegionTerm_row19, i2DepthMass_row19, hqeq]
    unfold Algebra.regionTerm44
    try simp only [inv_inv, pow_one]
    field_simp
    <;> ring

theorem i2_case8b_reindexed (q t d U V T : ℂ) (n : ℕ × ℕ) :
    i2SpatialTerm q t d U V T 20 (i2Case8bEquiv n).val =
      (-q * (1 - t ^ 2) ^ 2 * (d ^ 0) * t ^ 4 * (T * U) ^ 2 * (T * V) ^ 0 * i2DepthMass q 20) * (T * V * t / d) ^ n.1 * ((T * V) ^ 2 * t ^ 2) ^ n.2 := by
  unfold i2SpatialTerm
  rw [i2DepthAt_row20]
  unfold shellMonomial
  rw [i2Case8b_cartan _ _ (by omega)]
  simp only [i2Case8bEquiv_val]
  have he : 3 * (-(n.1 : ℤ)) + 2 * (-2*(n.2 : ℤ)-2) + 2 * (-(n.2 : ℤ)-2) + 3 * (4) + 4 * (-(-(n.1 : ℤ))-(-2*(n.2 : ℤ)-2)-2) = ((n.1 + 2 * n.2 + 4 : ℕ) : ℤ) := by omega
  have hn : (4) / 2 = ((2 : ℕ) : ℤ) := by omega
  have hb : (-(-(n.1 : ℤ))-(-2*(n.2 : ℤ)-2)-2) = ((n.1 + 2 * n.2 : ℕ) : ℤ) := by omega
  have hk : -(n.1 : ℤ) = -((n.1 : ℕ) : ℤ) := by omega
  rw [he]
  try rw [hn]
  try rw [hb]
  try rw [hk]
  simp only [zpow_neg, zpow_natCast, pow_add, pow_mul, mul_pow, pow_zero, pow_one, inv_pow, div_eq_mul_inv]
  ring

theorem summable_norm_i2_case8b (q t d U V T : ℂ)
    (hN : ‖T * V * t / d‖ < 1)
    (hE : ‖(T * V) ^ 2 * t ^ 2‖ < 1) :
    Summable (fun p : I2SpatialRow 20 => ‖i2SpatialTerm q t d U V T 20 p.val‖) := by
  apply i2Case8bEquiv.summable_iff.mp
  convert i2_summable_norm_two_geometric (-q * (1 - t ^ 2) ^ 2 * (d ^ 0) * t ^ 4 * (T * U) ^ 2 * (T * V) ^ 0 * i2DepthMass q 20) (T * V * t / d) ((T * V) ^ 2 * t ^ 2) hN hE using 1
  exact funext fun n => congrArg norm (i2_case8b_reindexed q t d U V T n)

theorem hasSum_i2_case8b_regionTerm (q t d U V T : ℂ)
    (hq : q * t ^ 2 = 1) (hd : d ≠ 0)
    (hQ : ‖t ^ 2‖ < 1)
    (hN : ‖T * V * t / d‖ < 1)
    (hE : ‖(T * V) ^ 2 * t ^ 2‖ < 1)
    : HasSum (fun p : I2SpatialRow 20 => i2SpatialTerm q t d U V T 20 p.val)
      (i2RegionTerm 20 t d (T * U) (T * V)) := by
  have h := i2_hasSum_two_geometric (-q * (1 - t ^ 2) ^ 2 * (d ^ 0) * t ^ 4 * (T * U) ^ 2 * (T * V) ^ 0 * i2DepthMass q 20) (T * V * t / d) ((T * V) ^ 2 * t ^ 2) hN hE
  apply i2Case8bEquiv.hasSum_iff.mp
  convert h using 1
  · exact funext fun n => i2_case8b_reindexed q t d U V T n
  · have ht : t ≠ 0 := by
      intro ht
      simp [ht] at hq
    have hqeq : q = (t ^ 2)⁻¹ := by
      calc
        q = q * (t ^ 2 * (t ^ 2)⁻¹) := by rw [mul_inv_cancel₀ (pow_ne_zero 2 ht), mul_one]
        _ = (t ^ 2)⁻¹ := by rw [← mul_assoc, hq, one_mul]
    have hnQ := i2_geometric_denominator_ne (t ^ 2) hQ
    have hnN := i2_geometric_denominator_ne (T * V * t / d) hN
    have hnE := i2_geometric_denominator_ne ((T * V) ^ 2 * t ^ 2) hE
    rw [i2RegionTerm_row20, i2DepthMass_row20, hqeq]
    unfold Algebra.regionTerm45
    try simp only [inv_inv, pow_one]
    field_simp
    <;> ring

theorem i2_case8c_reindexed (q t d U V T : ℂ) (n : ℕ × ℕ) :
    i2SpatialTerm q t d U V T 21 (i2Case8cEquiv n).val =
      (-q * (1 - t ^ 2) ^ 2 * (d ^ 0) * t ^ 2 * (T * U) ^ 1 * (T * V) ^ 1 * i2DepthMass q 21) * (T * V * t / d) ^ n.1 * ((T * V) ^ 2 * t ^ 2) ^ n.2 := by
  unfold i2SpatialTerm
  rw [i2DepthAt_row21]
  unfold shellMonomial
  rw [i2Case8c_cartan _ _ (by omega)]
  simp only [i2Case8cEquiv_val]
  have he : 3 * (-(n.1 : ℤ)) + 2 * (-2*(n.2 : ℤ)-2) + 2 * (-(n.2 : ℤ)-2) + 3 * (2) + 4 * (-(-(n.1 : ℤ))-(-2*(n.2 : ℤ)-2)-1) = ((n.1 + 2 * n.2 + 2 : ℕ) : ℤ) := by omega
  have hn : (2) / 2 = ((1 : ℕ) : ℤ) := by omega
  have hb : (-(-(n.1 : ℤ))-(-2*(n.2 : ℤ)-2)-1) = ((n.1 + 2 * n.2 + 1 : ℕ) : ℤ) := by omega
  have hk : -(n.1 : ℤ) = -((n.1 : ℕ) : ℤ) := by omega
  rw [he]
  try rw [hn]
  try rw [hb]
  try rw [hk]
  simp only [zpow_neg, zpow_natCast, pow_add, pow_mul, mul_pow, pow_zero, pow_one, inv_pow, div_eq_mul_inv]
  ring

theorem summable_norm_i2_case8c (q t d U V T : ℂ)
    (hN : ‖T * V * t / d‖ < 1)
    (hE : ‖(T * V) ^ 2 * t ^ 2‖ < 1) :
    Summable (fun p : I2SpatialRow 21 => ‖i2SpatialTerm q t d U V T 21 p.val‖) := by
  apply i2Case8cEquiv.summable_iff.mp
  convert i2_summable_norm_two_geometric (-q * (1 - t ^ 2) ^ 2 * (d ^ 0) * t ^ 2 * (T * U) ^ 1 * (T * V) ^ 1 * i2DepthMass q 21) (T * V * t / d) ((T * V) ^ 2 * t ^ 2) hN hE using 1
  exact funext fun n => congrArg norm (i2_case8c_reindexed q t d U V T n)

theorem hasSum_i2_case8c_regionTerm (q t d U V T : ℂ)
    (hq : q * t ^ 2 = 1) (hd : d ≠ 0)
    (hQ : ‖t ^ 2‖ < 1)
    (hN : ‖T * V * t / d‖ < 1)
    (hE : ‖(T * V) ^ 2 * t ^ 2‖ < 1)
    : HasSum (fun p : I2SpatialRow 21 => i2SpatialTerm q t d U V T 21 p.val)
      (i2RegionTerm 21 t d (T * U) (T * V)) := by
  have h := i2_hasSum_two_geometric (-q * (1 - t ^ 2) ^ 2 * (d ^ 0) * t ^ 2 * (T * U) ^ 1 * (T * V) ^ 1 * i2DepthMass q 21) (T * V * t / d) ((T * V) ^ 2 * t ^ 2) hN hE
  apply i2Case8cEquiv.hasSum_iff.mp
  convert h using 1
  · exact funext fun n => i2_case8c_reindexed q t d U V T n
  · have ht : t ≠ 0 := by
      intro ht
      simp [ht] at hq
    have hqeq : q = (t ^ 2)⁻¹ := by
      calc
        q = q * (t ^ 2 * (t ^ 2)⁻¹) := by rw [mul_inv_cancel₀ (pow_ne_zero 2 ht), mul_one]
        _ = (t ^ 2)⁻¹ := by rw [← mul_assoc, hq, one_mul]
    have hnQ := i2_geometric_denominator_ne (t ^ 2) hQ
    have hnN := i2_geometric_denominator_ne (T * V * t / d) hN
    have hnE := i2_geometric_denominator_ne ((T * V) ^ 2 * t ^ 2) hE
    rw [i2RegionTerm_row21, i2DepthMass_row21, hqeq]
    unfold Algebra.regionTerm46
    try simp only [inv_inv, pow_one]
    field_simp
    <;> ring

theorem i2_case8d_reindexed (q t d U V T : ℂ) (n : ℕ × ℕ) :
    i2SpatialTerm q t d U V T 22 (i2Case8dEquiv n).val =
      (-q * (1 - t ^ 2) ^ 2 * (d ^ 0) * t ^ 0 * (T * U) ^ 0 * (T * V) ^ 2 * i2DepthMass q 22) * (T * V * t / d) ^ n.1 * ((T * V) ^ 2 * t ^ 2) ^ n.2 := by
  unfold i2SpatialTerm
  rw [i2DepthAt_row22]
  unfold shellMonomial
  rw [i2Case8d_cartan _ _ (by omega)]
  simp only [i2Case8dEquiv_val]
  have he : 3 * (-(n.1 : ℤ)) + 2 * (-2*(n.2 : ℤ)-2) + 2 * (-(n.2 : ℤ)-2) + 3 * (0) + 4 * (-(-(n.1 : ℤ))-(-2*(n.2 : ℤ)-2)) = ((n.1 + 2 * n.2 : ℕ) : ℤ) := by omega
  have hn : (0) / 2 = ((0 : ℕ) : ℤ) := by omega
  have hb : (-(-(n.1 : ℤ))-(-2*(n.2 : ℤ)-2)) = ((n.1 + 2 * n.2 + 2 : ℕ) : ℤ) := by omega
  have hk : -(n.1 : ℤ) = -((n.1 : ℕ) : ℤ) := by omega
  rw [he]
  try rw [hn]
  try rw [hb]
  try rw [hk]
  simp only [zpow_neg, zpow_natCast, pow_add, pow_mul, mul_pow, pow_zero, pow_one, inv_pow, div_eq_mul_inv]
  ring

theorem summable_norm_i2_case8d (q t d U V T : ℂ)
    (hN : ‖T * V * t / d‖ < 1)
    (hE : ‖(T * V) ^ 2 * t ^ 2‖ < 1) :
    Summable (fun p : I2SpatialRow 22 => ‖i2SpatialTerm q t d U V T 22 p.val‖) := by
  apply i2Case8dEquiv.summable_iff.mp
  convert i2_summable_norm_two_geometric (-q * (1 - t ^ 2) ^ 2 * (d ^ 0) * t ^ 0 * (T * U) ^ 0 * (T * V) ^ 2 * i2DepthMass q 22) (T * V * t / d) ((T * V) ^ 2 * t ^ 2) hN hE using 1
  exact funext fun n => congrArg norm (i2_case8d_reindexed q t d U V T n)

theorem hasSum_i2_case8d_regionTerm (q t d U V T : ℂ)
    (hq : q * t ^ 2 = 1) (hd : d ≠ 0)
    (hQ : ‖t ^ 2‖ < 1)
    (hN : ‖T * V * t / d‖ < 1)
    (hE : ‖(T * V) ^ 2 * t ^ 2‖ < 1)
    : HasSum (fun p : I2SpatialRow 22 => i2SpatialTerm q t d U V T 22 p.val)
      (i2RegionTerm 22 t d (T * U) (T * V)) := by
  have h := i2_hasSum_two_geometric (-q * (1 - t ^ 2) ^ 2 * (d ^ 0) * t ^ 0 * (T * U) ^ 0 * (T * V) ^ 2 * i2DepthMass q 22) (T * V * t / d) ((T * V) ^ 2 * t ^ 2) hN hE
  apply i2Case8dEquiv.hasSum_iff.mp
  convert h using 1
  · exact funext fun n => i2_case8d_reindexed q t d U V T n
  · have ht : t ≠ 0 := by
      intro ht
      simp [ht] at hq
    have hqeq : q = (t ^ 2)⁻¹ := by
      calc
        q = q * (t ^ 2 * (t ^ 2)⁻¹) := by rw [mul_inv_cancel₀ (pow_ne_zero 2 ht), mul_one]
        _ = (t ^ 2)⁻¹ := by rw [← mul_assoc, hq, one_mul]
    have hnQ := i2_geometric_denominator_ne (t ^ 2) hQ
    have hnN := i2_geometric_denominator_ne (T * V * t / d) hN
    have hnE := i2_geometric_denominator_ne ((T * V) ^ 2 * t ^ 2) hE
    rw [i2RegionTerm_row22, i2DepthMass_row22, hqeq]
    unfold Algebra.regionTerm47
    try simp only [inv_inv, pow_one]
    field_simp
    <;> ring

theorem i2_case9_reindexed (q t d U V T : ℂ) (n : ℕ × ℕ × ℕ) :
    i2SpatialTerm q t d U V T 23 (i2Case9Equiv n).val =
      (-q * (1 - t ^ 2) ^ 2 * (d ^ 0) * t ^ 6 * (T * U) ^ 3 * (T * V) ^ 0 * i2DepthMass q 23) * (T * V * t / d) ^ n.1 * ((T * V) ^ 2 * t ^ 2) ^ n.2.1 * (T * U * t ^ 2) ^ n.2.2 := by
  unfold i2SpatialTerm
  rw [i2DepthAt_row23]
  unfold shellMonomial
  rw [i2Case9_cartan]
  simp only [i2Case9Equiv_val]
  have he : 3 * (-(n.1 : ℤ)) + 2 * (-2*(n.2.1 : ℤ)-(n.2.2 : ℤ)-3) + 2 * (-(n.2.1 : ℤ)-(n.2.2 : ℤ)-3) + 3 * (2*(-2*(n.2.1 : ℤ)-(n.2.2 : ℤ)-3)-4*(-(n.2.1 : ℤ)-(n.2.2 : ℤ)-3)) + 4 * (2*(-(n.2.1 : ℤ)-(n.2.2 : ℤ)-3)-2*(-2*(n.2.1 : ℤ)-(n.2.2 : ℤ)-3)-(-(n.1 : ℤ))) = ((n.1 + 2 * n.2.1 + 2 * n.2.2 + 6 : ℕ) : ℤ) := by omega
  have hn : (2*(-2*(n.2.1 : ℤ)-(n.2.2 : ℤ)-3)-4*(-(n.2.1 : ℤ)-(n.2.2 : ℤ)-3)) / 2 = ((n.2.2 + 3 : ℕ) : ℤ) := by omega
  have hb : (2*(-(n.2.1 : ℤ)-(n.2.2 : ℤ)-3)-2*(-2*(n.2.1 : ℤ)-(n.2.2 : ℤ)-3)-(-(n.1 : ℤ))) = ((n.1 + 2 * n.2.1 : ℕ) : ℤ) := by omega
  have hk : -(n.1 : ℤ) = -((n.1 : ℕ) : ℤ) := by omega
  rw [he]
  try rw [hn]
  try rw [hb]
  try rw [hk]
  simp only [zpow_neg, zpow_natCast, pow_add, pow_mul, mul_pow, pow_zero, pow_one, inv_pow, div_eq_mul_inv]
  ring

theorem summable_norm_i2_case9 (q t d U V T : ℂ)
    (hN : ‖T * V * t / d‖ < 1)
    (hE : ‖(T * V) ^ 2 * t ^ 2‖ < 1)
    (hF : ‖T * U * t ^ 2‖ < 1) :
    Summable (fun p : I2SpatialRow 23 => ‖i2SpatialTerm q t d U V T 23 p.val‖) := by
  apply i2Case9Equiv.summable_iff.mp
  convert summable_norm_three_geometric (-q * (1 - t ^ 2) ^ 2 * (d ^ 0) * t ^ 6 * (T * U) ^ 3 * (T * V) ^ 0 * i2DepthMass q 23) (T * V * t / d) ((T * V) ^ 2 * t ^ 2) (T * U * t ^ 2) hN hE hF using 1
  exact funext fun n => congrArg norm (i2_case9_reindexed q t d U V T n)

theorem hasSum_i2_case9_regionTerm (q t d U V T : ℂ)
    (hq : q * t ^ 2 = 1) (hd : d ≠ 0)
    (hQ : ‖t ^ 2‖ < 1)
    (hN : ‖T * V * t / d‖ < 1)
    (hE : ‖(T * V) ^ 2 * t ^ 2‖ < 1)
    (hF : ‖T * U * t ^ 2‖ < 1)
    : HasSum (fun p : I2SpatialRow 23 => i2SpatialTerm q t d U V T 23 p.val)
      (i2RegionTerm 23 t d (T * U) (T * V)) := by
  have h := hasSum_three_geometric (-q * (1 - t ^ 2) ^ 2 * (d ^ 0) * t ^ 6 * (T * U) ^ 3 * (T * V) ^ 0 * i2DepthMass q 23) (T * V * t / d) ((T * V) ^ 2 * t ^ 2) (T * U * t ^ 2) hN hE hF
  apply i2Case9Equiv.hasSum_iff.mp
  convert h using 1
  · exact funext fun n => i2_case9_reindexed q t d U V T n
  · have ht : t ≠ 0 := by
      intro ht
      simp [ht] at hq
    have hqeq : q = (t ^ 2)⁻¹ := by
      calc
        q = q * (t ^ 2 * (t ^ 2)⁻¹) := by rw [mul_inv_cancel₀ (pow_ne_zero 2 ht), mul_one]
        _ = (t ^ 2)⁻¹ := by rw [← mul_assoc, hq, one_mul]
    have hnQ := i2_geometric_denominator_ne (t ^ 2) hQ
    have hnN := i2_geometric_denominator_ne (T * V * t / d) hN
    have hnE := i2_geometric_denominator_ne ((T * V) ^ 2 * t ^ 2) hE
    have hnF := i2_geometric_denominator_ne (T * U * t ^ 2) hF
    rw [i2RegionTerm_row23, i2DepthMass_row23, hqeq]
    unfold Algebra.regionTerm48
    try simp only [inv_inv, pow_one]
    field_simp
    <;> ring

theorem i2_case10_reindexed (q t d U V T : ℂ) (n : ℕ × ℕ × ℕ) :
    i2SpatialTerm q t d U V T 24 (i2Case10Equiv n).val =
      (-q * (1 - t ^ 2) ^ 2 * (d ^ 0) * t ^ 8 * (T * U) ^ 3 * (T * V) ^ 0 * i2DepthMass q 24) * (T * V * t / d) ^ n.1 * (T * U * t ^ 2) ^ n.2.1 * (T * U * t ^ 4) ^ n.2.2 := by
  unfold i2SpatialTerm
  rw [i2DepthAt_row24]
  unfold shellMonomial
  rw [i2Case10_cartan]
  simp only [i2Case10Equiv_val]
  have he : 3 * (-(n.1 : ℤ)) + 2 * (-(n.2.1 : ℤ)-2) + 2 * (-(n.2.1 : ℤ)-(n.2.2 : ℤ)-3) + 3 * (-2*(-(n.2.1 : ℤ)-(n.2.2 : ℤ)-3)) + 4 * (-(-(n.1 : ℤ))) = ((n.1 + 2 * n.2.1 + 4 * n.2.2 + 8 : ℕ) : ℤ) := by omega
  have hn : (-2*(-(n.2.1 : ℤ)-(n.2.2 : ℤ)-3)) / 2 = ((n.2.1 + n.2.2 + 3 : ℕ) : ℤ) := by omega
  have hb : (-(-(n.1 : ℤ))) = ((n.1 : ℕ) : ℤ) := by omega
  have hk : -(n.1 : ℤ) = -((n.1 : ℕ) : ℤ) := by omega
  rw [he]
  try rw [hn]
  try rw [hb]
  try rw [hk]
  simp only [zpow_neg, zpow_natCast, pow_add, pow_mul, mul_pow, pow_zero, pow_one, inv_pow, div_eq_mul_inv]
  ring

theorem summable_norm_i2_case10 (q t d U V T : ℂ)
    (hN : ‖T * V * t / d‖ < 1)
    (hF : ‖T * U * t ^ 2‖ < 1)
    (hG : ‖T * U * t ^ 4‖ < 1) :
    Summable (fun p : I2SpatialRow 24 => ‖i2SpatialTerm q t d U V T 24 p.val‖) := by
  apply i2Case10Equiv.summable_iff.mp
  convert summable_norm_three_geometric (-q * (1 - t ^ 2) ^ 2 * (d ^ 0) * t ^ 8 * (T * U) ^ 3 * (T * V) ^ 0 * i2DepthMass q 24) (T * V * t / d) (T * U * t ^ 2) (T * U * t ^ 4) hN hF hG using 1
  exact funext fun n => congrArg norm (i2_case10_reindexed q t d U V T n)

theorem hasSum_i2_case10_regionTerm (q t d U V T : ℂ)
    (hq : q * t ^ 2 = 1) (hd : d ≠ 0)
    (hQ : ‖t ^ 2‖ < 1)
    (hN : ‖T * V * t / d‖ < 1)
    (hF : ‖T * U * t ^ 2‖ < 1)
    (hG : ‖T * U * t ^ 4‖ < 1)
    : HasSum (fun p : I2SpatialRow 24 => i2SpatialTerm q t d U V T 24 p.val)
      (i2RegionTerm 24 t d (T * U) (T * V)) := by
  have h := hasSum_three_geometric (-q * (1 - t ^ 2) ^ 2 * (d ^ 0) * t ^ 8 * (T * U) ^ 3 * (T * V) ^ 0 * i2DepthMass q 24) (T * V * t / d) (T * U * t ^ 2) (T * U * t ^ 4) hN hF hG
  apply i2Case10Equiv.hasSum_iff.mp
  convert h using 1
  · exact funext fun n => i2_case10_reindexed q t d U V T n
  · have ht : t ≠ 0 := by
      intro ht
      simp [ht] at hq
    have hqeq : q = (t ^ 2)⁻¹ := by
      calc
        q = q * (t ^ 2 * (t ^ 2)⁻¹) := by rw [mul_inv_cancel₀ (pow_ne_zero 2 ht), mul_one]
        _ = (t ^ 2)⁻¹ := by rw [← mul_assoc, hq, one_mul]
    have hnQ := i2_geometric_denominator_ne (t ^ 2) hQ
    have hnN := i2_geometric_denominator_ne (T * V * t / d) hN
    have hnF := i2_geometric_denominator_ne (T * U * t ^ 2) hF
    have hnG := i2_geometric_denominator_ne (T * U * t ^ 4) hG
    rw [i2RegionTerm_row24, i2DepthMass_row24, hqeq]
    unfold Algebra.regionTerm49
    try simp only [inv_inv, pow_one]
    field_simp
    <;> ring

end FourierJacobi.Analysis
