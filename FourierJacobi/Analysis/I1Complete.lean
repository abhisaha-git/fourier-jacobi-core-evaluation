import FourierJacobi.Analysis.MasterSeries

/-!+# Infinite I1 valuation rows

The monomial below is the independent entry/minor valuation monomial, with
the actual I1 coefficient incorporated using q*t^2=1.  It is not defined by
any finite region fraction. Each lattice cone is parameterized explicitly;
both inverse laws and every infinite geometric evaluation are kernel checked.
The parity refinements of rows 3a and 8a are kept visible.
-/

noncomputable section
namespace FourierJacobi.Analysis
open FourierJacobi.Valuations

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

def i1Raw (t d U V T : ℂ) (p : ℤ × ℤ × ℤ) (c : ℕ) : ℂ :=
  let ell := (cartanIndices 1 p.1 p.2.1 p.2.2 c).1
  let b := (cartanIndices 1 p.1 p.2.1 p.2.2 c).2
  (1 - t ^ 2) ^ 3 * d ^ p.1 *
    t ^ (3 * p.1 + 2 * p.2.1 + 2 * p.2.2 + 3 * ell + 4 * b - 2) *
    (T * U) ^ (ell / 2) * (T * V) ^ b

theorem i1Raw_eq_shell (q t d U V T : ℂ) (ht : t ≠ 0)
    (hqt : q * t ^ 2 = 1) (p : ℤ × ℤ × ℤ) (c : ℕ) :
    i1Raw t d U V T p c = shellCoeff q 1 * shellMonomial t d U V T 1 p c := by
  have hq : q = (t ^ 2)⁻¹ := by
    calc
      q = q * (t ^ 2 * (t ^ 2)⁻¹) := by rw [mul_inv_cancel₀ (pow_ne_zero 2 ht), mul_one]
      _ = (t ^ 2)⁻¹ := by rw [← mul_assoc, hqt, one_mul]
  have hi : q⁻¹ = t ^ 2 := by rw [hq, inv_inv]
  unfold i1Raw shellMonomial shellCoeff
  simp only [one_ne_zero, ↓reduceIte]
  rw [zpow_sub₀ ht, hi, hq]
  simp only [zpow_ofNat, div_eq_mul_inv]
  ring

theorem i1_summable_norm_two_geometric (C a b : ℂ)
    (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    Summable (fun n : ℕ × ℕ => ‖C * a ^ n.1 * b ^ n.2‖) := by
  have h := (geometric_norm_summable a ha).mul_norm (geometric_norm_summable b hb)
  simpa only [norm_mul, mul_assoc] using h.mul_left ‖C‖

theorem i1_hasSum_two_geometric (C a b : ℂ)
    (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    HasSum (fun n : ℕ × ℕ => C * a ^ n.1 * b ^ n.2)
      (C * (1 - a)⁻¹ * (1 - b)⁻¹) := by
  have hA := (hasSum_geometric_of_norm_lt_one ha).tsum_eq
  have hB := (hasSum_geometric_of_norm_lt_one hb).tsum_eq
  have hs := (i1_summable_norm_two_geometric C a b ha hb).of_norm
  have he : (∑' n : ℕ × ℕ, C * a ^ n.1 * b ^ n.2) =
      C * (1 - a)⁻¹ * (1 - b)⁻¹ := by
    rw [hs.tsum_prod]
    simp only [tsum_mul_left, hB, tsum_mul_right, hA]
  exact he ▸ hs.hasSum

/-- Source I1 row 1, with integer valuation inequalities. -/
abbrev I1R1Row := {p : ℤ × ℤ × ℤ //
  let k := p.1; let j := p.2.1; let h := p.2.2; 1 ≤ k ∧ -2 * k ≤ j ∧ -k ≤ h}

def i1r1Equiv : (ℕ × ℕ × ℕ) ≃ I1R1Row where
  toFun n := ⟨(by
    rcases n with ⟨a, b, c⟩
    exact ((a : ℤ) + 1, (b : ℤ) - 2 * (a : ℤ) - 2, (c : ℤ) - (a : ℤ) - 1)), by
      rcases n with ⟨a, b, c⟩
      dsimp
      omega⟩
  invFun p := (by
    let k := p.val.1; let j := p.val.2.1; let h := p.val.2.2
    exact ((k - 1).toNat, ( j + 2 * k).toNat, ( h + k).toNat))
  left_inv n := by
    rcases n with ⟨a, b, c⟩
    simp only [Prod.mk.injEq]
    try dsimp
    omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩,hp⟩
    dsimp at hp ⊢
    simp only [Prod.mk.injEq]
    omega

@[simp] theorem i1r1Equiv_val (a b c : ℕ) :
    (i1r1Equiv (a,b,c)).val = ((a : ℤ) + 1, (b : ℤ) - 2 * (a : ℤ) - 2, (c : ℤ) - (a : ℤ) - 1) := rfl

theorem i1r1_cartan (p : I1R1Row) (depth : ℕ) :
    cartanIndices 1 p.val.1 p.val.2.1 p.val.2.2 depth = (2, p.val.1 - 1) := by
  rw [← tableOne_correct _ _ _ _ (by omega)]
  rcases p with ⟨⟨k,j,h⟩,hp⟩
  dsimp at hp ⊢
  
  unfold tableOne collisionRows
  split_ifs <;> simp only [Prod.mk.injEq] <;> omega

theorem i1r1_reindexed (t d U V T : ℂ)  (depth : ℕ)
    (n : ℕ × ℕ × ℕ) :
    i1Raw t d U V T (i1r1Equiv n).val depth = ((1 - t ^ 2) ^ 3 * d * (T * U) * t) * (d * T * V * t) ^ n.1 * (t ^ 2) ^ n.2.1 * (t ^ 2) ^ n.2.2 := by
  rcases n with ⟨a, b, c⟩
  unfold i1Raw
  
  rw [i1r1_cartan]
  
  simp only [i1r1Equiv_val]
  have he : 3 * ((a : ℤ) + 1) + 2 * ( (b : ℤ) - 2 * (a : ℤ) - 2) + 2 * ( (c : ℤ) - (a : ℤ) - 1) +
      3 * (2) + 4 * ( ((a : ℤ) + 1) - 1) - 2 = ((a + 2*b + 2*c + 1 : ℕ) : ℤ) := by omega
  have hk : (a : ℤ) + 1 = ((a+1 : ℕ) : ℤ) := by omega
  have hb :  ((a : ℤ) + 1) - 1 = ((a : ℕ) : ℤ) := by omega
  have hl : (2) / 2 = ((1 : ℕ) : ℤ) := by omega
  rw [he, hl, hb]
  try rw [hk]
  
  simp only [zpow_neg, zpow_natCast, zpow_ofNat, pow_add, pow_mul, mul_pow,
    pow_one, pow_zero, one_mul, mul_one, mul_inv_rev, div_eq_mul_inv, inv_pow]
  ring

theorem hasSum_i1r1_raw (t d U V T : ℂ)  (depth : ℕ)
    (h0 : ‖d * T * V * t‖ < 1)
    (h1 : ‖t ^ 2‖ < 1)
    (h2 : ‖t ^ 2‖ < 1) :
    HasSum (fun p : I1R1Row => i1Raw t d U V T p.val depth)
      (((1 - t ^ 2) ^ 3 * d * (T * U) * t) * (1 - d * T * V * t)⁻¹ * (1 - t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹) := by
  apply i1r1Equiv.hasSum_iff.mp
  convert hasSum_three_geometric
    ((1 - t ^ 2) ^ 3 * d * (T * U) * t) (d * T * V * t) (t ^ 2) (t ^ 2)
    h0 h1 h2 using 1
  exact funext fun n => i1r1_reindexed t d U V T depth n

theorem summable_norm_i1r1_raw (t d U V T : ℂ)  (depth : ℕ)
    (h0 : ‖d * T * V * t‖ < 1)
    (h1 : ‖t ^ 2‖ < 1)
    (h2 : ‖t ^ 2‖ < 1) :
    Summable (fun p : I1R1Row => ‖i1Raw t d U V T p.val depth‖) := by
  apply i1r1Equiv.summable_iff.mp
  convert summable_norm_three_geometric
    ((1 - t ^ 2) ^ 3 * d * (T * U) * t) (d * T * V * t) (t ^ 2) (t ^ 2)
    h0 h1 h2 using 1
  exact funext fun n => congrArg norm
    (i1r1_reindexed t d U V T depth n)

/-- Source I1 row 2, with integer valuation inequalities. -/
abbrev I1R2Row := {p : ℤ × ℤ × ℤ //
  let k := p.1; let j := p.2.1; let h := p.2.2; 1 ≤ k ∧ -2 * k ≤ j ∧ h < -k}

def i1r2Equiv : (ℕ × ℕ × ℕ) ≃ I1R2Row where
  toFun n := ⟨(by
    rcases n with ⟨a, b, c⟩
    exact ((a : ℤ) + 1, (b : ℤ) - 2 * (a : ℤ) - 2, -(a : ℤ) - (c : ℤ) - 2)), by
      rcases n with ⟨a, b, c⟩
      dsimp
      omega⟩
  invFun p := (by
    let k := p.val.1; let j := p.val.2.1; let h := p.val.2.2
    exact ((k - 1).toNat, ( j + 2 * k).toNat, ( -h - k - 1).toNat))
  left_inv n := by
    rcases n with ⟨a, b, c⟩
    simp only [Prod.mk.injEq]
    try dsimp
    omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩,hp⟩
    dsimp at hp ⊢
    simp only [Prod.mk.injEq]
    omega

@[simp] theorem i1r2Equiv_val (a b c : ℕ) :
    (i1r2Equiv (a,b,c)).val = ((a : ℤ) + 1, (b : ℤ) - 2 * (a : ℤ) - 2, -(a : ℤ) - (c : ℤ) - 2) := rfl

theorem i1r2_cartan (p : I1R2Row) (depth : ℕ) :
    cartanIndices 1 p.val.1 p.val.2.1 p.val.2.2 depth = (-2*p.val.1-2*p.val.2.2, p.val.1) := by
  rw [← tableOne_correct _ _ _ _ (by omega)]
  rcases p with ⟨⟨k,j,h⟩,hp⟩
  dsimp at hp ⊢
  
  unfold tableOne collisionRows
  split_ifs <;> simp only [Prod.mk.injEq] <;> omega

theorem i1r2_reindexed (t d U V T : ℂ)  (depth : ℕ)
    (n : ℕ × ℕ × ℕ) :
    i1Raw t d U V T (i1r2Equiv n).val depth = ((1 - t ^ 2) ^ 3 * d * (T * U) * (T * V) * t ^ 3) * (d * T * V * t) ^ n.1 * (t ^ 2) ^ n.2.1 * (T * U * t ^ 4) ^ n.2.2 := by
  rcases n with ⟨a, b, c⟩
  unfold i1Raw
  
  rw [i1r2_cartan]
  
  simp only [i1r2Equiv_val]
  have he : 3 * ((a : ℤ) + 1) + 2 * ( (b : ℤ) - 2 * (a : ℤ) - 2) + 2 * ( -(a : ℤ) - (c : ℤ) - 2) +
      3 * (-2*((a : ℤ) + 1)-2*( -(a : ℤ) - (c : ℤ) - 2)) + 4 * ( ((a : ℤ) + 1)) - 2 = ((a + 2*b + 4*c + 3 : ℕ) : ℤ) := by omega
  have hk : (a : ℤ) + 1 = ((a+1 : ℕ) : ℤ) := by omega
  have hb :  ((a : ℤ) + 1) = ((a+1 : ℕ) : ℤ) := by omega
  have hl : (-2*((a : ℤ) + 1)-2*( -(a : ℤ) - (c : ℤ) - 2)) / 2 = ((c+1 : ℕ) : ℤ) := by omega
  rw [he, hl, hb]
  try rw [hk]
  
  simp only [zpow_neg, zpow_natCast, zpow_ofNat, pow_add, pow_mul, mul_pow,
    pow_one, pow_zero, one_mul, mul_one, mul_inv_rev, div_eq_mul_inv, inv_pow]
  ring

theorem hasSum_i1r2_raw (t d U V T : ℂ)  (depth : ℕ)
    (h0 : ‖d * T * V * t‖ < 1)
    (h1 : ‖t ^ 2‖ < 1)
    (h2 : ‖T * U * t ^ 4‖ < 1) :
    HasSum (fun p : I1R2Row => i1Raw t d U V T p.val depth)
      (((1 - t ^ 2) ^ 3 * d * (T * U) * (T * V) * t ^ 3) * (1 - d * T * V * t)⁻¹ * (1 - t ^ 2)⁻¹ * (1 - T * U * t ^ 4)⁻¹) := by
  apply i1r2Equiv.hasSum_iff.mp
  convert hasSum_three_geometric
    ((1 - t ^ 2) ^ 3 * d * (T * U) * (T * V) * t ^ 3) (d * T * V * t) (t ^ 2) (T * U * t ^ 4)
    h0 h1 h2 using 1
  exact funext fun n => i1r2_reindexed t d U V T depth n

theorem summable_norm_i1r2_raw (t d U V T : ℂ)  (depth : ℕ)
    (h0 : ‖d * T * V * t‖ < 1)
    (h1 : ‖t ^ 2‖ < 1)
    (h2 : ‖T * U * t ^ 4‖ < 1) :
    Summable (fun p : I1R2Row => ‖i1Raw t d U V T p.val depth‖) := by
  apply i1r2Equiv.summable_iff.mp
  convert summable_norm_three_geometric
    ((1 - t ^ 2) ^ 3 * d * (T * U) * (T * V) * t ^ 3) (d * T * V * t) (t ^ 2) (T * U * t ^ 4)
    h0 h1 h2 using 1
  exact funext fun n => congrArg norm
    (i1r2_reindexed t d U V T depth n)

/-- Source I1 row 3ae, with integer valuation inequalities. -/
abbrev I1R3AERow := {p : ℤ × ℤ × ℤ //
  let k := p.1; let j := p.2.1; let h := p.2.2; 1 ≤ k ∧ j < -2*k ∧ k+j ≤ h ∧ j ≤ 2*h ∧ j % 2 = 0}

def i1r3aeEquiv : (ℕ × ℕ × ℕ) ≃ I1R3AERow where
  toFun n := ⟨(by
    rcases n with ⟨a, b, c⟩
    exact ((a : ℤ)+1,-2*(a : ℤ)-2*(b : ℤ)-4,-(a : ℤ)-(b : ℤ)-2+(c : ℤ))), by
      rcases n with ⟨a, b, c⟩
      dsimp
      omega⟩
  invFun p := (by
    let k := p.val.1; let j := p.val.2.1; let h := p.val.2.2
    exact ((k-1).toNat, ((-j-2*k-2)/2).toNat, (h-j/2).toNat))
  left_inv n := by
    rcases n with ⟨a, b, c⟩
    simp only [Prod.mk.injEq]
    try dsimp
    omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩,hp⟩
    dsimp at hp ⊢
    simp only [Prod.mk.injEq]
    omega

@[simp] theorem i1r3aeEquiv_val (a b c : ℕ) :
    (i1r3aeEquiv (a,b,c)).val = ((a : ℤ)+1,-2*(a : ℤ)-2*(b : ℤ)-4,-(a : ℤ)-(b : ℤ)-2+(c : ℤ)) := rfl

theorem i1r3ae_cartan (p : I1R3AERow) (depth : ℕ) :
    cartanIndices 1 p.val.1 p.val.2.1 p.val.2.2 depth = (2,-p.val.1-p.val.2.1-1) := by
  rw [← tableOne_correct _ _ _ _ (by omega)]
  rcases p with ⟨⟨k,j,h⟩,hp⟩
  dsimp at hp ⊢
  have hp0 : 1 ≤ k ∧ j < -2*k ∧ k+j ≤ h ∧ j ≤ 2*h := ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1⟩
  clear hp
  rw [tableOne, if_pos hp0.1, if_neg (by omega : ¬ -2*k ≤ j),
    if_neg (by omega : ¬ h < k+j)]
  rw [collisionRows, if_pos (by omega : j-1+1 ≤ 2*h)]
  norm_num

theorem i1r3ae_reindexed (t d U V T : ℂ)  (depth : ℕ)
    (n : ℕ × ℕ × ℕ) :
    i1Raw t d U V T (i1r3aeEquiv n).val depth = ((1 - t ^ 2) ^ 3 * d * (T * U) * (T * V)^2 * t^3) * (d * T * V * t) ^ n.1 * ((T * V) ^ 2 * t ^ 2) ^ n.2.1 * (t ^ 2) ^ n.2.2 := by
  rcases n with ⟨a, b, c⟩
  unfold i1Raw
  
  rw [i1r3ae_cartan]
  
  simp only [i1r3aeEquiv_val]
  have he : 3 * ((a : ℤ)+1) + 2 * (-2*(a : ℤ)-2*(b : ℤ)-4) + 2 * (-(a : ℤ)-(b : ℤ)-2+(c : ℤ)) +
      3 * (2) + 4 * (-((a : ℤ)+1)-(-2*(a : ℤ)-2*(b : ℤ)-4)-1) - 2 = ((a+2*b+2*c+3 : ℕ) : ℤ) := by omega
  have hk : (a : ℤ)+1 = ((a+1 : ℕ) : ℤ) := by omega
  have hb : -((a : ℤ)+1)-(-2*(a : ℤ)-2*(b : ℤ)-4)-1 = ((a+2*b+2 : ℕ) : ℤ) := by omega
  have hl : (2) / 2 = ((1 : ℕ) : ℤ) := by omega
  rw [he, hl, hb]
  try rw [hk]
  
  simp only [zpow_neg, zpow_natCast, zpow_ofNat, pow_add, pow_mul, mul_pow,
    pow_one, pow_zero, one_mul, mul_one, mul_inv_rev, div_eq_mul_inv, inv_pow]
  ring

theorem hasSum_i1r3ae_raw (t d U V T : ℂ)  (depth : ℕ)
    (h0 : ‖d * T * V * t‖ < 1)
    (h1 : ‖(T * V) ^ 2 * t ^ 2‖ < 1)
    (h2 : ‖t ^ 2‖ < 1) :
    HasSum (fun p : I1R3AERow => i1Raw t d U V T p.val depth)
      (((1 - t ^ 2) ^ 3 * d * (T * U) * (T * V)^2 * t^3) * (1 - d * T * V * t)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹) := by
  apply i1r3aeEquiv.hasSum_iff.mp
  convert hasSum_three_geometric
    ((1 - t ^ 2) ^ 3 * d * (T * U) * (T * V)^2 * t^3) (d * T * V * t) ((T * V) ^ 2 * t ^ 2) (t ^ 2)
    h0 h1 h2 using 1
  exact funext fun n => i1r3ae_reindexed t d U V T depth n

theorem summable_norm_i1r3ae_raw (t d U V T : ℂ)  (depth : ℕ)
    (h0 : ‖d * T * V * t‖ < 1)
    (h1 : ‖(T * V) ^ 2 * t ^ 2‖ < 1)
    (h2 : ‖t ^ 2‖ < 1) :
    Summable (fun p : I1R3AERow => ‖i1Raw t d U V T p.val depth‖) := by
  apply i1r3aeEquiv.summable_iff.mp
  convert summable_norm_three_geometric
    ((1 - t ^ 2) ^ 3 * d * (T * U) * (T * V)^2 * t^3) (d * T * V * t) ((T * V) ^ 2 * t ^ 2) (t ^ 2)
    h0 h1 h2 using 1
  exact funext fun n => congrArg norm
    (i1r3ae_reindexed t d U V T depth n)

/-- Source I1 row 3ao, with integer valuation inequalities. -/
abbrev I1R3AORow := {p : ℤ × ℤ × ℤ //
  let k := p.1; let j := p.2.1; let h := p.2.2; 1 ≤ k ∧ j < -2*k ∧ k+j ≤ h ∧ j ≤ 2*h ∧ j % 2 = 1}

def i1r3aoEquiv : (ℕ × ℕ × ℕ) ≃ I1R3AORow where
  toFun n := ⟨(by
    rcases n with ⟨a, b, c⟩
    exact ((a : ℤ)+1,-2*(a : ℤ)-2*(b : ℤ)-3,-(a : ℤ)-(b : ℤ)-1+(c : ℤ))), by
      rcases n with ⟨a, b, c⟩
      dsimp
      omega⟩
  invFun p := (by
    let k := p.val.1; let j := p.val.2.1; let h := p.val.2.2
    exact ((k-1).toNat, ((-j-2*k-1)/2).toNat, (h-(j+1)/2).toNat))
  left_inv n := by
    rcases n with ⟨a, b, c⟩
    simp only [Prod.mk.injEq]
    try dsimp
    omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩,hp⟩
    dsimp at hp ⊢
    simp only [Prod.mk.injEq]
    omega

@[simp] theorem i1r3aoEquiv_val (a b c : ℕ) :
    (i1r3aoEquiv (a,b,c)).val = ((a : ℤ)+1,-2*(a : ℤ)-2*(b : ℤ)-3,-(a : ℤ)-(b : ℤ)-1+(c : ℤ)) := rfl

theorem i1r3ao_cartan (p : I1R3AORow) (depth : ℕ) :
    cartanIndices 1 p.val.1 p.val.2.1 p.val.2.2 depth = (2,-p.val.1-p.val.2.1-1) := by
  rw [← tableOne_correct _ _ _ _ (by omega)]
  rcases p with ⟨⟨k,j,h⟩,hp⟩
  dsimp at hp ⊢
  have hp0 : 1 ≤ k ∧ j < -2*k ∧ k+j ≤ h ∧ j ≤ 2*h := ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1⟩
  clear hp
  rw [tableOne, if_pos hp0.1, if_neg (by omega : ¬ -2*k ≤ j),
    if_neg (by omega : ¬ h < k+j)]
  rw [collisionRows, if_pos (by omega : j-1+1 ≤ 2*h)]
  norm_num

theorem i1r3ao_reindexed (t d U V T : ℂ)  (depth : ℕ)
    (n : ℕ × ℕ × ℕ) :
    i1Raw t d U V T (i1r3aoEquiv n).val depth = ((1 - t ^ 2) ^ 3 * d * (T * U) * (T * V) * t^3) * (d * T * V * t) ^ n.1 * ((T * V) ^ 2 * t ^ 2) ^ n.2.1 * (t ^ 2) ^ n.2.2 := by
  rcases n with ⟨a, b, c⟩
  unfold i1Raw
  
  rw [i1r3ao_cartan]
  
  simp only [i1r3aoEquiv_val]
  have he : 3 * ((a : ℤ)+1) + 2 * (-2*(a : ℤ)-2*(b : ℤ)-3) + 2 * (-(a : ℤ)-(b : ℤ)-1+(c : ℤ)) +
      3 * (2) + 4 * (-((a : ℤ)+1)-(-2*(a : ℤ)-2*(b : ℤ)-3)-1) - 2 = ((a+2*b+2*c+3 : ℕ) : ℤ) := by omega
  have hk : (a : ℤ)+1 = ((a+1 : ℕ) : ℤ) := by omega
  have hb : -((a : ℤ)+1)-(-2*(a : ℤ)-2*(b : ℤ)-3)-1 = ((a+2*b+1 : ℕ) : ℤ) := by omega
  have hl : (2) / 2 = ((1 : ℕ) : ℤ) := by omega
  rw [he, hl, hb]
  try rw [hk]
  
  simp only [zpow_neg, zpow_natCast, zpow_ofNat, pow_add, pow_mul, mul_pow,
    pow_one, pow_zero, one_mul, mul_one, mul_inv_rev, div_eq_mul_inv, inv_pow]
  ring

theorem hasSum_i1r3ao_raw (t d U V T : ℂ)  (depth : ℕ)
    (h0 : ‖d * T * V * t‖ < 1)
    (h1 : ‖(T * V) ^ 2 * t ^ 2‖ < 1)
    (h2 : ‖t ^ 2‖ < 1) :
    HasSum (fun p : I1R3AORow => i1Raw t d U V T p.val depth)
      (((1 - t ^ 2) ^ 3 * d * (T * U) * (T * V) * t^3) * (1 - d * T * V * t)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹) := by
  apply i1r3aoEquiv.hasSum_iff.mp
  convert hasSum_three_geometric
    ((1 - t ^ 2) ^ 3 * d * (T * U) * (T * V) * t^3) (d * T * V * t) ((T * V) ^ 2 * t ^ 2) (t ^ 2)
    h0 h1 h2 using 1
  exact funext fun n => i1r3ao_reindexed t d U V T depth n

theorem summable_norm_i1r3ao_raw (t d U V T : ℂ)  (depth : ℕ)
    (h0 : ‖d * T * V * t‖ < 1)
    (h1 : ‖(T * V) ^ 2 * t ^ 2‖ < 1)
    (h2 : ‖t ^ 2‖ < 1) :
    Summable (fun p : I1R3AORow => ‖i1Raw t d U V T p.val depth‖) := by
  apply i1r3aoEquiv.summable_iff.mp
  convert summable_norm_three_geometric
    ((1 - t ^ 2) ^ 3 * d * (T * U) * (T * V) * t^3) (d * T * V * t) ((T * V) ^ 2 * t ^ 2) (t ^ 2)
    h0 h1 h2 using 1
  exact funext fun n => congrArg norm
    (i1r3ao_reindexed t d U V T depth n)

/-- Source I1 row 3b, with integer valuation inequalities. -/
abbrev I1R3BRow := {p : ℤ × ℤ × ℤ //
  let k := p.1; let j := p.2.1; let h := p.2.2; 1 ≤ k ∧ j < -2*k ∧ k+j ≤ h ∧ 2*h = j-1}

def i1r3bEquiv : (ℕ × ℕ) ≃ I1R3BRow where
  toFun n := ⟨(by
    rcases n with ⟨a, b⟩
    exact ((a : ℤ)+1,-2*(a : ℤ)-2*(b : ℤ)-3,-(a : ℤ)-(b : ℤ)-2)), by
      rcases n with ⟨a, b⟩
      dsimp
      omega⟩
  invFun p := (by
    let k := p.val.1; let j := p.val.2.1; let h := p.val.2.2
    exact ((k-1).toNat, ((-j-2*k-1)/2).toNat))
  left_inv n := by
    rcases n with ⟨a, b⟩
    simp only [Prod.mk.injEq]
    try dsimp
    omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩,hp⟩
    dsimp at hp ⊢
    simp only [Prod.mk.injEq]
    omega

@[simp] theorem i1r3bEquiv_val (a b : ℕ) :
    (i1r3bEquiv (a,b)).val = ((a : ℤ)+1,-2*(a : ℤ)-2*(b : ℤ)-3,-(a : ℤ)-(b : ℤ)-2) := rfl

theorem i1r3b_cartan (p : I1R3BRow)  :
    cartanIndices 1 p.val.1 p.val.2.1 p.val.2.2 0 = (2,-p.val.1-p.val.2.1-1) := by
  rw [← tableOne_correct _ _ _ _ (by omega)]
  rcases p with ⟨⟨k,j,h⟩,hp⟩
  dsimp at hp ⊢
  
  unfold tableOne collisionRows
  split_ifs <;> simp only [Prod.mk.injEq] <;> omega

theorem i1r3b_reindexed (t d U V T : ℂ)  
    (n : ℕ × ℕ) :
    i1Raw t d U V T (i1r3bEquiv n).val 0 = ((1 - t ^ 2) ^ 3 * d * (T * U) * (T * V) * t) * (d * T * V * t) ^ n.1 * ((T * V) ^ 2 * t ^ 2) ^ n.2 := by
  rcases n with ⟨a, b⟩
  unfold i1Raw
  simp only [Nat.cast_zero]
  rw [i1r3b_cartan]
  
  simp only [i1r3bEquiv_val]
  have he : 3 * ((a : ℤ)+1) + 2 * (-2*(a : ℤ)-2*(b : ℤ)-3) + 2 * (-(a : ℤ)-(b : ℤ)-2) +
      3 * (2) + 4 * (-((a : ℤ)+1)-(-2*(a : ℤ)-2*(b : ℤ)-3)-1) - 2 = ((a+2*b+1 : ℕ) : ℤ) := by omega
  have hk : (a : ℤ)+1 = ((a+1 : ℕ) : ℤ) := by omega
  have hb : -((a : ℤ)+1)-(-2*(a : ℤ)-2*(b : ℤ)-3)-1 = ((a+2*b+1 : ℕ) : ℤ) := by omega
  have hl : (2) / 2 = ((1 : ℕ) : ℤ) := by omega
  rw [he, hl, hb]
  try rw [hk]
  
  simp only [zpow_neg, zpow_natCast, zpow_ofNat, pow_add, pow_mul, mul_pow,
    pow_one, pow_zero, one_mul, mul_one, mul_inv_rev, div_eq_mul_inv, inv_pow]
  ring

theorem hasSum_i1r3b_raw (t d U V T : ℂ)  
    (h0 : ‖d * T * V * t‖ < 1)
    (h1 : ‖(T * V) ^ 2 * t ^ 2‖ < 1) :
    HasSum (fun p : I1R3BRow => i1Raw t d U V T p.val 0)
      (((1 - t ^ 2) ^ 3 * d * (T * U) * (T * V) * t) * (1 - d * T * V * t)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹) := by
  apply i1r3bEquiv.hasSum_iff.mp
  convert i1_hasSum_two_geometric
    ((1 - t ^ 2) ^ 3 * d * (T * U) * (T * V) * t) (d * T * V * t) ((T * V) ^ 2 * t ^ 2)
    h0 h1 using 1
  exact funext fun n => i1r3b_reindexed t d U V T n

theorem summable_norm_i1r3b_raw (t d U V T : ℂ)  
    (h0 : ‖d * T * V * t‖ < 1)
    (h1 : ‖(T * V) ^ 2 * t ^ 2‖ < 1) :
    Summable (fun p : I1R3BRow => ‖i1Raw t d U V T p.val 0‖) := by
  apply i1r3bEquiv.summable_iff.mp
  convert i1_summable_norm_two_geometric
    ((1 - t ^ 2) ^ 3 * d * (T * U) * (T * V) * t) (d * T * V * t) ((T * V) ^ 2 * t ^ 2)
    h0 h1 using 1
  exact funext fun n => congrArg norm
    (i1r3b_reindexed t d U V T n)

/-- Source I1 row 3c, with integer valuation inequalities. -/
abbrev I1R3CRow := {p : ℤ × ℤ × ℤ //
  let k := p.1; let j := p.2.1; let h := p.2.2; 1 ≤ k ∧ j < -2*k ∧ k+j ≤ h ∧ 2*h = j-1}

def i1r3cEquiv : (ℕ × ℕ) ≃ I1R3CRow where
  toFun n := ⟨(by
    rcases n with ⟨a, b⟩
    exact ((a : ℤ)+1,-2*(a : ℤ)-2*(b : ℤ)-3,-(a : ℤ)-(b : ℤ)-2)), by
      rcases n with ⟨a, b⟩
      dsimp
      omega⟩
  invFun p := (by
    let k := p.val.1; let j := p.val.2.1; let h := p.val.2.2
    exact ((k-1).toNat, ((-j-2*k-1)/2).toNat))
  left_inv n := by
    rcases n with ⟨a, b⟩
    simp only [Prod.mk.injEq]
    try dsimp
    omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩,hp⟩
    dsimp at hp ⊢
    simp only [Prod.mk.injEq]
    omega

@[simp] theorem i1r3cEquiv_val (a b : ℕ) :
    (i1r3cEquiv (a,b)).val = ((a : ℤ)+1,-2*(a : ℤ)-2*(b : ℤ)-3,-(a : ℤ)-(b : ℤ)-2) := rfl

theorem i1r3c_cartan (p : I1R3CRow) (depth : ℕ) (hdepth : 1 ≤ depth) :
    cartanIndices 1 p.val.1 p.val.2.1 p.val.2.2 depth = (0,-p.val.1-p.val.2.1) := by
  rw [← tableOne_correct _ _ _ _ (by omega)]
  rcases p with ⟨⟨k,j,h⟩,hp⟩
  dsimp at hp ⊢
  
  unfold tableOne collisionRows
  split_ifs <;> simp only [Prod.mk.injEq] <;> omega

theorem i1r3c_reindexed (t d U V T : ℂ) (ht : t ≠ 0) (depth : ℕ) (hdepth : 1 ≤ depth)
    (n : ℕ × ℕ) :
    i1Raw t d U V T (i1r3cEquiv n).val depth = ((1 - t ^ 2) ^ 3 * d * (T * V)^2 / t) * (d * T * V * t) ^ n.1 * ((T * V) ^ 2 * t ^ 2) ^ n.2 := by
  rcases n with ⟨a, b⟩
  unfold i1Raw
  
  rw [i1r3c_cartan]
  all_goals try omega
  simp only [i1r3cEquiv_val]
  have he : 3 * ((a : ℤ)+1) + 2 * (-2*(a : ℤ)-2*(b : ℤ)-3) + 2 * (-(a : ℤ)-(b : ℤ)-2) +
      3 * (0) + 4 * (-((a : ℤ)+1)-(-2*(a : ℤ)-2*(b : ℤ)-3)) - 2 = ((a+2*b : ℕ) : ℤ) - 1 := by omega
  have hk : (a : ℤ)+1 = ((a+1 : ℕ) : ℤ) := by omega
  have hb : -((a : ℤ)+1)-(-2*(a : ℤ)-2*(b : ℤ)-3) = ((a+2*b+2 : ℕ) : ℤ) := by omega
  have hl : (0) / 2 = ((0 : ℕ) : ℤ) := by omega
  rw [he, hl, hb]
  try rw [hk]
  rw [zpow_sub₀ ht]
  simp only [zpow_neg, zpow_natCast, zpow_ofNat, pow_add, pow_mul, mul_pow,
    pow_one, pow_zero, one_mul, mul_one, mul_inv_rev, div_eq_mul_inv, inv_pow]
  ring

theorem hasSum_i1r3c_raw (t d U V T : ℂ) (ht : t ≠ 0) (depth : ℕ) (hdepth : 1 ≤ depth)
    (h0 : ‖d * T * V * t‖ < 1)
    (h1 : ‖(T * V) ^ 2 * t ^ 2‖ < 1) :
    HasSum (fun p : I1R3CRow => i1Raw t d U V T p.val depth)
      (((1 - t ^ 2) ^ 3 * d * (T * V)^2 / t) * (1 - d * T * V * t)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹) := by
  apply i1r3cEquiv.hasSum_iff.mp
  convert i1_hasSum_two_geometric
    ((1 - t ^ 2) ^ 3 * d * (T * V)^2 / t) (d * T * V * t) ((T * V) ^ 2 * t ^ 2)
    h0 h1 using 1
  exact funext fun n => i1r3c_reindexed t d U V T ht depth hdepth n

theorem summable_norm_i1r3c_raw (t d U V T : ℂ) (ht : t ≠ 0) (depth : ℕ) (hdepth : 1 ≤ depth)
    (h0 : ‖d * T * V * t‖ < 1)
    (h1 : ‖(T * V) ^ 2 * t ^ 2‖ < 1) :
    Summable (fun p : I1R3CRow => ‖i1Raw t d U V T p.val depth‖) := by
  apply i1r3cEquiv.summable_iff.mp
  convert i1_summable_norm_two_geometric
    ((1 - t ^ 2) ^ 3 * d * (T * V)^2 / t) (d * T * V * t) ((T * V) ^ 2 * t ^ 2)
    h0 h1 using 1
  exact funext fun n => congrArg norm
    (i1r3c_reindexed t d U V T ht depth hdepth n)

/-- Source I1 row 4, with integer valuation inequalities. -/
abbrev I1R4Row := {p : ℤ × ℤ × ℤ //
  let k := p.1; let j := p.2.1; let h := p.2.2; 1 ≤ k ∧ j < -2*k ∧ k+j ≤ h ∧ 2*h ≤ j-2}

def i1r4Equiv : (ℕ × ℕ × ℕ) ≃ I1R4Row where
  toFun n := ⟨(by
    rcases n with ⟨a, b, c⟩
    exact ((a : ℤ)+1,-2*(a : ℤ)-2*(b : ℤ)-(c : ℤ)-4,-(a : ℤ)-(b : ℤ)-(c : ℤ)-3)), by
      rcases n with ⟨a, b, c⟩
      dsimp
      omega⟩
  invFun p := (by
    let k := p.val.1; let j := p.val.2.1; let h := p.val.2.2
    exact ((k-1).toNat, (h-k-j).toNat, (j-2*h-2).toNat))
  left_inv n := by
    rcases n with ⟨a, b, c⟩
    simp only [Prod.mk.injEq]
    try dsimp
    omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩,hp⟩
    dsimp at hp ⊢
    simp only [Prod.mk.injEq]
    omega

@[simp] theorem i1r4Equiv_val (a b c : ℕ) :
    (i1r4Equiv (a,b,c)).val = ((a : ℤ)+1,-2*(a : ℤ)-2*(b : ℤ)-(c : ℤ)-4,-(a : ℤ)-(b : ℤ)-(c : ℤ)-3) := rfl

theorem i1r4_cartan (p : I1R4Row) (depth : ℕ) :
    cartanIndices 1 p.val.1 p.val.2.1 p.val.2.2 depth = (2*p.val.2.1-4*p.val.2.2,2*p.val.2.2-2*p.val.2.1-p.val.1) := by
  rw [← tableOne_correct _ _ _ _ (by omega)]
  rcases p with ⟨⟨k,j,h⟩,hp⟩
  dsimp at hp ⊢
  
  unfold tableOne collisionRows
  split_ifs <;> simp only [Prod.mk.injEq] <;> omega

theorem i1r4_reindexed (t d U V T : ℂ)  (depth : ℕ)
    (n : ℕ × ℕ × ℕ) :
    i1Raw t d U V T (i1r4Equiv n).val depth = ((1 - t ^ 2) ^ 3 * d * (T * U)^2 * (T * V) * t^3) * (d * T * V * t) ^ n.1 * ((T * V) ^ 2 * t ^ 2) ^ n.2.1 * (T * U * t ^ 2) ^ n.2.2 := by
  rcases n with ⟨a, b, c⟩
  unfold i1Raw
  
  rw [i1r4_cartan]
  
  simp only [i1r4Equiv_val]
  have he : 3 * ((a : ℤ)+1) + 2 * (-2*(a : ℤ)-2*(b : ℤ)-(c : ℤ)-4) + 2 * (-(a : ℤ)-(b : ℤ)-(c : ℤ)-3) +
      3 * (2*(-2*(a : ℤ)-2*(b : ℤ)-(c : ℤ)-4)-4*(-(a : ℤ)-(b : ℤ)-(c : ℤ)-3)) + 4 * (2*(-(a : ℤ)-(b : ℤ)-(c : ℤ)-3)-2*(-2*(a : ℤ)-2*(b : ℤ)-(c : ℤ)-4)-((a : ℤ)+1)) - 2 = ((a+2*b+2*c+3 : ℕ) : ℤ) := by omega
  have hk : (a : ℤ)+1 = ((a+1 : ℕ) : ℤ) := by omega
  have hb : 2*(-(a : ℤ)-(b : ℤ)-(c : ℤ)-3)-2*(-2*(a : ℤ)-2*(b : ℤ)-(c : ℤ)-4)-((a : ℤ)+1) = ((a+2*b+1 : ℕ) : ℤ) := by omega
  have hl : (2*(-2*(a : ℤ)-2*(b : ℤ)-(c : ℤ)-4)-4*(-(a : ℤ)-(b : ℤ)-(c : ℤ)-3)) / 2 = ((c+2 : ℕ) : ℤ) := by omega
  rw [he, hl, hb]
  try rw [hk]
  
  simp only [zpow_neg, zpow_natCast, zpow_ofNat, pow_add, pow_mul, mul_pow,
    pow_one, pow_zero, one_mul, mul_one, mul_inv_rev, div_eq_mul_inv, inv_pow]
  ring

theorem hasSum_i1r4_raw (t d U V T : ℂ)  (depth : ℕ)
    (h0 : ‖d * T * V * t‖ < 1)
    (h1 : ‖(T * V) ^ 2 * t ^ 2‖ < 1)
    (h2 : ‖T * U * t ^ 2‖ < 1) :
    HasSum (fun p : I1R4Row => i1Raw t d U V T p.val depth)
      (((1 - t ^ 2) ^ 3 * d * (T * U)^2 * (T * V) * t^3) * (1 - d * T * V * t)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (1 - T * U * t ^ 2)⁻¹) := by
  apply i1r4Equiv.hasSum_iff.mp
  convert hasSum_three_geometric
    ((1 - t ^ 2) ^ 3 * d * (T * U)^2 * (T * V) * t^3) (d * T * V * t) ((T * V) ^ 2 * t ^ 2) (T * U * t ^ 2)
    h0 h1 h2 using 1
  exact funext fun n => i1r4_reindexed t d U V T depth n

theorem summable_norm_i1r4_raw (t d U V T : ℂ)  (depth : ℕ)
    (h0 : ‖d * T * V * t‖ < 1)
    (h1 : ‖(T * V) ^ 2 * t ^ 2‖ < 1)
    (h2 : ‖T * U * t ^ 2‖ < 1) :
    Summable (fun p : I1R4Row => ‖i1Raw t d U V T p.val depth‖) := by
  apply i1r4Equiv.summable_iff.mp
  convert summable_norm_three_geometric
    ((1 - t ^ 2) ^ 3 * d * (T * U)^2 * (T * V) * t^3) (d * T * V * t) ((T * V) ^ 2 * t ^ 2) (T * U * t ^ 2)
    h0 h1 h2 using 1
  exact funext fun n => congrArg norm
    (i1r4_reindexed t d U V T depth n)

/-- Source I1 row 5, with integer valuation inequalities. -/
abbrev I1R5Row := {p : ℤ × ℤ × ℤ //
  let k := p.1; let j := p.2.1; let h := p.2.2; 1 ≤ k ∧ j < -2*k ∧ h < k+j}

def i1r5Equiv : (ℕ × ℕ × ℕ) ≃ I1R5Row where
  toFun n := ⟨(by
    rcases n with ⟨a, b, c⟩
    exact ((a : ℤ)+1,-2*(a : ℤ)-(b : ℤ)-3,-(a : ℤ)-(b : ℤ)-(c : ℤ)-3)), by
      rcases n with ⟨a, b, c⟩
      dsimp
      omega⟩
  invFun p := (by
    let k := p.val.1; let j := p.val.2.1; let h := p.val.2.2
    exact ((k-1).toNat, (-j-2*k-1).toNat, (k+j-h-1).toNat))
  left_inv n := by
    rcases n with ⟨a, b, c⟩
    simp only [Prod.mk.injEq]
    try dsimp
    omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩,hp⟩
    dsimp at hp ⊢
    simp only [Prod.mk.injEq]
    omega

@[simp] theorem i1r5Equiv_val (a b c : ℕ) :
    (i1r5Equiv (a,b,c)).val = ((a : ℤ)+1,-2*(a : ℤ)-(b : ℤ)-3,-(a : ℤ)-(b : ℤ)-(c : ℤ)-3) := rfl

theorem i1r5_cartan (p : I1R5Row) (depth : ℕ) :
    cartanIndices 1 p.val.1 p.val.2.1 p.val.2.2 depth = (-2*p.val.1-2*p.val.2.2,p.val.1) := by
  rw [← tableOne_correct _ _ _ _ (by omega)]
  rcases p with ⟨⟨k,j,h⟩,hp⟩
  dsimp at hp ⊢
  
  unfold tableOne collisionRows
  split_ifs <;> simp only [Prod.mk.injEq] <;> omega

theorem i1r5_reindexed (t d U V T : ℂ)  (depth : ℕ)
    (n : ℕ × ℕ × ℕ) :
    i1Raw t d U V T (i1r5Equiv n).val depth = ((1 - t ^ 2) ^ 3 * d * (T * U)^2 * (T * V) * t^5) * (d * T * V * t) ^ n.1 * (T * U * t ^ 2) ^ n.2.1 * (T * U * t ^ 4) ^ n.2.2 := by
  rcases n with ⟨a, b, c⟩
  unfold i1Raw
  
  rw [i1r5_cartan]
  
  simp only [i1r5Equiv_val]
  have he : 3 * ((a : ℤ)+1) + 2 * (-2*(a : ℤ)-(b : ℤ)-3) + 2 * (-(a : ℤ)-(b : ℤ)-(c : ℤ)-3) +
      3 * (-2*((a : ℤ)+1)-2*(-(a : ℤ)-(b : ℤ)-(c : ℤ)-3)) + 4 * (((a : ℤ)+1)) - 2 = ((a+2*b+4*c+5 : ℕ) : ℤ) := by omega
  have hk : (a : ℤ)+1 = ((a+1 : ℕ) : ℤ) := by omega
  have hb : ((a : ℤ)+1) = ((a+1 : ℕ) : ℤ) := by omega
  have hl : (-2*((a : ℤ)+1)-2*(-(a : ℤ)-(b : ℤ)-(c : ℤ)-3)) / 2 = ((b+c+2 : ℕ) : ℤ) := by omega
  rw [he, hl, hb]
  try rw [hk]
  
  simp only [zpow_neg, zpow_natCast, zpow_ofNat, pow_add, pow_mul, mul_pow,
    pow_one, pow_zero, one_mul, mul_one, mul_inv_rev, div_eq_mul_inv, inv_pow]
  ring

theorem hasSum_i1r5_raw (t d U V T : ℂ)  (depth : ℕ)
    (h0 : ‖d * T * V * t‖ < 1)
    (h1 : ‖T * U * t ^ 2‖ < 1)
    (h2 : ‖T * U * t ^ 4‖ < 1) :
    HasSum (fun p : I1R5Row => i1Raw t d U V T p.val depth)
      (((1 - t ^ 2) ^ 3 * d * (T * U)^2 * (T * V) * t^5) * (1 - d * T * V * t)⁻¹ * (1 - T * U * t ^ 2)⁻¹ * (1 - T * U * t ^ 4)⁻¹) := by
  apply i1r5Equiv.hasSum_iff.mp
  convert hasSum_three_geometric
    ((1 - t ^ 2) ^ 3 * d * (T * U)^2 * (T * V) * t^5) (d * T * V * t) (T * U * t ^ 2) (T * U * t ^ 4)
    h0 h1 h2 using 1
  exact funext fun n => i1r5_reindexed t d U V T depth n

theorem summable_norm_i1r5_raw (t d U V T : ℂ)  (depth : ℕ)
    (h0 : ‖d * T * V * t‖ < 1)
    (h1 : ‖T * U * t ^ 2‖ < 1)
    (h2 : ‖T * U * t ^ 4‖ < 1) :
    Summable (fun p : I1R5Row => ‖i1Raw t d U V T p.val depth‖) := by
  apply i1r5Equiv.summable_iff.mp
  convert summable_norm_three_geometric
    ((1 - t ^ 2) ^ 3 * d * (T * U)^2 * (T * V) * t^5) (d * T * V * t) (T * U * t ^ 2) (T * U * t ^ 4)
    h0 h1 h2 using 1
  exact funext fun n => congrArg norm
    (i1r5_reindexed t d U V T depth n)

/-- Source I1 row 6a, with integer valuation inequalities. -/
abbrev I1R6ARow := {p : ℤ × ℤ × ℤ //
  let k := p.1; let j := p.2.1; let h := p.2.2; k = 0 ∧ 0 ≤ j ∧ 0 ≤ h}

def i1r6aEquiv : (ℕ × ℕ) ≃ I1R6ARow where
  toFun n := ⟨(by
    rcases n with ⟨a, b⟩
    exact (0,(a : ℤ),(b : ℤ))), by
      rcases n with ⟨a, b⟩
      dsimp
      omega⟩
  invFun p := (by
    let k := p.val.1; let j := p.val.2.1; let h := p.val.2.2
    exact ((j).toNat, (h).toNat))
  left_inv n := by
    rcases n with ⟨a, b⟩
    simp only [Prod.mk.injEq]
    try dsimp
    omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩,hp⟩
    dsimp at hp ⊢
    simp only [Prod.mk.injEq]
    omega

@[simp] theorem i1r6aEquiv_val (a b : ℕ) :
    (i1r6aEquiv (a,b)).val = (0,(a : ℤ),(b : ℤ)) := rfl

theorem i1r6a_cartan (p : I1R6ARow) (depth : ℕ) :
    cartanIndices 1 p.val.1 p.val.2.1 p.val.2.2 depth = (0,1) := by
  rw [← tableOne_correct _ _ _ _ (by omega)]
  rcases p with ⟨⟨k,j,h⟩,hp⟩
  dsimp at hp ⊢
  
  unfold tableOne collisionRows
  split_ifs <;> simp only [Prod.mk.injEq] <;> omega

theorem i1r6a_reindexed (t d U V T : ℂ)  (depth : ℕ)
    (n : ℕ × ℕ) :
    i1Raw t d U V T (i1r6aEquiv n).val depth = ((1 - t ^ 2) ^ 3 * (T * V) * t^2) * (t ^ 2) ^ n.1 * (t ^ 2) ^ n.2 := by
  rcases n with ⟨a, b⟩
  unfold i1Raw
  
  rw [i1r6a_cartan]
  
  simp only [i1r6aEquiv_val]
  have he : 3 * (0) + 2 * ((a : ℤ)) + 2 * ((b : ℤ)) +
      3 * (0) + 4 * (1) - 2 = ((2*a+2*b+2 : ℕ) : ℤ) := by omega
  have hk : 0 = ((0 : ℕ) : ℤ) := by omega
  have hb : 1 = ((1 : ℕ) : ℤ) := by omega
  have hl : (0) / 2 = ((0 : ℕ) : ℤ) := by omega
  rw [he, hl, hb]
  try rw [hk]
  
  simp only [zpow_neg, zpow_natCast, zpow_ofNat, pow_add, pow_mul, mul_pow,
    pow_one, pow_zero, one_mul, mul_one, mul_inv_rev, div_eq_mul_inv, inv_pow]
  ring

theorem hasSum_i1r6a_raw (t d U V T : ℂ)  (depth : ℕ)
    (h0 : ‖t ^ 2‖ < 1)
    (h1 : ‖t ^ 2‖ < 1) :
    HasSum (fun p : I1R6ARow => i1Raw t d U V T p.val depth)
      (((1 - t ^ 2) ^ 3 * (T * V) * t^2) * (1 - t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹) := by
  apply i1r6aEquiv.hasSum_iff.mp
  convert i1_hasSum_two_geometric
    ((1 - t ^ 2) ^ 3 * (T * V) * t^2) (t ^ 2) (t ^ 2)
    h0 h1 using 1
  exact funext fun n => i1r6a_reindexed t d U V T depth n

theorem summable_norm_i1r6a_raw (t d U V T : ℂ)  (depth : ℕ)
    (h0 : ‖t ^ 2‖ < 1)
    (h1 : ‖t ^ 2‖ < 1) :
    Summable (fun p : I1R6ARow => ‖i1Raw t d U V T p.val depth‖) := by
  apply i1r6aEquiv.summable_iff.mp
  convert i1_summable_norm_two_geometric
    ((1 - t ^ 2) ^ 3 * (T * V) * t^2) (t ^ 2) (t ^ 2)
    h0 h1 using 1
  exact funext fun n => congrArg norm
    (i1r6a_reindexed t d U V T depth n)

/-- Source I1 row 6b, with integer valuation inequalities. -/
abbrev I1R6BRow := {p : ℤ × ℤ × ℤ //
  let k := p.1; let j := p.2.1; let h := p.2.2; k ≤ -1 ∧ 0 ≤ j ∧ 0 ≤ h}

def i1r6bEquiv : (ℕ × ℕ × ℕ) ≃ I1R6BRow where
  toFun n := ⟨(by
    rcases n with ⟨a, b, c⟩
    exact (-(a : ℤ)-1,(b : ℤ),(c : ℤ))), by
      rcases n with ⟨a, b, c⟩
      dsimp
      omega⟩
  invFun p := (by
    let k := p.val.1; let j := p.val.2.1; let h := p.val.2.2
    exact ((-k-1).toNat, (j).toNat, (h).toNat))
  left_inv n := by
    rcases n with ⟨a, b, c⟩
    simp only [Prod.mk.injEq]
    try dsimp
    omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩,hp⟩
    dsimp at hp ⊢
    simp only [Prod.mk.injEq]
    omega

@[simp] theorem i1r6bEquiv_val (a b c : ℕ) :
    (i1r6bEquiv (a,b,c)).val = (-(a : ℤ)-1,(b : ℤ),(c : ℤ)) := rfl

theorem i1r6b_cartan (p : I1R6BRow) (depth : ℕ) :
    cartanIndices 1 p.val.1 p.val.2.1 p.val.2.2 depth = (2,-p.val.1-1) := by
  rw [← tableOne_correct _ _ _ _ (by omega)]
  rcases p with ⟨⟨k,j,h⟩,hp⟩
  dsimp at hp ⊢
  
  unfold tableOne collisionRows
  split_ifs <;> simp only [Prod.mk.injEq] <;> omega

theorem i1r6b_reindexed (t d U V T : ℂ)  (depth : ℕ)
    (n : ℕ × ℕ × ℕ) :
    i1Raw t d U V T (i1r6bEquiv n).val depth = ((1 - t ^ 2) ^ 3 * (T * U) * t / d) * (T * V * t / d) ^ n.1 * (t ^ 2) ^ n.2.1 * (t ^ 2) ^ n.2.2 := by
  rcases n with ⟨a, b, c⟩
  unfold i1Raw
  
  rw [i1r6b_cartan]
  
  simp only [i1r6bEquiv_val]
  have he : 3 * (-(a : ℤ)-1) + 2 * ((b : ℤ)) + 2 * ((c : ℤ)) +
      3 * (2) + 4 * (-(-(a : ℤ)-1)-1) - 2 = ((a+2*b+2*c+1 : ℕ) : ℤ) := by omega
  have hk : -(a : ℤ)-1 = -(((a+1) : ℕ) : ℤ) := by omega
  have hb : -(-(a : ℤ)-1)-1 = ((a : ℕ) : ℤ) := by omega
  have hl : (2) / 2 = ((1 : ℕ) : ℤ) := by omega
  rw [he, hl, hb]
  try rw [hk]
  
  simp only [zpow_neg, zpow_natCast, zpow_ofNat, pow_add, pow_mul, mul_pow,
    pow_one, pow_zero, one_mul, mul_one, mul_inv_rev, div_eq_mul_inv, inv_pow]
  ring

theorem hasSum_i1r6b_raw (t d U V T : ℂ)  (depth : ℕ)
    (h0 : ‖T * V * t / d‖ < 1)
    (h1 : ‖t ^ 2‖ < 1)
    (h2 : ‖t ^ 2‖ < 1) :
    HasSum (fun p : I1R6BRow => i1Raw t d U V T p.val depth)
      (((1 - t ^ 2) ^ 3 * (T * U) * t / d) * (1 - T * V * t / d)⁻¹ * (1 - t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹) := by
  apply i1r6bEquiv.hasSum_iff.mp
  convert hasSum_three_geometric
    ((1 - t ^ 2) ^ 3 * (T * U) * t / d) (T * V * t / d) (t ^ 2) (t ^ 2)
    h0 h1 h2 using 1
  exact funext fun n => i1r6b_reindexed t d U V T depth n

theorem summable_norm_i1r6b_raw (t d U V T : ℂ)  (depth : ℕ)
    (h0 : ‖T * V * t / d‖ < 1)
    (h1 : ‖t ^ 2‖ < 1)
    (h2 : ‖t ^ 2‖ < 1) :
    Summable (fun p : I1R6BRow => ‖i1Raw t d U V T p.val depth‖) := by
  apply i1r6bEquiv.summable_iff.mp
  convert summable_norm_three_geometric
    ((1 - t ^ 2) ^ 3 * (T * U) * t / d) (T * V * t / d) (t ^ 2) (t ^ 2)
    h0 h1 h2 using 1
  exact funext fun n => congrArg norm
    (i1r6b_reindexed t d U V T depth n)

/-- Source I1 row 7, with integer valuation inequalities. -/
abbrev I1R7Row := {p : ℤ × ℤ × ℤ //
  let k := p.1; let j := p.2.1; let h := p.2.2; k ≤ 0 ∧ 0 ≤ j ∧ h < 0}

def i1r7Equiv : (ℕ × ℕ × ℕ) ≃ I1R7Row where
  toFun n := ⟨(by
    rcases n with ⟨a, b, c⟩
    exact (-(a : ℤ),(b : ℤ),-(c : ℤ)-1)), by
      rcases n with ⟨a, b, c⟩
      dsimp
      omega⟩
  invFun p := (by
    let k := p.val.1; let j := p.val.2.1; let h := p.val.2.2
    exact ((-k).toNat, (j).toNat, (-h-1).toNat))
  left_inv n := by
    rcases n with ⟨a, b, c⟩
    simp only [Prod.mk.injEq]
    try dsimp
    omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩,hp⟩
    dsimp at hp ⊢
    simp only [Prod.mk.injEq]
    omega

@[simp] theorem i1r7Equiv_val (a b c : ℕ) :
    (i1r7Equiv (a,b,c)).val = (-(a : ℤ),(b : ℤ),-(c : ℤ)-1) := rfl

theorem i1r7_cartan (p : I1R7Row) (depth : ℕ) :
    cartanIndices 1 p.val.1 p.val.2.1 p.val.2.2 depth = (-2*p.val.2.2,-p.val.1) := by
  rw [← tableOne_correct _ _ _ _ (by omega)]
  rcases p with ⟨⟨k,j,h⟩,hp⟩
  dsimp at hp ⊢
  
  unfold tableOne collisionRows
  split_ifs <;> simp only [Prod.mk.injEq] <;> omega

theorem i1r7_reindexed (t d U V T : ℂ)  (depth : ℕ)
    (n : ℕ × ℕ × ℕ) :
    i1Raw t d U V T (i1r7Equiv n).val depth = ((1 - t ^ 2) ^ 3 * (T * U) * t^2) * (T * V * t / d) ^ n.1 * (t ^ 2) ^ n.2.1 * (T * U * t ^ 4) ^ n.2.2 := by
  rcases n with ⟨a, b, c⟩
  unfold i1Raw
  
  rw [i1r7_cartan]
  
  simp only [i1r7Equiv_val]
  have he : 3 * (-(a : ℤ)) + 2 * ((b : ℤ)) + 2 * (-(c : ℤ)-1) +
      3 * (-2*(-(c : ℤ)-1)) + 4 * (-(-(a : ℤ))) - 2 = ((a+2*b+4*c+2 : ℕ) : ℤ) := by omega
  have hk : -(a : ℤ) = -((a : ℕ) : ℤ) := by omega
  have hb : -(-(a : ℤ)) = ((a : ℕ) : ℤ) := by omega
  have hl : (-2*(-(c : ℤ)-1)) / 2 = ((c+1 : ℕ) : ℤ) := by omega
  rw [he, hl, hb]
  try rw [hk]
  
  simp only [zpow_neg, zpow_natCast, zpow_ofNat, pow_add, pow_mul, mul_pow,
    pow_one, pow_zero, one_mul, mul_one, mul_inv_rev, div_eq_mul_inv, inv_pow]
  ring

theorem hasSum_i1r7_raw (t d U V T : ℂ)  (depth : ℕ)
    (h0 : ‖T * V * t / d‖ < 1)
    (h1 : ‖t ^ 2‖ < 1)
    (h2 : ‖T * U * t ^ 4‖ < 1) :
    HasSum (fun p : I1R7Row => i1Raw t d U V T p.val depth)
      (((1 - t ^ 2) ^ 3 * (T * U) * t^2) * (1 - T * V * t / d)⁻¹ * (1 - t ^ 2)⁻¹ * (1 - T * U * t ^ 4)⁻¹) := by
  apply i1r7Equiv.hasSum_iff.mp
  convert hasSum_three_geometric
    ((1 - t ^ 2) ^ 3 * (T * U) * t^2) (T * V * t / d) (t ^ 2) (T * U * t ^ 4)
    h0 h1 h2 using 1
  exact funext fun n => i1r7_reindexed t d U V T depth n

theorem summable_norm_i1r7_raw (t d U V T : ℂ)  (depth : ℕ)
    (h0 : ‖T * V * t / d‖ < 1)
    (h1 : ‖t ^ 2‖ < 1)
    (h2 : ‖T * U * t ^ 4‖ < 1) :
    Summable (fun p : I1R7Row => ‖i1Raw t d U V T p.val depth‖) := by
  apply i1r7Equiv.summable_iff.mp
  convert summable_norm_three_geometric
    ((1 - t ^ 2) ^ 3 * (T * U) * t^2) (T * V * t / d) (t ^ 2) (T * U * t ^ 4)
    h0 h1 h2 using 1
  exact funext fun n => congrArg norm
    (i1r7_reindexed t d U V T depth n)

/-- Source I1 row 8ae, with integer valuation inequalities. -/
abbrev I1R8AERow := {p : ℤ × ℤ × ℤ //
  let k := p.1; let j := p.2.1; let h := p.2.2; k ≤ 0 ∧ j < 0 ∧ j ≤ h ∧ j ≤ 2*h ∧ j % 2 = 0}

def i1r8aeEquiv : (ℕ × ℕ × ℕ) ≃ I1R8AERow where
  toFun n := ⟨(by
    rcases n with ⟨a, b, c⟩
    exact (-(a : ℤ),-2*(b : ℤ)-2,-(b : ℤ)-1+(c : ℤ))), by
      rcases n with ⟨a, b, c⟩
      dsimp
      omega⟩
  invFun p := (by
    let k := p.val.1; let j := p.val.2.1; let h := p.val.2.2
    exact ((-k).toNat, ((-j-2)/2).toNat, (h-j/2).toNat))
  left_inv n := by
    rcases n with ⟨a, b, c⟩
    simp only [Prod.mk.injEq]
    try dsimp
    omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩,hp⟩
    dsimp at hp ⊢
    simp only [Prod.mk.injEq]
    omega

@[simp] theorem i1r8aeEquiv_val (a b c : ℕ) :
    (i1r8aeEquiv (a,b,c)).val = (-(a : ℤ),-2*(b : ℤ)-2,-(b : ℤ)-1+(c : ℤ)) := rfl

theorem i1r8ae_cartan (p : I1R8AERow) (depth : ℕ) :
    cartanIndices 1 p.val.1 p.val.2.1 p.val.2.2 depth = (2,-p.val.1-p.val.2.1-1) := by
  rw [← tableOne_correct _ _ _ _ (by omega)]
  rcases p with ⟨⟨k,j,h⟩,hp⟩
  dsimp at hp ⊢
  have hp0 : k ≤ 0 ∧ j < 0 ∧ j ≤ h ∧ j ≤ 2*h := ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1⟩
  clear hp
  rw [tableOne, if_neg (by omega : ¬ 1 ≤ k), if_neg (by omega : ¬ 0 ≤ j),
    if_neg (by omega : ¬ h < j)]
  rw [collisionRows, if_pos (by omega : j-1+1 ≤ 2*h)]
  norm_num

theorem i1r8ae_reindexed (t d U V T : ℂ)  (depth : ℕ)
    (n : ℕ × ℕ × ℕ) :
    i1Raw t d U V T (i1r8aeEquiv n).val depth = ((1 - t ^ 2) ^ 3 * (T * U) * (T * V) * t^2) * (T * V * t / d) ^ n.1 * ((T * V) ^ 2 * t ^ 2) ^ n.2.1 * (t ^ 2) ^ n.2.2 := by
  rcases n with ⟨a, b, c⟩
  unfold i1Raw
  
  rw [i1r8ae_cartan]
  
  simp only [i1r8aeEquiv_val]
  have he : 3 * (-(a : ℤ)) + 2 * (-2*(b : ℤ)-2) + 2 * (-(b : ℤ)-1+(c : ℤ)) +
      3 * (2) + 4 * (-(-(a : ℤ))-(-2*(b : ℤ)-2)-1) - 2 = ((a+2*b+2*c+2 : ℕ) : ℤ) := by omega
  have hk : -(a : ℤ) = -((a : ℕ) : ℤ) := by omega
  have hb : -(-(a : ℤ))-(-2*(b : ℤ)-2)-1 = ((a+2*b+1 : ℕ) : ℤ) := by omega
  have hl : (2) / 2 = ((1 : ℕ) : ℤ) := by omega
  rw [he, hl, hb]
  try rw [hk]
  
  simp only [zpow_neg, zpow_natCast, zpow_ofNat, pow_add, pow_mul, mul_pow,
    pow_one, pow_zero, one_mul, mul_one, mul_inv_rev, div_eq_mul_inv, inv_pow]
  ring

theorem hasSum_i1r8ae_raw (t d U V T : ℂ)  (depth : ℕ)
    (h0 : ‖T * V * t / d‖ < 1)
    (h1 : ‖(T * V) ^ 2 * t ^ 2‖ < 1)
    (h2 : ‖t ^ 2‖ < 1) :
    HasSum (fun p : I1R8AERow => i1Raw t d U V T p.val depth)
      (((1 - t ^ 2) ^ 3 * (T * U) * (T * V) * t^2) * (1 - T * V * t / d)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹) := by
  apply i1r8aeEquiv.hasSum_iff.mp
  convert hasSum_three_geometric
    ((1 - t ^ 2) ^ 3 * (T * U) * (T * V) * t^2) (T * V * t / d) ((T * V) ^ 2 * t ^ 2) (t ^ 2)
    h0 h1 h2 using 1
  exact funext fun n => i1r8ae_reindexed t d U V T depth n

theorem summable_norm_i1r8ae_raw (t d U V T : ℂ)  (depth : ℕ)
    (h0 : ‖T * V * t / d‖ < 1)
    (h1 : ‖(T * V) ^ 2 * t ^ 2‖ < 1)
    (h2 : ‖t ^ 2‖ < 1) :
    Summable (fun p : I1R8AERow => ‖i1Raw t d U V T p.val depth‖) := by
  apply i1r8aeEquiv.summable_iff.mp
  convert summable_norm_three_geometric
    ((1 - t ^ 2) ^ 3 * (T * U) * (T * V) * t^2) (T * V * t / d) ((T * V) ^ 2 * t ^ 2) (t ^ 2)
    h0 h1 h2 using 1
  exact funext fun n => congrArg norm
    (i1r8ae_reindexed t d U V T depth n)

/-- Source I1 row 8ao, with integer valuation inequalities. -/
abbrev I1R8AORow := {p : ℤ × ℤ × ℤ //
  let k := p.1; let j := p.2.1; let h := p.2.2; k ≤ 0 ∧ j < 0 ∧ j ≤ h ∧ j ≤ 2*h ∧ j % 2 = 1}

def i1r8aoEquiv : (ℕ × ℕ × ℕ) ≃ I1R8AORow where
  toFun n := ⟨(by
    rcases n with ⟨a, b, c⟩
    exact (-(a : ℤ),-2*(b : ℤ)-1,-(b : ℤ)+(c : ℤ))), by
      rcases n with ⟨a, b, c⟩
      dsimp
      omega⟩
  invFun p := (by
    let k := p.val.1; let j := p.val.2.1; let h := p.val.2.2
    exact ((-k).toNat, ((-j-1)/2).toNat, (h-(j+1)/2).toNat))
  left_inv n := by
    rcases n with ⟨a, b, c⟩
    simp only [Prod.mk.injEq]
    try dsimp
    omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩,hp⟩
    dsimp at hp ⊢
    simp only [Prod.mk.injEq]
    omega

@[simp] theorem i1r8aoEquiv_val (a b c : ℕ) :
    (i1r8aoEquiv (a,b,c)).val = (-(a : ℤ),-2*(b : ℤ)-1,-(b : ℤ)+(c : ℤ)) := rfl

theorem i1r8ao_cartan (p : I1R8AORow) (depth : ℕ) :
    cartanIndices 1 p.val.1 p.val.2.1 p.val.2.2 depth = (2,-p.val.1-p.val.2.1-1) := by
  rw [← tableOne_correct _ _ _ _ (by omega)]
  rcases p with ⟨⟨k,j,h⟩,hp⟩
  dsimp at hp ⊢
  have hp0 : k ≤ 0 ∧ j < 0 ∧ j ≤ h ∧ j ≤ 2*h := ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1⟩
  clear hp
  rw [tableOne, if_neg (by omega : ¬ 1 ≤ k), if_neg (by omega : ¬ 0 ≤ j),
    if_neg (by omega : ¬ h < j)]
  rw [collisionRows, if_pos (by omega : j-1+1 ≤ 2*h)]
  norm_num

theorem i1r8ao_reindexed (t d U V T : ℂ)  (depth : ℕ)
    (n : ℕ × ℕ × ℕ) :
    i1Raw t d U V T (i1r8aoEquiv n).val depth = ((1 - t ^ 2) ^ 3 * (T * U) * t^2) * (T * V * t / d) ^ n.1 * ((T * V) ^ 2 * t ^ 2) ^ n.2.1 * (t ^ 2) ^ n.2.2 := by
  rcases n with ⟨a, b, c⟩
  unfold i1Raw
  
  rw [i1r8ao_cartan]
  
  simp only [i1r8aoEquiv_val]
  have he : 3 * (-(a : ℤ)) + 2 * (-2*(b : ℤ)-1) + 2 * (-(b : ℤ)+(c : ℤ)) +
      3 * (2) + 4 * (-(-(a : ℤ))-(-2*(b : ℤ)-1)-1) - 2 = ((a+2*b+2*c+2 : ℕ) : ℤ) := by omega
  have hk : -(a : ℤ) = -((a : ℕ) : ℤ) := by omega
  have hb : -(-(a : ℤ))-(-2*(b : ℤ)-1)-1 = ((a+2*b : ℕ) : ℤ) := by omega
  have hl : (2) / 2 = ((1 : ℕ) : ℤ) := by omega
  rw [he, hl, hb]
  try rw [hk]
  
  simp only [zpow_neg, zpow_natCast, zpow_ofNat, pow_add, pow_mul, mul_pow,
    pow_one, pow_zero, one_mul, mul_one, mul_inv_rev, div_eq_mul_inv, inv_pow]
  ring

theorem hasSum_i1r8ao_raw (t d U V T : ℂ)  (depth : ℕ)
    (h0 : ‖T * V * t / d‖ < 1)
    (h1 : ‖(T * V) ^ 2 * t ^ 2‖ < 1)
    (h2 : ‖t ^ 2‖ < 1) :
    HasSum (fun p : I1R8AORow => i1Raw t d U V T p.val depth)
      (((1 - t ^ 2) ^ 3 * (T * U) * t^2) * (1 - T * V * t / d)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹) := by
  apply i1r8aoEquiv.hasSum_iff.mp
  convert hasSum_three_geometric
    ((1 - t ^ 2) ^ 3 * (T * U) * t^2) (T * V * t / d) ((T * V) ^ 2 * t ^ 2) (t ^ 2)
    h0 h1 h2 using 1
  exact funext fun n => i1r8ao_reindexed t d U V T depth n

theorem summable_norm_i1r8ao_raw (t d U V T : ℂ)  (depth : ℕ)
    (h0 : ‖T * V * t / d‖ < 1)
    (h1 : ‖(T * V) ^ 2 * t ^ 2‖ < 1)
    (h2 : ‖t ^ 2‖ < 1) :
    Summable (fun p : I1R8AORow => ‖i1Raw t d U V T p.val depth‖) := by
  apply i1r8aoEquiv.summable_iff.mp
  convert summable_norm_three_geometric
    ((1 - t ^ 2) ^ 3 * (T * U) * t^2) (T * V * t / d) ((T * V) ^ 2 * t ^ 2) (t ^ 2)
    h0 h1 h2 using 1
  exact funext fun n => congrArg norm
    (i1r8ao_reindexed t d U V T depth n)

/-- Source I1 row 8b, with integer valuation inequalities. -/
abbrev I1R8BRow := {p : ℤ × ℤ × ℤ //
  let k := p.1; let j := p.2.1; let h := p.2.2; k ≤ 0 ∧ j < 0 ∧ j ≤ h ∧ 2*h = j-1}

def i1r8bEquiv : (ℕ × ℕ) ≃ I1R8BRow where
  toFun n := ⟨(by
    rcases n with ⟨a, b⟩
    exact (-(a : ℤ),-2*(b : ℤ)-1,-(b : ℤ)-1)), by
      rcases n with ⟨a, b⟩
      dsimp
      omega⟩
  invFun p := (by
    let k := p.val.1; let j := p.val.2.1; let h := p.val.2.2
    exact ((-k).toNat, ((-j-1)/2).toNat))
  left_inv n := by
    rcases n with ⟨a, b⟩
    simp only [Prod.mk.injEq]
    try dsimp
    omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩,hp⟩
    dsimp at hp ⊢
    simp only [Prod.mk.injEq]
    omega

@[simp] theorem i1r8bEquiv_val (a b : ℕ) :
    (i1r8bEquiv (a,b)).val = (-(a : ℤ),-2*(b : ℤ)-1,-(b : ℤ)-1) := rfl

theorem i1r8b_cartan (p : I1R8BRow)  :
    cartanIndices 1 p.val.1 p.val.2.1 p.val.2.2 0 = (2,-p.val.1-p.val.2.1-1) := by
  rw [← tableOne_correct _ _ _ _ (by omega)]
  rcases p with ⟨⟨k,j,h⟩,hp⟩
  dsimp at hp ⊢
  
  unfold tableOne collisionRows
  split_ifs <;> simp only [Prod.mk.injEq] <;> omega

theorem i1r8b_reindexed (t d U V T : ℂ)  
    (n : ℕ × ℕ) :
    i1Raw t d U V T (i1r8bEquiv n).val 0 = ((1 - t ^ 2) ^ 3 * (T * U)) * (T * V * t / d) ^ n.1 * ((T * V) ^ 2 * t ^ 2) ^ n.2 := by
  rcases n with ⟨a, b⟩
  unfold i1Raw
  simp only [Nat.cast_zero]
  rw [i1r8b_cartan]
  
  simp only [i1r8bEquiv_val]
  have he : 3 * (-(a : ℤ)) + 2 * (-2*(b : ℤ)-1) + 2 * (-(b : ℤ)-1) +
      3 * (2) + 4 * (-(-(a : ℤ))-(-2*(b : ℤ)-1)-1) - 2 = ((a+2*b : ℕ) : ℤ) := by omega
  have hk : -(a : ℤ) = -((a : ℕ) : ℤ) := by omega
  have hb : -(-(a : ℤ))-(-2*(b : ℤ)-1)-1 = ((a+2*b : ℕ) : ℤ) := by omega
  have hl : (2) / 2 = ((1 : ℕ) : ℤ) := by omega
  rw [he, hl, hb]
  try rw [hk]
  
  simp only [zpow_neg, zpow_natCast, zpow_ofNat, pow_add, pow_mul, mul_pow,
    pow_one, pow_zero, one_mul, mul_one, mul_inv_rev, div_eq_mul_inv, inv_pow]
  ring

theorem hasSum_i1r8b_raw (t d U V T : ℂ)  
    (h0 : ‖T * V * t / d‖ < 1)
    (h1 : ‖(T * V) ^ 2 * t ^ 2‖ < 1) :
    HasSum (fun p : I1R8BRow => i1Raw t d U V T p.val 0)
      (((1 - t ^ 2) ^ 3 * (T * U)) * (1 - T * V * t / d)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹) := by
  apply i1r8bEquiv.hasSum_iff.mp
  convert i1_hasSum_two_geometric
    ((1 - t ^ 2) ^ 3 * (T * U)) (T * V * t / d) ((T * V) ^ 2 * t ^ 2)
    h0 h1 using 1
  exact funext fun n => i1r8b_reindexed t d U V T n

theorem summable_norm_i1r8b_raw (t d U V T : ℂ)  
    (h0 : ‖T * V * t / d‖ < 1)
    (h1 : ‖(T * V) ^ 2 * t ^ 2‖ < 1) :
    Summable (fun p : I1R8BRow => ‖i1Raw t d U V T p.val 0‖) := by
  apply i1r8bEquiv.summable_iff.mp
  convert i1_summable_norm_two_geometric
    ((1 - t ^ 2) ^ 3 * (T * U)) (T * V * t / d) ((T * V) ^ 2 * t ^ 2)
    h0 h1 using 1
  exact funext fun n => congrArg norm
    (i1r8b_reindexed t d U V T n)

/-- Source I1 row 8c, with integer valuation inequalities. -/
abbrev I1R8CRow := {p : ℤ × ℤ × ℤ //
  let k := p.1; let j := p.2.1; let h := p.2.2; k ≤ 0 ∧ j < 0 ∧ j ≤ h ∧ 2*h = j-1}

def i1r8cEquiv : (ℕ × ℕ) ≃ I1R8CRow where
  toFun n := ⟨(by
    rcases n with ⟨a, b⟩
    exact (-(a : ℤ),-2*(b : ℤ)-1,-(b : ℤ)-1)), by
      rcases n with ⟨a, b⟩
      dsimp
      omega⟩
  invFun p := (by
    let k := p.val.1; let j := p.val.2.1; let h := p.val.2.2
    exact ((-k).toNat, ((-j-1)/2).toNat))
  left_inv n := by
    rcases n with ⟨a, b⟩
    simp only [Prod.mk.injEq]
    try dsimp
    omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩,hp⟩
    dsimp at hp ⊢
    simp only [Prod.mk.injEq]
    omega

@[simp] theorem i1r8cEquiv_val (a b : ℕ) :
    (i1r8cEquiv (a,b)).val = (-(a : ℤ),-2*(b : ℤ)-1,-(b : ℤ)-1) := rfl

theorem i1r8c_cartan (p : I1R8CRow) (depth : ℕ) (hdepth : 1 ≤ depth) :
    cartanIndices 1 p.val.1 p.val.2.1 p.val.2.2 depth = (0,-p.val.1-p.val.2.1) := by
  rw [← tableOne_correct _ _ _ _ (by omega)]
  rcases p with ⟨⟨k,j,h⟩,hp⟩
  dsimp at hp ⊢
  
  unfold tableOne collisionRows
  split_ifs <;> simp only [Prod.mk.injEq] <;> omega

theorem i1r8c_reindexed (t d U V T : ℂ) (ht : t ≠ 0) (depth : ℕ) (hdepth : 1 ≤ depth)
    (n : ℕ × ℕ) :
    i1Raw t d U V T (i1r8cEquiv n).val depth = ((1 - t ^ 2) ^ 3 * (T * V) / t^2) * (T * V * t / d) ^ n.1 * ((T * V) ^ 2 * t ^ 2) ^ n.2 := by
  rcases n with ⟨a, b⟩
  unfold i1Raw
  
  rw [i1r8c_cartan]
  all_goals try omega
  simp only [i1r8cEquiv_val]
  have he : 3 * (-(a : ℤ)) + 2 * (-2*(b : ℤ)-1) + 2 * (-(b : ℤ)-1) +
      3 * (0) + 4 * (-(-(a : ℤ))-(-2*(b : ℤ)-1)) - 2 = ((a+2*b : ℕ) : ℤ) - 2 := by omega
  have hk : -(a : ℤ) = -((a : ℕ) : ℤ) := by omega
  have hb : -(-(a : ℤ))-(-2*(b : ℤ)-1) = ((a+2*b+1 : ℕ) : ℤ) := by omega
  have hl : (0) / 2 = ((0 : ℕ) : ℤ) := by omega
  rw [he, hl, hb]
  try rw [hk]
  rw [zpow_sub₀ ht]
  simp only [zpow_neg, zpow_natCast, zpow_ofNat, pow_add, pow_mul, mul_pow,
    pow_one, pow_zero, one_mul, mul_one, mul_inv_rev, div_eq_mul_inv, inv_pow]
  ring

theorem hasSum_i1r8c_raw (t d U V T : ℂ) (ht : t ≠ 0) (depth : ℕ) (hdepth : 1 ≤ depth)
    (h0 : ‖T * V * t / d‖ < 1)
    (h1 : ‖(T * V) ^ 2 * t ^ 2‖ < 1) :
    HasSum (fun p : I1R8CRow => i1Raw t d U V T p.val depth)
      (((1 - t ^ 2) ^ 3 * (T * V) / t^2) * (1 - T * V * t / d)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹) := by
  apply i1r8cEquiv.hasSum_iff.mp
  convert i1_hasSum_two_geometric
    ((1 - t ^ 2) ^ 3 * (T * V) / t^2) (T * V * t / d) ((T * V) ^ 2 * t ^ 2)
    h0 h1 using 1
  exact funext fun n => i1r8c_reindexed t d U V T ht depth hdepth n

theorem summable_norm_i1r8c_raw (t d U V T : ℂ) (ht : t ≠ 0) (depth : ℕ) (hdepth : 1 ≤ depth)
    (h0 : ‖T * V * t / d‖ < 1)
    (h1 : ‖(T * V) ^ 2 * t ^ 2‖ < 1) :
    Summable (fun p : I1R8CRow => ‖i1Raw t d U V T p.val depth‖) := by
  apply i1r8cEquiv.summable_iff.mp
  convert i1_summable_norm_two_geometric
    ((1 - t ^ 2) ^ 3 * (T * V) / t^2) (T * V * t / d) ((T * V) ^ 2 * t ^ 2)
    h0 h1 using 1
  exact funext fun n => congrArg norm
    (i1r8c_reindexed t d U V T ht depth hdepth n)

/-- Source I1 row 9, with integer valuation inequalities. -/
abbrev I1R9Row := {p : ℤ × ℤ × ℤ //
  let k := p.1; let j := p.2.1; let h := p.2.2; k ≤ 0 ∧ j < 0 ∧ j ≤ h ∧ 2*h ≤ j-2}

def i1r9Equiv : (ℕ × ℕ × ℕ) ≃ I1R9Row where
  toFun n := ⟨(by
    rcases n with ⟨a, b, c⟩
    exact (-(a : ℤ),-2*(b : ℤ)-(c : ℤ)-2,-(b : ℤ)-(c : ℤ)-2)), by
      rcases n with ⟨a, b, c⟩
      dsimp
      omega⟩
  invFun p := (by
    let k := p.val.1; let j := p.val.2.1; let h := p.val.2.2
    exact ((-k).toNat, (h-j).toNat, (j-2*h-2).toNat))
  left_inv n := by
    rcases n with ⟨a, b, c⟩
    simp only [Prod.mk.injEq]
    try dsimp
    omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩,hp⟩
    dsimp at hp ⊢
    simp only [Prod.mk.injEq]
    omega

@[simp] theorem i1r9Equiv_val (a b c : ℕ) :
    (i1r9Equiv (a,b,c)).val = (-(a : ℤ),-2*(b : ℤ)-(c : ℤ)-2,-(b : ℤ)-(c : ℤ)-2) := rfl

theorem i1r9_cartan (p : I1R9Row) (depth : ℕ) :
    cartanIndices 1 p.val.1 p.val.2.1 p.val.2.2 depth = (2*p.val.2.1-4*p.val.2.2,2*p.val.2.2-2*p.val.2.1-p.val.1) := by
  rw [← tableOne_correct _ _ _ _ (by omega)]
  rcases p with ⟨⟨k,j,h⟩,hp⟩
  dsimp at hp ⊢
  
  unfold tableOne collisionRows
  split_ifs <;> simp only [Prod.mk.injEq] <;> omega

theorem i1r9_reindexed (t d U V T : ℂ)  (depth : ℕ)
    (n : ℕ × ℕ × ℕ) :
    i1Raw t d U V T (i1r9Equiv n).val depth = ((1 - t ^ 2) ^ 3 * (T * U)^2 * t^2) * (T * V * t / d) ^ n.1 * ((T * V) ^ 2 * t ^ 2) ^ n.2.1 * (T * U * t ^ 2) ^ n.2.2 := by
  rcases n with ⟨a, b, c⟩
  unfold i1Raw
  
  rw [i1r9_cartan]
  
  simp only [i1r9Equiv_val]
  have he : 3 * (-(a : ℤ)) + 2 * (-2*(b : ℤ)-(c : ℤ)-2) + 2 * (-(b : ℤ)-(c : ℤ)-2) +
      3 * (2*(-2*(b : ℤ)-(c : ℤ)-2)-4*(-(b : ℤ)-(c : ℤ)-2)) + 4 * (2*(-(b : ℤ)-(c : ℤ)-2)-2*(-2*(b : ℤ)-(c : ℤ)-2)-(-(a : ℤ))) - 2 = ((a+2*b+2*c+2 : ℕ) : ℤ) := by omega
  have hk : -(a : ℤ) = -((a : ℕ) : ℤ) := by omega
  have hb : 2*(-(b : ℤ)-(c : ℤ)-2)-2*(-2*(b : ℤ)-(c : ℤ)-2)-(-(a : ℤ)) = ((a+2*b : ℕ) : ℤ) := by omega
  have hl : (2*(-2*(b : ℤ)-(c : ℤ)-2)-4*(-(b : ℤ)-(c : ℤ)-2)) / 2 = ((c+2 : ℕ) : ℤ) := by omega
  rw [he, hl, hb]
  try rw [hk]
  
  simp only [zpow_neg, zpow_natCast, zpow_ofNat, pow_add, pow_mul, mul_pow,
    pow_one, pow_zero, one_mul, mul_one, mul_inv_rev, div_eq_mul_inv, inv_pow]
  ring

theorem hasSum_i1r9_raw (t d U V T : ℂ)  (depth : ℕ)
    (h0 : ‖T * V * t / d‖ < 1)
    (h1 : ‖(T * V) ^ 2 * t ^ 2‖ < 1)
    (h2 : ‖T * U * t ^ 2‖ < 1) :
    HasSum (fun p : I1R9Row => i1Raw t d U V T p.val depth)
      (((1 - t ^ 2) ^ 3 * (T * U)^2 * t^2) * (1 - T * V * t / d)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (1 - T * U * t ^ 2)⁻¹) := by
  apply i1r9Equiv.hasSum_iff.mp
  convert hasSum_three_geometric
    ((1 - t ^ 2) ^ 3 * (T * U)^2 * t^2) (T * V * t / d) ((T * V) ^ 2 * t ^ 2) (T * U * t ^ 2)
    h0 h1 h2 using 1
  exact funext fun n => i1r9_reindexed t d U V T depth n

theorem summable_norm_i1r9_raw (t d U V T : ℂ)  (depth : ℕ)
    (h0 : ‖T * V * t / d‖ < 1)
    (h1 : ‖(T * V) ^ 2 * t ^ 2‖ < 1)
    (h2 : ‖T * U * t ^ 2‖ < 1) :
    Summable (fun p : I1R9Row => ‖i1Raw t d U V T p.val depth‖) := by
  apply i1r9Equiv.summable_iff.mp
  convert summable_norm_three_geometric
    ((1 - t ^ 2) ^ 3 * (T * U)^2 * t^2) (T * V * t / d) ((T * V) ^ 2 * t ^ 2) (T * U * t ^ 2)
    h0 h1 h2 using 1
  exact funext fun n => congrArg norm
    (i1r9_reindexed t d U V T depth n)

/-- Source I1 row 10, with integer valuation inequalities. -/
abbrev I1R10Row := {p : ℤ × ℤ × ℤ //
  let k := p.1; let j := p.2.1; let h := p.2.2; k ≤ 0 ∧ j < 0 ∧ h < j}

def i1r10Equiv : (ℕ × ℕ × ℕ) ≃ I1R10Row where
  toFun n := ⟨(by
    rcases n with ⟨a, b, c⟩
    exact (-(a : ℤ),-(b : ℤ)-1,-(b : ℤ)-(c : ℤ)-2)), by
      rcases n with ⟨a, b, c⟩
      dsimp
      omega⟩
  invFun p := (by
    let k := p.val.1; let j := p.val.2.1; let h := p.val.2.2
    exact ((-k).toNat, (-j-1).toNat, (j-h-1).toNat))
  left_inv n := by
    rcases n with ⟨a, b, c⟩
    simp only [Prod.mk.injEq]
    try dsimp
    omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩,hp⟩
    dsimp at hp ⊢
    simp only [Prod.mk.injEq]
    omega

@[simp] theorem i1r10Equiv_val (a b c : ℕ) :
    (i1r10Equiv (a,b,c)).val = (-(a : ℤ),-(b : ℤ)-1,-(b : ℤ)-(c : ℤ)-2) := rfl

theorem i1r10_cartan (p : I1R10Row) (depth : ℕ) :
    cartanIndices 1 p.val.1 p.val.2.1 p.val.2.2 depth = (-2*p.val.2.2,-p.val.1) := by
  rw [← tableOne_correct _ _ _ _ (by omega)]
  rcases p with ⟨⟨k,j,h⟩,hp⟩
  dsimp at hp ⊢
  
  unfold tableOne collisionRows
  split_ifs <;> simp only [Prod.mk.injEq] <;> omega

theorem i1r10_reindexed (t d U V T : ℂ)  (depth : ℕ)
    (n : ℕ × ℕ × ℕ) :
    i1Raw t d U V T (i1r10Equiv n).val depth = ((1 - t ^ 2) ^ 3 * (T * U)^2 * t^4) * (T * V * t / d) ^ n.1 * (T * U * t ^ 2) ^ n.2.1 * (T * U * t ^ 4) ^ n.2.2 := by
  rcases n with ⟨a, b, c⟩
  unfold i1Raw
  
  rw [i1r10_cartan]
  
  simp only [i1r10Equiv_val]
  have he : 3 * (-(a : ℤ)) + 2 * (-(b : ℤ)-1) + 2 * (-(b : ℤ)-(c : ℤ)-2) +
      3 * (-2*(-(b : ℤ)-(c : ℤ)-2)) + 4 * (-(-(a : ℤ))) - 2 = ((a+2*b+4*c+4 : ℕ) : ℤ) := by omega
  have hk : -(a : ℤ) = -((a : ℕ) : ℤ) := by omega
  have hb : -(-(a : ℤ)) = ((a : ℕ) : ℤ) := by omega
  have hl : (-2*(-(b : ℤ)-(c : ℤ)-2)) / 2 = ((b+c+2 : ℕ) : ℤ) := by omega
  rw [he, hl, hb]
  try rw [hk]
  
  simp only [zpow_neg, zpow_natCast, zpow_ofNat, pow_add, pow_mul, mul_pow,
    pow_one, pow_zero, one_mul, mul_one, mul_inv_rev, div_eq_mul_inv, inv_pow]
  ring

theorem hasSum_i1r10_raw (t d U V T : ℂ)  (depth : ℕ)
    (h0 : ‖T * V * t / d‖ < 1)
    (h1 : ‖T * U * t ^ 2‖ < 1)
    (h2 : ‖T * U * t ^ 4‖ < 1) :
    HasSum (fun p : I1R10Row => i1Raw t d U V T p.val depth)
      (((1 - t ^ 2) ^ 3 * (T * U)^2 * t^4) * (1 - T * V * t / d)⁻¹ * (1 - T * U * t ^ 2)⁻¹ * (1 - T * U * t ^ 4)⁻¹) := by
  apply i1r10Equiv.hasSum_iff.mp
  convert hasSum_three_geometric
    ((1 - t ^ 2) ^ 3 * (T * U)^2 * t^4) (T * V * t / d) (T * U * t ^ 2) (T * U * t ^ 4)
    h0 h1 h2 using 1
  exact funext fun n => i1r10_reindexed t d U V T depth n

theorem summable_norm_i1r10_raw (t d U V T : ℂ)  (depth : ℕ)
    (h0 : ‖T * V * t / d‖ < 1)
    (h1 : ‖T * U * t ^ 2‖ < 1)
    (h2 : ‖T * U * t ^ 4‖ < 1) :
    Summable (fun p : I1R10Row => ‖i1Raw t d U V T p.val depth‖) := by
  apply i1r10Equiv.summable_iff.mp
  convert summable_norm_three_geometric
    ((1 - t ^ 2) ^ 3 * (T * U)^2 * t^4) (T * V * t / d) (T * U * t ^ 2) (T * U * t ^ 4)
    h0 h1 h2 using 1
  exact funext fun n => congrArg norm
    (i1r10_reindexed t d U V T depth n)

end FourierJacobi.Analysis
