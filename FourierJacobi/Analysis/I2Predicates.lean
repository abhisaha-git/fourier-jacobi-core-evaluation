import FourierJacobi.Analysis.I2Domains

namespace FourierJacobi.Analysis

@[simp] theorem i2SpatialPredicate_row0 (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 0 p ↔ (2 ≤ p.1 ∧ -2*p.1 ≤ p.2.1 ∧ -p.1 ≤ p.2.2) := Iff.rfl
@[simp] theorem i2DepthPredicate_row0 (c : ℕ) : i2DepthPredicate 0 c ↔ (True) := Iff.rfl
@[simp] theorem i2SpatialPredicate_row1 (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 1 p ↔ (p.1 = 1 ∧ -2 ≤ p.2.1 ∧ -1 ≤ p.2.2) := Iff.rfl
@[simp] theorem i2DepthPredicate_row1 (c : ℕ) : i2DepthPredicate 1 c ↔ (True) := Iff.rfl
@[simp] theorem i2SpatialPredicate_row2 (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 2 p ↔ (1 ≤ p.1 ∧ -2*p.1 ≤ p.2.1 ∧ p.2.2 < -p.1) := Iff.rfl
@[simp] theorem i2DepthPredicate_row2 (c : ℕ) : i2DepthPredicate 2 c ↔ (True) := Iff.rfl
@[simp] theorem i2SpatialPredicate_row3 (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 3 p ↔ (1 ≤ p.1 ∧ p.2.1 < -2*p.1 ∧ p.1+p.2.1 ≤ p.2.2 ∧ p.2.1-1 ≤ 2*p.2.2) := Iff.rfl
@[simp] theorem i2DepthPredicate_row3 (c : ℕ) : i2DepthPredicate 3 c ↔ (True) := Iff.rfl
@[simp] theorem i2SpatialPredicate_row4 (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 4 p ↔ (1 ≤ p.1 ∧ p.2.1 < -2*p.1 ∧ p.1+p.2.1 ≤ p.2.2 ∧ 2*p.2.2 = p.2.1-2) := Iff.rfl
@[simp] theorem i2DepthPredicate_row4 (c : ℕ) : i2DepthPredicate 4 c ↔ (c = 0) := Iff.rfl
@[simp] theorem i2SpatialPredicate_row5 (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 5 p ↔ (1 ≤ p.1 ∧ p.2.1 < -2*p.1 ∧ p.1+p.2.1 ≤ p.2.2 ∧ 2*p.2.2 = p.2.1-2) := Iff.rfl
@[simp] theorem i2DepthPredicate_row5 (c : ℕ) : i2DepthPredicate 5 c ↔ (c = 1) := Iff.rfl
@[simp] theorem i2SpatialPredicate_row6 (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 6 p ↔ (1 ≤ p.1 ∧ p.2.1 < -2*p.1 ∧ p.1+p.2.1 ≤ p.2.2 ∧ 2*p.2.2 = p.2.1-2) := Iff.rfl
@[simp] theorem i2DepthPredicate_row6 (c : ℕ) : i2DepthPredicate 6 c ↔ (2 ≤ c) := Iff.rfl
@[simp] theorem i2SpatialPredicate_row7 (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 7 p ↔ (1 ≤ p.1 ∧ p.2.1 < -2*p.1 ∧ p.1+p.2.1 ≤ p.2.2 ∧ 2*p.2.2 ≤ p.2.1-3) := Iff.rfl
@[simp] theorem i2DepthPredicate_row7 (c : ℕ) : i2DepthPredicate 7 c ↔ (True) := Iff.rfl
@[simp] theorem i2SpatialPredicate_row8 (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 8 p ↔ (1 ≤ p.1 ∧ p.2.1 < -2*p.1 ∧ p.2.2 < p.1+p.2.1) := Iff.rfl
@[simp] theorem i2DepthPredicate_row8 (c : ℕ) : i2DepthPredicate 8 c ↔ (True) := Iff.rfl
@[simp] theorem i2SpatialPredicate_row9 (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 9 p ↔ (p.1 = 0 ∧ 0 ≤ p.2.1 ∧ -1 ≤ p.2.2) := Iff.rfl
@[simp] theorem i2DepthPredicate_row9 (c : ℕ) : i2DepthPredicate 9 c ↔ (True) := Iff.rfl
@[simp] theorem i2SpatialPredicate_row10 (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 10 p ↔ (p.1 = 0 ∧ p.2.1 = -1 ∧ -1 ≤ p.2.2) := Iff.rfl
@[simp] theorem i2DepthPredicate_row10 (c : ℕ) : i2DepthPredicate 10 c ↔ (True) := Iff.rfl
@[simp] theorem i2SpatialPredicate_row11 (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 11 p ↔ (p.1 = 0 ∧ -1 ≤ p.2.1 ∧ p.2.2 ≤ -2) := Iff.rfl
@[simp] theorem i2DepthPredicate_row11 (c : ℕ) : i2DepthPredicate 11 c ↔ (True) := Iff.rfl
@[simp] theorem i2SpatialPredicate_row12 (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 12 p ↔ (p.1 = -1 ∧ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2) := Iff.rfl
@[simp] theorem i2DepthPredicate_row12 (c : ℕ) : i2DepthPredicate 12 c ↔ (True) := Iff.rfl
@[simp] theorem i2SpatialPredicate_row13 (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 13 p ↔ (p.1 = -1 ∧ p.2.1 = -1 ∧ -1 ≤ p.2.2) := Iff.rfl
@[simp] theorem i2DepthPredicate_row13 (c : ℕ) : i2DepthPredicate 13 c ↔ (True) := Iff.rfl
@[simp] theorem i2SpatialPredicate_row14 (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 14 p ↔ (p.1 = -1 ∧ p.2.1 = -1 ∧ p.2.2 ≤ -2) := Iff.rfl
@[simp] theorem i2DepthPredicate_row14 (c : ℕ) : i2DepthPredicate 14 c ↔ (True) := Iff.rfl
@[simp] theorem i2SpatialPredicate_row15 (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 15 p ↔ (p.1 ≤ -2 ∧ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2) := Iff.rfl
@[simp] theorem i2DepthPredicate_row15 (c : ℕ) : i2DepthPredicate 15 c ↔ (True) := Iff.rfl
@[simp] theorem i2SpatialPredicate_row16 (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 16 p ↔ (p.1 ≤ -2 ∧ p.2.1 = -1 ∧ -1 ≤ p.2.2) := Iff.rfl
@[simp] theorem i2DepthPredicate_row16 (c : ℕ) : i2DepthPredicate 16 c ↔ (True) := Iff.rfl
@[simp] theorem i2SpatialPredicate_row17 (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 17 p ↔ (p.1 ≤ -2 ∧ p.2.1 = -1 ∧ p.2.2 ≤ -2) := Iff.rfl
@[simp] theorem i2DepthPredicate_row17 (c : ℕ) : i2DepthPredicate 17 c ↔ (True) := Iff.rfl
@[simp] theorem i2SpatialPredicate_row18 (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 18 p ↔ (p.1 ≤ -1 ∧ 0 ≤ p.2.1 ∧ p.2.2 ≤ -1) := Iff.rfl
@[simp] theorem i2DepthPredicate_row18 (c : ℕ) : i2DepthPredicate 18 c ↔ (True) := Iff.rfl
@[simp] theorem i2SpatialPredicate_row19 (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 19 p ↔ (p.1 ≤ 0 ∧ p.2.1 < -1 ∧ p.2.1 ≤ p.2.2 ∧ p.2.1-1 ≤ 2*p.2.2) := Iff.rfl
@[simp] theorem i2DepthPredicate_row19 (c : ℕ) : i2DepthPredicate 19 c ↔ (True) := Iff.rfl
@[simp] theorem i2SpatialPredicate_row20 (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 20 p ↔ (p.1 ≤ 0 ∧ p.2.1 < -1 ∧ p.2.1 ≤ p.2.2 ∧ 2*p.2.2 = p.2.1-2) := Iff.rfl
@[simp] theorem i2DepthPredicate_row20 (c : ℕ) : i2DepthPredicate 20 c ↔ (c = 0) := Iff.rfl
@[simp] theorem i2SpatialPredicate_row21 (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 21 p ↔ (p.1 ≤ 0 ∧ p.2.1 < -1 ∧ p.2.1 ≤ p.2.2 ∧ 2*p.2.2 = p.2.1-2) := Iff.rfl
@[simp] theorem i2DepthPredicate_row21 (c : ℕ) : i2DepthPredicate 21 c ↔ (c = 1) := Iff.rfl
@[simp] theorem i2SpatialPredicate_row22 (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 22 p ↔ (p.1 ≤ 0 ∧ p.2.1 < -1 ∧ p.2.1 ≤ p.2.2 ∧ 2*p.2.2 = p.2.1-2) := Iff.rfl
@[simp] theorem i2DepthPredicate_row22 (c : ℕ) : i2DepthPredicate 22 c ↔ (2 ≤ c) := Iff.rfl
@[simp] theorem i2SpatialPredicate_row23 (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 23 p ↔ (p.1 ≤ 0 ∧ p.2.1 < -1 ∧ p.2.1 ≤ p.2.2 ∧ 2*p.2.2 ≤ p.2.1-3) := Iff.rfl
@[simp] theorem i2DepthPredicate_row23 (c : ℕ) : i2DepthPredicate 23 c ↔ (True) := Iff.rfl
@[simp] theorem i2SpatialPredicate_row24 (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 24 p ↔ (p.1 ≤ 0 ∧ p.2.1 < -1 ∧ p.2.2 < p.2.1) := Iff.rfl
@[simp] theorem i2DepthPredicate_row24 (c : ℕ) : i2DepthPredicate 24 c ↔ (True) := Iff.rfl


end FourierJacobi.Analysis
