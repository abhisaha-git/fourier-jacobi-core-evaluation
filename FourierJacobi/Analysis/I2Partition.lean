import FourierJacobi.Analysis.I2Predicates
import Mathlib.Data.Fintype.Fin

/-! Disjoint and exhaustive original integer/depth partition for I2eq4. -/

namespace FourierJacobi.Analysis

set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

def i2TailClassify (positive : Bool) (j h : ℤ) (c : ℕ) : Fin 25 :=
  if j - 1 ≤ 2 * h then (if positive then 3 else 19)
  else if 2 * h = j - 2 then
    if c = 0 then (if positive then 4 else 20)
    else if c = 1 then (if positive then 5 else 21)
    else (if positive then 6 else 22)
  else (if positive then 7 else 23)

def i2Classify (k j h : ℤ) (c : ℕ) : Fin 25 :=
  if 1 ≤ k then
    if -2 * k ≤ j then
      if h < -k then 2 else if 2 ≤ k then 0 else 1
    else if h < k + j then 8 else i2TailClassify true j h c
  else if k = 0 then
    if -1 ≤ j then
      if h ≤ -2 then 11 else if 0 ≤ j then 9 else 10
    else if h < j then 24 else i2TailClassify false j h c
  else if 0 ≤ j then
    if h ≤ -1 then 18 else if k = -1 then 12 else 15
  else if j = -1 then
    if h ≤ -2 then (if k = -1 then 14 else 17)
    else (if k = -1 then 13 else 16)
  else if h < j then 24 else i2TailClassify false j h c

theorem i2Classify_mem (k j h : ℤ) (c : ℕ) :
    i2SpatialPredicate (i2Classify k j h c) (k,j,h) ∧
      i2DepthPredicate (i2Classify k j h c) c := by
  unfold i2Classify i2TailClassify
  split_ifs <;> norm_num at * <;> omega

theorem i2Classify_eq_of_mem (ν : Fin 25) (k j h : ℤ) (c : ℕ)
    (hp : i2SpatialPredicate ν (k,j,h)) (hc : i2DepthPredicate ν c) :
    i2Classify k j h c = ν := by
  fin_cases ν
  · change 2 ≤ k ∧ -2*k ≤ j ∧ -k ≤ h at hp
    change True at hc
    have h0 : 1 ≤ k := by omega
    have h1 : -2*k ≤ j := by omega
    have h2 : ¬(h < -k) := by omega
    have h3 : 2 ≤ k := by omega
    simp only [i2Classify, i2TailClassify, if_pos h0, if_pos h1, if_neg h2, if_pos h3,
      if_pos (rfl : true = true), if_neg (by decide : ¬ false = true), ite_self]
    rfl
  · change k = 1 ∧ -2 ≤ j ∧ -1 ≤ h at hp
    change True at hc
    have h0 : 1 ≤ k := by omega
    have h1 : -2*k ≤ j := by omega
    have h2 : ¬(h < -k) := by omega
    have h3 : ¬(2 ≤ k) := by omega
    simp only [i2Classify, i2TailClassify, if_pos h0, if_pos h1, if_neg h2, if_neg h3,
      if_pos (rfl : true = true), if_neg (by decide : ¬ false = true), ite_self]
    rfl
  · change 1 ≤ k ∧ -2*k ≤ j ∧ h < -k at hp
    change True at hc
    have h0 : 1 ≤ k := by omega
    have h1 : -2*k ≤ j := by omega
    have h2 : h < -k := by omega
    simp only [i2Classify, i2TailClassify, if_pos h0, if_pos h1, if_pos h2,
      if_pos (rfl : true = true), if_neg (by decide : ¬ false = true), ite_self]
    rfl
  · change 1 ≤ k ∧ j < -2*k ∧ k+j ≤ h ∧ j-1 ≤ 2*h at hp
    change True at hc
    have h0 : 1 ≤ k := by omega
    have h1 : ¬(-2*k ≤ j) := by omega
    have h2 : ¬(h < k+j) := by omega
    have h3 : j-1 ≤ 2*h := by omega
    simp only [i2Classify, i2TailClassify, if_pos h0, if_neg h1, if_neg h2, if_pos h3,
      if_pos (rfl : true = true), if_neg (by decide : ¬ false = true), ite_self]
    rfl
  · change 1 ≤ k ∧ j < -2*k ∧ k+j ≤ h ∧ 2*h = j-2 at hp
    change c = 0 at hc
    have h0 : 1 ≤ k := by omega
    have h1 : ¬(-2*k ≤ j) := by omega
    have h2 : ¬(h < k+j) := by omega
    have h3 : ¬(j-1 ≤ 2*h) := by omega
    have h4 : 2*h = j-2 := by omega
    have h5 : c = 0 := by omega
    simp only [i2Classify, i2TailClassify, if_pos h0, if_neg h1, if_neg h2, if_neg h3, if_pos h4, if_pos h5,
      if_pos (rfl : true = true), if_neg (by decide : ¬ false = true), ite_self]
    rfl
  · change 1 ≤ k ∧ j < -2*k ∧ k+j ≤ h ∧ 2*h = j-2 at hp
    change c = 1 at hc
    have h0 : 1 ≤ k := by omega
    have h1 : ¬(-2*k ≤ j) := by omega
    have h2 : ¬(h < k+j) := by omega
    have h3 : ¬(j-1 ≤ 2*h) := by omega
    have h4 : 2*h = j-2 := by omega
    have h5 : ¬(c = 0) := by omega
    have h6 : c = 1 := by omega
    simp only [i2Classify, i2TailClassify, if_pos h0, if_neg h1, if_neg h2, if_neg h3, if_pos h4, if_neg h5, if_pos h6,
      if_pos (rfl : true = true), if_neg (by decide : ¬ false = true), ite_self]
    rfl
  · change 1 ≤ k ∧ j < -2*k ∧ k+j ≤ h ∧ 2*h = j-2 at hp
    change 2 ≤ c at hc
    have h0 : 1 ≤ k := by omega
    have h1 : ¬(-2*k ≤ j) := by omega
    have h2 : ¬(h < k+j) := by omega
    have h3 : ¬(j-1 ≤ 2*h) := by omega
    have h4 : 2*h = j-2 := by omega
    have h5 : ¬(c = 0) := by omega
    have h6 : ¬(c = 1) := by omega
    simp only [i2Classify, i2TailClassify, if_pos h0, if_neg h1, if_neg h2, if_neg h3, if_pos h4, if_neg h5, if_neg h6,
      if_pos (rfl : true = true), if_neg (by decide : ¬ false = true), ite_self]
    rfl
  · change 1 ≤ k ∧ j < -2*k ∧ k+j ≤ h ∧ 2*h ≤ j-3 at hp
    change True at hc
    have h0 : 1 ≤ k := by omega
    have h1 : ¬(-2*k ≤ j) := by omega
    have h2 : ¬(h < k+j) := by omega
    have h3 : ¬(j-1 ≤ 2*h) := by omega
    have h4 : ¬(2*h = j-2) := by omega
    simp only [i2Classify, i2TailClassify, if_pos h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4,
      if_pos (rfl : true = true), if_neg (by decide : ¬ false = true), ite_self]
    rfl
  · change 1 ≤ k ∧ j < -2*k ∧ h < k+j at hp
    change True at hc
    have h0 : 1 ≤ k := by omega
    have h1 : ¬(-2*k ≤ j) := by omega
    have h2 : h < k+j := by omega
    simp only [i2Classify, i2TailClassify, if_pos h0, if_neg h1, if_pos h2,
      if_pos (rfl : true = true), if_neg (by decide : ¬ false = true), ite_self]
    rfl
  · change k = 0 ∧ 0 ≤ j ∧ -1 ≤ h at hp
    change True at hc
    have h0 : ¬(1 ≤ k) := by omega
    have h1 : k = 0 := by omega
    have h2 : -1 ≤ j := by omega
    have h3 : ¬(h ≤ -2) := by omega
    have h4 : 0 ≤ j := by omega
    simp only [i2Classify, i2TailClassify, if_neg h0, if_pos h1, if_pos h2, if_neg h3, if_pos h4,
      if_pos (rfl : true = true), if_neg (by decide : ¬ false = true), ite_self]
    rfl
  · change k = 0 ∧ j = -1 ∧ -1 ≤ h at hp
    change True at hc
    have h0 : ¬(1 ≤ k) := by omega
    have h1 : k = 0 := by omega
    have h2 : -1 ≤ j := by omega
    have h3 : ¬(h ≤ -2) := by omega
    have h4 : ¬(0 ≤ j) := by omega
    simp only [i2Classify, i2TailClassify, if_neg h0, if_pos h1, if_pos h2, if_neg h3, if_neg h4,
      if_pos (rfl : true = true), if_neg (by decide : ¬ false = true), ite_self]
    rfl
  · change k = 0 ∧ -1 ≤ j ∧ h ≤ -2 at hp
    change True at hc
    have h0 : ¬(1 ≤ k) := by omega
    have h1 : k = 0 := by omega
    have h2 : -1 ≤ j := by omega
    have h3 : h ≤ -2 := by omega
    simp only [i2Classify, i2TailClassify, if_neg h0, if_pos h1, if_pos h2, if_pos h3,
      if_pos (rfl : true = true), if_neg (by decide : ¬ false = true), ite_self]
    rfl
  · change k = -1 ∧ 0 ≤ j ∧ 0 ≤ h at hp
    change True at hc
    have h0 : ¬(1 ≤ k) := by omega
    have h1 : ¬(k = 0) := by omega
    have h2 : 0 ≤ j := by omega
    have h3 : ¬(h ≤ -1) := by omega
    have h4 : k = -1 := by omega
    simp only [i2Classify, i2TailClassify, if_neg h0, if_neg h1, if_pos h2, if_neg h3, if_pos h4,
      if_pos (rfl : true = true), if_neg (by decide : ¬ false = true), ite_self]
    rfl
  · change k = -1 ∧ j = -1 ∧ -1 ≤ h at hp
    change True at hc
    have h0 : ¬(1 ≤ k) := by omega
    have h1 : ¬(k = 0) := by omega
    have h2 : ¬(0 ≤ j) := by omega
    have h3 : j = -1 := by omega
    have h4 : ¬(h ≤ -2) := by omega
    have h5 : k = -1 := by omega
    simp only [i2Classify, i2TailClassify, if_neg h0, if_neg h1, if_neg h2, if_pos h3, if_neg h4, if_pos h5,
      if_pos (rfl : true = true), if_neg (by decide : ¬ false = true), ite_self]
    rfl
  · change k = -1 ∧ j = -1 ∧ h ≤ -2 at hp
    change True at hc
    have h0 : ¬(1 ≤ k) := by omega
    have h1 : ¬(k = 0) := by omega
    have h2 : ¬(0 ≤ j) := by omega
    have h3 : j = -1 := by omega
    have h4 : h ≤ -2 := by omega
    have h5 : k = -1 := by omega
    simp only [i2Classify, i2TailClassify, if_neg h0, if_neg h1, if_neg h2, if_pos h3, if_pos h4, if_pos h5,
      if_pos (rfl : true = true), if_neg (by decide : ¬ false = true), ite_self]
    rfl
  · change k ≤ -2 ∧ 0 ≤ j ∧ 0 ≤ h at hp
    change True at hc
    have h0 : ¬(1 ≤ k) := by omega
    have h1 : ¬(k = 0) := by omega
    have h2 : 0 ≤ j := by omega
    have h3 : ¬(h ≤ -1) := by omega
    have h4 : ¬(k = -1) := by omega
    simp only [i2Classify, i2TailClassify, if_neg h0, if_neg h1, if_pos h2, if_neg h3, if_neg h4,
      if_pos (rfl : true = true), if_neg (by decide : ¬ false = true), ite_self]
    rfl
  · change k ≤ -2 ∧ j = -1 ∧ -1 ≤ h at hp
    change True at hc
    have h0 : ¬(1 ≤ k) := by omega
    have h1 : ¬(k = 0) := by omega
    have h2 : ¬(0 ≤ j) := by omega
    have h3 : j = -1 := by omega
    have h4 : ¬(h ≤ -2) := by omega
    have h5 : ¬(k = -1) := by omega
    simp only [i2Classify, i2TailClassify, if_neg h0, if_neg h1, if_neg h2, if_pos h3, if_neg h4, if_neg h5,
      if_pos (rfl : true = true), if_neg (by decide : ¬ false = true), ite_self]
    rfl
  · change k ≤ -2 ∧ j = -1 ∧ h ≤ -2 at hp
    change True at hc
    have h0 : ¬(1 ≤ k) := by omega
    have h1 : ¬(k = 0) := by omega
    have h2 : ¬(0 ≤ j) := by omega
    have h3 : j = -1 := by omega
    have h4 : h ≤ -2 := by omega
    have h5 : ¬(k = -1) := by omega
    simp only [i2Classify, i2TailClassify, if_neg h0, if_neg h1, if_neg h2, if_pos h3, if_pos h4, if_neg h5,
      if_pos (rfl : true = true), if_neg (by decide : ¬ false = true), ite_self]
    rfl
  · change k ≤ -1 ∧ 0 ≤ j ∧ h ≤ -1 at hp
    change True at hc
    have h0 : ¬(1 ≤ k) := by omega
    have h1 : ¬(k = 0) := by omega
    have h2 : 0 ≤ j := by omega
    have h3 : h ≤ -1 := by omega
    simp only [i2Classify, i2TailClassify, if_neg h0, if_neg h1, if_pos h2, if_pos h3,
      if_pos (rfl : true = true), if_neg (by decide : ¬ false = true), ite_self]
    rfl
  · change k ≤ 0 ∧ j < -1 ∧ j ≤ h ∧ j-1 ≤ 2*h at hp
    change True at hc
    have h0 : ¬(1 ≤ k) := by omega
    have h1 : ¬(-1 ≤ j) := by omega
    have h2 : ¬(0 ≤ j) := by omega
    have h3 : ¬(j = -1) := by omega
    have h4 : ¬(h < j) := by omega
    have h5 : j-1 ≤ 2*h := by omega
    simp only [i2Classify, i2TailClassify, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos h5,
      if_pos (rfl : true = true), if_neg (by decide : ¬ false = true), ite_self]
    rfl
  · change k ≤ 0 ∧ j < -1 ∧ j ≤ h ∧ 2*h = j-2 at hp
    change c = 0 at hc
    have h0 : ¬(1 ≤ k) := by omega
    have h1 : ¬(-1 ≤ j) := by omega
    have h2 : ¬(0 ≤ j) := by omega
    have h3 : ¬(j = -1) := by omega
    have h4 : ¬(h < j) := by omega
    have h5 : ¬(j-1 ≤ 2*h) := by omega
    have h6 : 2*h = j-2 := by omega
    have h7 : c = 0 := by omega
    simp only [i2Classify, i2TailClassify, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_pos h6, if_pos h7,
      if_pos (rfl : true = true), if_neg (by decide : ¬ false = true), ite_self]
    rfl
  · change k ≤ 0 ∧ j < -1 ∧ j ≤ h ∧ 2*h = j-2 at hp
    change c = 1 at hc
    have h0 : ¬(1 ≤ k) := by omega
    have h1 : ¬(-1 ≤ j) := by omega
    have h2 : ¬(0 ≤ j) := by omega
    have h3 : ¬(j = -1) := by omega
    have h4 : ¬(h < j) := by omega
    have h5 : ¬(j-1 ≤ 2*h) := by omega
    have h6 : 2*h = j-2 := by omega
    have h7 : ¬(c = 0) := by omega
    have h8 : c = 1 := by omega
    simp only [i2Classify, i2TailClassify, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_pos h6, if_neg h7, if_pos h8,
      if_pos (rfl : true = true), if_neg (by decide : ¬ false = true), ite_self]
    rfl
  · change k ≤ 0 ∧ j < -1 ∧ j ≤ h ∧ 2*h = j-2 at hp
    change 2 ≤ c at hc
    have h0 : ¬(1 ≤ k) := by omega
    have h1 : ¬(-1 ≤ j) := by omega
    have h2 : ¬(0 ≤ j) := by omega
    have h3 : ¬(j = -1) := by omega
    have h4 : ¬(h < j) := by omega
    have h5 : ¬(j-1 ≤ 2*h) := by omega
    have h6 : 2*h = j-2 := by omega
    have h7 : ¬(c = 0) := by omega
    have h8 : ¬(c = 1) := by omega
    simp only [i2Classify, i2TailClassify, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_pos h6, if_neg h7, if_neg h8,
      if_pos (rfl : true = true), if_neg (by decide : ¬ false = true), ite_self]
    rfl
  · change k ≤ 0 ∧ j < -1 ∧ j ≤ h ∧ 2*h ≤ j-3 at hp
    change True at hc
    have h0 : ¬(1 ≤ k) := by omega
    have h1 : ¬(-1 ≤ j) := by omega
    have h2 : ¬(0 ≤ j) := by omega
    have h3 : ¬(j = -1) := by omega
    have h4 : ¬(h < j) := by omega
    have h5 : ¬(j-1 ≤ 2*h) := by omega
    have h6 : ¬(2*h = j-2) := by omega
    simp only [i2Classify, i2TailClassify, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6,
      if_pos (rfl : true = true), if_neg (by decide : ¬ false = true), ite_self]
    rfl
  · change k ≤ 0 ∧ j < -1 ∧ h < j at hp
    change True at hc
    have h0 : ¬(1 ≤ k) := by omega
    have h1 : ¬(-1 ≤ j) := by omega
    have h2 : ¬(0 ≤ j) := by omega
    have h3 : ¬(j = -1) := by omega
    have h4 : h < j := by omega
    simp only [i2Classify, i2TailClassify, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_pos h4,
      if_pos (rfl : true = true), if_neg (by decide : ¬ false = true), ite_self]
    rfl

theorem i2_rows_partition (k j h : ℤ) (c : ℕ) :
    ∃! ν : Fin 25, i2SpatialPredicate ν (k,j,h) ∧ i2DepthPredicate ν c := by
  refine ⟨i2Classify k j h c, i2Classify_mem k j h c, ?_⟩
  intro ν hν
  exact (i2Classify_eq_of_mem ν k j h c hν.1 hν.2).symm

end FourierJacobi.Analysis
