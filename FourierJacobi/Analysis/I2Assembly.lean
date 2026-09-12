import FourierJacobi.Analysis.I2Complete
import FourierJacobi.Analysis.I2Predicates
import FourierJacobi.Analysis.CoreParameters

/-! Full original I2 four-coordinate lattice sum, including cancellation depth. -/

noncomputable section

namespace FourierJacobi.Analysis

open FourierJacobi.Valuations

set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

theorem i2_cartan_depth_constant (ν : Fin 25) (p : I2SpatialRow ν) (c : ℕ)
    (hc : i2DepthPredicate ν c) :
    cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 c =
      cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 (i2DepthAt ν) := by
  fin_cases ν
  · change cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 c = cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 (i2DepthAt 0)
    change i2DepthPredicate 0 c at hc
    rw [i2Case1a_cartan p c, i2Case1a_cartan p (i2DepthAt 0)]
  · change cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 c = cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 (i2DepthAt 1)
    change i2DepthPredicate 1 c at hc
    rw [i2Case1b_cartan p c, i2Case1b_cartan p (i2DepthAt 1)]
  · change cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 c = cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 (i2DepthAt 2)
    change i2DepthPredicate 2 c at hc
    rw [i2Case2_cartan p c, i2Case2_cartan p (i2DepthAt 2)]
  · change cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 c = cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 (i2DepthAt 3)
    change i2DepthPredicate 3 c at hc
    rw [i2Case3a_cartan p c, i2Case3a_cartan p (i2DepthAt 3)]
  · change cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 c = cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 (i2DepthAt 4)
    change i2DepthPredicate 4 c at hc
    rw [i2Case3b_cartan p c (by simpa using hc), i2Case3b_cartan p (i2DepthAt 4) (by rw [i2DepthAt_row4])]
  · change cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 c = cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 (i2DepthAt 5)
    change i2DepthPredicate 5 c at hc
    rw [i2Case3c_cartan p c (by simpa using hc), i2Case3c_cartan p (i2DepthAt 5) (by rw [i2DepthAt_row5])]
  · change cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 c = cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 (i2DepthAt 6)
    change i2DepthPredicate 6 c at hc
    rw [i2Case3d_cartan p c (by simpa using hc), i2Case3d_cartan p (i2DepthAt 6) (by rw [i2DepthAt_row6])]
  · change cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 c = cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 (i2DepthAt 7)
    change i2DepthPredicate 7 c at hc
    rw [i2Case4_cartan p c, i2Case4_cartan p (i2DepthAt 7)]
  · change cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 c = cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 (i2DepthAt 8)
    change i2DepthPredicate 8 c at hc
    rw [i2Case5_cartan p c, i2Case5_cartan p (i2DepthAt 8)]
  · change cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 c = cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 (i2DepthAt 9)
    change i2DepthPredicate 9 c at hc
    rw [i2Case6a_cartan p c, i2Case6a_cartan p (i2DepthAt 9)]
  · change cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 c = cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 (i2DepthAt 10)
    change i2DepthPredicate 10 c at hc
    rw [i2Case6aa_cartan p c, i2Case6aa_cartan p (i2DepthAt 10)]
  · change cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 c = cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 (i2DepthAt 11)
    change i2DepthPredicate 11 c at hc
    rw [i2Case6aaa_cartan p c, i2Case6aaa_cartan p (i2DepthAt 11)]
  · change cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 c = cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 (i2DepthAt 12)
    change i2DepthPredicate 12 c at hc
    rw [i2Case6b_cartan p c, i2Case6b_cartan p (i2DepthAt 12)]
  · change cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 c = cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 (i2DepthAt 13)
    change i2DepthPredicate 13 c at hc
    rw [i2Case6bb_cartan p c, i2Case6bb_cartan p (i2DepthAt 13)]
  · change cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 c = cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 (i2DepthAt 14)
    change i2DepthPredicate 14 c at hc
    rw [i2Case6bbb_cartan p c, i2Case6bbb_cartan p (i2DepthAt 14)]
  · change cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 c = cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 (i2DepthAt 15)
    change i2DepthPredicate 15 c at hc
    rw [i2Case6c_cartan p c, i2Case6c_cartan p (i2DepthAt 15)]
  · change cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 c = cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 (i2DepthAt 16)
    change i2DepthPredicate 16 c at hc
    rw [i2Case6cc_cartan p c, i2Case6cc_cartan p (i2DepthAt 16)]
  · change cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 c = cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 (i2DepthAt 17)
    change i2DepthPredicate 17 c at hc
    rw [i2Case6ccc_cartan p c, i2Case6ccc_cartan p (i2DepthAt 17)]
  · change cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 c = cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 (i2DepthAt 18)
    change i2DepthPredicate 18 c at hc
    rw [i2Case7_cartan p c, i2Case7_cartan p (i2DepthAt 18)]
  · change cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 c = cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 (i2DepthAt 19)
    change i2DepthPredicate 19 c at hc
    rw [i2Case8a_cartan p c, i2Case8a_cartan p (i2DepthAt 19)]
  · change cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 c = cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 (i2DepthAt 20)
    change i2DepthPredicate 20 c at hc
    rw [i2Case8b_cartan p c (by simpa using hc), i2Case8b_cartan p (i2DepthAt 20) (by rw [i2DepthAt_row20])]
  · change cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 c = cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 (i2DepthAt 21)
    change i2DepthPredicate 21 c at hc
    rw [i2Case8c_cartan p c (by simpa using hc), i2Case8c_cartan p (i2DepthAt 21) (by rw [i2DepthAt_row21])]
  · change cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 c = cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 (i2DepthAt 22)
    change i2DepthPredicate 22 c at hc
    rw [i2Case8d_cartan p c (by simpa using hc), i2Case8d_cartan p (i2DepthAt 22) (by rw [i2DepthAt_row22])]
  · change cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 c = cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 (i2DepthAt 23)
    change i2DepthPredicate 23 c at hc
    rw [i2Case9_cartan p c, i2Case9_cartan p (i2DepthAt 23)]
  · change cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 c = cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 (i2DepthAt 24)
    change i2DepthPredicate 24 c at hc
    rw [i2Case10_cartan p c, i2Case10_cartan p (i2DepthAt 24)]

theorem hasSum_i2_spatial (q t d U V T : ℂ) (ν : Fin 25)
    (hq : q * t ^ 2 = 1) (hd : d ≠ 0) (h : GeometricRange t d U V T) :
    HasSum (fun p : I2SpatialRow ν => i2SpatialTerm q t d U V T ν p.val)
      (i2RegionTerm ν t d (T * U) (T * V)) := by
  fin_cases ν
  · exact hasSum_i2_case1a_regionTerm q t d U V T hq hd h.t2 h.p
  · exact hasSum_i2_case1b_regionTerm q t d U V T hq hd h.t2
  · exact hasSum_i2_case2_regionTerm q t d U V T hq hd h.t2 h.p h.g
  · exact hasSum_i2_case3a_regionTerm q t d U V T hq hd h.t2 h.p h.e
  · exact hasSum_i2_case3b_regionTerm q t d U V T hq hd h.t2 h.p h.e
  · exact hasSum_i2_case3c_regionTerm q t d U V T hq hd h.t2 h.p h.e
  · exact hasSum_i2_case3d_regionTerm q t d U V T hq hd h.t2 h.p h.e
  · exact hasSum_i2_case4_regionTerm q t d U V T hq hd h.t2 h.p h.e h.f
  · exact hasSum_i2_case5_regionTerm q t d U V T hq hd h.t2 h.p h.f h.g
  · exact hasSum_i2_case6a_regionTerm q t d U V T hq hd h.t2
  · exact hasSum_i2_case6aa_regionTerm q t d U V T hq hd h.t2
  · exact hasSum_i2_case6aaa_regionTerm q t d U V T hq hd h.t2 h.g
  · exact hasSum_i2_case6b_regionTerm q t d U V T hq hd h.t2
  · exact hasSum_i2_case6bb_regionTerm q t d U V T hq hd h.t2
  · exact hasSum_i2_case6bbb_regionTerm q t d U V T hq hd h.t2 h.g
  · exact hasSum_i2_case6c_regionTerm q t d U V T hq hd h.t2 h.n
  · exact hasSum_i2_case6cc_regionTerm q t d U V T hq hd h.t2 h.n
  · exact hasSum_i2_case6ccc_regionTerm q t d U V T hq hd h.t2 h.n h.g
  · exact hasSum_i2_case7_regionTerm q t d U V T hq hd h.t2 h.n h.g
  · exact hasSum_i2_case8a_regionTerm q t d U V T hq hd h.t2 h.n h.e
  · exact hasSum_i2_case8b_regionTerm q t d U V T hq hd h.t2 h.n h.e
  · exact hasSum_i2_case8c_regionTerm q t d U V T hq hd h.t2 h.n h.e
  · exact hasSum_i2_case8d_regionTerm q t d U V T hq hd h.t2 h.n h.e
  · exact hasSum_i2_case9_regionTerm q t d U V T hq hd h.t2 h.n h.e h.f
  · exact hasSum_i2_case10_regionTerm q t d U V T hq hd h.t2 h.n h.f h.g

theorem summable_norm_i2_spatial (q t d U V T : ℂ) (ν : Fin 25)
    (h : GeometricRange t d U V T) :
    Summable (fun p : I2SpatialRow ν => ‖i2SpatialTerm q t d U V T ν p.val‖) := by
  fin_cases ν
  · exact summable_norm_i2_case1a q t d U V T h.t2 h.p
  · exact summable_norm_i2_case1b q t d U V T h.t2
  · exact summable_norm_i2_case2 q t d U V T h.t2 h.p h.g
  · exact summable_norm_i2_case3a q t d U V T h.t2 h.p h.e
  · exact summable_norm_i2_case3b q t d U V T h.p h.e
  · exact summable_norm_i2_case3c q t d U V T h.p h.e
  · exact summable_norm_i2_case3d q t d U V T h.p h.e
  · exact summable_norm_i2_case4 q t d U V T h.p h.e h.f
  · exact summable_norm_i2_case5 q t d U V T h.p h.f h.g
  · exact summable_norm_i2_case6a q t d U V T h.t2
  · exact summable_norm_i2_case6aa q t d U V T h.t2
  · exact summable_norm_i2_case6aaa q t d U V T h.t2 h.g
  · exact summable_norm_i2_case6b q t d U V T h.t2
  · exact summable_norm_i2_case6bb q t d U V T h.t2
  · exact summable_norm_i2_case6bbb q t d U V T h.g
  · exact summable_norm_i2_case6c q t d U V T h.t2 h.n
  · exact summable_norm_i2_case6cc q t d U V T h.t2 h.n
  · exact summable_norm_i2_case6ccc q t d U V T h.n h.g
  · exact summable_norm_i2_case7 q t d U V T h.t2 h.n h.g
  · exact summable_norm_i2_case8a q t d U V T h.t2 h.n h.e
  · exact summable_norm_i2_case8b q t d U V T h.n h.e
  · exact summable_norm_i2_case8c q t d U V T h.n h.e
  · exact summable_norm_i2_case8d q t d U V T h.n h.e
  · exact summable_norm_i2_case9 q t d U V T h.n h.e h.f
  · exact summable_norm_i2_case10 q t d U V T h.n h.f h.g

def i2DepthWeight (q : ℂ) (ν : Fin 25) (p : I2SpatialRow ν) (c : ℕ) : ℂ := by
  classical
  exact if i2DepthPredicate ν c then collisionWeight q 2 p.val.2.1 p.val.2.2 c else 0

theorem hasSum_i2_probability_ge_two (q : ℂ) (hq : ‖q⁻¹‖ < 1) :
    HasSum (fun c : ℕ => if 2 ≤ c then collisionProbability q c else 0)
      (q⁻¹ ^ 2 / (1 - q⁻¹)) := by
  apply (hasSum_nat_add_iff' 2).mp
  simpa [Finset.sum_range_succ, div_eq_mul_inv, Nat.add_assoc]
    using hasSum_collisionProbability_tail q 1 hq

theorem hasSum_i2_depthWeight (q : ℂ) (ν : Fin 25) (p : I2SpatialRow ν)
    (hq₀ : q ≠ 0) (hq₁ : q - 1 ≠ 0) (hq : ‖q⁻¹‖ < 1) :
    HasSum (i2DepthWeight q ν p) (i2DepthMass q ν) := by
  classical
  fin_cases ν
  · change HasSum (fun c : ℕ => i2DepthWeight q 0 p c) (i2DepthMass q 0)
    simpa only [i2DepthWeight, i2DepthPredicate_row0, if_true, i2DepthMass_row0]
      using hasSum_collisionWeight q 2 p.val.2.1 p.val.2.2 hq₀ hq₁ hq
  · change HasSum (fun c : ℕ => i2DepthWeight q 1 p c) (i2DepthMass q 1)
    simpa only [i2DepthWeight, i2DepthPredicate_row1, if_true, i2DepthMass_row1]
      using hasSum_collisionWeight q 2 p.val.2.1 p.val.2.2 hq₀ hq₁ hq
  · change HasSum (fun c : ℕ => i2DepthWeight q 2 p c) (i2DepthMass q 2)
    simpa only [i2DepthWeight, i2DepthPredicate_row2, if_true, i2DepthMass_row2]
      using hasSum_collisionWeight q 2 p.val.2.1 p.val.2.2 hq₀ hq₁ hq
  · change HasSum (fun c : ℕ => i2DepthWeight q 3 p c) (i2DepthMass q 3)
    simpa only [i2DepthWeight, i2DepthPredicate_row3, if_true, i2DepthMass_row3]
      using hasSum_collisionWeight q 2 p.val.2.1 p.val.2.2 hq₀ hq₁ hq
  · change HasSum (fun c : ℕ => i2DepthWeight q 4 p c) (i2DepthMass q 4)
    have hp := p.property
    change i2SpatialPredicate 4 p.val at hp
    simp only [i2SpatialPredicate_row4] at hp
    have he : 2 * p.val.2.2 = p.val.2.1 - 2 := by omega
    have hw (c : ℕ) : collisionWeight q 2 p.val.2.1 p.val.2.2 c = collisionProbability q c := by
      simp [collisionWeight, he]
    simp only [i2DepthWeight, i2DepthPredicate_row4, hw, i2DepthMass_row4]
    convert hasSum_ite_eq (α := ℂ) (β := ℕ) 0 ((q - 2) / (q - 1)) using 1
    funext c
    split_ifs with hc
    · subst c
      simp [collisionProbability]
    · rfl
  · change HasSum (fun c : ℕ => i2DepthWeight q 5 p c) (i2DepthMass q 5)
    have hp := p.property
    change i2SpatialPredicate 5 p.val at hp
    simp only [i2SpatialPredicate_row5] at hp
    have he : 2 * p.val.2.2 = p.val.2.1 - 2 := by omega
    have hw (c : ℕ) : collisionWeight q 2 p.val.2.1 p.val.2.2 c = collisionProbability q c := by
      simp [collisionWeight, he]
    simp only [i2DepthWeight, i2DepthPredicate_row5, hw, i2DepthMass_row5]
    convert hasSum_ite_eq (α := ℂ) (β := ℕ) 1 (q⁻¹) using 1
    funext c
    split_ifs with hc
    · subst c
      simp [collisionProbability]
    · rfl
  · change HasSum (fun c : ℕ => i2DepthWeight q 6 p c) (i2DepthMass q 6)
    have hp := p.property
    change i2SpatialPredicate 6 p.val at hp
    simp only [i2SpatialPredicate_row6] at hp
    have he : 2 * p.val.2.2 = p.val.2.1 - 2 := by omega
    have hw (c : ℕ) : collisionWeight q 2 p.val.2.1 p.val.2.2 c = collisionProbability q c := by
      simp [collisionWeight, he]
    simp only [i2DepthWeight, i2DepthPredicate_row6, hw, i2DepthMass_row6]
    exact hasSum_i2_probability_ge_two q hq
  · change HasSum (fun c : ℕ => i2DepthWeight q 7 p c) (i2DepthMass q 7)
    simpa only [i2DepthWeight, i2DepthPredicate_row7, if_true, i2DepthMass_row7]
      using hasSum_collisionWeight q 2 p.val.2.1 p.val.2.2 hq₀ hq₁ hq
  · change HasSum (fun c : ℕ => i2DepthWeight q 8 p c) (i2DepthMass q 8)
    simpa only [i2DepthWeight, i2DepthPredicate_row8, if_true, i2DepthMass_row8]
      using hasSum_collisionWeight q 2 p.val.2.1 p.val.2.2 hq₀ hq₁ hq
  · change HasSum (fun c : ℕ => i2DepthWeight q 9 p c) (i2DepthMass q 9)
    simpa only [i2DepthWeight, i2DepthPredicate_row9, if_true, i2DepthMass_row9]
      using hasSum_collisionWeight q 2 p.val.2.1 p.val.2.2 hq₀ hq₁ hq
  · change HasSum (fun c : ℕ => i2DepthWeight q 10 p c) (i2DepthMass q 10)
    simpa only [i2DepthWeight, i2DepthPredicate_row10, if_true, i2DepthMass_row10]
      using hasSum_collisionWeight q 2 p.val.2.1 p.val.2.2 hq₀ hq₁ hq
  · change HasSum (fun c : ℕ => i2DepthWeight q 11 p c) (i2DepthMass q 11)
    simpa only [i2DepthWeight, i2DepthPredicate_row11, if_true, i2DepthMass_row11]
      using hasSum_collisionWeight q 2 p.val.2.1 p.val.2.2 hq₀ hq₁ hq
  · change HasSum (fun c : ℕ => i2DepthWeight q 12 p c) (i2DepthMass q 12)
    simpa only [i2DepthWeight, i2DepthPredicate_row12, if_true, i2DepthMass_row12]
      using hasSum_collisionWeight q 2 p.val.2.1 p.val.2.2 hq₀ hq₁ hq
  · change HasSum (fun c : ℕ => i2DepthWeight q 13 p c) (i2DepthMass q 13)
    simpa only [i2DepthWeight, i2DepthPredicate_row13, if_true, i2DepthMass_row13]
      using hasSum_collisionWeight q 2 p.val.2.1 p.val.2.2 hq₀ hq₁ hq
  · change HasSum (fun c : ℕ => i2DepthWeight q 14 p c) (i2DepthMass q 14)
    simpa only [i2DepthWeight, i2DepthPredicate_row14, if_true, i2DepthMass_row14]
      using hasSum_collisionWeight q 2 p.val.2.1 p.val.2.2 hq₀ hq₁ hq
  · change HasSum (fun c : ℕ => i2DepthWeight q 15 p c) (i2DepthMass q 15)
    simpa only [i2DepthWeight, i2DepthPredicate_row15, if_true, i2DepthMass_row15]
      using hasSum_collisionWeight q 2 p.val.2.1 p.val.2.2 hq₀ hq₁ hq
  · change HasSum (fun c : ℕ => i2DepthWeight q 16 p c) (i2DepthMass q 16)
    simpa only [i2DepthWeight, i2DepthPredicate_row16, if_true, i2DepthMass_row16]
      using hasSum_collisionWeight q 2 p.val.2.1 p.val.2.2 hq₀ hq₁ hq
  · change HasSum (fun c : ℕ => i2DepthWeight q 17 p c) (i2DepthMass q 17)
    simpa only [i2DepthWeight, i2DepthPredicate_row17, if_true, i2DepthMass_row17]
      using hasSum_collisionWeight q 2 p.val.2.1 p.val.2.2 hq₀ hq₁ hq
  · change HasSum (fun c : ℕ => i2DepthWeight q 18 p c) (i2DepthMass q 18)
    simpa only [i2DepthWeight, i2DepthPredicate_row18, if_true, i2DepthMass_row18]
      using hasSum_collisionWeight q 2 p.val.2.1 p.val.2.2 hq₀ hq₁ hq
  · change HasSum (fun c : ℕ => i2DepthWeight q 19 p c) (i2DepthMass q 19)
    simpa only [i2DepthWeight, i2DepthPredicate_row19, if_true, i2DepthMass_row19]
      using hasSum_collisionWeight q 2 p.val.2.1 p.val.2.2 hq₀ hq₁ hq
  · change HasSum (fun c : ℕ => i2DepthWeight q 20 p c) (i2DepthMass q 20)
    have hp := p.property
    change i2SpatialPredicate 20 p.val at hp
    simp only [i2SpatialPredicate_row20] at hp
    have he : 2 * p.val.2.2 = p.val.2.1 - 2 := by omega
    have hw (c : ℕ) : collisionWeight q 2 p.val.2.1 p.val.2.2 c = collisionProbability q c := by
      simp [collisionWeight, he]
    simp only [i2DepthWeight, i2DepthPredicate_row20, hw, i2DepthMass_row20]
    convert hasSum_ite_eq (α := ℂ) (β := ℕ) 0 ((q - 2) / (q - 1)) using 1
    funext c
    split_ifs with hc
    · subst c
      simp [collisionProbability]
    · rfl
  · change HasSum (fun c : ℕ => i2DepthWeight q 21 p c) (i2DepthMass q 21)
    have hp := p.property
    change i2SpatialPredicate 21 p.val at hp
    simp only [i2SpatialPredicate_row21] at hp
    have he : 2 * p.val.2.2 = p.val.2.1 - 2 := by omega
    have hw (c : ℕ) : collisionWeight q 2 p.val.2.1 p.val.2.2 c = collisionProbability q c := by
      simp [collisionWeight, he]
    simp only [i2DepthWeight, i2DepthPredicate_row21, hw, i2DepthMass_row21]
    convert hasSum_ite_eq (α := ℂ) (β := ℕ) 1 (q⁻¹) using 1
    funext c
    split_ifs with hc
    · subst c
      simp [collisionProbability]
    · rfl
  · change HasSum (fun c : ℕ => i2DepthWeight q 22 p c) (i2DepthMass q 22)
    have hp := p.property
    change i2SpatialPredicate 22 p.val at hp
    simp only [i2SpatialPredicate_row22] at hp
    have he : 2 * p.val.2.2 = p.val.2.1 - 2 := by omega
    have hw (c : ℕ) : collisionWeight q 2 p.val.2.1 p.val.2.2 c = collisionProbability q c := by
      simp [collisionWeight, he]
    simp only [i2DepthWeight, i2DepthPredicate_row22, hw, i2DepthMass_row22]
    exact hasSum_i2_probability_ge_two q hq
  · change HasSum (fun c : ℕ => i2DepthWeight q 23 p c) (i2DepthMass q 23)
    simpa only [i2DepthWeight, i2DepthPredicate_row23, if_true, i2DepthMass_row23]
      using hasSum_collisionWeight q 2 p.val.2.1 p.val.2.2 hq₀ hq₁ hq
  · change HasSum (fun c : ℕ => i2DepthWeight q 24 p c) (i2DepthMass q 24)
    simpa only [i2DepthWeight, i2DepthPredicate_row24, if_true, i2DepthMass_row24]
      using hasSum_collisionWeight q 2 p.val.2.1 p.val.2.2 hq₀ hq₁ hq

def i2BareTerm (q t d U V T : ℂ) (ν : Fin 25) (p : I2SpatialRow ν) : ℂ :=
  -q * shellMonomial t d U V T 2 p.val (i2DepthAt ν)

theorem i2DepthMass_ne (q : ℂ) (ν : Fin 25)
    (hq₀ : q ≠ 0) (hq₁ : q - 1 ≠ 0) (hq₂ : q - 2 ≠ 0) (hq : ‖q⁻¹‖ < 1) :
    i2DepthMass q ν ≠ 0 := by
  unfold i2DepthMass
  split_ifs
  · exact div_ne_zero hq₂ hq₁
  · exact inv_ne_zero hq₀
  · exact div_ne_zero (pow_ne_zero 2 (inv_ne_zero hq₀)) (i2_geometric_denominator_ne _ hq)
  · exact one_ne_zero

theorem summable_norm_i2_bare (q t d U V T : ℂ) (ν : Fin 25)
    (hq₀ : q ≠ 0) (hq₁ : q - 1 ≠ 0) (hq₂ : q - 2 ≠ 0) (hq : ‖q⁻¹‖ < 1)
    (h : GeometricRange t d U V T) :
    Summable (fun p : I2SpatialRow ν => ‖i2BareTerm q t d U V T ν p‖) := by
  have hm := i2DepthMass_ne q ν hq₀ hq₁ hq₂ hq
  have hs := (summable_norm_i2_spatial q t d U V T ν h).mul_right ‖(i2DepthMass q ν)⁻¹‖
  have he (p : I2SpatialRow ν) : i2BareTerm q t d U V T ν p =
      i2SpatialTerm q t d U V T ν p.val * (i2DepthMass q ν)⁻¹ := by
    unfold i2BareTerm i2SpatialTerm
    rw [mul_assoc, mul_inv_cancel₀ hm, mul_one]
  simpa only [he, norm_mul] using hs

def i2RowFamily (q t d U V T : ℂ) (ν : Fin 25) (p : I2SpatialRow ν × ℕ) : ℂ := by
  classical
  exact if i2DepthPredicate ν p.2 then
    masterTerm q t d U V T 2 (p.1.val.1, p.1.val.2.1, p.1.val.2.2, p.2) else 0

theorem i2RowFamily_eq (q t d U V T : ℂ) (ν : Fin 25) (p : I2SpatialRow ν × ℕ) :
    i2RowFamily q t d U V T ν p = i2BareTerm q t d U V T ν p.1 * i2DepthWeight q ν p.1 p.2 := by
  classical
  unfold i2RowFamily i2DepthWeight
  split_ifs with hc
  · unfold masterTerm shellCoeff i2BareTerm
    simp only [show (2 : ℤ) ≠ 0 by decide, show (2 : ℤ) ≠ 1 by decide, if_false]
    congr 2
    unfold shellMonomial
    rw [i2_cartan_depth_constant ν p.1 p.2 hc]
  · simp

theorem summable_norm_i2_rowFamily (q t d U V T : ℂ) (ν : Fin 25)
    (hq₀ : q ≠ 0) (hq₁ : q - 1 ≠ 0) (hq₂ : q - 2 ≠ 0) (hq : ‖q⁻¹‖ < 1)
    (h : GeometricRange t d U V T) :
    Summable (fun p : I2SpatialRow ν × ℕ => ‖i2RowFamily q t d U V T ν p‖) := by
  classical
  have hb := summable_norm_i2_bare q t d U V T ν hq₀ hq₁ hq₂ hq h
  have hs := summable_norm_weighted_collision q 2 (fun p : I2SpatialRow ν => p.val.2.1)
    (fun p : I2SpatialRow ν => p.val.2.2) (i2BareTerm q t d U V T ν) hq hb
  apply hs.of_nonneg_of_le (fun p => norm_nonneg _)
  intro p
  rw [i2RowFamily_eq]
  unfold i2DepthWeight
  split_ifs <;> simp <;> positivity

theorem hasSum_i2_rowFamily (q t d U V T : ℂ) (ν : Fin 25)
    (hq₀ : q ≠ 0) (hq₁ : q - 1 ≠ 0) (hq₂ : q - 2 ≠ 0) (hq : ‖q⁻¹‖ < 1)
    (hqt : q * t ^ 2 = 1) (hd : d ≠ 0) (h : GeometricRange t d U V T) :
    HasSum (i2RowFamily q t d U V T ν) (i2RegionTerm ν t d (T * U) (T * V)) := by
  have hs := (summable_norm_i2_rowFamily q t d U V T ν hq₀ hq₁ hq₂ hq h).of_norm
  have hdpth (p : I2SpatialRow ν) :=
    (hasSum_i2_depthWeight q ν p hq₀ hq₁ hq).mul_left (i2BareTerm q t d U V T ν p)
  have he : (∑' p : I2SpatialRow ν × ℕ, i2RowFamily q t d U V T ν p) =
      i2RegionTerm ν t d (T * U) (T * V) := by
    rw [hs.tsum_prod]
    simp only [i2RowFamily_eq, (hdpth _).tsum_eq]
    exact (hasSum_i2_spatial q t d U V T ν hqt hd h).tsum_eq
  exact he ▸ hs.hasSum

end FourierJacobi.Analysis
