import FourierJacobi.Analysis.CoreParameters

/-!
# The literal paper quotient on its natural parameter domain

The four-factor products are independently matched, with multiplicities, to
the algebraic expressions. Their nonvanishing below is proved from unitary
Satake parameters and the stated interior or signed-endpoint conditions.
No Weyl-wall exclusions are needed for these denominator statements.
-/

noncomputable section

namespace FourierJacobi.Analysis

open FourierJacobi.Algebra

theorem paperD1_eq_d₁ (q : ℝ) (a b d : ℂ) :
    paperD1 q a b d = d₁ (inverseSqrt q : ℂ) a b d := by
  simp only [paperD1, satakeTuple, d₁, fourFactors,
    Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, mul_one]
  ring

theorem paperD2_eq_d₂ (q : ℝ) (a b d : ℂ) :
    paperD2 q a b d = d₂ (inverseSqrt q : ℂ) a b d := by
  simp only [paperD2, satakeTuple, d₂, fourFactors,
    Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, mul_one, div_eq_mul_inv]
  ring

theorem paperC_ne_zero (q : ℝ) (hq : 1 < q) : paperC q ≠ 0 := by
  rw [paperC_eq_poincare q (by linarith)]
  exact poincare_coe_ne_zero _

theorem paperD1_ne_zero_of_norm_le_one (q : ℝ) (hq : 1 < q)
    (a b d : ℂ) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hd : ‖d‖ ≤ 1) :
    paperD1 q a b d ≠ 0 := by
  rw [paperD1_eq_d₁]
  apply fourFactors_ne_zero ha hb
  have ht₀ := inverseSqrt_pos hq
  have ht₁ := inverseSqrt_lt_one hq
  have htn : ‖(inverseSqrt q : ℂ)‖ = inverseSqrt q := by
    simp [abs_of_pos ht₀]
  rw [norm_mul, htn]
  nlinarith

theorem paperD2_ne_zero_interior (q : ℝ) (hq : 1 < q)
    (a b d : ℂ) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hd : inverseSqrt q < ‖d‖) : paperD2 q a b d ≠ 0 := by
  rw [paperD2_eq_d₂]
  apply fourFactors_ne_zero ha hb
  have ht₀ := inverseSqrt_pos hq
  have hd₀ : 0 < ‖d‖ := lt_trans ht₀ hd
  have htn : ‖(inverseSqrt q : ℂ)‖ = inverseSqrt q := by
    simp [abs_of_pos ht₀]
  rw [norm_div, htn]
  exact (div_lt_one hd₀).mpr hd

/-- In the open interior, the actual denominator is nonzero even on Weyl walls. -/
theorem paper_denominator_interior_ne_zero (q : ℝ) (hq : 1 < q)
    (a b d : ℂ) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hdlo : inverseSqrt q < ‖d‖) (hdhi : ‖d‖ ≤ 1) :
    paperC q * paperD1 q a b d * paperD2 q a b d ≠ 0 :=
  mul_ne_zero
    (mul_ne_zero (paperC_ne_zero q hq)
      (paperD1_ne_zero_of_norm_le_one q hq a b d ha hb hdhi))
    (paperD2_ne_zero_interior q hq a b d ha hb hdlo)

theorem fourFactors_one_ne_zero (a b : ℂ) (ha : a ≠ 1) (hb : b ≠ 1) :
    fourFactors a b 1 ≠ 0 := by
  have hai : a⁻¹ ≠ 1 := by simpa using ha
  have hbi : b⁻¹ ≠ 1 := by simpa using hb
  simp only [fourFactors, mul_one]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero
    (sub_ne_zero.mpr ha.symm) (sub_ne_zero.mpr hai.symm))
    (sub_ne_zero.mpr hb.symm)) (sub_ne_zero.mpr hbi.symm)

theorem paperD2_special_positive (q : ℝ) (hq : 1 < q) (a b : ℂ) :
    paperD2 q a b (inverseSqrt q : ℂ) = fourFactors a b 1 := by
  rw [paperD2_eq_d₂, d₂]
  have htne : (inverseSqrt q : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (inverseSqrt_pos hq)
  rw [div_self htne]

theorem paperD2_special_negative (q : ℝ) (hq : 1 < q) (a b : ℂ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    paperD2 q a b (-(inverseSqrt q : ℂ)) = satakeNumerator a b := by
  rw [paperD2_eq_d₂]
  have htne : (inverseSqrt q : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (inverseSqrt_pos hq)
  exact special_negative_d₂ _ _ _ htne (unit_ne_zero ha) (unit_ne_zero hb)

theorem paper_denominator_special_positive_ne_zero (q : ℝ) (hq : 1 < q)
    (a b : ℂ) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (ha₁ : a ≠ 1) (hb₁ : b ≠ 1) :
    paperC q * paperD1 q a b (inverseSqrt q : ℂ) *
      paperD2 q a b (inverseSqrt q : ℂ) ≠ 0 := by
  have htn : ‖(inverseSqrt q : ℂ)‖ ≤ 1 :=
    (coe_norm_lt_one (inverseSqrt_pos hq).le (inverseSqrt_lt_one hq)).le
  apply mul_ne_zero
    (mul_ne_zero (paperC_ne_zero q hq)
      (paperD1_ne_zero_of_norm_le_one q hq a b _ ha hb htn))
  rw [paperD2_special_positive q hq]
  exact fourFactors_one_ne_zero a b ha₁ hb₁

theorem paper_denominator_special_negative_ne_zero (q : ℝ) (hq : 1 < q)
    (a b : ℂ) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (ha₁ : a ≠ -1) (hb₁ : b ≠ -1) :
    paperC q * paperD1 q a b (-(inverseSqrt q : ℂ)) *
      paperD2 q a b (-(inverseSqrt q : ℂ)) ≠ 0 := by
  have htn : ‖-(inverseSqrt q : ℂ)‖ ≤ 1 := by
    simpa only [norm_neg] using
      (coe_norm_lt_one (inverseSqrt_pos hq).le (inverseSqrt_lt_one hq)).le
  apply mul_ne_zero
    (mul_ne_zero (paperC_ne_zero q hq)
      (paperD1_ne_zero_of_norm_le_one q hq a b _ ha hb htn))
  rw [paperD2_special_negative q hq a b ha hb]
  apply satakeNumerator_unitary_ne_zero ha hb
  · intro he
    apply ha₁
    linear_combination he
  · intro he
    apply hb₁
    linear_combination he

/-- Both literal special denominators are justified from precisely the endpoint
exclusions a,b ≠ ε, where ε is a sign. This asserts no endpoint series convergence. -/
theorem paper_denominator_special_ne_zero (q : ℝ) (hq : 1 < q)
    (a b ε : ℂ) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hε : ε = 1 ∨ ε = -1) (haε : a ≠ ε) (hbε : b ≠ ε) :
    paperC q * paperD1 q a b (ε * (inverseSqrt q : ℂ)) *
      paperD2 q a b (ε * (inverseSqrt q : ℂ)) ≠ 0 := by
  rcases hε with rfl | rfl
  · simpa only [one_mul] using
      paper_denominator_special_positive_ne_zero q hq a b ha hb haε hbε
  · simpa only [neg_one_mul] using
      paper_denominator_special_negative_ne_zero q hq a b ha hb haε hbε

end FourierJacobi.Analysis
