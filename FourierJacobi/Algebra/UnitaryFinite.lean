import FourierJacobi.Algebra.FiniteCalculation
import FourierJacobi.Algebra.UnitaryParameters

/-!
# The finite principal formula for unitary parameters

All auxiliary nonvanishing conditions are derived from norm-one parameters,
0 < t < 1, and the four explicitly excluded Weyl walls. The input is still
the finite algebraic expression, rather than the Fourier--Jacobi period.
-/

namespace FourierJacobi
namespace Algebra

/-- The squared expression in the paper is independent of the chosen square root. -/
theorem square_root_satake {K : Type*} [Field K] (a z : K)
    (ha : a ≠ 0) (hz : z ^ 2 = a) :
    (z⁻¹ + z) ^ 2 = a + 2 + a⁻¹ := by
  have hz₀ : z ≠ 0 := by
    intro he
    apply ha
    rw [← hz, he]
    simp
  rw [← hz]
  field_simp
  ring

theorem coe_pow_norm_lt_one {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t < 1)
    {n : ℕ} (hn : n ≠ 0) : ‖(t : ℂ) ^ n‖ < 1 := by
  rw [norm_pow]
  exact pow_lt_one₀ (norm_nonneg _) (coe_norm_lt_one ht₀ ht₁) hn

theorem poincare_coe_ne_zero (t : ℝ) : poincare (t : ℂ) ≠ 0 := by
  have hp : 0 < poincare t := by unfold poincare; positivity
  have hc : poincare (t : ℂ) = ((poincare t : ℝ) : ℂ) := by
    simp [poincare]
  rw [hc]
  exact_mod_cast ne_of_gt hp

theorem n₂_unitary_ne_zero {t : ℝ} {a b : ℂ}
    (ht₀ : 0 ≤ t) (ht₁ : t < 1) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    n₂ (t : ℂ) a b ≠ 0 := by
  have hx := coe_pow_norm_lt_one ht₀ ht₁ (by decide : (2 : ℕ) ≠ 0)
  have hab : ‖a * b‖ = 1 := by simp [ha, hb]
  have hab' : ‖a / b‖ = 1 := by simp [ha, hb]
  have hba : ‖b / a‖ = 1 := by simp [ha, hb]
  have hi : ‖(a * b)⁻¹‖ = 1 := by simp [ha, hb]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero
    (by simpa [mul_assoc] using one_sub_mul_ne_zero_of_norm_lt_one hab hx)
    (one_sub_mul_ne_zero_of_norm_lt_one hab' hx))
    (one_sub_mul_ne_zero_of_norm_lt_one hba hx))
    (one_sub_mul_ne_zero_of_norm_lt_one hi hx)

theorem weylU_unitary {a b : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (i : Fin 8) :
    ‖weylU a b i‖ = 1 := by
  fin_cases i <;> simp [weylU, ha, hb]

theorem weylV_unitary {a b : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (i : Fin 8) :
    ‖weylV a b i‖ = 1 := by
  fin_cases i <;> simp [weylV, ha, hb]

theorem regionRegular_unitary {t : ℝ} {d U V : ℂ}
    (ht₀ : 0 ≤ t) (ht₁ : t < 1) (hd : ‖d‖ = 1)
    (hU : ‖U‖ = 1) (hV : ‖V‖ = 1) : RegionRegular (t : ℂ) d U V := by
  have hx := coe_norm_lt_one ht₀ ht₁
  have hx₂ := coe_pow_norm_lt_one ht₀ ht₁ (by decide : (2 : ℕ) ≠ 0)
  have hx₄ := coe_pow_norm_lt_one ht₀ ht₁ (by decide : (4 : ℕ) ≠ 0)
  have hdV : ‖d * V‖ = 1 := by simp [hd, hV]
  have hVd : ‖V / d‖ = 1 := by simp [hd, hV]
  have hV₂ : ‖V ^ 2‖ = 1 := by simp [hV]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact one_sub_mul_ne_zero_of_norm_lt_one hdV hx
  · simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      one_sub_mul_ne_zero_of_norm_lt_one hVd hx
  · exact one_sub_mul_ne_zero_of_norm_lt_one hV₂ hx₂
  · exact one_sub_mul_ne_zero_of_norm_lt_one hU hx₂
  · exact one_sub_mul_ne_zero_of_norm_lt_one hU hx₄

theorem finiteRegular_unitary {t : ℝ} {a b d : ℂ}
    (ht₀ : 0 ≤ t) (ht₁ : t < 1) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hd : ‖d‖ = 1)
    (ha₁ : a - 1 ≠ 0) (hb₁ : b - 1 ≠ 0) (hab : a - b ≠ 0)
    (hab₁ : a * b - 1 ≠ 0) : FiniteRegular (t : ℂ) a b d := by
  have ha₀ := unit_ne_zero ha
  have hb₀ := unit_ne_zero hb
  have hd₀ := unit_ne_zero hd
  have hx := coe_norm_lt_one ht₀ ht₁
  have hdt : ‖d * (t : ℂ)‖ < 1 := by simpa [norm_mul, hd] using hx
  have htd : ‖(t : ℂ) / d‖ < 1 := by simpa [norm_div, hd] using hx
  have hD₁ : d₁ (t : ℂ) a b d ≠ 0 := fourFactors_ne_zero ha hb hdt
  have hD₂ : d₂ (t : ℂ) a b d ≠ 0 := fourFactors_ne_zero ha hb htd
  have hWall : weylWall a b ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero ha₁ hab) hb₁) hab₁
  refine ⟨ha₀, hb₀, hd₀, ha₁, hb₁, hab, hab₁, ?_, ?_⟩
  · rw [weyl_common_euler_factorization (t : ℂ) a b d ha₀ hb₀ hd₀]
    exact mul_ne_zero
      (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hWall
        (pow_ne_zero 2 ha₀)) (pow_ne_zero 2 hb₀)) hd₀)
        (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 ha₀) (pow_ne_zero 2 hb₀))
          (pow_ne_zero 4 hd₀)))
      (mul_ne_zero hD₁ hD₂)
  · intro i
    exact regionRegular_unitary ht₀ ht₁ hd (weylU_unitary ha hb i) (weylV_unitary ha hb i)

/-- The finite principal formula, with no auxiliary denominator assumptions. -/
theorem finite_principal_unitary (q t : ℝ) (a b d : ℂ)
    (ht₀ : 0 ≤ t) (ht₁ : t < 1) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hd : ‖d‖ = 1)
    (ha₁ : a - 1 ≠ 0) (hb₁ : b - 1 ≠ 0) (hab : a - b ≠ 0)
    (hab₁ : a * b - 1 ≠ 0) :
    (2 / ((q : ℂ) + 1) * finiteCore (t : ℂ) a b d) *
      principalNormalizer (t : ℂ) a b d =
      2 / ((q : ℂ) + 1) * (a + 2 + a⁻¹) * (b + 2 + b⁻¹) /
        ((1 + d * (t : ℂ)) * (1 + (t : ℂ) / d)) := by
  have hx := coe_norm_lt_one ht₀ ht₁
  have hx₂ := coe_pow_norm_lt_one ht₀ ht₁ (by decide : (2 : ℕ) ≠ 0)
  have hdi : ‖d⁻¹‖ = 1 := by simp [hd]
  have hdt : ‖d * (t : ℂ)‖ < 1 := by simpa [norm_mul, hd] using hx
  have htd : ‖(t : ℂ) / d‖ < 1 := by simpa [norm_div, hd] using hx
  apply finite_sum_principal_formula (q : ℂ) (t : ℂ) a b d
    (finiteRegular_unitary ht₀ ht₁ ha hb hd ha₁ hb₁ hab hab₁)
    (poincare_coe_ne_zero t) (fourFactors_ne_zero ha hb hx₂)
    (n₂_unitary_ne_zero ht₀ ht₁ ha hb)
    (fourFactors_ne_zero ha hb hdt) (fourFactors_ne_zero ha hb htd)
  · simpa using one_sub_mul_ne_zero_of_norm_lt_one (norm_one : ‖(1 : ℂ)‖ = 1) hx₂
  · exact one_sub_mul_ne_zero_of_norm_lt_one hd hx
  · exact one_add_mul_ne_zero_of_norm_lt_one hd hx
  · simpa [div_eq_mul_inv, mul_comm] using one_sub_mul_ne_zero_of_norm_lt_one hdi hx
  · simpa [div_eq_mul_inv, mul_comm] using one_add_mul_ne_zero_of_norm_lt_one hdi hx

/-- Substitute the positive square-root branch required by the paper. -/
theorem finite_principal_inverseSqrt (q : ℝ) (hq : 1 < q) (a b d : ℂ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hd : ‖d‖ = 1)
    (ha₁ : a - 1 ≠ 0) (hb₁ : b - 1 ≠ 0) (hab : a - b ≠ 0)
    (hab₁ : a * b - 1 ≠ 0) :
    (2 / ((q : ℂ) + 1) * finiteCore (inverseSqrt q : ℂ) a b d) *
      principalNormalizer (inverseSqrt q : ℂ) a b d =
      2 / ((q : ℂ) + 1) * (a + 2 + a⁻¹) * (b + 2 + b⁻¹) /
        ((1 + d * (inverseSqrt q : ℂ)) * (1 + (inverseSqrt q : ℂ) / d)) :=
  finite_principal_unitary q (inverseSqrt q) a b d
    (le_of_lt (inverseSqrt_pos hq)) (inverseSqrt_lt_one hq) ha hb hd ha₁ hb₁ hab hab₁

/-- The paper's square-root notation, for the finite input on the regular locus. -/
theorem finite_principal_square_roots (q : ℝ) (hq : 1 < q) (a b d A B : ℂ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hd : ‖d‖ = 1)
    (hA : A ^ 2 = a) (hB : B ^ 2 = b)
    (ha₁ : a - 1 ≠ 0) (hb₁ : b - 1 ≠ 0) (hab : a - b ≠ 0)
    (hab₁ : a * b - 1 ≠ 0) :
    (2 / ((q : ℂ) + 1) * finiteCore (inverseSqrt q : ℂ) a b d) *
      principalNormalizer (inverseSqrt q : ℂ) a b d =
      2 / ((q : ℂ) + 1) * (A⁻¹ + A) ^ 2 * (B⁻¹ + B) ^ 2 /
        ((1 + d * (inverseSqrt q : ℂ)) * (1 + (inverseSqrt q : ℂ) / d)) := by
  rw [square_root_satake a A (unit_ne_zero ha) hA,
    square_root_satake b B (unit_ne_zero hb) hB]
  exact finite_principal_inverseSqrt q hq a b d ha hb hd ha₁ hb₁ hab hab₁

theorem one_add_inv_ne_zero {z : ℂ} (hz : z ≠ 0) (h : 1 + z ≠ 0) :
    1 + z⁻¹ ≠ 0 := by
  intro he
  have he' := congrArg (fun x : ℂ => x * z) he
  apply h
  simpa [add_mul, hz, add_comm] using he'

theorem weylV_one_add_ne_zero {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hA : 1 + a ≠ 0) (hB : 1 + b ≠ 0) (i : Fin 8) :
    1 + weylV a b i ≠ 0 := by
  have hAi := one_add_inv_ne_zero ha hA
  have hBi := one_add_inv_ne_zero hb hB
  fin_cases i
  · simpa [weylV] using hA
  · simpa [weylV] using hB
  · simpa [weylV] using hA
  · simpa [weylV] using hBi
  · simpa [weylV] using hB
  · simpa [weylV] using hAi
  · simpa [weylV] using hBi
  · simpa [weylV] using hAi

theorem satakeNumerator_unitary_ne_zero {a b : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hA : 1 + a ≠ 0) (hB : 1 + b ≠ 0) : satakeNumerator a b ≠ 0 :=
  div_ne_zero (mul_ne_zero (pow_ne_zero 2 hA) (pow_ne_zero 2 hB))
    (mul_ne_zero (unit_ne_zero ha) (unit_ne_zero hb))

theorem regionRegular_special_negative {t : ℝ} {U V : ℂ}
    (ht₀ : 0 < t) (ht₁ : t < 1) (hU : ‖U‖ = 1) (hV : ‖V‖ = 1)
    (hV₁ : 1 + V ≠ 0) : RegionRegular (t : ℂ) (-(t : ℂ)) U V := by
  have htne : (t : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ht₀
  have hx₂ := coe_pow_norm_lt_one (le_of_lt ht₀) ht₁ (by decide : (2 : ℕ) ≠ 0)
  have base := regionRegular_unitary (le_of_lt ht₀) ht₁
    (norm_one : ‖(1 : ℂ)‖ = 1) hU hV
  refine ⟨?_, ?_, base.e, base.f, base.g⟩
  · convert one_add_mul_ne_zero_of_norm_lt_one hV hx₂ using 1
    ring
  · have he : V * (t : ℂ) / (-(t : ℂ)) = -V := by
      rw [div_neg, mul_div_cancel_right₀ V htne]
    simpa [he] using hV₁

theorem finiteRegular_special_negative {t : ℝ} {a b : ℂ}
    (ht₀ : 0 < t) (ht₁ : t < 1) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (ha₁ : a - 1 ≠ 0) (hb₁ : b - 1 ≠ 0) (hab : a - b ≠ 0)
    (hab₁ : a * b - 1 ≠ 0) (hA : 1 + a ≠ 0) (hB : 1 + b ≠ 0) :
    FiniteRegular (t : ℂ) a b (-(t : ℂ)) := by
  have ha₀ := unit_ne_zero ha
  have hb₀ := unit_ne_zero hb
  have htne : (t : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ht₀
  have hd₀ : -(t : ℂ) ≠ 0 := neg_ne_zero.mpr htne
  have hx₂ := coe_pow_norm_lt_one (le_of_lt ht₀) ht₁ (by decide : (2 : ℕ) ≠ 0)
  have hf : fourFactors a b (-(t : ℂ) ^ 2) ≠ 0 :=
    fourFactors_ne_zero ha hb (by simpa using hx₂)
  have hD₁ : d₁ (t : ℂ) a b (-(t : ℂ)) ≠ 0 := by
    rwa [special_negative_d₁]
  have hD₂ : d₂ (t : ℂ) a b (-(t : ℂ)) ≠ 0 := by
    rw [special_negative_d₂ (t : ℂ) a b htne ha₀ hb₀]
    exact satakeNumerator_unitary_ne_zero ha hb hA hB
  have hWall : weylWall a b ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero ha₁ hab) hb₁) hab₁
  refine ⟨ha₀, hb₀, hd₀, ha₁, hb₁, hab, hab₁, ?_, ?_⟩
  · rw [weyl_common_euler_factorization (t : ℂ) a b (-(t : ℂ)) ha₀ hb₀ hd₀]
    exact mul_ne_zero
      (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hWall
        (pow_ne_zero 2 ha₀)) (pow_ne_zero 2 hb₀)) hd₀)
        (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 ha₀) (pow_ne_zero 2 hb₀))
          (pow_ne_zero 4 hd₀)))
      (mul_ne_zero hD₁ hD₂)
  · intro i
    exact regionRegular_special_negative ht₀ ht₁ (weylU_unitary ha hb i)
      (weylV_unitary ha hb i) (weylV_one_add_ne_zero ha₀ hb₀ hA hB i)

/-- The finite negative-special formula on the regular unitary Satake locus. -/
theorem finite_special_negative_unitary (q t : ℝ) (a b : ℂ)
    (ht₀ : 0 < t) (ht₁ : t < 1) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (ha₁ : a - 1 ≠ 0) (hb₁ : b - 1 ≠ 0) (hab : a - b ≠ 0)
    (hab₁ : a * b - 1 ≠ 0) (hA : 1 + a ≠ 0) (hB : 1 + b ≠ 0) :
    (2 / ((q : ℂ) + 1) * finiteCore (t : ℂ) a b (-(t : ℂ))) *
      specialNormalizer (t : ℂ) a b (-1) = 2 / ((q : ℂ) + 1) := by
  have htne : (t : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ht₀
  have hx₂ := coe_pow_norm_lt_one (le_of_lt ht₀) ht₁ (by decide : (2 : ℕ) ≠ 0)
  have hx₄ := coe_pow_norm_lt_one (le_of_lt ht₀) ht₁ (by decide : (4 : ℕ) ≠ 0)
  apply finite_sum_special_negative_formula (q : ℂ) (t : ℂ) a b
    (finiteRegular_special_negative ht₀ ht₁ ha hb ha₁ hb₁ hab hab₁ hA hB)
    htne (poincare_coe_ne_zero t) (satakeNumerator_unitary_ne_zero ha hb hA hB)
    (fourFactors_ne_zero ha hb hx₂) (n₂_unitary_ne_zero (le_of_lt ht₀) ht₁ ha hb)
    (fourFactors_ne_zero ha hb (by simpa using hx₂))
  · simpa using one_sub_mul_ne_zero_of_norm_lt_one (norm_one : ‖(1 : ℂ)‖ = 1) hx₂
  · simpa using one_sub_mul_ne_zero_of_norm_lt_one (norm_one : ‖(1 : ℂ)‖ = 1) hx₄

theorem finite_special_negative_inverseSqrt (q : ℝ) (hq : 1 < q) (a b : ℂ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (ha₁ : a - 1 ≠ 0) (hb₁ : b - 1 ≠ 0) (hab : a - b ≠ 0)
    (hab₁ : a * b - 1 ≠ 0) (hA : 1 + a ≠ 0) (hB : 1 + b ≠ 0) :
    (2 / ((q : ℂ) + 1) * finiteCore (inverseSqrt q : ℂ) a b (-(inverseSqrt q : ℂ))) *
      specialNormalizer (inverseSqrt q : ℂ) a b (-1) = 2 / ((q : ℂ) + 1) :=
  finite_special_negative_unitary q (inverseSqrt q) a b
    (inverseSqrt_pos hq) (inverseSqrt_lt_one hq) ha hb ha₁ hb₁ hab hab₁ hA hB

end Algebra
end FourierJacobi
