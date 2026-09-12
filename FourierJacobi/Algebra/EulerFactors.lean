import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Euler factors and normalization

Here t denotes the positive real q^(-1/2), subsequently embedded in the field.
The definitions in this file are explicit rational expressions. They are not
definitions of an L-function or of a Fourier--Jacobi period.
-/

namespace FourierJacobi
namespace Algebra
variable {K : Type*} [Field K]

def poincare (t : K) : K := 1 + 2 * t ^ 2 + 2 * t ^ 4 + 2 * t ^ 6 + t ^ 8

theorem poincare_factorization (t : K) :
    poincare t = (1 + t ^ 2) ^ 2 * (1 + t ^ 4) := by
  unfold poincare
  ring

def satakeNumerator (a b : K) : K := (1 + a) ^ 2 * (1 + b) ^ 2 / (a * b)

theorem satakeNumerator_eq (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    satakeNumerator a b = (a + 2 + a⁻¹) * (b + 2 + b⁻¹) := by
  unfold satakeNumerator
  field_simp
  ring

def fourFactors (a b x : K) : K :=
  (1 - a * x) * (1 - a⁻¹ * x) * (1 - b * x) * (1 - b⁻¹ * x)

def n₁ (t a b : K) : K := fourFactors a b (t ^ 2)

def n₂ (t a b : K) : K :=
  (1 - a * b * t ^ 2) * (1 - a / b * t ^ 2) *
    (1 - b / a * t ^ 2) * (1 - (a * b)⁻¹ * t ^ 2)

def d₁ (t a b d : K) : K := fourFactors a b (d * t)
def d₂ (t a b d : K) : K := fourFactors a b (t / d)

/-- The rational expression obtained for the core on the regular parameter locus. -/
def closedCore (t a b d : K) : K :=
  satakeNumerator a b * (1 - t ^ 2) * n₁ t a b * n₂ t a b /
    (poincare t * d₁ t a b d * d₂ t a b d)

def piAdjointInverse (t a b : K) : K := (1 - t ^ 2) ^ 2 * n₁ t a b * n₂ t a b

def principalAdjointInverse (t d : K) : K :=
  (1 - d * t) * (1 + d * t) * (1 - t ^ 2) * (1 - t / d) * (1 + t / d)

theorem principalAdjointInverse_eq (t d : K) :
    principalAdjointInverse t d =
      (1 - d ^ 2 * t ^ 2) * (1 - t ^ 2) * (1 - t ^ 2 / d ^ 2) := by
  unfold principalAdjointInverse
  simp only [div_eq_mul_inv]
  ring

def principalTensorInverse (t a b d : K) : K :=
  (1 - d * t) * (1 - t / d) * d₁ t a b d * d₂ t a b d

def principalNormalizer (t a b d : K) : K :=
  (1 - t ^ 4) * (1 - t ^ 8) * principalTensorInverse t a b d /
    (piAdjointInverse t a b * principalAdjointInverse t d)

/-- Cancellation isolated from the larger Satake products, to keep its proof small. -/
theorem principal_cancellation (t d p n₁ n₂ d₁ d₂ : K)
    (hc : poincare t ≠ 0) (hn₁ : n₁ ≠ 0) (hn₂ : n₂ ≠ 0)
    (hd₁ : d₁ ≠ 0) (hd₂ : d₂ ≠ 0) (ht : 1 - t ^ 2 ≠ 0)
    (hm : 1 - d * t ≠ 0) (hp : 1 + d * t ≠ 0)
    (him : 1 - t / d ≠ 0) (hip : 1 + t / d ≠ 0) :
    (p * (1 - t ^ 2) * n₁ * n₂ / (poincare t * d₁ * d₂)) *
      ((1 - t ^ 4) * (1 - t ^ 8) * ((1 - d * t) * (1 - t / d) * d₁ * d₂) /
        ((1 - t ^ 2) ^ 2 * n₁ * n₂ * principalAdjointInverse t d)) =
      p / ((1 + d * t) * (1 + t / d)) := by
  unfold principalAdjointInverse
  generalize d * t = x at *
  generalize t / d = y at *
  field_simp
  simp only [poincare]
  ring

theorem normalized_closedCore_principal (t a b d : K)
    (hc : poincare t ≠ 0) (hn₁ : n₁ t a b ≠ 0) (hn₂ : n₂ t a b ≠ 0)
    (hd₁ : d₁ t a b d ≠ 0) (hd₂ : d₂ t a b d ≠ 0)
    (ht : 1 - t ^ 2 ≠ 0)
    (hm : 1 - d * t ≠ 0) (hp : 1 + d * t ≠ 0)
    (him : 1 - t / d ≠ 0) (hip : 1 + t / d ≠ 0) :
    closedCore t a b d * principalNormalizer t a b d =
      satakeNumerator a b / ((1 + d * t) * (1 + t / d)) :=
  principal_cancellation t d (satakeNumerator a b) (n₁ t a b) (n₂ t a b)
    (d₁ t a b d) (d₂ t a b d) hc hn₁ hn₂ hd₁ hd₂ ht hm hp him hip

def specialTensorInverse (t a b e : K) : K :=
  (1 - e * t ^ 2) * fourFactors a b (e * t ^ 2)

def specialNormalizer (t a b e : K) : K :=
  (1 - t ^ 4) * (1 - t ^ 8) * specialTensorInverse t a b e /
    (piAdjointInverse t a b * (1 - t ^ 4))

theorem special_negative_d₁ (t a b : K) :
    d₁ t a b (-t) = fourFactors a b (-t ^ 2) := by
  unfold d₁
  congr 1
  ring

theorem special_negative_d₂ (t a b : K) (ht : t ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) :
    d₂ t a b (-t) = satakeNumerator a b := by
  unfold d₂ fourFactors satakeNumerator
  field_simp
  ring

theorem special_negative_cancellation (t p n₁ n₂ f : K)
    (hc : poincare t ≠ 0) (hp : p ≠ 0) (hn₁ : n₁ ≠ 0) (hn₂ : n₂ ≠ 0)
    (hf : f ≠ 0) (ht : 1 - t ^ 2 ≠ 0) (ht₄ : 1 - t ^ 4 ≠ 0) :
    (p * (1 - t ^ 2) * n₁ * n₂ / (poincare t * f * p)) *
      ((1 - t ^ 4) * (1 - t ^ 8) * ((1 + t ^ 2) * f) /
        ((1 - t ^ 2) ^ 2 * n₁ * n₂ * (1 - t ^ 4))) = 1 := by
  field_simp
  simp only [poincare]
  ring

theorem normalized_closedCore_special_negative (t a b : K)
    (ht₀ : t ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : poincare t ≠ 0) (hp : satakeNumerator a b ≠ 0)
    (hn₁ : n₁ t a b ≠ 0) (hn₂ : n₂ t a b ≠ 0)
    (hf : fourFactors a b (-t ^ 2) ≠ 0)
    (ht : 1 - t ^ 2 ≠ 0) (ht₄ : 1 - t ^ 4 ≠ 0) :
    closedCore t a b (-t) * specialNormalizer t a b (-1) = 1 := by
  unfold closedCore specialNormalizer specialTensorInverse piAdjointInverse
  rw [special_negative_d₁, special_negative_d₂ t a b ht₀ ha hb]
  simp only [neg_one_mul, sub_neg_eq_add]
  exact special_negative_cancellation t (satakeNumerator a b) (n₁ t a b)
    (n₂ t a b) (fourFactors a b (-t ^ 2)) hc hp hn₁ hn₂ hf ht ht₄

/-- The positive special sign kills the entire damped expression before any limit. -/
theorem special_positive_prefactor (q x : K) : (1 - (1 : K)) / (q + 1) * x = 0 := by
  simp

end Algebra
end FourierJacobi
