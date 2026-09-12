import FourierJacobi.Algebra.Matrices
import FourierJacobi.Valuations.Cartan
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Order.AddGroupWithTop
import Mathlib.Tactic.LinearCombination

/-!
# Actual matrix valuation minima

This development connects the entry and minor calculation in `KLlemma` to
matrices over a general field with an additive valuation. Values lie in
`WithTop ℤ`, so the valuation of zero is infinity throughout. No Cartan
double-coset decomposition or measure-theoretic omission of zeros is assumed.
-/

namespace FourierJacobi
namespace Valuations

open LocalMatrix

variable {K : Type*} [Field K]

/-- The intrinsic minimum of valuations of all entries of a finite matrix. -/
def matrixMinimum {n m : ℕ} (v : AddValuation K (WithTop ℤ))
    (A : Matrix (Fin n) (Fin m) K) : WithTop ℤ :=
  Finset.univ.inf fun i => Finset.univ.inf fun j => v (A i j)

theorem le_matrixMinimum_iff {n m : ℕ} (v : AddValuation K (WithTop ℤ))
    (A : Matrix (Fin n) (Fin m) K) (b : WithTop ℤ) :
    b ≤ matrixMinimum v A ↔ ∀ i j, b ≤ v (A i j) := by
  simp [matrixMinimum]

theorem matrixMinimum_le_entry {n m : ℕ} (v : AddValuation K (WithTop ℤ))
    (A : Matrix (Fin n) (Fin m) K) (i : Fin n) (j : Fin m) :
    matrixMinimum v A ≤ v (A i j) :=
  (le_matrixMinimum_iff v A _).mp le_rfl i j

/-- Entry list in (KLlemmaeq2), without subtracting infinite valuations. -/
def entryListMinimum (v : AddValuation K (WithTop ℤ)) (a x y z : K) : WithTop ℤ :=
  min (min (min (min (min (min 0 (v a)) (v a⁻¹)) (v (a * x))) (v y))
    (v (a * y))) (v z)

/-- Minor list in (KLlemmaeq3), with all possible zeros retained. -/
def minorListMinimum (v : AddValuation K (WithTop ℤ)) (a x y z : K) : WithTop ℤ :=
  min (min (min (min (min (min (min (min 0 (v a)) (v a⁻¹)) (v (a * x)))
    (v y)) (v (a * y))) (v (a * z))) (v (z / a))) (v (a * (y ^ 2 - x * z)))

theorem actual_entry_minimum (v : AddValuation K (WithTop ℤ)) (a x y z : K) :
    matrixMinimum v (g a x y z) = entryListMinimum v a x y z := by
  apply le_antisymm
  · simp only [entryListMinimum, le_min_iff]
    have h := matrixMinimum_le_entry v (g a x y z)
    refine ⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · simpa [g, D, N, Matrix.mul_apply, Fin.sum_univ_succ] using (h 0 0)
    · simpa [g, D, N, Matrix.mul_apply, Fin.sum_univ_succ] using (h 1 1)
    · simpa [g, D, N, Matrix.mul_apply, Fin.sum_univ_succ] using (h 2 2)
    · simpa [g, D, N, Matrix.mul_apply, Fin.sum_univ_succ] using (h 1 2)
    · simpa [g, D, N, Matrix.mul_apply, Fin.sum_univ_succ] using (h 0 2)
    · simpa [g, D, N, Matrix.mul_apply, Fin.sum_univ_succ] using (h 1 3)
    · simpa [g, D, N, Matrix.mul_apply, Fin.sum_univ_succ] using (h 0 3)
  · apply (le_matrixMinimum_iff v _ _).mpr
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [g, D, N, Matrix.mul_apply, Fin.sum_univ_succ, entryListMinimum]

set_option maxHeartbeats 2000000 in
theorem actual_minor_minimum (v : AddValuation K (WithTop ℤ))
    (a x y z : K) (ha : a ≠ 0) :
    matrixMinimum v (secondCompound (g a x y z)) = minorListMinimum v a x y z := by
  rw [all_two_by_two_minors a x y z ha]
  apply le_antisymm
  · simp only [minorListMinimum, le_min_iff]
    have h := matrixMinimum_le_entry v
      (!![a, a * x, a * y, -a * y, -a * z, a * (y ^ 2 - x * z);
         0, a⁻¹, 0, 0, 0, -z / a;
         0, 0, 1, 0, 0, y;
         0, 0, 0, 1, 0, -y;
         0, 0, 0, 0, a, a * x;
         0, 0, 0, 0, 0, a⁻¹] : Matrix (Fin 6) (Fin 6) K)
    exact ⟨⟨⟨⟨⟨⟨⟨⟨by simpa using h 2 2, by simpa using h 0 0⟩,
      by simpa using h 1 1⟩, by simpa using h 0 1⟩, by simpa using h 2 5⟩,
      by simpa using h 0 2⟩, by simpa using h 0 4⟩,
      by simpa [neg_div] using h 1 5⟩, by simpa using h 0 5⟩
  · apply (le_matrixMinimum_iff v _ _).mpr
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [minorListMinimum, neg_div]

/-- The ultrametric minor bound, for arbitrary actual matrices including zeros. -/
theorem twice_entry_minimum_le_minor (v : AddValuation K (WithTop ℤ))
    (A : Matrix (Fin 4) (Fin 4) K) :
    matrixMinimum v A + matrixMinimum v A ≤ matrixMinimum v (secondCompound A) := by
  apply (le_matrixMinimum_iff v _ _).mpr
  intro i j
  apply v.map_le_sub
  · rw [v.map_mul]
    exact add_le_add (matrixMinimum_le_entry v A _ _) (matrixMinimum_le_entry v A _ _)
  · rw [v.map_mul]
    exact add_le_add (matrixMinimum_le_entry v A _ _) (matrixMinimum_le_entry v A _ _)

theorem actual_entry_minimum_le_zero (v : AddValuation K (WithTop ℤ))
    (a x y z : K) : matrixMinimum v (g a x y z) ≤ 0 := by
  rw [actual_entry_minimum]
  simp [entryListMinimum]

theorem actual_minor_minimum_le_zero (v : AddValuation K (WithTop ℤ))
    (a x y z : K) (ha : a ≠ 0) :
    matrixMinimum v (secondCompound (g a x y z)) ≤ 0 := by
  rw [actual_minor_minimum v a x y z ha]
  simp [minorListMinimum]

/-- The extrema are finite even when some coordinates or the determinant vanish. -/
theorem actual_minima_finite (v : AddValuation K (WithTop ℤ))
    (a x y z : K) (ha : a ≠ 0) :
    matrixMinimum v (g a x y z) ≠ ⊤ ∧
      matrixMinimum v (secondCompound (g a x y z)) ≠ ⊤ := by
  constructor
  · exact ne_top_of_le_ne_top (by simp) (actual_entry_minimum_le_zero v a x y z)
  · exact ne_top_of_le_ne_top (by simp) (actual_minor_minimum_le_zero v a x y z ha)

/-- Specialization of the actual entry minimum to the existing integer table. -/
theorem actual_entry_minimum_integer_zero (v : AddValuation K (WithTop ℤ))
    (a x y : K) (k j h : ℤ) (hk : v a = k) (hj : v x = j) (hh : v y = h) :
    matrixMinimum v (g a x y 0) = (entryMinimum 0 k j h : WithTop ℤ) := by
  rw [actual_entry_minimum]
  simp [entryListMinimum, entryMinimum, baseMinimum, hk, hj, hh, min_assoc]

/-- Specialization of the actual minor minimum when the central coordinate is zero. -/
theorem actual_minor_minimum_integer_zero (v : AddValuation K (WithTop ℤ))
    (a x y : K) (k j h c : ℤ) (hk : v a = k) (hj : v x = j) (hh : v y = h)
    (ha : a ≠ 0) :
    matrixMinimum v (secondCompound (g a x y 0)) = (minorMinimum 0 k j h c : WithTop ℤ) := by
  rw [actual_minor_minimum v a x y 0 ha]
  simp [minorListMinimum, minorMinimum, baseMinimum, hk, hj, hh, two_nsmul, two_mul]
  simp only [add_min, min_assoc]

theorem actual_entry_minimum_integer_nonzero (v : AddValuation K (WithTop ℤ))
    (a x y z : K) (r k j h : ℤ) (hr : r ≠ 0)
    (hk : v a = k) (hj : v x = j) (hh : v y = h) (hz : v z = (-r : ℤ)) :
    matrixMinimum v (g a x y z) = (entryMinimum r k j h : WithTop ℤ) := by
  rw [actual_entry_minimum]
  simp [entryListMinimum, entryMinimum, baseMinimum, hr, hk, hj, hh, hz, min_assoc]

/-- The only additional input needed for the integer minor table is the valuation
of the actual determinant polynomial; it is not a Cartan or period hypothesis. -/
theorem actual_minor_minimum_integer_nonzero (v : AddValuation K (WithTop ℤ))
    (a x y z : K) (r k j h c : ℤ) (hr : r ≠ 0) (ha : a ≠ 0)
    (hk : v a = k) (hj : v x = j) (hh : v y = h) (hz : v z = (-r : ℤ))
    (hd : v (y ^ 2 - x * z) = (determinantValuation r j h c : WithTop ℤ)) :
    matrixMinimum v (secondCompound (g a x y z)) = (minorMinimum r k j h c : WithTop ℤ) := by
  rw [actual_minor_minimum v a x y z ha]
  unfold minorListMinimum
  rw [v.map_mul a (y ^ 2 - x * z), hd]
  simp [minorMinimum, baseMinimum, hr, hk, hj, hh, hz, sub_eq_add_neg, add_comm]
  simp only [add_min, min_assoc, add_comm]

theorem nonzero_of_integer_valuation (v : AddValuation K (WithTop ℤ))
    (x : K) (k : ℤ) (hk : v x = k) : x ≠ 0 := by
  intro hx
  simp [hx] at hk

/-- The collision determinant valuation is proved from the actual field ratio.
This is the algebraic part of `expanded:collision`, before its measure calculation. -/
theorem actual_determinant_valuation (v : AddValuation K (WithTop ℤ))
    (x y z : K) (r j h c : ℤ)
    (hj : v x = j) (hh : v y = h) (hz : v z = (-r : ℤ))
    (hc : 2 * h = j - r → v (y ^ 2 / (x * z) - 1) = c) :
    v (y ^ 2 - x * z) = (determinantValuation r j h c : WithTop ℤ) := by
  have hxx := nonzero_of_integer_valuation v x j hj
  have hzz := nonzero_of_integer_valuation v z (-r) hz
  have hy2 : v (y ^ 2) = ((2 * h : ℤ) : WithTop ℤ) := by
    simp [hh, two_nsmul, two_mul]
  have hxz : v (x * z) = ((j - r : ℤ) : WithTop ℤ) := by
    simp [hj, hz, sub_eq_add_neg]
  by_cases heq : 2 * h = j - r
  · have hfactor : y ^ 2 - x * z = (x * z) * (y ^ 2 / (x * z) - 1) := by
      field_simp
    rw [hfactor, v.map_mul, hc heq, hxz, ← heq]
    simp [determinantValuation, heq]
  · have hne : v (y ^ 2) ≠ v (x * z) := by
      rw [hy2, hxz]
      exact_mod_cast heq
    rw [sub_eq_add_neg, v.map_add_of_distinct_val (by simpa using hne), v.map_neg,
      hy2, hxz]
    simp [determinantValuation, heq]

/-- A finite cancellation depth is nonnegative on the collision locus. -/
theorem actual_cancellation_depth_nonnegative (v : AddValuation K (WithTop ℤ))
    (x y z : K) (r j h c : ℤ)
    (hj : v x = j) (hh : v y = h) (hz : v z = (-r : ℤ))
    (heq : 2 * h = j - r) (hc : v (y ^ 2 / (x * z) - 1) = c) : 0 ≤ c := by
  have hratio : v (y ^ 2 / (x * z)) = 0 := by
    have hval : v (y ^ 2 / (x * z)) = ((2 * h - (j - r) : ℤ) : WithTop ℤ) := by
      simp [hj, hh, hz, two_nsmul, two_mul, sub_eq_add_neg]
    rw [hval, heq]
    simp
  have hv := v.map_sub (y ^ 2 / (x * z)) 1
  rw [hratio, v.map_one, min_self, hc] at hv
  exact_mod_cast hv

/-- Both intrinsic actual-matrix minima equal the integer-table inputs once
all relevant valuations are finite. The determinant valuation is derived,
not supplied as a hypothesis. -/
theorem actual_minima_integer_nonzero (v : AddValuation K (WithTop ℤ))
    (a x y z : K) (r k j h c : ℤ) (hr : r ≠ 0)
    (hk : v a = k) (hj : v x = j) (hh : v y = h) (hz : v z = (-r : ℤ))
    (hc : 2 * h = j - r → v (y ^ 2 / (x * z) - 1) = c) :
    matrixMinimum v (g a x y z) = (entryMinimum r k j h : WithTop ℤ) ∧
      matrixMinimum v (secondCompound (g a x y z)) =
        (minorMinimum r k j h c : WithTop ℤ) := by
  exact ⟨actual_entry_minimum_integer_nonzero v a x y z r k j h hr hk hj hh hz,
    actual_minor_minimum_integer_nonzero v a x y z r k j h c hr
      (nonzero_of_integer_valuation v a k hk) hk hj hh hz
      (actual_determinant_valuation v x y z r j h c hj hh hz hc)⟩

/-- The block shape after a primitive first column has been moved to `d e₁`
in the elementary proof of `expanded:cartan`. -/
def firstColumnShape (d b₁ b₂ c p q r s u w : K) : Matrix (Fin 4) (Fin 4) K :=
  !![d, b₁, b₂, c; 0, p, q, u; 0, r, s, w; 0, 0, 0, d⁻¹]

/-- Explicit right elimination, in the paper's anti-diagonal symplectic form. -/
def cartanEliminator (d b₁ b₂ c : K) : Matrix (Fin 4) (Fin 4) K :=
  !![1, -b₁ / d, -b₂ / d, -c / d;
     0, 1, 0, -b₂ / d;
     0, 0, 1, b₁ / d;
     0, 0, 0, 1]

theorem cartanEliminator_symplectic (d b₁ b₂ c : K) :
    (cartanEliminator d b₁ b₂ c).transpose * J * cartanEliminator d b₁ b₂ c = J := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cartanEliminator, J, Matrix.mul_apply, Matrix.transpose_apply,
      Fin.sum_univ_succ] <;> ring

/-- The concrete elimination step: symplecticity forces both unwanted lower
entries to disappear, and the surviving middle block has determinant one.
Primitive-vector transitivity and the choice of an integral first column are
separate obligations; this theorem does not assume or assert a Cartan decomposition. -/
theorem elementary_right_reduction (d b₁ b₂ c p q r s u w : K) (hd : d ≠ 0)
    (hsp : (firstColumnShape d b₁ b₂ c p q r s u w).transpose * J *
      firstColumnShape d b₁ b₂ c p q r s u w = J) :
    p * s - q * r = 1 ∧
      firstColumnShape d b₁ b₂ c p q r s u w * cartanEliminator d b₁ b₂ c =
        !![d, 0, 0, 0; 0, p, q, 0; 0, r, s, 0; 0, 0, 0, d⁻¹] := by
  have hdet := congrArg (fun A : Matrix (Fin 4) (Fin 4) K => A 1 2) hsp
  have hb₁ := congrArg (fun A : Matrix (Fin 4) (Fin 4) K => A 1 3) hsp
  have hb₂ := congrArg (fun A : Matrix (Fin 4) (Fin 4) K => A 2 3) hsp
  simp [firstColumnShape, J, Matrix.mul_apply, Matrix.transpose_apply,
    Fin.sum_univ_succ] at hdet hb₁ hb₂
  have hdu : d * u - p * b₂ + q * b₁ = 0 := by
    field_simp at hb₁ hb₂
    linear_combination -d * u * hdet - p * hb₂ + q * hb₁
  have hdw : d * w - r * b₂ + s * b₁ = 0 := by
    field_simp at hb₁ hb₂
    linear_combination -d * w * hdet - r * hb₂ + s * hb₁
  constructor
  · linear_combination hdet
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [firstColumnShape, cartanEliminator, Matrix.mul_apply,
        Fin.sum_univ_succ] <;> field_simp <;>
      (solve | ring | linear_combination hdu | linear_combination hdw)

end Valuations
end FourierJacobi
