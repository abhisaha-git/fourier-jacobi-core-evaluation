import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

/-!
# The finite-dimensional intertwining matrix

This file proves algebraic facts about the matrix displayed in Section 2.
It does not identify that matrix with an operator on a metaplectic representation.
The parameter r stands for q ^ (-2 * s).
-/

namespace FourierJacobi

open Matrix

variable {K : Type*} [Field K]

def intertwinerMatrix (q r : K) : Matrix (Fin 2) (Fin 2) K :=
  !![(1 - q⁻¹) * r / (1 - r), 1;
      q⁻¹, (1 - q⁻¹) / (1 - r)]

theorem intertwinerMatrix_at_endpoint (q : K) (hq : q ≠ 1) :
    intertwinerMatrix q q⁻¹ = !![q⁻¹, 1; q⁻¹, 1] := by
  have hr : 1 - q⁻¹ ≠ 0 := sub_ne_zero.mpr (Ne.symm (inv_ne_one.mpr hq))
  ext i j
  fin_cases i <;> fin_cases j <;> simp [intertwinerMatrix, hr]

def specialVector (q : K) : Fin 2 → K := ![1, -q⁻¹]

theorem endpoint_kills_specialVector (q : K) (hq : q ≠ 1) :
    (intertwinerMatrix q q⁻¹).mulVec (specialVector q) = 0 := by
  rw [intertwinerMatrix_at_endpoint q hq]
  ext i
  fin_cases i <;> simp [specialVector, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem endpoint_kernel (q : K) (hq : q ≠ 1) (v : Fin 2 → K) :
    (intertwinerMatrix q q⁻¹).mulVec v = 0 ↔ v 1 = -q⁻¹ * v 0 := by
  rw [intertwinerMatrix_at_endpoint q hq]
  simp [dotProduct, Fin.sum_univ_two, funext_iff, Fin.forall_fin_two]
  constructor <;> intro h <;> linear_combination h

/-- The real Gram matrix in the compact picture, with the paper's Haar normalization. -/
noncomputable def compactGram (q : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 / (q + 1), 0; 0, q / (q + 1)]

theorem compactGram_special_norm_sq (q : ℝ) (hq : 1 < q) :
    dotProduct (specialVector q) ((compactGram q).mulVec (specialVector q)) = q⁻¹ := by
  have hq0 : q ≠ 0 := by linarith
  have hq1 : q + 1 ≠ 0 := by linarith
  simp [specialVector, compactGram, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  field_simp

end FourierJacobi
