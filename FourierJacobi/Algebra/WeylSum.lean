import FourierJacobi.Algebra.WeylCoefficient10

/-! Assemble the separately checked coefficient identities. -/

namespace FourierJacobi
namespace Algebra
variable {K : Type*} [Field K]
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
-- Generated coefficient interfaces deliberately have uniform argument lists.
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

def allWeylCoefficients (t a b : K) : Fin 8 → Fin 11 → K := ![wcCoeffs0 t a b, wcCoeffs1 t a b, wcCoeffs2 t a b, wcCoeffs3 t a b, wcCoeffs4 t a b, wcCoeffs5 t a b, wcCoeffs6 t a b, wcCoeffs7 t a b]
theorem clearedExpansion (t a b d : K) (i : Fin 8) :
    weylClearedTerms t a b d i = evalCoefficients d (allWeylCoefficients t a b i) := by
  fin_cases i
  · exact clearedExpansion0 t a b d
  · exact clearedExpansion1 t a b d
  · exact clearedExpansion2 t a b d
  · exact clearedExpansion3 t a b d
  · exact clearedExpansion4 t a b d
  · exact clearedExpansion5 t a b d
  · exact clearedExpansion6 t a b d
  · exact clearedExpansion7 t a b d
theorem coefficientIdentity (t a b : K) (k : Fin 11) :
    (∑ i : Fin 8, allWeylCoefficients t a b i k) =
      if k = 5 then weylTargetCoefficient t a b else 0 := by
  fin_cases k
  · simpa only [allWeylCoefficients, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val, Fin.reduceFinMk, Fin.val_zero, Fin.val_succ, wcCoeffs0, wcCoeffs1, wcCoeffs2, wcCoeffs3, wcCoeffs4, wcCoeffs5, wcCoeffs6, wcCoeffs7, ite_true, ite_false, Fin.reduceEq, add_zero, add_assoc] using coefficientIdentity0 t a b
  · simpa only [allWeylCoefficients, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val, Fin.reduceFinMk, Fin.val_zero, Fin.val_succ, wcCoeffs0, wcCoeffs1, wcCoeffs2, wcCoeffs3, wcCoeffs4, wcCoeffs5, wcCoeffs6, wcCoeffs7, ite_true, ite_false, Fin.reduceEq, add_zero, add_assoc] using coefficientIdentity1 t a b
  · simpa only [allWeylCoefficients, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val, Fin.reduceFinMk, Fin.val_zero, Fin.val_succ, wcCoeffs0, wcCoeffs1, wcCoeffs2, wcCoeffs3, wcCoeffs4, wcCoeffs5, wcCoeffs6, wcCoeffs7, ite_true, ite_false, Fin.reduceEq, add_zero, add_assoc] using coefficientIdentity2 t a b
  · simpa only [allWeylCoefficients, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val, Fin.reduceFinMk, Fin.val_zero, Fin.val_succ, wcCoeffs0, wcCoeffs1, wcCoeffs2, wcCoeffs3, wcCoeffs4, wcCoeffs5, wcCoeffs6, wcCoeffs7, ite_true, ite_false, Fin.reduceEq, add_zero, add_assoc] using coefficientIdentity3 t a b
  · simpa only [allWeylCoefficients, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val, Fin.reduceFinMk, Fin.val_zero, Fin.val_succ, wcCoeffs0, wcCoeffs1, wcCoeffs2, wcCoeffs3, wcCoeffs4, wcCoeffs5, wcCoeffs6, wcCoeffs7, ite_true, ite_false, Fin.reduceEq, add_zero, add_assoc] using coefficientIdentity4 t a b
  · simpa only [allWeylCoefficients, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val, Fin.reduceFinMk, Fin.val_zero, Fin.val_succ, wcCoeffs0, wcCoeffs1, wcCoeffs2, wcCoeffs3, wcCoeffs4, wcCoeffs5, wcCoeffs6, wcCoeffs7, ite_true, ite_false, Fin.reduceEq, add_zero, add_assoc] using coefficientIdentity5 t a b
  · simpa only [allWeylCoefficients, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val, Fin.reduceFinMk, Fin.val_zero, Fin.val_succ, wcCoeffs0, wcCoeffs1, wcCoeffs2, wcCoeffs3, wcCoeffs4, wcCoeffs5, wcCoeffs6, wcCoeffs7, ite_true, ite_false, Fin.reduceEq, add_zero, add_assoc] using coefficientIdentity6 t a b
  · simpa only [allWeylCoefficients, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val, Fin.reduceFinMk, Fin.val_zero, Fin.val_succ, wcCoeffs0, wcCoeffs1, wcCoeffs2, wcCoeffs3, wcCoeffs4, wcCoeffs5, wcCoeffs6, wcCoeffs7, ite_true, ite_false, Fin.reduceEq, add_zero, add_assoc] using coefficientIdentity7 t a b
  · simpa only [allWeylCoefficients, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val, Fin.reduceFinMk, Fin.val_zero, Fin.val_succ, wcCoeffs0, wcCoeffs1, wcCoeffs2, wcCoeffs3, wcCoeffs4, wcCoeffs5, wcCoeffs6, wcCoeffs7, ite_true, ite_false, Fin.reduceEq, add_zero, add_assoc] using coefficientIdentity8 t a b
  · simpa only [allWeylCoefficients, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val, Fin.reduceFinMk, Fin.val_zero, Fin.val_succ, wcCoeffs0, wcCoeffs1, wcCoeffs2, wcCoeffs3, wcCoeffs4, wcCoeffs5, wcCoeffs6, wcCoeffs7, ite_true, ite_false, Fin.reduceEq, add_zero, add_assoc] using coefficientIdentity9 t a b
  · simpa only [allWeylCoefficients, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val, Fin.reduceFinMk, Fin.val_zero, Fin.val_succ, wcCoeffs0, wcCoeffs1, wcCoeffs2, wcCoeffs3, wcCoeffs4, wcCoeffs5, wcCoeffs6, wcCoeffs7, ite_true, ite_false, Fin.reduceEq, add_zero, add_assoc] using coefficientIdentity10 t a b
theorem weyl_polynomial_identity (t a b d : K) :
    (∑ i : Fin 8, weylClearedTerms t a b d i) = weylTargetNumerator t a b d := by
  simp_rw [clearedExpansion, evalCoefficients]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, coefficientIdentity]
  have ht : weylTargetNumerator t a b d = weylTargetCoefficient t a b * d ^ 5 := by
    unfold weylTargetNumerator weylTargetCoefficient
    ac_rfl
  rw [ht]
  norm_num [Fin.sum_univ_succ]


end Algebra
end FourierJacobi
