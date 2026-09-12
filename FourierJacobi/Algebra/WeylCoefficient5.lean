import FourierJacobi.Algebra.WeylCoefficient4

/-! Generated certificate for coefficient 5 in d. -/

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

theorem coefficientIdentity5 (t a b : K) : wc0_5 t a b + wc1_5 t a b + wc2_5 t a b + wc3_5 t a b + wc4_5 t a b + wc5_5 t a b + wc6_5 t a b + wc7_5 t a b = weylTargetCoefficient t a b := by
  unfold wc0_5 wc1_5 wc2_5 wc3_5 wc4_5 wc5_5 wc6_5 wc7_5
  simp only [weylWeightNumerators, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val, Fin.reduceFinMk]
  simp only [wh0_0, wh0_1, wh0_2, wh0_3, wh0_4, wh1_0, wh1_1, wh1_2, wh1_3, wh1_4, wh2_0, wh2_1, wh2_2, wh2_3, wh2_4, wh3_0, wh3_1, wh3_2, wh3_3, wh3_4, wh4_0, wh4_1, wh4_2, wh4_3, wh4_4, wh5_0, wh5_1, wh5_2, wh5_3, wh5_4, wh6_0, wh6_1, wh6_2, wh6_3, wh6_4, wh7_0, wh7_1, wh7_2, wh7_3, wh7_4, wr0_0, wr0_1, wr0_2, wr0_3, wr0_4, wr0_5, wr0_6, wr1_0, wr1_1, wr1_2, wr1_3, wr1_4, wr1_5, wr1_6, wr2_0, wr2_1, wr2_2, wr2_3, wr2_4, wr2_5, wr2_6, wr3_0, wr3_1, wr3_2, wr3_3, wr3_4, wr3_5, wr3_6, wr4_0, wr4_1, wr4_2, wr4_3, wr4_4, wr4_5, wr4_6, wr5_0, wr5_1, wr5_2, wr5_3, wr5_4, wr5_5, wr5_6, wr6_0, wr6_1, wr6_2, wr6_3, wr6_4, wr6_5, wr6_6, wr7_0, wr7_1, wr7_2, wr7_3, wr7_4, wr7_5, wr7_6, weylTargetCoefficient]
  norm_num
  all_goals ring


end Algebra
end FourierJacobi
