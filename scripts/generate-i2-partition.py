"""Generate the disjoint/exhaustive I2 integer and depth partition proof.

The classifier is an arithmetic decision tree. Lean checks membership and
uniqueness, with every row's original inequalities expanded explicitly.
"""
from pathlib import Path

root = Path(__file__).resolve().parents[1]
scope = {'__file__': str(root/'scripts/generate-i2-domains.py')}
data = (root/'scripts/generate-i2-domains.py').read_text(encoding='utf-8')
exec(data[:data.index("s = '''")], scope)

source = '''import FourierJacobi.Analysis.I2Predicates
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
'''
guards = [
 [('1 ≤ k',1),('-2*k ≤ j',1),('h < -k',0),('2 ≤ k',1)],
 [('1 ≤ k',1),('-2*k ≤ j',1),('h < -k',0),('2 ≤ k',0)],
 [('1 ≤ k',1),('-2*k ≤ j',1),('h < -k',1)],
 [('1 ≤ k',1),('-2*k ≤ j',0),('h < k+j',0),('j-1 ≤ 2*h',1)],
 [('1 ≤ k',1),('-2*k ≤ j',0),('h < k+j',0),('j-1 ≤ 2*h',0),('2*h = j-2',1),('c = 0',1)],
 [('1 ≤ k',1),('-2*k ≤ j',0),('h < k+j',0),('j-1 ≤ 2*h',0),('2*h = j-2',1),('c = 0',0),('c = 1',1)],
 [('1 ≤ k',1),('-2*k ≤ j',0),('h < k+j',0),('j-1 ≤ 2*h',0),('2*h = j-2',1),('c = 0',0),('c = 1',0)],
 [('1 ≤ k',1),('-2*k ≤ j',0),('h < k+j',0),('j-1 ≤ 2*h',0),('2*h = j-2',0)],
 [('1 ≤ k',1),('-2*k ≤ j',0),('h < k+j',1)],
 [('1 ≤ k',0),('k = 0',1),('-1 ≤ j',1),('h ≤ -2',0),('0 ≤ j',1)],
 [('1 ≤ k',0),('k = 0',1),('-1 ≤ j',1),('h ≤ -2',0),('0 ≤ j',0)],
 [('1 ≤ k',0),('k = 0',1),('-1 ≤ j',1),('h ≤ -2',1)],
 [('1 ≤ k',0),('k = 0',0),('0 ≤ j',1),('h ≤ -1',0),('k = -1',1)],
 [('1 ≤ k',0),('k = 0',0),('0 ≤ j',0),('j = -1',1),('h ≤ -2',0),('k = -1',1)],
 [('1 ≤ k',0),('k = 0',0),('0 ≤ j',0),('j = -1',1),('h ≤ -2',1),('k = -1',1)],
 [('1 ≤ k',0),('k = 0',0),('0 ≤ j',1),('h ≤ -1',0),('k = -1',0)],
 [('1 ≤ k',0),('k = 0',0),('0 ≤ j',0),('j = -1',1),('h ≤ -2',0),('k = -1',0)],
 [('1 ≤ k',0),('k = 0',0),('0 ≤ j',0),('j = -1',1),('h ≤ -2',1),('k = -1',0)],
 [('1 ≤ k',0),('k = 0',0),('0 ≤ j',1),('h ≤ -1',1)],
]
base = [('1 ≤ k',0),('-1 ≤ j',0),('0 ≤ j',0),('j = -1',0)]
guards += [
 base+[('h < j',0),('j-1 ≤ 2*h',1)],
 base+[('h < j',0),('j-1 ≤ 2*h',0),('2*h = j-2',1),('c = 0',1)],
 base+[('h < j',0),('j-1 ≤ 2*h',0),('2*h = j-2',1),('c = 0',0),('c = 1',1)],
 base+[('h < j',0),('j-1 ≤ 2*h',0),('2*h = j-2',1),('c = 0',0),('c = 1',0)],
 base+[('h < j',0),('j-1 ≤ 2*h',0),('2*h = j-2',0)],
 base+[('h < j',1)],
]
for row,path in zip(scope['rows'],guards):
    source+=f'  · change {row[1]} at hp\n'
    source+=f'    change {row[7]} at hc\n'
    for i,(guard,truth) in enumerate(path):
        claim=guard if truth else f'¬({guard})'
        source+=f'    have h{i} : {claim} := by omega\n'
    rules = [('if_pos' if truth else 'if_neg') + ' h'+str(i) for i,(_,truth) in enumerate(path)]
    source+='    simp only [i2Classify, i2TailClassify, '+', '.join(rules)+',\n'
    source+='      if_pos (rfl : true = true), if_neg (by decide : ¬ false = true), ite_self]\n'
    source+='    rfl\n'
source += '''
theorem i2_rows_partition (k j h : ℤ) (c : ℕ) :
    ∃! ν : Fin 25, i2SpatialPredicate ν (k,j,h) ∧ i2DepthPredicate ν c := by
  refine ⟨i2Classify k j h c, i2Classify_mem k j h c, ?_⟩
  intro ν hν
  exact (i2Classify_eq_of_mem ν k j h c hν.1 hν.2).symm

end FourierJacobi.Analysis
'''
(root/'FourierJacobi/Analysis/I2Partition.lean').write_text(source, encoding='utf-8')
