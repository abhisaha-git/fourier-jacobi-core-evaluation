"""Generate checked integer-domain data for the twenty-five I2 source rows.

This is source generation, not a proof certificate. Every generated domain map
has both inverse laws proved by Lean's kernel-checked arithmetic tactics.
"""
from pathlib import Path

root = Path(__file__).resolve().parents[1]
out = root / "FourierJacobi/Analysis/I2Domains.lean"

# name, original predicate, shape, to-map, inverse-map, ell, b, depth
rows = [
 ("1a", "2 ≤ k ∧ -2*k ≤ j ∧ -k ≤ h", 3,
  ("a+2", "b-2*(a+2)", "c-(a+2)"), ("k-2", "j+2*k", "h+k"), "4", "k-2", "True"),
 ("1b", "k = 1 ∧ -2 ≤ j ∧ -1 ≤ h", 2,
  ("1", "a-2", "b-1"), ("j+2", "h+1"), "2", "1", "True"),
 ("2", "1 ≤ k ∧ -2*k ≤ j ∧ h < -k", 3,
  ("a+1", "b-2*(a+1)", "-(a+1)-c-1"), ("k-1", "j+2*k", "-k-h-1"), "-2*k-2*h", "k", "True"),
 ("3a", "1 ≤ k ∧ j < -2*k ∧ k+j ≤ h ∧ j-1 ≤ 2*h", 4,
  ("a+1", "-2*(a+1)-2*b-e-1", "-(a+1)-b-1+c"),
  ("(-j-2*k-1)%2", "k-1", "(-j-2*k-1)/2", "h+k+((-j-2*k-1)/2)+1"), "4", "-k-j-2", "True"),
 ("3b", "1 ≤ k ∧ j < -2*k ∧ k+j ≤ h ∧ 2*h = j-2", 2,
  ("a+1", "-2*(a+1)-2*b-2", "-(a+1)-b-2"), ("k-1", "-h-k-2"), "4", "-k-j-2", "c = 0"),
 ("3c", "1 ≤ k ∧ j < -2*k ∧ k+j ≤ h ∧ 2*h = j-2", 2,
  ("a+1", "-2*(a+1)-2*b-2", "-(a+1)-b-2"), ("k-1", "-h-k-2"), "2", "-k-j-1", "c = 1"),
 ("3d", "1 ≤ k ∧ j < -2*k ∧ k+j ≤ h ∧ 2*h = j-2", 2,
  ("a+1", "-2*(a+1)-2*b-2", "-(a+1)-b-2"), ("k-1", "-h-k-2"), "0", "-k-j", "2 ≤ c"),
 ("4", "1 ≤ k ∧ j < -2*k ∧ k+j ≤ h ∧ 2*h ≤ j-3", 3,
  ("a+1", "-2*(a+1)-2*b-c-3", "-(a+1)-b-c-3"), ("k-1", "h-k-j", "j-2*h-3"), "2*j-4*h", "2*h-2*j-k", "True"),
 ("5", "1 ≤ k ∧ j < -2*k ∧ h < k+j", 3,
  ("a+1", "-2*(a+1)-b-1", "-(a+1)-b-c-2"), ("k-1", "-j-2*k-1", "k+j-h-1"), "-2*k-2*h", "k", "True"),
 ("6a", "k = 0 ∧ 0 ≤ j ∧ -1 ≤ h", 2,
  ("0", "a", "b-1"), ("j", "h+1"), "0", "2", "True"),
 ("6aa", "k = 0 ∧ j = -1 ∧ -1 ≤ h", 1,
  ("0", "-1", "a-1"), ("h+1",), "2", "1", "True"),
 ("6aaa", "k = 0 ∧ -1 ≤ j ∧ h ≤ -2", 2,
  ("0", "a-1", "-b-2"), ("j+1", "-h-2"), "-2*h", "0", "True"),
 ("6b", "k = -1 ∧ 0 ≤ j ∧ 0 ≤ h", 2,
  ("-1", "a", "b"), ("j", "h"), "2", "1", "True"),
 ("6bb", "k = -1 ∧ j = -1 ∧ -1 ≤ h", 1,
  ("-1", "-1", "a-1"), ("h+1",), "4", "0", "True"),
 ("6bbb", "k = -1 ∧ j = -1 ∧ h ≤ -2", 1,
  ("-1", "-1", "-a-2"), ("-h-2",), "-2*h", "1", "True"),
 ("6c", "k ≤ -2 ∧ 0 ≤ j ∧ 0 ≤ h", 3,
  ("-a-2", "b", "c"), ("-k-2", "j", "h"), "4", "-k-2", "True"),
 ("6cc", "k ≤ -2 ∧ j = -1 ∧ -1 ≤ h", 2,
  ("-a-2", "-1", "b-1"), ("-k-2", "h+1"), "4", "-k-1", "True"),
 ("6ccc", "k ≤ -2 ∧ j = -1 ∧ h ≤ -2", 2,
  ("-a-2", "-1", "-b-2"), ("-k-2", "-h-2"), "-2*h", "-k", "True"),
 ("7", "k ≤ -1 ∧ 0 ≤ j ∧ h ≤ -1", 3,
  ("-a-1", "b", "-c-1"), ("-k-1", "j", "-h-1"), "-2*h", "-k", "True"),
 ("8a", "k ≤ 0 ∧ j < -1 ∧ j ≤ h ∧ j-1 ≤ 2*h", 4,
  ("-a", "-2*b-e-2", "-b-e-1+c"),
  ("(-j-2)%2", "-k", "(-j-2)/2", "h+((-j-2)/2)+((-j-2)%2)+1"), "4", "-k-j-2", "True"),
 ("8b", "k ≤ 0 ∧ j < -1 ∧ j ≤ h ∧ 2*h = j-2", 2,
  ("-a", "-2*b-2", "-b-2"), ("-k", "-h-2"), "4", "-k-j-2", "c = 0"),
 ("8c", "k ≤ 0 ∧ j < -1 ∧ j ≤ h ∧ 2*h = j-2", 2,
  ("-a", "-2*b-2", "-b-2"), ("-k", "-h-2"), "2", "-k-j-1", "c = 1"),
 ("8d", "k ≤ 0 ∧ j < -1 ∧ j ≤ h ∧ 2*h = j-2", 2,
  ("-a", "-2*b-2", "-b-2"), ("-k", "-h-2"), "0", "-k-j", "2 ≤ c"),
 ("9", "k ≤ 0 ∧ j < -1 ∧ j ≤ h ∧ 2*h ≤ j-3", 3,
  ("-a", "-2*b-c-3", "-b-c-3"), ("-k", "h-j", "j-2*h-3"), "2*j-4*h", "2*h-2*j-k", "True"),
 ("10", "k ≤ 0 ∧ j < -1 ∧ h < j", 3,
  ("-a", "-b-2", "-b-c-3"), ("-k", "-j-2", "j-h-1"), "-2*h", "-k", "True"),
]

def subst(s, mapping):
    import re
    return re.sub(r"\b[a-z]\b", lambda m: mapping.get(m[0], m[0]), s)

s = '''import FourierJacobi.Valuations.Cartan
import Mathlib.Tactic.FinCases

/-!
The twenty-five original I2 valuation regions (I2eq4).  Coordinates are
integer valuations, not truncations.  The 3/8 collision blocks carry their
actual depth conditions; ordinary rows keep every depth and will later use
the collision distribution.  Every affine parametrization below has both
inverse laws checked in Lean. No sum or measure identity is assumed.
-/

namespace FourierJacobi.Analysis

open FourierJacobi.Valuations

set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
-- Uniform generated arithmetic proof scripts intentionally share simplifiers.
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

def i2SpatialPredicate (ν : Fin 25) (p : ℤ × ℤ × ℤ) : Prop :=
  let k := p.1
  let j := p.2.1
  let h := p.2.2
  match ν.val with
'''
for i, row in enumerate(rows):
    s += f"  | {i} => {row[1]}\n" if i < 24 else f"  | _ => {row[1]}\n"
s += '\ndef i2DepthPredicate (ν : Fin 25) (c : ℕ) : Prop :=\n  match ν.val with\n'
for i,row in enumerate(rows):
    if row[-1] != 'True': s += f"  | {i} => {row[-1]}\n"
s += '  | _ => True\n\nabbrev I2SpatialRow (ν : Fin 25) := {p : ℤ × ℤ × ℤ // i2SpatialPredicate ν p}\n\n'

for i, (name,pred,dim,coords,inv,ell,b,depth) in enumerate(rows):
    shape = {1:'ℕ',2:'ℕ × ℕ',3:'ℕ × ℕ × ℕ',4:'Fin 2 × ℕ × ℕ × ℕ'}[dim]
    natvars = {1:{'a':'n'},2:{'a':'n.1','b':'n.2'},3:{'a':'n.1','b':'n.2.1','c':'n.2.2'},4:{'e':'n.1.val','a':'n.2.1','b':'n.2.2.1','c':'n.2.2.2'}}[dim]
    intvars = {x:f'({v} : ℤ)' for x,v in natvars.items()}
    to = '('+', '.join(subst(x,intvars) for x in coords)+')'
    pvars = {'k':'p.val.1','j':'p.val.2.1','h':'p.val.2.2'}
    inverses = [f'({subst(x,pvars)}).toNat' for x in inv]
    if dim == 4: inverses[0] = f'⟨{inverses[0]}, by omega⟩'
    invstr = inverses[0] if dim ==1 else '('+', '.join(inverses)+')'
    s += f'def i2Case{name}Equiv : ({shape}) ≃ I2SpatialRow {i} where\n'
    to_pred = subst(pred, {x:'('+subst(v,intvars)+')' for x,v in zip(['k','j','h'],coords)})
    s += f'  toFun n := ⟨{to}, by change {to_pred}; omega⟩\n'
    s += f'  invFun p := {invstr}\n'
    s += '  left_inv n := by\n'
    if dim > 1:
        s += '    rcases n with ' + {2:'⟨a,b⟩',3:'⟨a,b,c⟩',4:'⟨⟨e,he⟩,a,b,c⟩'}[dim]+'\n'
    if name == '6b': s += '    rfl\n'
    else:
        s += '    dsimp\n'
        if dim>1:s += '    simp only [Prod.mk.injEq, Fin.mk.injEq, true_and, and_true] <;> omega\n'
        else:s += '    omega\n'
    s += f'  right_inv p := by\n    apply Subtype.ext\n    rcases p with ⟨⟨k,j,h⟩, hp⟩\n    change {pred} at hp\n    dsimp\n    simp only [Prod.mk.injEq, true_and, and_true] <;> omega\n\n'
    s += f'@[simp] theorem i2Case{name}Equiv_val (n : {shape}) :\n'
    s += f'    (i2Case{name}Equiv n).val = {to} := rfl\n\n'
    expected = f'({subst(ell,pvars)}, {subst(b,pvars)})'
    s += f'theorem i2Case{name}_cartan (p : I2SpatialRow {i}) (c : ℕ)'
    if depth!='True': s += f' (hc : {depth})'
    s += ' :\n'
    s += f'    cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 c = {expected} := by\n'
    s += '  have hp := p.property\n'
    s += f'  change {subst(pred,pvars)} at hp\n'
    s += '  rw [← tableTwo_correct _ _ _ _ (by omega)]\n'
    s += '  unfold tableTwo collisionRows\n  split_ifs <;> simp only [Prod.mk.injEq, true_and, and_true] <;> omega\n\n'
s += 'end FourierJacobi.Analysis\n'
out.write_text(s, encoding='utf-8')
print(out)
