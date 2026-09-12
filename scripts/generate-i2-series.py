"""Generate I2 spatial HasSum proofs from independently parameterized domains.

Sympy only computes affine exponents for source generation. Lean independently
checks every displayed exponent equality, every inverse map, and every HasSum.
"""
from pathlib import Path
import sympy as sp

root = Path(__file__).resolve().parents[1]
scope = {'__file__': str(root/'scripts/generate-i2-domains.py')}
generator = (root/'scripts/generate-i2-domains.py').read_text(encoding='utf-8')
exec(generator[:generator.index("s = '''")], scope)
rows = scope['rows']; subst = scope['subst']

names = ['Q','P','N','E','F','G']
ratios = {'Q':'t ^ 2','P':'d * T * V * t','N':'T * V * t / d',
          'E':'(T * V) ^ 2 * t ^ 2','F':'T * U * t ^ 2','G':'T * U * t ^ 4'}
ratio_data = {(0,2,0,0):'Q',(1,1,0,1):'P',(-1,1,0,1):'N',
              (0,2,0,2):'E',(0,2,1,0):'F',(0,4,1,0):'G'}

def nat_exp(poly, vars):
    terms=[]
    for a,v in vars.items():
        c=int(poly.coeff(sp.Symbol(a)))
        if c: terms.append(v if c==1 else f'{c} * {v}')
    c=int(poly.subs({sp.Symbol(a):0 for a in vars}))
    if c: terms.append(str(c))
    return ' + '.join(terms) or '0'

s='''import FourierJacobi.Analysis.I2Domains
import FourierJacobi.Analysis.I2Convergence

/-!
Independent infinite spatial sums for every I2 row. The unsummed terms use
the integer Cartan minima. Cancellation-depth masses are explicit; they are
the sum of the specified depth strata, not assumed geometric row fractions.
The separate depth bridge must identify these spatial sums with the full
four-coordinate master family before a complete I2 lattice theorem is claimed.
-/

noncomputable section

namespace FourierJacobi.Analysis

open FourierJacobi.Valuations

set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
-- Uniform generated proofs share simplifiers and arithmetic clearing tactics.
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

def i2DepthAt (ν : Fin 25) : ℕ :=
  if ν.val = 5 ∨ ν.val = 21 then 1
  else if ν.val = 6 ∨ ν.val = 22 then 2 else 0

def i2DepthMass (q : ℂ) (ν : Fin 25) : ℂ :=
  if ν.val = 4 ∨ ν.val = 20 then (q - 2) / (q - 1)
  else if ν.val = 5 ∨ ν.val = 21 then q⁻¹
  else if ν.val = 6 ∨ ν.val = 22 then q⁻¹ ^ 2 / (1 - q⁻¹) else 1

def i2SpatialTerm (q t d U V T : ℂ) (ν : Fin 25) (p : ℤ × ℤ × ℤ) : ℂ :=
  -q * shellMonomial t d U V T 2 p (i2DepthAt ν) * i2DepthMass q ν

def i2RegionTerm (ν : Fin 25) (t d U V : ℂ) : ℂ :=
  let P := 1 - d * V * t
  let N := 1 - V * t / d
  let E := 1 - V ^ 2 * t ^ 2
  let F := 1 - U * t ^ 2
  let G := 1 - U * t ^ 4
  match ν.val with
'''
for i,row in enumerate(rows):
    s+=f'  | {i if i<24 else "_"} => Algebra.regionTerm{i+25} t d U V P N E F G\n'
s+='\n'
for i,row in enumerate(rows):
    depth=1 if i in [5,21] else 2 if i in [6,22] else 0
    mass='(q - 2) / (q - 1)' if i in [4,20] else 'q⁻¹' if i in [5,21] else 'q⁻¹ ^ 2 / (1 - q⁻¹)' if i in [6,22] else '1'
    s+=f'@[simp] theorem i2DepthAt_row{i} : i2DepthAt {i} = {depth} := rfl\n'
    s+=f'@[simp] theorem i2DepthMass_row{i} (q : ℂ) : i2DepthMass q {i} = {mass} := rfl\n'
    s+=f'@[simp] theorem i2RegionTerm_row{i} (t d U V : ℂ) :\n'
    s+=f'    i2RegionTerm {i} t d U V = Algebra.regionTerm{i+25} t d U V\n'
    s+='      (1 - d * V * t) (1 - V * t / d) (1 - V ^ 2 * t ^ 2)\n      (1 - U * t ^ 2) (1 - U * t ^ 4) := rfl\n\n'

metadata=[]
for i,(name,pred,dim,coords,inv,ell,b,depth) in enumerate(rows):
    cs={z:sp.sympify(expr) for z,expr in zip(['k','j','h'],coords)}
    ellp=sp.expand(sp.sympify(ell).subs(cs, simultaneous=True))
    bp=sp.expand(sp.sympify(b).subs(cs, simultaneous=True))
    kp=cs['k']; np=sp.expand(ellp/2)
    ep=sp.expand(3*kp+2*cs['j']+2*cs['h']+3*ellp+4*bp)
    shape={1:'ℕ',2:'ℕ × ℕ',3:'ℕ × ℕ × ℕ',4:'Fin 2 × ℕ × ℕ × ℕ'}[dim]
    vs={1:{'a':'n'},2:{'a':'n.1','b':'n.2'},3:{'a':'n.1','b':'n.2.1','c':'n.2.2'},4:{'a':'n.2.1','b':'n.2.2.1','c':'n.2.2.2','e':'n.1.val'}}[dim]
    ivs={a:f'({v} : ℤ)' for a,v in vs.items()}
    const=[int(p.subs({sp.Symbol(v):0 for v in vs})) for p in [kp,ep,np,bp]]
    k0,e0,n0,b0=const
    df=f'd ^ {k0}' if k0>=0 else f'(d⁻¹) ^ {-k0}'
    C=f'(-q * (1 - t ^ 2) ^ 2 * ({df}) * t ^ {e0} * (T * U) ^ {n0} * (T * V) ^ {b0} * i2DepthMass q {i})'
    rnames=[]
    variables=[v for v in vs if v!='e']
    for v in variables:
        key=tuple(int(p.coeff(sp.Symbol(v))) for p in [kp,ep,np,bp])
        rnames.append(ratio_data[key])
    required=sorted(set(rnames),key=names.index)
    z='T * V * t ^ 2' if name=='3a' else 'T * V'
    expression=C
    if dim==4: expression+=f' * ({z}) ^ n.1.val'
    for v,r in zip(variables,rnames): expression+=f' * ({ratios[r]}) ^ {vs[v]}'
    s+=f'theorem i2_case{name}_reindexed (q t d U V T : ℂ) (n : {shape}) :\n'
    s+=f'    i2SpatialTerm q t d U V T {i} (i2Case{name}Equiv n).val =\n      {expression} := by\n'
    s+=f'  unfold i2SpatialTerm\n  rw [i2DepthAt_row{i}]\n  unfold shellMonomial\n'
    s+=f'  rw [i2Case{name}_cartan'
    if depth!='True': s+=' _ _ (by omega)'
    s+=']\n'
    s+=f'  simp only [i2Case{name}Equiv_val]\n'
    # All t/U/V exponents are nonnegative affine integer polynomials.
    ek='3 * ('+subst(coords[0],ivs)+') + 2 * ('+subst(coords[1],ivs)+') + 2 * ('+subst(coords[2],ivs)+') + 3 * ('+subst(str(ellp),ivs)+') + 4 * ('+subst(str(bp),ivs)+')'
    # Written Cartan formulas are syntactically inherited rather than simplified.
    emap={x:'('+subst(cs0,ivs)+')' for x,cs0 in zip(['k','j','h'],coords)}
    elllean=subst(ell,emap); blean=subst(b,emap)
    ek='3 * ('+subst(coords[0],ivs)+') + 2 * ('+subst(coords[1],ivs)+') + 2 * ('+subst(coords[2],ivs)+') + 3 * ('+elllean+') + 4 * ('+blean+')'
    s+=f'  have he : {ek} = (({nat_exp(ep,vs)} : ℕ) : ℤ) := by omega\n'
    s+=f'  have hn : ({elllean}) / 2 = (({nat_exp(np,vs)} : ℕ) : ℤ) := by omega\n'
    s+=f'  have hb : ({blean}) = (({nat_exp(bp,vs)} : ℕ) : ℤ) := by omega\n'
    sign=1 if k0>=0 and all(kp.coeff(sp.Symbol(v))>=0 for v in vs) else -1
    krhs=f'(({nat_exp(sp.expand(sign*kp),vs)} : ℕ) : ℤ)'
    if sign==-1:krhs='-'+krhs
    s+=f'  have hk : {subst(coords[0],ivs)} = {krhs} := by omega\n'
    s+='  rw [he]\n  try rw [hn]\n  try rw [hb]\n  try rw [hk]\n'
    s+='  simp only [zpow_neg, zpow_natCast, pow_add, pow_mul, mul_pow, pow_zero, pow_one, inv_pow, div_eq_mul_inv]\n  ring\n\n'
    # Unordered norm summability on original spatial subtype.
    pars=' (q t d U V T : ℂ)\n'
    hyps=''.join(f'    (h{r} : ‖{ratios[r]}‖ < 1)' for r in required)
    hyps=hyps.replace(')    (',')\n    (')
    if dim==4: helper='i2_summable_norm_parity_geometric'; args=f'{C} ({z}) '
    elif dim==3:helper='summable_norm_three_geometric'; args=f'{C} '
    elif dim==2:helper='i2_summable_norm_two_geometric';args=f'{C} '
    else:helper='i2_summable_norm_one_geometric';args=f'{C} '
    args+=' '.join(f'({ratios[r]})' for r in rnames)+' '+' '.join(f'h{r}' for r in rnames)
    s+=f'theorem summable_norm_i2_case{name}'+pars+hyps+' :\n'
    s+=f'    Summable (fun p : I2SpatialRow {i} => ‖i2SpatialTerm q t d U V T {i} p.val‖) := by\n'
    s+=f'  apply i2Case{name}Equiv.summable_iff.mp\n  convert {helper} {args} using 1\n'
    s+=f'  exact funext fun n => congrArg norm (i2_case{name}_reindexed q t d U V T n)\n\n'
    hshelper={'i2_summable_norm_parity_geometric':'i2_hasSum_parity_geometric',
      'summable_norm_three_geometric':'hasSum_three_geometric',
      'i2_summable_norm_two_geometric':'i2_hasSum_two_geometric',
      'i2_summable_norm_one_geometric':'i2_hasSum_one_geometric'}[helper]
    # Need the shell-volume denominator even when not itself a ratio in this row.
    req2=sorted(set(required+['Q']),key=names.index)
    hs=''.join(f'    (h{r} : ‖{ratios[r]}‖ < 1)\n' for r in req2)
    s+=f'theorem hasSum_i2_case{name}_regionTerm (q t d U V T : ℂ)\n'
    s+='    (hq : q * t ^ 2 = 1) (hd : d ≠ 0)\n'+hs
    s+=f'    : HasSum (fun p : I2SpatialRow {i} => i2SpatialTerm q t d U V T {i} p.val)\n'
    s+=f'      (i2RegionTerm {i} t d (T * U) (T * V)) := by\n'
    s+=f'  have h := {hshelper} {args}\n'
    s+=f'  apply i2Case{name}Equiv.hasSum_iff.mp\n  convert h using 1\n'
    s+=f'  · exact funext fun n => i2_case{name}_reindexed q t d U V T n\n'
    s+='  · have ht : t ≠ 0 := by\n      intro ht\n      simp [ht] at hq\n'
    s+='    have hqeq : q = (t ^ 2)⁻¹ := by\n'
    s+='      calc\n        q = q * (t ^ 2 * (t ^ 2)⁻¹) := by rw [mul_inv_cancel₀ (pow_ne_zero 2 ht), mul_one]\n        _ = (t ^ 2)⁻¹ := by rw [← mul_assoc, hq, one_mul]\n'
    for r in req2:s+=f'    have hn{r} := i2_geometric_denominator_ne ({ratios[r]}) h{r}\n'
    s+=f'    rw [i2RegionTerm_row{i}, i2DepthMass_row{i}, hqeq]\n'
    s+=f'    unfold Algebra.regionTerm{i+25}\n'
    s+='    try simp only [inv_inv, pow_one]\n'
    s+='    field_simp\n    <;> ring\n\n'
    metadata.append((i,name,dim,str(ep),str(np),str(bp),const,rnames))
s+='end FourierJacobi.Analysis\n'
(root/'FourierJacobi/Analysis/I2Complete.lean').write_text(s,encoding='utf-8')
print('Generated I2Complete.lean with twenty-five source-domain sums.')
for row in metadata:print(row)
