"""Generate explicit I1 cone maps and Lean proofs; no computational certificates.

The generated declarations are proof drafts, not proof certificates. This is
an authoring aid, not a reproduction step: the final I1Complete.lean contains
subsequent manual elaboration, import, and linter fixes and is authoritative.
This script does not recreate that final checked file verbatim. Do not rerun it
over the delivered source as part of a Lake build or verification workflow.
"""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'FourierJacobi/Analysis/I1Complete.lean'

header = '''import FourierJacobi.Analysis.MasterSeries

/-!+# Infinite I1 valuation rows

The monomial below is the independent entry/minor valuation monomial, with
the actual I1 coefficient incorporated using q*t^2=1.  It is not defined by
any finite region fraction. Each lattice cone is parameterized explicitly;
both inverse laws and every infinite geometric evaluation are kernel checked.
The parity refinements of rows 3a and 8a are kept visible.
-/

noncomputable section
namespace FourierJacobi.Analysis
open FourierJacobi.Valuations

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

def i1Raw (t d U V T : ℂ) (p : ℤ × ℤ × ℤ) (c : ℕ) : ℂ :=
  let ell := (cartanIndices 1 p.1 p.2.1 p.2.2 c).1
  let b := (cartanIndices 1 p.1 p.2.1 p.2.2 c).2
  (1 - t ^ 2) ^ 3 * d ^ p.1 *
    t ^ (3 * p.1 + 2 * p.2.1 + 2 * p.2.2 + 3 * ell + 4 * b - 2) *
    (T * U) ^ (ell / 2) * (T * V) ^ b

theorem i1Raw_eq_shell (q t d U V T : ℂ) (ht : t ≠ 0)
    (hqt : q * t ^ 2 = 1) (p : ℤ × ℤ × ℤ) (c : ℕ) :
    i1Raw t d U V T p c = shellCoeff q 1 * shellMonomial t d U V T 1 p c := by
  have hq : q = (t ^ 2)⁻¹ := by
    calc
      q = q * (t ^ 2 * (t ^ 2)⁻¹) := by rw [mul_inv_cancel₀ (pow_ne_zero 2 ht), mul_one]
      _ = (t ^ 2)⁻¹ := by rw [← mul_assoc, hqt, one_mul]
  have hi : q⁻¹ = t ^ 2 := by rw [hq, inv_inv]
  unfold i1Raw shellMonomial shellCoeff
  simp only [one_ne_zero, ↓reduceIte]
  rw [zpow_sub₀ ht, hi, hq]
  simp only [zpow_ofNat, div_eq_mul_inv]
  ring

theorem i1_summable_norm_two_geometric (C a b : ℂ)
    (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    Summable (fun n : ℕ × ℕ => ‖C * a ^ n.1 * b ^ n.2‖) := by
  have h := (geometric_norm_summable a ha).mul_norm (geometric_norm_summable b hb)
  simpa only [norm_mul, mul_assoc] using h.mul_left ‖C‖

theorem i1_hasSum_two_geometric (C a b : ℂ)
    (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    HasSum (fun n : ℕ × ℕ => C * a ^ n.1 * b ^ n.2)
      (C * (1 - a)⁻¹ * (1 - b)⁻¹) := by
  have hA := (hasSum_geometric_of_norm_lt_one ha).tsum_eq
  have hB := (hasSum_geometric_of_norm_lt_one hb).tsum_eq
  have hs := (i1_summable_norm_two_geometric C a b ha hb).of_norm
  have he : (∑' n : ℕ × ℕ, C * a ^ n.1 * b ^ n.2) =
      C * (1 - a)⁻¹ * (1 - b)⁻¹ := by
    rw [hs.tsum_prod]
    simp only [tsum_mul_left, hB, tsum_mul_right, hA]
  exact he ▸ hs.hasSum

'''

# name, dimension, domain, coordinates, inverse, cartan formula, exponential total,
# k normalization, b normalization, ellhalf normalization, coefficient, ratios.
C='(1 - t ^ 2) ^ 3'
P='d * T * V * t'; N='T * V * t / d'; E='(T * V) ^ 2 * t ^ 2'
F='T * U * t ^ 2'; G='T * U * t ^ 4'; Z='t ^ 2'
rows=[]
def row(name,dim,dom,coord,inv,cart,exp,k,b,ell,Cf,ratios,depth='any'):
    rows.append(dict(name=name,dim=dim,dom=dom,coord=coord,inv=inv,cart=cart,
      exp=exp,k=k,b=b,ell=ell,Cf=Cf,ratios=ratios,depth=depth))

row('r1',3,'1 ≤ k ∧ -2 * k ≤ j ∧ -k ≤ h',
 '(a + 1, b - 2 * a - 2, c - a - 1)',
 '(k - 1, j + 2 * k, h + k)', '(2, k - 1)', 'a + 2*b + 2*c + 1',
 'a+1','a','1', f'{C} * d * (T * U) * t',[P,Z,Z])
row('r2',3,'1 ≤ k ∧ -2 * k ≤ j ∧ h < -k',
 '(a + 1, b - 2 * a - 2, -a - c - 2)',
 '(k - 1, j + 2 * k, -h - k - 1)', '(-2*k-2*h, k)', 'a + 2*b + 4*c + 3',
 'a+1','a+1','c+1', f'{C} * d * (T * U) * (T * V) * t ^ 3',[P,Z,G])
for parity,jj,hh,bb,Cf in [
 ('e','-2*a-2*b-4','-a-b-2+c','a+2*b+2',f'{C} * d * (T * U) * (T * V)^2 * t^3'),
 ('o','-2*a-2*b-3','-a-b-1+c','a+2*b+1',f'{C} * d * (T * U) * (T * V) * t^3')]:
 row('r3a'+parity,3,'1 ≤ k ∧ j < -2*k ∧ k+j ≤ h ∧ j ≤ 2*h ∧ j % 2 = '+('0' if parity=='e' else '1'),
  f'(a+1,{jj},{hh})',
  '(k-1,(-j-2*k-2)/2,h-j/2)' if parity=='e' else '(k-1,(-j-2*k-1)/2,h-(j+1)/2)',
  '(2,-k-j-1)','a+2*b+2*c+3','a+1',bb,'1',Cf,[P,E,Z])
for label,ell,b,ex,Cf,dep in [
 ('r3b','2','-k-j-1','a+2*b+1',f'{C} * d * (T * U) * (T * V) * t','zero'),
 ('r3c','0','-k-j','a+2*b-1',f'{C} * d * (T * V)^2 / t','positive')]:
 row(label,2,'1 ≤ k ∧ j < -2*k ∧ k+j ≤ h ∧ 2*h = j-1',
  '(a+1,-2*a-2*b-3,-a-b-2)','(k-1,(-j-2*k-1)/2)',
  f'({ell},{b})',ex,'a+1','a+2*b+1' if label=='r3b' else 'a+2*b+2',
  '1' if label=='r3b' else '0',Cf,[P,E],dep)
row('r4',3,'1 ≤ k ∧ j < -2*k ∧ k+j ≤ h ∧ 2*h ≤ j-2',
 '(a+1,-2*a-2*b-c-4,-a-b-c-3)','(k-1,h-k-j,j-2*h-2)',
 '(2*j-4*h,2*h-2*j-k)','a+2*b+2*c+3','a+1','a+2*b+1','c+2',
 f'{C} * d * (T * U)^2 * (T * V) * t^3',[P,E,F])
row('r5',3,'1 ≤ k ∧ j < -2*k ∧ h < k+j',
 '(a+1,-2*a-b-3,-a-b-c-3)','(k-1,-j-2*k-1,k+j-h-1)',
 '(-2*k-2*h,k)','a+2*b+4*c+5','a+1','a+1','b+c+2',
 f'{C} * d * (T * U)^2 * (T * V) * t^5',[P,F,G])
row('r6a',2,'k = 0 ∧ 0 ≤ j ∧ 0 ≤ h',
 '(0,a,b)','(j,h)','(0,1)','2*a+2*b+2','0','1','0',
 f'{C} * (T * V) * t^2',[Z,Z])
row('r6b',3,'k ≤ -1 ∧ 0 ≤ j ∧ 0 ≤ h',
 '(-a-1,b,c)','(-k-1,j,h)','(2,-k-1)','a+2*b+2*c+1','-(a+1)','a','1',
 f'{C} * (T * U) * t / d',[N,Z,Z])
row('r7',3,'k ≤ 0 ∧ 0 ≤ j ∧ h < 0',
 '(-a,b,-c-1)','(-k,j,-h-1)','(-2*h,-k)','a+2*b+4*c+2','-a','a','c+1',
 f'{C} * (T * U) * t^2',[N,Z,G])
for parity,jj,hh,bb,Cf in [
 ('e','-2*b-2','-b-1+c','a+2*b+1',f'{C} * (T * U) * (T * V) * t^2'),
 ('o','-2*b-1','-b+c','a+2*b',f'{C} * (T * U) * t^2')]:
 row('r8a'+parity,3,'k ≤ 0 ∧ j < 0 ∧ j ≤ h ∧ j ≤ 2*h ∧ j % 2 = '+('0' if parity=='e' else '1'),
  f'(-a,{jj},{hh})','(-k,(-j-2)/2,h-j/2)' if parity=='e' else '(-k,(-j-1)/2,h-(j+1)/2)',
  '(2,-k-j-1)','a+2*b+2*c+2','-a',bb,'1',Cf,[N,E,Z])
for label,ell,b,ex,Cf,dep in [
 ('r8b','2','-k-j-1','a+2*b',f'{C} * (T * U)','zero'),
 ('r8c','0','-k-j','a+2*b-2',f'{C} * (T * V) / t^2','positive')]:
 row(label,2,'k ≤ 0 ∧ j < 0 ∧ j ≤ h ∧ 2*h = j-1',
  '(-a,-2*b-1,-b-1)','(-k,(-j-1)/2)',
  f'({ell},{b})',ex,'-a','a+2*b' if label=='r8b' else 'a+2*b+1',
  '1' if label=='r8b' else '0',Cf,[N,E],dep)
row('r9',3,'k ≤ 0 ∧ j < 0 ∧ j ≤ h ∧ 2*h ≤ j-2',
 '(-a,-2*b-c-2,-b-c-2)','(-k,h-j,j-2*h-2)',
 '(2*j-4*h,2*h-2*j-k)','a+2*b+2*c+2','-a','a+2*b','c+2',
 f'{C} * (T * U)^2 * t^2',[N,E,F])
row('r10',3,'k ≤ 0 ∧ j < 0 ∧ h < j',
 '(-a,-b-1,-b-c-2)','(-k,-j-1,j-h-1)',
 '(-2*h,-k)','a+2*b+4*c+4','-a','a','b+c+2',
 f'{C} * (T * U)^2 * t^4',[N,F,G])

import re
def casts(s):
    return re.sub(r'\b([abc])\b',lambda m: f'({m[1]} : ℤ)',s)
def coords(s,vars):
    return s[1:-1].split(',')
parts=[header]
for r in rows:
    nm=r['name']; dim=r['dim']; typ='ℕ × ℕ × ℕ' if dim==3 else 'ℕ × ℕ'
    ns=['a','b','c'][:dim]; coord=casts(r['coord']); inv=coords(r['inv'],None)
    domain='I1'+nm.upper()+'Row'; eqv='i1'+nm+'Equiv'
    dep='depth' if r['depth']!='zero' else '0'
    depArgs='(depth : ℕ)' if r['depth']=='any' else ('(depth : ℕ) (hdepth : 1 ≤ depth)' if r['depth']=='positive' else '')
    cart=r['cart']; valcart=cart.replace('k','p.val.1').replace('j','p.val.2.1').replace('h','p.val.2.2')
    cartProof='unfold tableOne collisionRows\n  split_ifs <;> simp only [Prod.mk.injEq] <;> omega'
    if nm in ['r3ae','r3ao']:
      cartProof='''rw [tableOne, if_pos hp0.1, if_neg (by omega : ¬ -2*k ≤ j),
    if_neg (by omega : ¬ h < k+j)]
  rw [collisionRows, if_pos (by omega : j-1+1 ≤ 2*h)]
  norm_num'''
    if nm in ['r8ae','r8ao']:
      cartProof='''rw [tableOne, if_neg (by omega : ¬ 1 ≤ k), if_neg (by omega : ¬ 0 ≤ j),
    if_neg (by omega : ¬ h < j)]
  rw [collisionRows, if_pos (by omega : j-1+1 ≤ 2*h)]
  norm_num'''
    parts.append(f'''/-- Source I1 row {nm[1:]}, with integer valuation inequalities. -/
abbrev {domain} := {{p : ℤ × ℤ × ℤ //
  let k := p.1; let j := p.2.1; let h := p.2.2; {r['dom']}}}

def {eqv} : ({typ}) ≃ {domain} where
  toFun n := ⟨(by
    rcases n with ⟨{', '.join(ns)}⟩
    exact {coord}), by
      rcases n with ⟨{', '.join(ns)}⟩
      dsimp
      omega⟩
  invFun p := (by
    let k := p.val.1; let j := p.val.2.1; let h := p.val.2.2
    exact ({', '.join('('+v+').toNat' for v in inv)}))
  left_inv n := by
    rcases n with ⟨{', '.join(ns)}⟩
    simp only [Prod.mk.injEq]
    try dsimp
    omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩,hp⟩
    dsimp at hp ⊢
    simp only [Prod.mk.injEq]
    omega

@[simp] theorem {eqv}_val ({' '.join(ns)} : ℕ) :
    ({eqv} ({','.join(ns)})).val = {coord} := rfl

theorem i1{nm}_cartan (p : {domain}) {depArgs} :
    cartanIndices 1 p.val.1 p.val.2.1 p.val.2.2 {dep} = {valcart} := by
  rw [← tableOne_correct _ _ _ _ (by omega)]
  rcases p with ⟨⟨k,j,h⟩,hp⟩
  dsimp at hp ⊢
  {('have hp0 : ' + r['dom'].rsplit(' ∧ ',1)[0] + ' := ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1⟩\n  clear hp' ) if nm in ['r3ae','r3ao','r8ae','r8ao'] else ''}
  {cartProof}

''')
    kexpr,jexpr,hexpr=coords(coord,None)
    ellval,bval=coords(r['cart'],None)
    def subvars(s):
      return re.sub(r'\b([kjh])\b',lambda m:{'k':kexpr,'j':jexpr,'h':hexpr}[m[1]].join(('(',')')),s)
    ellval=subvars(ellval); bval=subvars(bval)
    ex=r['exp']; shift=0
    if r['depth']=='positive':
      shift=1 if nm=='r3c' else 2
      ex=ex.rsplit('-',1)[0]
    he=f'(({ex} : ℕ) : ℤ)'+(f' - {shift}' if shift else '')
    kn=r['k']
    if kn.startswith('-'): kn=f'-(({kn[1:]} : ℕ) : ℤ)'
    else: kn=f'(({kn} : ℕ) : ℤ)'
    args='t d U V T p' # unused
    hs=', '.join(f'h{ix} : ‖{rat}‖ < 1' for ix,rat in enumerate(r['ratios']))
    argsLean='\n    '.join(f'(h{ix} : ‖{rat}‖ < 1)' for ix,rat in enumerate(r['ratios']))
    mon=' * '.join(f'({rat}) ^ n.{proj}' for rat,proj in zip(r['ratios'],['1','2.1','2.2'] if dim==3 else ['1','2']))
    rr=f"({r['Cf']}) * {mon}"
    depUse=' depth' if r['depth']=='any' else (' depth hdepth' if r['depth']=='positive' else '')
    htArg='(ht : t ≠ 0)' if shift else ''
    parts.append(f'''theorem i1{nm}_reindexed (t d U V T : ℂ) {htArg} {depArgs}
    (n : {typ}) :
    i1Raw t d U V T ({eqv} n).val {dep} = {rr} := by
  rcases n with ⟨{', '.join(ns)}⟩
  unfold i1Raw
  {'simp only [Nat.cast_zero]' if r['depth']=='zero' else ''}
  rw [i1{nm}_cartan]
  {'all_goals try omega' if r['depth']=='positive' else ''}
  simp only [{eqv}_val]
  have he : 3 * ({kexpr}) + 2 * ({jexpr}) + 2 * ({hexpr}) +
      3 * ({ellval}) + 4 * ({bval}) - 2 = {he} := by omega
  have hk : {kexpr} = {kn} := by omega
  have hb : {bval} = (({r['b']} : ℕ) : ℤ) := by omega
  have hl : ({ellval}) / 2 = (({r['ell']} : ℕ) : ℤ) := by omega
  rw [he, hl, hb]
  try rw [hk]
  {f'rw [zpow_sub₀ ht]' if shift else ''}
  simp only [zpow_neg, zpow_natCast, zpow_ofNat, pow_add, pow_mul, mul_pow,
    pow_one, pow_zero, one_mul, mul_one, mul_inv_rev, div_eq_mul_inv, inv_pow]
  ring

theorem hasSum_i1{nm}_raw (t d U V T : ℂ) {htArg} {depArgs}
    {argsLean} :
    HasSum (fun p : {domain} => i1Raw t d U V T p.val {dep})
      (({r['Cf']}) * {' * '.join('(1 - '+rat+')⁻¹' for rat in r['ratios'])}) := by
  apply {eqv}.hasSum_iff.mp
  convert {'hasSum_three_geometric' if dim==3 else 'i1_hasSum_two_geometric'}
    ({r['Cf']}) {' '.join('('+rat+')' for rat in r['ratios'])}
    {' '.join('h'+str(ix) for ix in range(dim))} using 1
  exact funext fun n => i1{nm}_reindexed t d U V T{' ht' if shift else ''}{depUse} n

theorem summable_norm_i1{nm}_raw (t d U V T : ℂ) {htArg} {depArgs}
    {argsLean} :
    Summable (fun p : {domain} => ‖i1Raw t d U V T p.val {dep}‖) := by
  apply {eqv}.summable_iff.mp
  convert {'summable_norm_three_geometric' if dim==3 else 'i1_summable_norm_two_geometric'}
    ({r['Cf']}) {' '.join('('+rat+')' for rat in r['ratios'])}
    {' '.join('h'+str(ix) for ix in range(dim))} using 1
  exact funext fun n => congrArg norm
    (i1{nm}_reindexed t d U V T{' ht' if shift else ''}{depUse} n)

''')
parts.append('end FourierJacobi.Analysis\n')
OUT.write_text(''.join(parts),encoding='utf-8')
print(OUT)

partition='''import FourierJacobi.Analysis.I1Complete

/-! Exact disjoint and exhaustive partition of the complete I1 lattice,
including every cancellation depth and both parity refinements. -/
namespace FourierJacobi.Analysis
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

def i1CellIndex (p : LatticeIndex) : Fin 17 :=
  let k := p.1; let j := p.2.1; let h := p.2.2.1; let c := p.2.2.2
  if 1 ≤ k then
    if -2*k ≤ j then
      if -k ≤ h then 0 else 1
    else if h < k+j then 7
    else if j ≤ 2*h then
      if j % 2 = 0 then 2 else 3
    else if 2*h = j-1 then
      if c = 0 then 4 else 5
    else 6
  else if 0 ≤ j then
    if h < 0 then 10
    else if k = 0 then 8 else 9
  else if h < j then 16
  else if j ≤ 2*h then
    if j % 2 = 0 then 11 else 12
  else if 2*h = j-1 then
    if c = 0 then 13 else 14
  else 15

abbrev I1Cell (i : Fin 17) := {p : LatticeIndex // i1CellIndex p = i}

/-- The library fiber equivalence proves both inverse laws. -/
def i1PartitionEquiv : (Σ i : Fin 17, I1Cell i) ≃ LatticeIndex :=
  Equiv.sigmaFiberEquiv i1CellIndex

@[simp] theorem i1PartitionEquiv_val (p : Σ i : Fin 17, I1Cell i) :
    i1PartitionEquiv p = p.2.val := rfl

'''
for i,r in enumerate(rows):
    nm=r['name']; domain='I1'+nm.upper()+'Row'; eqv='i1'+nm+'DepthEquiv'
    iszero=r['depth']=='zero'; ispos=r['depth']=='positive'
    index=domain if iszero else domain+' × ℕ'
    pr='p' if iszero else 'p.1'
    dep='0' if iszero else ('p.2 + 1' if ispos else 'p.2')
    depcond=' ∧ c = 0' if iszero else (' ∧ 1 ≤ c' if ispos else '')
    conjdom='('+r['dom']+')'+depcond
    partition+=f'''theorem i1{nm}_cell_iff (k j h : ℤ) (c : ℕ) :
    i1CellIndex (k,j,h,c) = {i} ↔ {conjdom} := by
  unfold i1CellIndex
  dsimp
  split_ifs <;> norm_num <;> omega

def {eqv} : ({index}) ≃ I1Cell {i} where
  toFun p := ⟨({pr}.val.1,{pr}.val.2.1,{pr}.val.2.2,{dep}), by
    apply (i1{nm}_cell_iff _ _ _ _).mpr
    {'exact ⟨'+pr+'.property, by omega⟩' if iszero or ispos else 'exact '+pr+'.property'}⟩
  invFun p := {'(' if not iszero else ''}⟨(p.val.1,p.val.2.1,p.val.2.2.1), by
    have hp := (i1{nm}_cell_iff _ _ _ _).mp p.property
    exact {'hp.1' if iszero or ispos else 'hp'}⟩{', p.val.2.2.2 - 1)' if ispos else (', p.val.2.2.2)' if not iszero else '')}
  left_inv p := by
    {'rfl' if iszero else ('rcases p with ⟨p,c⟩\n    simp' if ispos else 'rfl')}
  right_inv p := by
    rcases p with ⟨⟨k,j,h,c⟩,hp⟩
    apply Subtype.ext
    have hh := (i1{nm}_cell_iff k j h c).mp hp
    {'change (k,j,h,0) = (k,j,h,c)\n    exact congrArg (fun z : ℕ => (k,j,h,z)) hh.2.symm' if iszero else ('change (k,j,h,c-1+1) = (k,j,h,c)\n    exact congrArg (fun z : ℕ => (k,j,h,z)) (Nat.sub_add_cancel hh.2)' if ispos else 'rfl')}

@[simp] theorem {eqv}_val (p : {index}) :
    ({eqv} p).val = ({pr}.val.1,{pr}.val.2.1,{pr}.val.2.2,{dep}) := rfl

'''
partition+='end FourierJacobi.Analysis\n'
(ROOT/'FourierJacobi/Analysis/I1Partition.lean').write_text(partition,encoding='utf-8')

assembly='''import FourierJacobi.Analysis.I1Partition
import FourierJacobi.Analysis.CoreParameters

/-! Complete I1 depth weights, absolute summability, and restored row sums. -/
noncomputable section
namespace FourierJacobi.Analysis
open FourierJacobi.Valuations
open FourierJacobi.Algebra
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

theorem i1_qinv_eq (q t : ℂ) (ht : t ≠ 0) (hqt : q * t ^ 2 = 1) :
    q⁻¹ = t ^ 2 := by
  have he : q = (t ^ 2)⁻¹ := by
    calc
      q = q * (t ^ 2 * (t ^ 2)⁻¹) := by rw [mul_inv_cancel₀ (pow_ne_zero 2 ht), mul_one]
      _ = (t ^ 2)⁻¹ := by rw [← mul_assoc, hqt, one_mul]
  rw [he, inv_inv]

theorem i1_prob0_eq (q t : ℂ) (ht : t ≠ 0) (hqt : q*t^2=1)
    (hz : 1-t^2 ≠ 0) : collisionProbability q 0 = (1-2*t^2)/(1-t^2) := by
  have he : q = (t^2)⁻¹ := by
    rw [← i1_qinv_eq q t ht hqt, inv_inv]
  simp only [collisionProbability, if_true]
  rw [he]
  field_simp [ht,hz]
  <;> ring

theorem i1_summable_norm_prob_tail (q : ℂ) (hq : ‖q⁻¹‖ < 1) :
    Summable (fun c : ℕ => ‖collisionProbability q (c+1)‖) := by
  simpa only [collisionProbability_succ, norm_mul] using
    (geometric_norm_summable q⁻¹ hq).mul_left ‖q⁻¹‖

theorem i1_hasSum_product {ι κ : Type*} (f : ι → ℂ) (g : κ → ℂ)
    (s z : ℂ) (hf : HasSum f s) (hg : HasSum g z)
    (hfn : Summable (fun p => ‖f p‖)) (hgn : Summable (fun p => ‖g p‖)) :
    HasSum (fun p : ι × κ => f p.1 * g p.2) (s*z) := by
  have hs := (hfn.mul_norm hgn).of_norm
  have he := tsum_mul_tsum_of_summable_norm hfn hgn
  rw [hf.tsum_eq,hg.tsum_eq] at he
  exact he.symm ▸ hs.hasSum

'''
ratioField={P:'p',N:'n',E:'e',F:'f',G:'g',Z:'t2'}
cellValues=[]
simpleValues=[]
regionByCell=[10,11,None,None,13,14,15,16,17,18,19,None,None,21,22,23,24]
Pden='(1 - d * (T * V) * t)'; Nden='(1 - (T * V) * t / d)'
Eden='(1 - (T * V)^2 * t^2)'; Fden='(1 - (T * U) * t^2)'; Gden='(1 - (T * U) * t^4)'
for i,r in enumerate(rows):
    nm=r['name']; domain='I1'+nm.upper()+'Row'; eqv='i1'+nm+'DepthEquiv'
    iszero=r['depth']=='zero'; ispos=r['depth']=='positive'
    index=domain if iszero else domain+' × ℕ'
    pr='p' if iszero else 'p.1'
    dep='0' if iszero else ('p.2 + 1' if ispos else 'p.2')
    cdepth='1' if ispos else '0'
    rawValue=f"({r['Cf']}) * "+' * '.join('(1 - '+rat+')⁻¹' for rat in r['ratios'])
    value=rawValue+((' * (collisionProbability q 0)') if iszero else (' * (q⁻¹ * (1 - q⁻¹)⁻¹)' if ispos else ''))
    cellValues.append(value)
    reg=regionByCell[i]
    if reg is None:
      mult=f'(T * V)^{2 if nm=="r3ae" else 1}' if nm not in ['r8ao'] else '1'
      dpart='d * ' if nm.startswith('r3') else ''
      tp='3' if nm.startswith('r3') else '2'
      den=Pden if nm.startswith('r3') else Nden
      simple=f'(1-t^2)^2 * {dpart}(T*U) * {mult} * t^{tp} * {den}⁻¹ * {Eden}⁻¹'
    else:
      simple=f'regionTerm{reg} t d (T*U) (T*V) {Pden} {Nden} {Eden} {Fden} {Gden}'
    simpleValues.append(simple)
    rawArgs=(' ht 1 (by omega)' if ispos else ('' if iszero else ' 0'))
    convargs=' '.join('h.'+ratioField[rat] for rat in r['ratios'])
    monRight=f'i1Raw t d U V T {pr}.val {cdepth} * '+(
      'collisionProbability q 0' if iszero else
      ('collisionProbability q (p.2+1)' if ispos else
       f'collisionWeight q 1 {pr}.val.2.1 {pr}.val.2.2 p.2'))
    assembly+=f'''theorem i1{nm}_master_reindexed (q t d U V T : ℂ) (ht : t ≠ 0)
    (hqt : q*t^2=1) (p : {index}) :
    masterTerm q t d U V T 1 ({eqv} p).val =
      {monRight} := by
  rw [{eqv}_val]
  unfold masterTerm
  rw [← i1Raw_eq_shell q t d U V T ht hqt]
'''
    if not iszero:
      assembly+=f'''  have he : i1Raw t d U V T {pr}.val ({dep}) =
      i1Raw t d U V T {pr}.val {cdepth} := by
    unfold i1Raw
    rw [i1{nm}_cartan, i1{nm}_cartan]
    {'all_goals omega' if ispos else ''}
  rw [he]
'''
    if iszero or ispos:
      assembly+=f'''  have hc : 2*{pr}.val.2.2 = {pr}.val.2.1-1 := {pr}.property.2.2.2
  simp only [collisionWeight, one_ne_zero, hc, ne_eq, not_true_eq_false, false_or, if_false]
'''
    assembly+='\n'
    assembly+=f'''theorem hasSum_i1{nm}_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hq0 : q ≠ 0) (hq1 : q-1 ≠ 0)
    (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    HasSum (fun p : I1Cell {i} => masterTerm q t d U V T 1 p.val)
      ({value}) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hs := hasSum_i1{nm}_raw t d U V T{rawArgs} {convargs}
  have hn := summable_norm_i1{nm}_raw t d U V T{rawArgs} {convargs}
  apply {eqv}.hasSum_iff.mp
'''
    if iszero:
      assembly+=f'''  convert hs.mul_right (collisionProbability q 0) using 1
  all_goals try rfl
'''
    elif ispos:
      assembly+=f'''  have hg := hasSum_collisionProbability_tail q 0 hq
  simp only [Nat.add_zero, zero_add, pow_one] at hg
  convert i1_hasSum_product (fun p : {domain} => i1Raw t d U V T p.val 1)
    (fun c : ℕ => collisionProbability q (c+1)) _ _ hs hg hn
    (i1_summable_norm_prob_tail q hq) using 1
'''
    else:
      assembly+=f'''  convert hasSum_weighted_collision q 1
    (fun p : {domain} => p.val.2.1) (fun p : {domain} => p.val.2.2)
    (fun p : {domain} => i1Raw t d U V T p.val 0) _ hq0 hq1 hq hs hn using 1
'''
    assembly+=f'''  exact funext fun p => i1{nm}_master_reindexed q t d U V T ht hqt p

theorem summable_norm_i1{nm}_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    Summable (fun p : I1Cell {i} => ‖masterTerm q t d U V T 1 p.val‖) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hn := summable_norm_i1{nm}_raw t d U V T{rawArgs} {convargs}
  apply {eqv}.summable_iff.mp
'''
    if iszero:
      assembly+='  convert hn.mul_right ‖collisionProbability q 0‖ using 1\n  all_goals try rfl\n'
      assembly+=f'''  exact funext fun p => by
    simpa only [norm_mul, Function.comp_apply] using
      congrArg norm (i1{nm}_master_reindexed q t d U V T ht hqt p)
'''
    elif ispos:
      assembly+='  convert hn.mul_norm (i1_summable_norm_prob_tail q hq) using 1\n'
      assembly+=f'''  exact funext fun p => congrArg norm (i1{nm}_master_reindexed q t d U V T ht hqt p)
'''
    else:
      assembly+=f'''  convert summable_norm_weighted_collision q 1
    (fun p : {domain} => p.val.2.1) (fun p : {domain} => p.val.2.2)
    (fun p : {domain} => i1Raw t d U V T p.val 0) hq hn using 1
  exact funext fun p => congrArg norm (i1{nm}_master_reindexed q t d U V T ht hqt p)
'''
    assembly+='\n'
    assembly+=f'''theorem i1{nm}_value_eq (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hqt : q*t^2=1)
    (h : GeometricRange t d U V T) :
    ({value}) = ({simple}) := by
  have hz := norm_one_sub_ne_zero h.t2
  have hp := norm_one_sub_ne_zero h.p
  have hn := norm_one_sub_ne_zero h.n
  have he := norm_one_sub_ne_zero h.e
  have hf := norm_one_sub_ne_zero h.f
  have hg := norm_one_sub_ne_zero h.g
  {'rw [i1_prob0_eq q t ht hqt hz]' if iszero else ('rw [i1_qinv_eq q t ht hqt]' if ispos else '')}
  {'unfold regionTerm'+str(reg) if reg is not None else ''}
  simp only [pow_one, mul_assoc] at *
  field_simp [hz,hp,hn,he,hf,hg,ht,hd]
  <;> ring

'''
assembly+='def i1CellValue (q t d U V T : ℂ) : Fin 17 → ℂ :=\n  !['+',\n    '.join(cellValues)+']\n\n'
assembly+='''theorem hasSum_i1_cell (q t d U V T : ℂ)
    (ht : t ≠ 0) (hq0 : q ≠ 0) (hq1 : q-1 ≠ 0)
    (hqt : q*t^2=1) (h : GeometricRange t d U V T) (i : Fin 17) :
    HasSum (fun p : I1Cell i => masterTerm q t d U V T 1 p.val)
      (i1CellValue q t d U V T i) := by
  fin_cases i
'''
for r in rows:
    assembly+=f"  · exact hasSum_i1{r['name']}_master q t d U V T ht hq0 hq1 hqt h\n"
assembly+='''
theorem summable_norm_i1_cell (q t d U V T : ℂ)
    (ht : t ≠ 0) (hqt : q*t^2=1) (h : GeometricRange t d U V T) (i : Fin 17) :
    Summable (fun p : I1Cell i => ‖masterTerm q t d U V T 1 p.val‖) := by
  fin_cases i
'''
for r in rows:
    assembly+=f"  · exact summable_norm_i1{r['name']}_master q t d U V T ht hqt h\n"
assembly+='''
/-- Absolute summability of the actual complete I1 lattice, before rearrangement. -/
theorem summable_norm_i1_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    Summable (fun p : LatticeIndex => ‖masterTerm q t d U V T 1 p‖) := by
  apply i1PartitionEquiv.summable_iff.mp
  apply (summable_sigma_of_nonneg (fun p => norm_nonneg _)).mpr
  exact ⟨summable_norm_i1_cell q t d U V T ht hqt h, (hasSum_fintype _).summable⟩

theorem hasSum_i1_master_cells (q t d U V T : ℂ)
    (ht : t ≠ 0) (hq0 : q ≠ 0) (hq1 : q-1 ≠ 0)
    (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    HasSum (masterTerm q t d U V T 1) (∑ i : Fin 17, i1CellValue q t d U V T i) := by
  have hs := (summable_norm_i1_master q t d U V T ht hqt h).of_norm
  apply i1PartitionEquiv.hasSum_iff.mp
  exact (hasSum_fintype (i1CellValue q t d U V T)).sigma_of_hasSum
    (hasSum_i1_cell q t d U V T ht hq0 hq1 hqt h)
    (i1PartitionEquiv.summable_iff.mpr hs)

'''
assembly+='def i1CellSimplified (t d U V T : ℂ) : Fin 17 → ℂ :=\n  !['+',\n    '.join(simpleValues)+']\n\n'
stored=[f'regionTerm{r} t d (T*U) (T*V) {Pden} {Nden} {Eden} {Fden} {Gden}' for r in range(10,25)]
assembly+='def i1StoredRows (t d U V T : ℂ) : Fin 15 → ℂ :=\n  !['+',\n    '.join(stored)+']\n\n'
assembly+='''theorem i1StoredRows_eq_regionTerms (t d U V T : ℂ) (i : Fin 15) :
    i1StoredRows t d U V T i =
      regionTerms t d (T*U) (T*V) ⟨10+i.val, by omega⟩ := by
  fin_cases i <;> rfl

theorem i1CellValue_eq_simplified (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hqt : q*t^2=1)
    (h : GeometricRange t d U V T) (i : Fin 17) :
    i1CellValue q t d U V T i = i1CellSimplified t d U V T i := by
  fin_cases i
'''
for r in rows:
    assembly+=f"  · exact i1{r['name']}_value_eq q t d U V T ht hd hqt h\n"
assembly+='''
theorem i1CellSimplified_sum (t d U V T : ℂ) :
    (∑ i : Fin 17, i1CellSimplified t d U V T i) =
      ∑ i : Fin 15, i1StoredRows t d U V T i := by
  simp only [i1CellSimplified, i1StoredRows, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]
  unfold '''+' '.join('regionTerm'+str(r) for r in range(10,25))+'''
  simp only [pow_one]
  ring

theorem i1CellValue_sum_eq_regions (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hqt : q*t^2=1)
    (h : GeometricRange t d U V T) :
    (∑ i : Fin 17, i1CellValue q t d U V T i) =
      ∑ i : Fin 15, regionTerms t d (T*U) (T*V) ⟨10+i.val, by omega⟩ := by
  calc
    _ = ∑ i : Fin 17, i1CellSimplified t d U V T i := by
      apply Finset.sum_congr rfl
      intro i hi
      exact i1CellValue_eq_simplified q t d U V T ht hd hqt h i
    _ = ∑ i : Fin 15, i1StoredRows t d U V T i := i1CellSimplified_sum t d U V T
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      exact i1StoredRows_eq_regionTerms t d U V T i

/-- The complete infinite I1 master lattice equals the exact stored fifteen
restored row fractions. Absolute summability was established before this
partition and parity recombination. Damping remains in each unsummed term. -/
theorem hasSum_i1_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hq0 : q ≠ 0) (hq1 : q-1 ≠ 0)
    (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    HasSum (masterTerm q t d U V T 1)
      (∑ i : Fin 15, regionTerms t d (T*U) (T*V) ⟨10+i.val, by omega⟩) := by
  rw [← i1CellValue_sum_eq_regions q t d U V T ht hd hqt h]
  exact hasSum_i1_master_cells q t d U V T ht hq0 hq1 hqt h

theorem i1_basic_nonzero (q t : ℂ) (hqt : q*t^2=1) (hz : ‖t^2‖<1) :
    t ≠ 0 ∧ q ≠ 0 ∧ q-1 ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro ht
    simp [ht] at hqt
  · intro hq
    simp [hq] at hqt
  · intro hq
    have he : q = 1 := sub_eq_zero.mp hq
    have he' : t^2=1 := by simpa only [he,one_mul] using hqt
    rw [he',norm_one] at hz
    exact (lt_irrefl (1 : ℝ)) hz

/-- All auxiliary nonzero q/t hypotheses follow from the independent
normalization equation and the convergent parameter range. -/
theorem hasSum_i1_master_of_geometricRange (q t d U V T : ℂ)
    (hd : d ≠ 0) (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    HasSum (masterTerm q t d U V T 1)
      (∑ i : Fin 15, regionTerms t d (T*U) (T*V) ⟨10+i.val, by omega⟩) := by
  obtain ⟨ht,hq0,hq1⟩ := i1_basic_nonzero q t hqt h.t2
  exact hasSum_i1_master q t d U V T ht hd hq0 hq1 hqt h

/-- Natural real damping and unitary monomial hypotheses. The strict
inequality T*t < ‖δ‖ covers damped endpoint and undamped interior cases. -/
theorem i1_master_of_bounds (q t T : ℝ) (d U V : ℂ)
    (hqt : q*t^2=1) (ht0 : 0<t) (ht1 : t<1) (hT0 : 0≤T) (hT1 : T≤1)
    (hdlo : t≤‖d‖) (hdhi : ‖d‖≤1) (hstrict : T*t<‖d‖)
    (hU : ‖U‖=1) (hV : ‖V‖=1) :
    Summable (fun p : LatticeIndex => ‖masterTerm (q:ℂ) (t:ℂ) d U V (T:ℂ) 1 p‖) ∧
    HasSum (masterTerm (q:ℂ) (t:ℂ) d U V (T:ℂ) 1)
      (∑ i : Fin 15, regionTerms (t:ℂ) d ((T:ℂ)*U) ((T:ℂ)*V) ⟨10+i.val, by omega⟩) := by
  have h := geometricRange_of_bounds ht0 ht1 hT0 hT1 hdlo hdhi hstrict hU hV
  have he : (q:ℂ)*(t:ℂ)^2=1 := by exact_mod_cast hqt
  have ht : (t:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ht0
  have hd : d ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le ht0 hdlo)
  exact ⟨summable_norm_i1_master q t d U V T ht he h,
    hasSum_i1_master_of_geometricRange q t d U V T hd he h⟩

'''
assembly+='end FourierJacobi.Analysis\n'
(ROOT/'FourierJacobi/Analysis/I1Assembly.lean').write_text(assembly,encoding='utf-8')

sourceRows='''import FourierJacobi.Analysis.I1Assembly

/-! One HasSum declaration for each of the fifteen restored source rows.
The two parity rows use the explicit disjoint sum of their checked cells. -/
noncomputable section
namespace FourierJacobi.Analysis
open FourierJacobi.Algebra
set_option linter.unusedSimpArgs false

'''
sourceGroups=[('1',[0]),('2',[1]),('3a',[2,3]),('3b',[4]),('3c',[5]),
 ('4',[6]),('5',[7]),('6a',[8]),('6b',[9]),('7',[10]),('8a',[11,12]),
 ('8b',[13]),('8c',[14]),('9',[15]),('10',[16])]
for sr,(label,ids) in enumerate(sourceGroups):
    if len(ids)==1:
      ix=ids[0]; nm=rows[ix]['name']
      funct=f'(fun p : I1Cell {ix} => masterTerm q t d U V T 1 p.val)'
    else:
      x,y=ids
      funct=f'''(Sum.elim (fun p : I1Cell {x} => masterTerm q t d U V T 1 p.val)
        (fun p : I1Cell {y} => masterTerm q t d U V T 1 p.val))'''
    sourceRows+=f'''theorem hasSum_i1_source_case{label} (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hq0 : q ≠ 0) (hq1 : q-1 ≠ 0)
    (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    HasSum {funct}
      (regionTerms t d (T*U) (T*V) {10+sr}) := by
'''
    if len(ids)==1:
      sourceRows+=f'''  have hs := hasSum_i1{nm}_master q t d U V T ht hq0 hq1 hqt h
  rw [i1{nm}_value_eq q t d U V T ht hd hqt h] at hs
  exact hs

'''
    else:
      x,y=ids; nm1,nm2=rows[x]['name'],rows[y]['name']
      sourceRows+=f'''  have h1 := hasSum_i1{nm1}_master q t d U V T ht hq0 hq1 hqt h
  have h2 := hasSum_i1{nm2}_master q t d U V T ht hq0 hq1 hqt h
  rw [i1{nm1}_value_eq q t d U V T ht hd hqt h] at h1
  rw [i1{nm2}_value_eq q t d U V T ht hd hqt h] at h2
  have hs := h1.sum (f := {funct}) h2
  convert hs using 1
  change regionTerm{10+sr} t d (T*U) (T*V) {Pden} {Nden} {Eden} {Fden} {Gden} = _
  unfold regionTerm{10+sr}
  simp only [pow_one]
  ring

'''
sourceRows+='end FourierJacobi.Analysis\n'
(ROOT/'FourierJacobi/Analysis/I1SourceRows.lean').write_text(sourceRows,encoding='utf-8')
