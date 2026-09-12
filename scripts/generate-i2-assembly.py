"""Generate the finite case dispatch in the full I2 lattice proof."""
from pathlib import Path
root=Path(__file__).resolve().parents[1]
g=root/'scripts/generate-i2-domains.py'; x={'__file__':str(g)}
exec(g.read_text(encoding='utf-8').split("s = '''")[0],x)
rows=x['rows']
ratio_names=[['t2','p'],['t2'],['t2','p','g'],['t2','p','e'],['t2','p','e'],['t2','p','e'],['t2','p','e'],['t2','p','e','f'],['t2','p','f','g'],['t2'],['t2'],['t2','g'],['t2'],['t2'],['t2','g'],['t2','n'],['t2','n'],['t2','n','g'],['t2','n','g'],['t2','n','e'],['t2','n','e'],['t2','n','e'],['t2','n','e'],['t2','n','e','f'],['t2','n','f','g']]
norm_ratio_names=[['t2','p'],['t2'],['t2','p','g'],['t2','p','e'],['p','e'],['p','e'],['p','e'],['p','e','f'],['p','f','g'],['t2'],['t2'],['t2','g'],['t2'],['t2'],['g'],['t2','n'],['t2','n'],['n','g'],['t2','n','g'],['t2','n','e'],['n','e'],['n','e'],['n','e'],['n','e','f'],['n','f','g']]
s='''import FourierJacobi.Analysis.I2Complete
import FourierJacobi.Analysis.I2Predicates
import FourierJacobi.Analysis.CoreParameters

/-! Full original I2 four-coordinate lattice sum, including cancellation depth. -/

noncomputable section

namespace FourierJacobi.Analysis

open FourierJacobi.Valuations

set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

theorem i2_cartan_depth_constant (ν : Fin 25) (p : I2SpatialRow ν) (c : ℕ)
    (hc : i2DepthPredicate ν c) :
    cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 c =
      cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 (i2DepthAt ν) := by
  fin_cases ν
'''
for i,r in enumerate(rows):
    name=r[0]; depth=r[-1]
    arg=' (by simpa using hc)' if depth!='True' else ''
    arg2=f' (by rw [i2DepthAt_row{i}])' if depth!='True' else ''
    s+=f'  · change cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 c = cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 (i2DepthAt {i})\n'
    s+=f'    change i2DepthPredicate {i} c at hc\n'
    s+=f'    rw [i2Case{name}_cartan p c{arg}, i2Case{name}_cartan p (i2DepthAt {i}){arg2}]\n'
s+='''
theorem hasSum_i2_spatial (q t d U V T : ℂ) (ν : Fin 25)
    (hq : q * t ^ 2 = 1) (hd : d ≠ 0) (h : GeometricRange t d U V T) :
    HasSum (fun p : I2SpatialRow ν => i2SpatialTerm q t d U V T ν p.val)
      (i2RegionTerm ν t d (T * U) (T * V)) := by
  fin_cases ν
'''
for i,r in enumerate(rows):s+=f'  · exact hasSum_i2_case{r[0]}_regionTerm q t d U V T hq hd '+ ' '.join('h.'+n for n in ratio_names[i])+'\n'
s+='''
theorem summable_norm_i2_spatial (q t d U V T : ℂ) (ν : Fin 25)
    (h : GeometricRange t d U V T) :
    Summable (fun p : I2SpatialRow ν => ‖i2SpatialTerm q t d U V T ν p.val‖) := by
  fin_cases ν
'''
for i,r in enumerate(rows):s+=f'  · exact summable_norm_i2_case{r[0]} q t d U V T '+ ' '.join('h.'+n for n in norm_ratio_names[i])+'\n'
s+='''
def i2DepthWeight (q : ℂ) (ν : Fin 25) (p : I2SpatialRow ν) (c : ℕ) : ℂ := by
  classical
  exact if i2DepthPredicate ν c then collisionWeight q 2 p.val.2.1 p.val.2.2 c else 0

theorem hasSum_i2_probability_ge_two (q : ℂ) (hq : ‖q⁻¹‖ < 1) :
    HasSum (fun c : ℕ => if 2 ≤ c then collisionProbability q c else 0)
      (q⁻¹ ^ 2 / (1 - q⁻¹)) := by
  apply (hasSum_nat_add_iff' 2).mp
  simpa [Finset.sum_range_succ, div_eq_mul_inv, Nat.add_assoc]
    using hasSum_collisionProbability_tail q 1 hq

theorem hasSum_i2_depthWeight (q : ℂ) (ν : Fin 25) (p : I2SpatialRow ν)
    (hq₀ : q ≠ 0) (hq₁ : q - 1 ≠ 0) (hq : ‖q⁻¹‖ < 1) :
    HasSum (i2DepthWeight q ν p) (i2DepthMass q ν) := by
  classical
  fin_cases ν
'''
for i,r in enumerate(rows):
    s+=f'  · change HasSum (fun c : ℕ => i2DepthWeight q {i} p c) (i2DepthMass q {i})\n'
    if r[-1]=='True':
        s+=f'    simpa only [i2DepthWeight, i2DepthPredicate_row{i}, if_true, i2DepthMass_row{i}]\n'
        s+='      using hasSum_collisionWeight q 2 p.val.2.1 p.val.2.2 hq₀ hq₁ hq\n'
    else:
        s+='    have hp := p.property\n'
        s+=f'    change i2SpatialPredicate {i} p.val at hp\n'
        s+=f'    simp only [i2SpatialPredicate_row{i}] at hp\n'
        s+='    have he : 2 * p.val.2.2 = p.val.2.1 - 2 := by omega\n'
        s+='    have hw (c : ℕ) : collisionWeight q 2 p.val.2.1 p.val.2.2 c = collisionProbability q c := by\n'
        s+='      simp [collisionWeight, he]\n'
        s+=f'    simp only [i2DepthWeight, i2DepthPredicate_row{i}, hw, i2DepthMass_row{i}]\n'
        if r[-1]=='2 ≤ c': s+='    exact hasSum_i2_probability_ge_two q hq\n'
        else:
            c=0 if r[-1]=='c = 0' else 1
            mass='(q - 2) / (q - 1)' if c==0 else 'q⁻¹'
            s+=f'    convert hasSum_ite_eq (α := ℂ) (β := ℕ) {c} ({mass}) using 1\n'
            s+='    funext c\n    split_ifs with hc\n'
            s+='    · subst c\n      simp [collisionProbability]\n    · rfl\n'
s+='''
def i2BareTerm (q t d U V T : ℂ) (ν : Fin 25) (p : I2SpatialRow ν) : ℂ :=
  -q * shellMonomial t d U V T 2 p.val (i2DepthAt ν)

theorem i2DepthMass_ne (q : ℂ) (ν : Fin 25)
    (hq₀ : q ≠ 0) (hq₁ : q - 1 ≠ 0) (hq₂ : q - 2 ≠ 0) (hq : ‖q⁻¹‖ < 1) :
    i2DepthMass q ν ≠ 0 := by
  unfold i2DepthMass
  split_ifs
  · exact div_ne_zero hq₂ hq₁
  · exact inv_ne_zero hq₀
  · exact div_ne_zero (pow_ne_zero 2 (inv_ne_zero hq₀)) (i2_geometric_denominator_ne _ hq)
  · exact one_ne_zero

theorem summable_norm_i2_bare (q t d U V T : ℂ) (ν : Fin 25)
    (hq₀ : q ≠ 0) (hq₁ : q - 1 ≠ 0) (hq₂ : q - 2 ≠ 0) (hq : ‖q⁻¹‖ < 1)
    (h : GeometricRange t d U V T) :
    Summable (fun p : I2SpatialRow ν => ‖i2BareTerm q t d U V T ν p‖) := by
  have hm := i2DepthMass_ne q ν hq₀ hq₁ hq₂ hq
  have hs := (summable_norm_i2_spatial q t d U V T ν h).mul_right ‖(i2DepthMass q ν)⁻¹‖
  have he (p : I2SpatialRow ν) : i2BareTerm q t d U V T ν p =
      i2SpatialTerm q t d U V T ν p.val * (i2DepthMass q ν)⁻¹ := by
    unfold i2BareTerm i2SpatialTerm
    rw [mul_assoc, mul_inv_cancel₀ hm, mul_one]
  simpa only [he, norm_mul] using hs

def i2RowFamily (q t d U V T : ℂ) (ν : Fin 25) (p : I2SpatialRow ν × ℕ) : ℂ := by
  classical
  exact if i2DepthPredicate ν p.2 then
    masterTerm q t d U V T 2 (p.1.val.1, p.1.val.2.1, p.1.val.2.2, p.2) else 0

theorem i2RowFamily_eq (q t d U V T : ℂ) (ν : Fin 25) (p : I2SpatialRow ν × ℕ) :
    i2RowFamily q t d U V T ν p = i2BareTerm q t d U V T ν p.1 * i2DepthWeight q ν p.1 p.2 := by
  classical
  unfold i2RowFamily i2DepthWeight
  split_ifs with hc
  · unfold masterTerm shellCoeff i2BareTerm
    simp only [show (2 : ℤ) ≠ 0 by decide, show (2 : ℤ) ≠ 1 by decide, if_false]
    congr 2
    unfold shellMonomial
    rw [i2_cartan_depth_constant ν p.1 p.2 hc]
  · simp

theorem summable_norm_i2_rowFamily (q t d U V T : ℂ) (ν : Fin 25)
    (hq₀ : q ≠ 0) (hq₁ : q - 1 ≠ 0) (hq₂ : q - 2 ≠ 0) (hq : ‖q⁻¹‖ < 1)
    (h : GeometricRange t d U V T) :
    Summable (fun p : I2SpatialRow ν × ℕ => ‖i2RowFamily q t d U V T ν p‖) := by
  classical
  have hb := summable_norm_i2_bare q t d U V T ν hq₀ hq₁ hq₂ hq h
  have hs := summable_norm_weighted_collision q 2 (fun p : I2SpatialRow ν => p.val.2.1)
    (fun p : I2SpatialRow ν => p.val.2.2) (i2BareTerm q t d U V T ν) hq hb
  apply hs.of_nonneg_of_le (fun p => norm_nonneg _)
  intro p
  rw [i2RowFamily_eq]
  unfold i2DepthWeight
  split_ifs <;> simp <;> positivity

theorem hasSum_i2_rowFamily (q t d U V T : ℂ) (ν : Fin 25)
    (hq₀ : q ≠ 0) (hq₁ : q - 1 ≠ 0) (hq₂ : q - 2 ≠ 0) (hq : ‖q⁻¹‖ < 1)
    (hqt : q * t ^ 2 = 1) (hd : d ≠ 0) (h : GeometricRange t d U V T) :
    HasSum (i2RowFamily q t d U V T ν) (i2RegionTerm ν t d (T * U) (T * V)) := by
  have hs := (summable_norm_i2_rowFamily q t d U V T ν hq₀ hq₁ hq₂ hq h).of_norm
  have hdpth (p : I2SpatialRow ν) :=
    (hasSum_i2_depthWeight q ν p hq₀ hq₁ hq).mul_left (i2BareTerm q t d U V T ν p)
  have he : (∑' p : I2SpatialRow ν × ℕ, i2RowFamily q t d U V T ν p) =
      i2RegionTerm ν t d (T * U) (T * V) := by
    rw [hs.tsum_prod]
    simp only [i2RowFamily_eq, (hdpth _).tsum_eq]
    exact (hasSum_i2_spatial q t d U V T ν hqt hd h).tsum_eq
  exact he ▸ hs.hasSum

end FourierJacobi.Analysis
'''
(root/'FourierJacobi/Analysis/I2Assembly.lean').write_text(s,encoding='utf-8')
print('Generated I2Assembly depth and row-family bridges.')
