import FourierJacobi.Analysis.LatticeLimits

/-! Finite Weyl grouping of the already norm-summable independent family.
These interfaces are used by the actual Haar integration proof. -/

noncomputable section
namespace FourierJacobi.Analysis
open FourierJacobi.Algebra

def centralWeightedTerm (q : ℝ) (a b d : ℂ) (T : ℝ) (r : Fin 3)
    (p : LatticeIndex) : ℂ := ∑ i : Fin 8, weightedLatticeTerm q a b d T (i,r,p)

def centralLatticeCore (q : ℝ) (a b d : ℂ) (T : ℝ) (r : Fin 3) : ℂ :=
  ∑ i : Fin 8, (weylWeights (inverseSqrt q : ℂ) a b i / paperC q) *
    ∑' p : LatticeIndex, masterTerm (q : ℂ) (inverseSqrt q : ℂ) d
      (weylU a b i) (weylV a b i) (T : ℂ) (r.val : ℤ) p

theorem centralLatticeCore_sum (q : ℝ) (a b d : ℂ) (T : ℝ) :
    (∑ r : Fin 3, centralLatticeCore q a b d T r) = latticeCore q a b d T := by
  unfold centralLatticeCore latticeCore
  rw [Finset.sum_comm, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.mul_sum]
  ring

theorem summable_central_norm_majorant (q T : ℝ) (a b d : ℂ) (hq : 2 < q)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hT₀ : 0 ≤ T) (hT₁ : T ≤ 1)
    (hd₀ : inverseSqrt q ≤ ‖d‖) (hd₁ : ‖d‖ ≤ 1)
    (hstrict : T * inverseSqrt q < ‖d‖) (r : Fin 3) :
    Summable (fun p : LatticeIndex =>
      ∑ i : Fin 8, ‖weightedLatticeTerm q a b d T (i,r,p)‖) := by
  have hs := summable_norm_weightedLatticeTerm q T a b d hq ha hb hT₀ hT₁ hd₀ hd₁ hstrict
  exact summable_sum (s := Finset.univ) (fun i _ => (hs.prod_factor i).prod_factor r)

theorem hasSum_centralWeightedTerm (q T : ℝ) (a b d : ℂ) (hq : 2 < q)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hT₀ : 0 ≤ T) (hT₁ : T ≤ 1)
    (hd₀ : inverseSqrt q ≤ ‖d‖) (hd₁ : ‖d‖ ≤ 1)
    (hstrict : T * inverseSqrt q < ‖d‖) (r : Fin 3) :
    HasSum (centralWeightedTerm q a b d T r) (centralLatticeCore q a b d T r) := by
  unfold centralWeightedTerm centralLatticeCore
  have hs := summable_norm_weightedLatticeTerm q T a b d hq ha hb hT₀ hT₁ hd₀ hd₁ hstrict
  have hi (i : Fin 8) := ((hs.prod_factor i).prod_factor r).of_norm.hasSum
  have he := hasSum_sum (s := Finset.univ) (fun i _ => hi i)
  simpa only [weightedLatticeTerm, tsum_mul_left] using he

end FourierJacobi.Analysis
