import FourierJacobi.Analysis.I0Master
import FourierJacobi.Analysis.I1Assembly
import FourierJacobi.Analysis.I2Master
import FourierJacobi.Analysis.MasterDamping
import FourierJacobi.Analysis.RationalLimits
import Mathlib.Algebra.BigOperators.Field

/-!
The independent complete lattice family, its absolute summability, evaluation,
and Abel limits. No Haar integral or spherical coefficient is defined here.
-/

noncomputable section
namespace FourierJacobi.Analysis
open FourierJacobi.Algebra Filter
open scoped Topology
set_option maxHeartbeats 4000000

/-- The independent left side (L) of the brief. It is used as a mathematical
sum only in the summability ranges established below. -/
def latticeCore (q : ℝ) (a b d : ℂ) (T : ℝ) : ℂ :=
  (∑ i : Fin 8, weylWeights (inverseSqrt q : ℂ) a b i *
    ∑ r : Fin 3, ∑' p : LatticeIndex,
      masterTerm (q : ℂ) (inverseSqrt q : ℂ) d (weylU a b i) (weylV a b i)
        (T : ℂ) (r.val : ℤ) p) / paperC q

def weightedLatticeTerm (q : ℝ) (a b d : ℂ) (T : ℝ)
    (p : Fin 8 × Fin 3 × LatticeIndex) : ℂ :=
  (weylWeights (inverseSqrt q : ℂ) a b p.1 / paperC q) *
    masterTerm (q : ℂ) (inverseSqrt q : ℂ) d (weylU a b p.1) (weylV a b p.1)
      (T : ℂ) (p.2.1.val : ℤ) p.2.2

theorem fifty_rows_split (f : Fin 50 → ℂ) :
    (∑ i : Fin 10, f (i.castLE (by decide))) +
    (∑ i : Fin 15, f ⟨10 + i.val, by omega⟩) +
    (∑ i : Fin 25, f ⟨25 + i.val, by omega⟩) = ∑ i : Fin 50, f i := by
  rw [Fin.sum_univ_add (a := 10) (b := 40),
    Fin.sum_univ_add (a := 15) (b := 25)]
  simp only [Fin.castLE, Fin.castAdd, Fin.natAdd, ← Nat.add_assoc]
  abel

theorem summable_norm_central_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hq0 : q ≠ 0) (hq1 : q - 1 ≠ 0)
    (hq2 : q - 2 ≠ 0) (hqt : q * t ^ 2 = 1) (h : GeometricRange t d U V T)
    (r : Fin 3) : Summable (fun p : LatticeIndex => ‖masterTerm q t d U V T (r.val : ℤ) p‖) := by
  fin_cases r
  · exact summable_norm_i0_master q t d U V T h
  · exact summable_norm_i1_master q t d U V T ht hqt h
  · exact summable_norm_i2_master q t d U V T ht hd hq0 hq1 hq2 hqt h

theorem central_master_sum_eq_rows (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hq0 : q ≠ 0) (hq1 : q - 1 ≠ 0)
    (hq2 : q - 2 ≠ 0) (hqt : q * t ^ 2 = 1) (h : GeometricRange t d U V T) :
    (∑ r : Fin 3, ∑' p : LatticeIndex, masterTerm q t d U V T (r.val : ℤ) p) =
      ∑ ν : Fin 50, regionTerms t d (T * U) (T * V) ν := by
  have h0 := (hasSum_i0_master q t d U V T h).tsum_eq
  have h1 := (hasSum_i1_master q t d U V T ht hd hq0 hq1 hqt h).tsum_eq
  have h2 := (hasSum_i2_master q t d U V T ht hd hq0 hq1 hq2 hqt h).tsum_eq
  conv_lhs => simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (∑' p, masterTerm q t d U V T 0 p) +
    ((∑' p, masterTerm q t d U V T 1 p) + ((∑' p, masterTerm q t d U V T 2 p) + 0)) = _
  rw [h0, h1, h2]
  simpa only [add_zero, add_assoc, i2Offset] using
    fifty_rows_split (regionTerms t d (T * U) (T * V))

theorem natural_master_parameters {q : ℝ} (hq : 2 < q) :
    (inverseSqrt q : ℂ) ≠ 0 ∧ (q : ℂ) ≠ 0 ∧
      (q : ℂ) - 1 ≠ 0 ∧ (q : ℂ) - 2 ≠ 0 ∧
      (q : ℂ) * (inverseSqrt q : ℂ) ^ 2 = 1 := by
  have hq' : 1 < q := by linarith
  refine ⟨?_, ?_, ?_, ?_, inverseSqrt_coe_mul q hq'⟩
  · exact_mod_cast ne_of_gt (inverseSqrt_pos hq')
  · exact_mod_cast (ne_of_gt (show 0 < q by linarith))
  · exact_mod_cast (ne_of_gt (show 0 < q - 1 by linarith))
  · exact_mod_cast (ne_of_gt (show 0 < q - 2 by linarith))

theorem summable_norm_weightedLatticeTerm (q T : ℝ) (a b d : ℂ) (hq : 2 < q)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hT₀ : 0 ≤ T) (hT₁ : T ≤ 1)
    (hd₀ : inverseSqrt q ≤ ‖d‖) (hd₁ : ‖d‖ ≤ 1)
    (hstrict : T * inverseSqrt q < ‖d‖) :
    Summable (fun p : Fin 8 × Fin 3 × LatticeIndex => ‖weightedLatticeTerm q a b d T p‖) := by
  obtain ⟨ht, hq0, hq1, hq2, hqt⟩ := natural_master_parameters hq
  have hq' : 1 < q := by linarith
  have hd : d ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (inverseSqrt_pos hq') hd₀)
  apply (summable_prod_of_nonneg (fun p => norm_nonneg _)).mpr
  refine ⟨?_, (hasSum_fintype _).summable⟩
  intro i
  apply (summable_prod_of_nonneg (fun p => norm_nonneg _)).mpr
  refine ⟨?_, (hasSum_fintype _).summable⟩
  intro r
  have hg := geometricRange_of_bounds (inverseSqrt_pos hq') (inverseSqrt_lt_one hq')
    hT₀ hT₁ hd₀ hd₁ hstrict (weylU_unitary ha hb i) (weylV_unitary ha hb i)
  have hs := summable_norm_central_master (q : ℂ) (inverseSqrt q : ℂ) d
    (weylU a b i) (weylV a b i) (T : ℂ) ht hd hq0 hq1 hq2 hqt hg r
  simpa only [weightedLatticeTerm, norm_mul] using
    hs.mul_left ‖weylWeights (inverseSqrt q : ℂ) a b i / paperC q‖

theorem latticeCore_eq_dampedRational (q T : ℝ) (a b d : ℂ) (hq : 2 < q)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hT₀ : 0 ≤ T) (hT₁ : T ≤ 1)
    (hd₀ : inverseSqrt q ≤ ‖d‖) (hd₁ : ‖d‖ ≤ 1)
    (hstrict : T * inverseSqrt q < ‖d‖) :
    latticeCore q a b d T = dampedRational (inverseSqrt q) a b d T := by
  obtain ⟨ht, hq0, hq1, hq2, hqt⟩ := natural_master_parameters hq
  have hq' : 1 < q := by linarith
  have hd : d ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (inverseSqrt_pos hq') hd₀)
  unfold latticeCore dampedRational
  rw [paperC_eq_poincare q (by linarith)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact central_master_sum_eq_rows (q : ℂ) (inverseSqrt q : ℂ) d
    (weylU a b i) (weylV a b i) (T : ℂ) ht hd hq0 hq1 hq2 hqt
    (geometricRange_of_bounds (inverseSqrt_pos hq') (inverseSqrt_lt_one hq')
      hT₀ hT₁ hd₀ hd₁ hstrict (weylU_unitary ha hb i) (weylV_unitary ha hb i))

/-- The full unordered family has the independently defined core as its sum.
The hypothesis is absolute summability of this family, proved above from the
natural parameter bounds; no rearrangement is made before that proof. -/
theorem hasSum_weightedLatticeTerm_of_norm (q T : ℝ) (a b d : ℂ)
    (hn : Summable (fun p : Fin 8 × Fin 3 × LatticeIndex =>
      ‖weightedLatticeTerm q a b d T p‖)) :
    HasSum (weightedLatticeTerm q a b d T) (latticeCore q a b d T) := by
  have hs := hn.of_norm
  have he : (∑' p, weightedLatticeTerm q a b d T p) = latticeCore q a b d T := by
    rw [hs.tsum_prod, tsum_fintype]
    unfold latticeCore
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    rw [(hs.prod_factor i).tsum_prod, tsum_fintype]
    simp only [weightedLatticeTerm, tsum_mul_left]
    rw [← Finset.mul_sum]
    ring
  exact he ▸ hs.hasSum

theorem hasSum_weightedLatticeTerm (q T : ℝ) (a b d : ℂ) (hq : 2 < q)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hT₀ : 0 ≤ T) (hT₁ : T ≤ 1)
    (hd₀ : inverseSqrt q ≤ ‖d‖) (hd₁ : ‖d‖ ≤ 1)
    (hstrict : T * inverseSqrt q < ‖d‖) :
    HasSum (weightedLatticeTerm q a b d T) (latticeCore q a b d T) :=
  hasSum_weightedLatticeTerm_of_norm q T a b d
    (summable_norm_weightedLatticeTerm q T a b d hq ha hb hT₀ hT₁ hd₀ hd₁ hstrict)

end FourierJacobi.Analysis
