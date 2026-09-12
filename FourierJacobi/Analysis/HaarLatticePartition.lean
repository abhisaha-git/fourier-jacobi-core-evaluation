import FourierJacobi.Analysis.HaarKernel
import FourierJacobi.Analysis.MasterSeries
import FourierJacobi.Valuations.KernelShells

/-!
# The actual measurable valuation-and-cancellation lattice partition

The sets below are defined by the actual field valuations. The cancellation
index is forced to zero away from the collision locus and at central value zero.
Exhaustivity holds off the explicitly specified coordinate/determinant null set.
-/

noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Filter ValuativeRel

namespace FourierJacobi.Analysis
open FourierJacobi.Valuations

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- r=0 means exactly z=0; other r specify the actual central valuation -r. -/
def CentralRepresentative (r : ℤ) (z : K) : Prop :=
  (r = 0 ∧ z = 0) ∨ (r ≠ 0 ∧ localFieldValuation K z = ((-r : ℤ) : WithTop ℤ))

theorem centralRepresentative_coreCentral (π : Kˣ)
    (hπ : localFieldValuation K (π:K) = 1) (r : Fin 3) :
    CentralRepresentative K (r.val:ℤ) (coreCentral K π r) := by
  by_cases hr : r=0
  · subst r
    exact Or.inl ⟨rfl, coreCentral_zero K π⟩
  · have hr' : (r.val:ℤ) ≠ 0 := by
      intro he
      apply hr
      apply Fin.ext
      change r.val = 0
      exact Int.ofNat_eq_zero.mp he
    have hmem : (π:K) ∈ 𝒪[K] :=
      (localFieldValuation_nonnegative_iff K (π:K)).mp (by rw [hπ]; norm_num)
    let πo : 𝒪[K] := ⟨(π:K),hmem⟩
    have hv := FourierJacobi.Measure.canonical_uniformizer_zpow K πo hπ (-(r.val:ℤ))
    exact Or.inr ⟨hr', by simpa only [coreCentral, hr, if_false] using hv⟩

/-- Actual master lattice fibre in multiplicative/additive field coordinates. -/
def haarLatticeCell (r : ℤ) (z : K) (i : LatticeIndex) : Set (HaarPoint K) :=
  {p | localFieldValuation K (p.1 : K) = (i.1 : WithTop ℤ) ∧
    localFieldValuation K p.2.1 = (i.2.1 : WithTop ℤ) ∧
    localFieldValuation K p.2.2 = (i.2.2.1 : WithTop ℤ) ∧
    if r = 0 ∨ 2*i.2.2.1 ≠ i.2.1-r then i.2.2.2 = 0
    else localFieldValuation K (p.2.2^2/(p.2.1*z)-1) =
      ((i.2.2.2 : ℤ) : WithTop ℤ)}

theorem haarLatticeCell_disjoint (r : ℤ) (z : K) {i i' : LatticeIndex} (hii : i ≠ i') :
    Disjoint (haarLatticeCell K r z i) (haarLatticeCell K r z i') := by
  rcases i with ⟨k,j,h,c⟩
  rcases i' with ⟨k',j',h',c'⟩
  rw [Set.disjoint_left]
  intro p hp hp'
  obtain ⟨hk,hj,hh,hc⟩ := hp
  obtain ⟨hk',hj',hh',hc'⟩ := hp'
  have ek : k=k' := WithTop.coe_injective (hk.symm.trans hk')
  have ej : j=j' := WithTop.coe_injective (hj.symm.trans hj')
  have eh : h=h' := WithTop.coe_injective (hh.symm.trans hh')
  subst k' j' h'
  have ec : c=c' := by
    by_cases he : r=0 ∨ 2*h ≠ j-r
    · simp only [he, if_true] at hc hc'
      exact hc.trans hc'.symm
    · simp only [he, if_false] at hc hc'
      exact Int.natCast_inj.mp (WithTop.coe_injective (hc.symm.trans hc'))
  exact hii (by subst c'; rfl)

theorem haarLatticeCell_exhaustive (r : ℤ) (z : K) (hz : CentralRepresentative K r z)
    (p : HaarPoint K) (hp : p.2.1 ≠ 0 ∧ p.2.2 ≠ 0 ∧ p.2.2^2-p.2.1*z ≠ 0) :
    ∃ i : LatticeIndex, p ∈ haarLatticeCell K r z i := by
  let k := coreScaleExponent K p.1
  have hk : localFieldValuation K (p.1:K) = (k : WithTop ℤ) :=
    (coreScaleExponent_coe K p.1).symm
  obtain ⟨j,hj⟩ := WithTop.ne_top_iff_exists.mp
    ((localFieldValuation_ne_top K p.2.1).mpr hp.1)
  obtain ⟨h,hh⟩ := WithTop.ne_top_iff_exists.mp
    ((localFieldValuation_ne_top K p.2.2).mpr hp.2.1)
  have hj' := hj.symm
  have hh' := hh.symm
  by_cases he : r=0 ∨ 2*h ≠ j-r
  · refine ⟨(k,j,h,0), hk, hj', hh', ?_⟩
    simp only [he, if_true]
  · have hr : r ≠ 0 := fun hr => he (Or.inl hr)
    have heq : 2*h=j-r := Classical.not_not.mp (fun hh => he (Or.inr hh))
    have hz' : localFieldValuation K z = ((-r : ℤ) : WithTop ℤ) := by
      rcases hz with ⟨hr',_⟩ | ⟨_,hz'⟩
      · exact (hr hr').elim
      · exact hz'
    have hz0 : z ≠ 0 := nonzero_of_integer_valuation _ _ _ hz'
    have hd0 : p.2.2^2/(p.2.1*z)-1 ≠ 0 := by
      intro hed
      apply hp.2.2
      exact sub_eq_zero.mpr ((div_eq_one_iff_eq (mul_ne_zero hp.1 hz0)).mp
        (sub_eq_zero.mp hed))
    obtain ⟨c,hc⟩ := WithTop.ne_top_iff_exists.mp
      ((localFieldValuation_ne_top K _).mpr hd0)
    have hcn := actual_cancellation_depth_nonnegative (localFieldValuation K)
      p.2.1 p.2.2 z r j h c hj' hh' hz' heq hc.symm
    refine ⟨(k,j,h,c.toNat), hk, hj', hh', ?_⟩
    simpa only [he, if_false, Int.toNat_of_nonneg hcn] using hc.symm

theorem haarLatticeCell_kernelCoordinates (r : ℤ) (z : K)
    (hz : CentralRepresentative K r z) (i : LatticeIndex)
    (p : HaarPoint K) (hp : p ∈ haarLatticeCell K r z i) :
    KernelShellCoordinates K (coreAtCentral K z p) r i.1 i.2.1 i.2.2.1 i.2.2.2 := by
  rcases i with ⟨k,j,h,c⟩
  obtain ⟨hk,hj,hh,hc⟩ := hp
  rcases hz with ⟨hr,hz⟩ | ⟨hr,hz⟩
  · subst r z
    have ec : c=0 := by simpa only [true_or, if_true] using hc
    subst c
    exact kernelShellCoordinates_zero K p.1 p.2.1 p.2.2 k j h hk hj hh
  · apply kernelShellCoordinates_nonzero K p.1 p.2.1 p.2.2 z r k j h c hr hk hj hh hz
    intro heq
    simpa only [hr, heq, ne_eq, not_true_eq_false, or_self, if_false] using hc

section Measurability
variable [MeasurableSpace K] [BorelSpace K]

local instance : SecondCountableTopology K := kernelField_secondCountable K
local instance : T2Space K := kernelField_t2Space K

theorem haarLatticeCell_measurableSet (r : ℤ) (z : K) (i : LatticeIndex) :
    MeasurableSet (haarLatticeCell K r z i) := by
  have hv := kernel_localFieldValuation_measurable K
  have ha : Measurable (fun p : HaarPoint K => (p.1:K)) :=
    (show Measurable (fun a : Kˣ => (a:K)) from MeasurableSpace.le_map_comap).comp
      measurable_fst
  have hx : Measurable (fun p : HaarPoint K => p.2.1) := measurable_snd.fst
  have hy : Measurable (fun p : HaarPoint K => p.2.2) := measurable_snd.snd
  have hk := (measurableSet_singleton (i.1 : WithTop ℤ)).preimage (hv.comp ha)
  have hj := (measurableSet_singleton (i.2.1 : WithTop ℤ)).preimage (hv.comp hx)
  have hh := (measurableSet_singleton (i.2.2.1 : WithTop ℤ)).preimage (hv.comp hy)
  have hc : MeasurableSet {p : HaarPoint K |
      if r=0 ∨ 2*i.2.2.1 ≠ i.2.1-r then i.2.2.2=0
      else localFieldValuation K (p.2.2^2/(p.2.1*z)-1) =
        ((i.2.2.2:ℤ) : WithTop ℤ)} := by
    split_ifs
    · by_cases hc : i.2.2.2=0 <;> simp only [hc, Set.ofPred_true, Set.ofPred_false,
        MeasurableSet.univ, MeasurableSet.empty]
    · exact (measurableSet_singleton ((i.2.2.2:ℤ) : WithTop ℤ)).preimage
        (hv.comp (((hy.pow_const 2).div (hx.mul_const z)).sub_const 1))
  exact hk.inter (hj.inter (hh.inter hc))

omit [MeasurableSpace K] [BorelSpace K] in
/-- Every actual point off the known null set lies in exactly one lattice fibre. -/
theorem haarLatticeCell_existsUnique (r : ℤ) (z : K) (hz : CentralRepresentative K r z)
    (p : HaarPoint K) (hp : p.2.1≠0 ∧ p.2.2≠0 ∧ p.2.2^2-p.2.1*z≠0) :
    ∃! i : LatticeIndex, p ∈ haarLatticeCell K r z i := by
  obtain ⟨i,hi⟩ := haarLatticeCell_exhaustive K r z hz p hp
  refine ⟨i,hi,?_⟩
  intro j hj
  by_contra hji
  exact (Set.disjoint_left.mp (haarLatticeCell_disjoint K r z hji)) hj hi

theorem haarLatticeCell_exhaustive_ae (μ : Measure K) [μ.IsAddHaarMeasure]
    (ν : Measure Kˣ) (r : ℤ) (z : K) (hz : CentralRepresentative K r z) :
    ∀ᵐ p : HaarPoint K ∂ν.prod (μ.prod μ),
      ∃! i : LatticeIndex, p ∈ haarLatticeCell K r z i := by
  let : NullSingletonClass μ := FourierJacobi.Measure.localField_haar_nullSingletonClass K μ
  filter_upwards [FourierJacobi.Measure.coordinates_determinant_ae_with_parameter μ μ ν z]
    with p hp
  exact haarLatticeCell_existsUnique K r z hz p hp

end Measurability
end FourierJacobi.Analysis
