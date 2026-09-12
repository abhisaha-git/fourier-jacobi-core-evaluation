import Mathlib.NumberTheory.LocalField.Basic
import FourierJacobi.Valuations.LocalField
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FunProp

/-!
# Exceptional sets for the valuation tables

This file concerns actual Borel product measures and polynomial zero sets.
It does not replace the original period by a finite expression.  The first
part supplies the non-isolation needed by mathlib's Haar atomlessness theorem
for every nonarchimedean local field. The second part proves nullity even for
arbitrary atomless measures on a topological field. Zero coordinates are
removed by almost-everywhere statements, never assigned a finite valuation.
-/

noncomputable section
open MeasureTheory Set Filter Topology

namespace FourierJacobi.Measure

section LocalField
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Every neighbourhood of zero in a nonarchimedean local field contains a
nonzero point. No residue characteristic or characteristic-zero restriction
is needed for this topological fact. -/
theorem localField_punctured_nhds : (𝓝[≠] (0 : K)).NeBot := by
  rw [nhdsWithin_neBot]
  intro s hs
  obtain ⟨γ, hγ, hγs⟩ := (IsValuativeTopology.hasBasis_nhds_zero' K).mem_iff.mp hs
  obtain ⟨b, hb⟩ := ValuativeRel.valuation_surjective γ
  have hb0 : b ≠ 0 := by
    intro h
    apply hγ
    rw [← hb, h, map_zero]
  obtain ⟨a, ha0, ha⟩ := Valuation.IsNontrivial.exists_lt_one (v := ValuativeRel.valuation K)
  refine ⟨b * a, hγs ?_, by simpa using mul_ne_zero hb0 ha0⟩
  change ValuativeRel.valuation K (b * a) < γ
  rw [map_mul, hb]
  simpa using mul_lt_mul_of_pos_left ha (pos_iff_ne_zero.mpr hγ)

end LocalField

section PolynomialNullSets
variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [SecondCountableTopology K]
  [T2Space K] [MeasurableSpace K] [BorelSpace K]
  (μ ν : MeasureTheory.Measure K) [NullSingletonClass ν]

/-- The determinant polynomial's zero set is Borel, including z = 0. -/
theorem measurableSet_determinant_zero (z : K) :
    MeasurableSet {p : K × K | p.2 ^ 2 - p.1 * z = 0} := by
  exact (isClosed_eq (by fun_prop) continuous_const).measurableSet

omit [TopologicalSpace K] [IsTopologicalRing K] [SecondCountableTopology K]
  [T2Space K] [MeasurableSpace K] [BorelSpace K] in
/-- For fixed y and nonzero z, the exceptional x section is a singleton. -/
theorem determinant_zero_section (y z : K) (hz : z ≠ 0) :
    {x : K | y ^ 2 - x * z = 0} = {y ^ 2 / z} := by
  ext x
  simp only [mem_ofPred_eq, mem_singleton_iff, sub_eq_zero]
  exact ⟨fun h => (eq_div_iff hz).mpr h.symm, fun h => ((eq_div_iff hz).mp h).symm⟩

/-- Nullity of y²-xz=0 under actual product measures; unlike the original
integer tables this theorem covers z=0 as well. -/
theorem determinant_zero_null (z : K) :
    (μ.prod ν) {p : K × K | p.2 ^ 2 - p.1 * z = 0} = 0 := by
  apply MeasureTheory.Measure.measure_prod_null_of_ae_null (measurableSet_determinant_zero z)
  filter_upwards [] with x
  change ν {y : K | y ^ 2 - x * z = 0} = 0
  have hfinite : Set.Finite {y : K | y ^ 2 - x * z = 0} := by
    have hpoly : (Polynomial.X ^ 2 - Polynomial.C (x * z) : Polynomial K) ≠ 0 := by
      intro h
      have hc := congrArg (fun p : Polynomial K => p.coeff 2) h
      norm_num at hc
    convert Polynomial.finite_setOfPred_isRoot hpoly using 1
    ext y
    simp [Polynomial.IsRoot]
  exact hfinite.measure_zero ν

variable [NullSingletonClass μ]

/-- Both additive coordinates and the determinant are nonzero almost
everywhere. This is the precise finite-coordinate locus of the tables. -/
theorem coordinates_determinant_ae (z : K) :
    ∀ᵐ p : K × K ∂μ.prod ν, p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ p.2 ^ 2 - p.1 * z ≠ 0 := by
  have hx : (μ.prod ν) {p : K × K | p.1 = 0} = 0 := by
    have he : {p : K × K | p.1 = 0} = ({0} : Set K) ×ˢ univ := by ext; simp
    rw [he]
    apply le_antisymm _ bot_le
    exact (MeasureTheory.Measure.prod_prod_le _ _).trans (by simp)
  have hy : (μ.prod ν) {p : K × K | p.2 = 0} = 0 := by
    have he : {p : K × K | p.2 = 0} = univ ×ˢ ({0} : Set K) := by ext; simp
    rw [he]
    apply le_antisymm _ bot_le
    exact (MeasureTheory.Measure.prod_prod_le _ _).trans (by simp)
  have hd := determinant_zero_null μ ν z
  have hx' : ∀ᵐ p : K × K ∂μ.prod ν, p.1 ≠ 0 := by simpa [ae_iff] using hx
  have hy' : ∀ᵐ p : K × K ∂μ.prod ν, p.2 ≠ 0 := by simpa [ae_iff] using hy
  have hd' : ∀ᵐ p : K × K ∂μ.prod ν, p.2 ^ 2 - p.1 * z ≠ 0 := by simpa [ae_iff] using hd
  filter_upwards [hx', hy', hd'] with p hp hq hd
  exact ⟨hp, hq, hd⟩

/-- Removing the exceptional set preserves the measure itself, hence every
Bochner integral and every integrability assertion for this product measure. -/
theorem restrict_goodCoordinates (z : K) :
    (μ.prod ν).restrict {p : K × K |
      p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ p.2 ^ 2 - p.1 * z ≠ 0} = μ.prod ν :=
  MeasureTheory.Measure.restrict_eq_self_of_ae_mem (coordinates_determinant_ae μ ν z)

/-- Extra, possibly unbounded coordinates do not spoil null-set removal.
No finiteness hypothesis on their measure is required. -/
theorem coordinates_determinant_ae_with_parameter {A : Type*} [MeasurableSpace A]
    (ρ : MeasureTheory.Measure A) (z : K) :
    ∀ᵐ p : A × (K × K) ∂ρ.prod (μ.prod ν),
      p.2.1 ≠ 0 ∧ p.2.2 ≠ 0 ∧ p.2.2 ^ 2 - p.2.1 * z ≠ 0 := by
  have h := coordinates_determinant_ae μ ν z
  rw [ae_iff] at h ⊢
  have he : {p : A × (K × K) |
    ¬ (p.2.1 ≠ 0 ∧ p.2.2 ≠ 0 ∧ p.2.2 ^ 2 - p.2.1 * z ≠ 0)} =
    univ ×ˢ {p : K × K |
    ¬ (p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ p.2 ^ 2 - p.1 * z ≠ 0)} := by ext; simp
  rw [he]
  apply le_antisymm _ bot_le
  exact (MeasureTheory.Measure.prod_prod_le _ _).trans_eq (by rw [h, mul_zero]; rfl)

end PolynomialNullSets

section LocalHaarApplication
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K]
  (μ : MeasureTheory.Measure K) [μ.IsAddHaarMeasure]

/-- Atomlessness is proved from the general local-field and Haar hypotheses,
not added as an assumption of the local-field application. -/
theorem localField_haar_nullSingletonClass : NullSingletonClass μ := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  let := isUniformAddGroup_of_addCommGroup (G := K)
  let : (𝓝[≠] (0 : K)).NeBot := localField_punctured_nhds K
  infer_instance

/-- The exceptional sets in expanded:null are null for additive Haar on
every nonarchimedean local field, including every field in Theorem 2.2. -/
theorem localField_coordinates_determinant_ae (z : K) :
    ∀ᵐ p : K × K ∂μ.prod μ,
      p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ p.2 ^ 2 - p.1 * z ≠ 0 := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  let := isUniformAddGroup_of_addCommGroup (G := K)
  let : (Valued.v (R := K) (Γ₀ := ValuativeRel.ValueGroupWithZero K)).RankOne :=
    { hom' := ValuativeRel.IsRankLeOne.nonempty.some.emb (R := K) |>.comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := ValuativeRel.IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  let : NontriviallyNormedField K := Valued.toNontriviallyNormedField
    (L := K) (Γ₀ := ValuativeRel.ValueGroupWithZero K)
  let : ProperSpace K := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K
  let : NullSingletonClass μ := localField_haar_nullSingletonClass K μ
  exact coordinates_determinant_ae μ μ z

/-- Integer coordinates become legitimate only after null-set removal. The
valuation here is constructed from the field's actual valuative relation. -/
theorem localField_finite_valuations_ae (z : K) :
    ∀ᵐ p : K × K ∂μ.prod μ, ∃ j h c : ℤ,
      Valuations.localFieldValuation K p.1 = (j : WithTop ℤ) ∧
      Valuations.localFieldValuation K p.2 = (h : WithTop ℤ) ∧
      Valuations.localFieldValuation K (p.2 ^ 2 - p.1 * z) = (c : WithTop ℤ) := by
  filter_upwards [localField_coordinates_determinant_ae K μ z] with p hp
  obtain ⟨j, hj⟩ := WithTop.ne_top_iff_exists.mp
    ((Valuations.localFieldValuation_ne_top K p.1).mpr hp.1)
  obtain ⟨h, hh⟩ := WithTop.ne_top_iff_exists.mp
    ((Valuations.localFieldValuation_ne_top K p.2).mpr hp.2.1)
  obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.mp
    ((Valuations.localFieldValuation_ne_top K _).mpr hp.2.2)
  exact ⟨j, h, c, hj.symm, hh.symm, hc.symm⟩

end LocalHaarApplication
end FourierJacobi.Measure
