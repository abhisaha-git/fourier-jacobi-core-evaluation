import FourierJacobi.Analysis.HaarCoreAssembly

/-! Unconditional evaluation and Abel limits for the explicit matrix-index
Weyl kernel with actual source-normalized local-field Haar measures.
Identification with a separately defined spherical coefficient is not assumed
and is not asserted here. -/

noncomputable section
namespace FourierJacobi.Analysis
open FourierJacobi.Algebra FourierJacobi.Valuations FourierJacobi.Measure
open MeasureTheory Filter
open scoped Topology

/-- The elementary scalar denominators in the displayed paper formula and
its principal/special prefactors follow from the natural parameter domain. -/
theorem core_scalar_denominators_ne_zero (q : ℝ) (a b : ℂ) (hq : 2 < q)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    (q : ℂ) ≠ 0 ∧ (q : ℂ) + 1 ≠ 0 ∧ (q : ℂ) - 1 ≠ 0 ∧
      (q : ℂ) - 2 ≠ 0 ∧ a * b ≠ 0 := by
  have hq₀ : (q : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (show 0 < q by linarith)
  have hqp : (q : ℂ) + 1 ≠ 0 := by
    exact_mod_cast ne_of_gt (show 0 < q + 1 by linarith)
  have hqm : (q : ℂ) - 1 ≠ 0 := by
    exact_mod_cast ne_of_gt (show 0 < q - 1 by linarith)
  have hqm₂ : (q : ℂ) - 2 ≠ 0 := by
    exact_mod_cast ne_of_gt (show 0 < q - 2 by linarith)
  exact ⟨hq₀, hqp, hqm, hqm₂, mul_ne_zero (unit_ne_zero ha) (unit_ne_zero hb)⟩

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K]
local notation "qK" => (residueCardinality K : ℝ)

theorem paperExplicitHaarCore_eq_latticeCore_damped
    (a b d : ℂ) (T : ℝ) (hq : 2 < qK) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hT₀ : 0 < T) (hT₁ : T < 1) (hd₀ : inverseSqrt qK ≤ ‖d‖) (hd₁ : ‖d‖ ≤ 1)
    (π : Kˣ) (hπ : localFieldValuation K (π : K) = (1 : WithTop ℤ)) :
    paperExplicitHaarCore K a b d T π = latticeCore qK a b d T := by
  apply paperExplicitHaarCore_eq_latticeCore K a b d T hq ha hb hT₀ hT₁.le hd₀ hd₁ ?_ π hπ
  have ht := inverseSqrt_pos (show 1 < qK by linarith)
  nlinarith

theorem explicitCoreIntegrand_integrable_damped
    (a b d : ℂ) (T : ℝ) (hq : 2 < qK) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hT₀ : 0 < T) (hT₁ : T < 1) (hd₀ : inverseSqrt qK ≤ ‖d‖) (hd₁ : ‖d‖ ≤ 1)
    (π : Kˣ) (hπ : localFieldValuation K (π : K) = (1 : WithTop ℤ)) (r : Fin 3) :
    Integrable (explicitCoreIntegrand K qK a b d T (coreCentral K π r))
      (paperCoreMeasure K) := by
  apply explicitCoreIntegrand_integrable K a b d T hq ha hb hT₀ hT₁.le hd₀ hd₁ ?_
    r (coreCentral K π r) (centralRepresentative_coreCentral K π hπ r)
  have ht := inverseSqrt_pos (show 1 < qK by linarith)
  nlinarith

theorem explicitCoreIntegrand_integrable_undamped
    (a b d : ℂ) (hq : 2 < qK) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hd₀ : inverseSqrt qK < ‖d‖) (hd₁ : ‖d‖ ≤ 1)
    (π : Kˣ) (hπ : localFieldValuation K (π : K) = (1 : WithTop ℤ)) (r : Fin 3) :
    Integrable (explicitCoreIntegrand K qK a b d 1 (coreCentral K π r))
      (paperCoreMeasure K) := by
  apply explicitCoreIntegrand_integrable K a b d 1 hq ha hb (by norm_num)
    (by norm_num) hd₀.le hd₁ (by simpa only [one_mul] using hd₀)
    r (coreCentral K π r) (centralRepresentative_coreCentral K π hπ r)

/-- The actual unscaled Haar core is evaluated first. -/
theorem paperExplicitHaarCore_eq_paperE
    (a b d : ℂ) (hq : 2 < qK) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hd₀ : inverseSqrt qK < ‖d‖) (hd₁ : ‖d‖ ≤ 1)
    (ha₁ : a ≠ 1) (hb₁ : b ≠ 1) (hab : a ≠ b) (hab₁ : a * b ≠ 1)
    (π : Kˣ) (hπ : localFieldValuation K (π : K) = (1 : WithTop ℤ)) :
    paperExplicitHaarCore K a b d 1 π = paperE qK a b d := by
  rw [paperExplicitHaarCore_eq_latticeCore K a b d 1 hq ha hb (by norm_num)
    (by norm_num) hd₀.le hd₁ (by simpa only [one_mul] using hd₀) π hπ]
  exact latticeCore_eq_paperE qK a b d hq ha hb hd₀ hd₁ ha₁ hb₁ hab hab₁

theorem tendsto_paperExplicitHaarCore_paperE
    (a b d : ℂ) (hq : 2 < qK) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hd₀ : inverseSqrt qK < ‖d‖) (hd₁ : ‖d‖ ≤ 1)
    (ha₁ : a ≠ 1) (hb₁ : b ≠ 1) (hab : a ≠ b) (hab₁ : a * b ≠ 1)
    (π : Kˣ) (hπ : localFieldValuation K (π : K) = (1 : WithTop ℤ)) :
    Tendsto (fun T => paperExplicitHaarCore K a b d T π)
      (𝓝[Set.Ioo 0 1] 1) (𝓝 (paperE qK a b d)) := by
  apply (tendsto_latticeCore_paperE qK a b d hq ha hb hd₀ hd₁ ha₁ hb₁ hab hab₁).congr'
  filter_upwards [self_mem_nhdsWithin] with T hT
  rw [paperExplicitHaarCore_eq_latticeCore_damped K a b d T hq ha hb
    hT.1 hT.2 hd₀.le hd₁ π hπ]

/-- Corrected RHS(77) = [2/(q+1)] RHS(184), at the actual explicit-kernel
Haar scope. The spherical-coefficient identification remains a separate bridge. -/
theorem corrected_principal_haar_comparison
    (a b d : ℂ) (hq : 2 < qK) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hd₀ : inverseSqrt qK < ‖d‖) (hd₁ : ‖d‖ ≤ 1)
    (ha₁ : a ≠ 1) (hb₁ : b ≠ 1) (hab : a ≠ b) (hab₁ : a * b ≠ 1)
    (π : Kˣ) (hπ : localFieldValuation K (π : K) = (1 : WithTop ℤ)) :
    (2 / ((qK : ℂ) + 1) * paperExplicitHaarCore K a b d 1 π =
      2 / ((qK : ℂ) + 1) * paperE qK a b d) ∧
    Tendsto (fun T => 2 / ((qK : ℂ) + 1) * paperExplicitHaarCore K a b d T π)
      (𝓝[Set.Ioo 0 1] 1) (𝓝 (2 / ((qK : ℂ) + 1) * paperE qK a b d)) := by
  exact ⟨congrArg (fun z => 2 / ((qK : ℂ) + 1) * z)
    (paperExplicitHaarCore_eq_paperE K a b d hq ha hb hd₀ hd₁ ha₁ hb₁ hab hab₁ π hπ),
    (tendsto_paperExplicitHaarCore_paperE K a b d hq ha hb hd₀ hd₁ ha₁ hb₁ hab hab₁ π hπ).const_mul _⟩

/-- Direct zero-product limit. It neither requires nor asserts an ordinary
undamped endpoint Haar integral. -/
theorem tendsto_haar_special_positive (a b : ℂ) (π : Kˣ) :
    Tendsto (fun T => ((1 - (1 : ℂ)) / ((qK : ℂ) + 1)) *
      paperExplicitHaarCore K a b (inverseSqrt qK : ℂ) T π)
      (𝓝[Set.Ioo 0 1] 1) (𝓝 0) :=
  tendsto_positive_zero_product qK
    (fun T => paperExplicitHaarCore K a b (inverseSqrt qK : ℂ) T π)

theorem tendsto_haar_special_negative
    (a b : ℂ) (hq : 2 < qK) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (ha₁ : a ≠ 1) (hb₁ : b ≠ 1) (hab : a ≠ b) (hab₁ : a * b ≠ 1)
    (haM : a ≠ -1) (hbM : b ≠ -1)
    (π : Kˣ) (hπ : localFieldValuation K (π : K) = (1 : WithTop ℤ)) :
    Tendsto (fun T => ((1 - (-1 : ℂ)) / ((qK : ℂ) + 1)) *
      paperExplicitHaarCore K a b (-(inverseSqrt qK : ℂ)) T π)
      (𝓝[Set.Ioo 0 1] 1)
      (𝓝 (((1 - (-1 : ℂ)) / ((qK : ℂ) + 1)) *
        paperE qK a b (-(inverseSqrt qK : ℂ)))) := by
  have hq' : 1 < qK := by linarith
  have hn : ‖-(inverseSqrt qK : ℂ)‖ = inverseSqrt qK := by
    simp [abs_of_pos (inverseSqrt_pos hq')]
  apply (tendsto_lattice_special_negative qK a b hq ha hb ha₁ hb₁ hab hab₁ haM hbM).congr'
  filter_upwards [self_mem_nhdsWithin] with T hT
  rw [paperExplicitHaarCore_eq_latticeCore_damped K a b (-(inverseSqrt qK : ℂ)) T
    hq ha hb hT.1 hT.2 (by rw [hn]) (by rw [hn]; exact (inverseSqrt_lt_one hq').le) π hπ]

/-- Corrected RHS(80) = RHS(191), with no extra factor, for the whole signed
product of actual damped explicit-kernel Haar integrals. -/
theorem corrected_special_haar_comparison
    (a b ε : ℂ) (hq : 2 < qK) (hε : ε = 1 ∨ ε = -1)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (ha₁ : a ≠ 1) (hb₁ : b ≠ 1) (hab : a ≠ b) (hab₁ : a * b ≠ 1)
    (haε : a ≠ ε) (hbε : b ≠ ε)
    (π : Kˣ) (hπ : localFieldValuation K (π : K) = (1 : WithTop ℤ)) :
    Tendsto (fun T => ((1 - ε) / ((qK : ℂ) + 1)) *
      paperExplicitHaarCore K a b (ε * (inverseSqrt qK : ℂ)) T π)
      (𝓝[Set.Ioo 0 1] 1)
      (𝓝 (((1 - ε) / ((qK : ℂ) + 1)) *
        paperE qK a b (ε * (inverseSqrt qK : ℂ)))) := by
  rcases hε with rfl | rfl
  · simpa only [sub_self, zero_div, zero_mul, one_mul] using
      tendsto_haar_special_positive K a b π
  · simpa only [neg_one_mul] using
      tendsto_haar_special_negative K a b hq ha hb ha₁ hb₁ hab hab₁ haε hbε π hπ

/-- Complete actual explicit-kernel Haar-core theorem: all three ordinary
integrals are integrable, their unscaled sum is E_q, the literal quotient is
regular, and the damped core converges to this value. -/
theorem explicit_haar_core_evaluation
    (a b d : ℂ) (hq : 2 < qK) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hd₀ : inverseSqrt qK < ‖d‖) (hd₁ : ‖d‖ ≤ 1)
    (ha₁ : a ≠ 1) (hb₁ : b ≠ 1) (hab : a ≠ b) (hab₁ : a * b ≠ 1)
    (π : Kˣ) (hπ : localFieldValuation K (π : K) = (1 : WithTop ℤ)) :
    (∀ r : Fin 3, Integrable
      (explicitCoreIntegrand K qK a b d 1 (coreCentral K π r)) (paperCoreMeasure K)) ∧
    paperExplicitHaarCore K a b d 1 π = paperE qK a b d ∧
    paperC qK * paperD1 qK a b d * paperD2 qK a b d ≠ 0 ∧
    Tendsto (fun T => paperExplicitHaarCore K a b d T π)
      (𝓝[Set.Ioo 0 1] 1) (𝓝 (paperE qK a b d)) := by
  exact ⟨explicitCoreIntegrand_integrable_undamped K a b d hq ha hb hd₀ hd₁ π hπ,
    paperExplicitHaarCore_eq_paperE K a b d hq ha hb hd₀ hd₁ ha₁ hb₁ hab hab₁ π hπ,
    paper_denominator_interior_ne_zero qK (by linarith) a b d ha hb hd₀ hd₁,
    tendsto_paperExplicitHaarCore_paperE K a b d hq ha hb hd₀ hd₁ ha₁ hb₁ hab hab₁ π hπ⟩

/-- At the special boundary every damped integral is justified, and the whole
signed product has the requested limit. No undamped endpoint integrability
or summability appears among either the hypotheses or conclusions. -/
theorem explicit_haar_special_abel
    (a b ε : ℂ) (hq : 2 < qK) (hε : ε = 1 ∨ ε = -1)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (ha₁ : a ≠ 1) (hb₁ : b ≠ 1) (hab : a ≠ b) (hab₁ : a * b ≠ 1)
    (haε : a ≠ ε) (hbε : b ≠ ε)
    (π : Kˣ) (hπ : localFieldValuation K (π : K) = (1 : WithTop ℤ)) :
    (∀ T ∈ Set.Ioo (0 : ℝ) 1, ∀ r : Fin 3,
      Integrable (explicitCoreIntegrand K qK a b (ε * (inverseSqrt qK : ℂ)) T
        (coreCentral K π r)) (paperCoreMeasure K)) ∧
    paperC qK * paperD1 qK a b (ε * (inverseSqrt qK : ℂ)) *
      paperD2 qK a b (ε * (inverseSqrt qK : ℂ)) ≠ 0 ∧
    Tendsto (fun T => ((1 - ε) / ((qK : ℂ) + 1)) *
      paperExplicitHaarCore K a b (ε * (inverseSqrt qK : ℂ)) T π)
      (𝓝[Set.Ioo 0 1] 1)
      (𝓝 (((1 - ε) / ((qK : ℂ) + 1)) *
        paperE qK a b (ε * (inverseSqrt qK : ℂ)))) := by
  have hq' : 1 < qK := by linarith
  refine ⟨?_, paper_denominator_special_ne_zero qK hq' a b ε ha hb hε haε hbε,
    corrected_special_haar_comparison K a b ε hq hε ha hb ha₁ hb₁ hab hab₁ haε hbε π hπ⟩
  intro T hT r
  have hnε : ‖ε‖ = 1 := by rcases hε with rfl | rfl <;> simp
  have hn : ‖ε * (inverseSqrt qK : ℂ)‖ = inverseSqrt qK := by
    simp [hnε, abs_of_pos (inverseSqrt_pos hq')]
  exact explicitCoreIntegrand_integrable_damped K a b (ε * (inverseSqrt qK : ℂ)) T
    hq ha hb hT.1 hT.2 (by rw [hn]) (by rw [hn]; exact (inverseSqrt_lt_one hq').le) π hπ r

end FourierJacobi.Analysis
