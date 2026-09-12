import FourierJacobi
import Lean.Util.CollectAxioms

/-! A checked implication audit for formalized_theorem_v1.pdf.
The displayed coefficient table, C, E, matrix, integrand and three prefactors
are transcribed here and identified with the existing checked objects. The
PDF's theorem clauses are then consequences of existing declarations.
No new analytic or representation-theoretic hypothesis is introduced. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option format.width 160
set_option pp.deepTerms true

noncomputable section
namespace FourierJacobiPdfV1
open FourierJacobi.Algebra FourierJacobi.Analysis FourierJacobi.Valuations
open FourierJacobi.LocalMatrix FourierJacobi.Measure MeasureTheory Filter
open ValuativeRel
open scoped Topology

def C (q : ℝ) : ℝ := 1 + 2 * q⁻¹ + 2 * (q⁻¹)^2 + 2 * (q⁻¹)^3 + (q⁻¹)^4

theorem C_coe (q : ℝ) : (C q : ℂ) = paperC q := by
  simp [C, paperC]

theorem C_eq_poincare (q : ℝ) (hq : 0 ≤ q) : C q = poincare (inverseSqrt q) := by
  apply Complex.ofReal_injective
  rw [C_coe, paperC_eq_poincare q hq]
  simp [poincare]

def roots (a b : ℂ) : Fin 8 → Fin 4 → ℂ :=
  ![![b*a⁻¹,b⁻¹,a⁻¹*b⁻¹,a⁻¹], ![a*b⁻¹,a⁻¹,a⁻¹*b⁻¹,b⁻¹],
    ![a⁻¹*b⁻¹,b,b*a⁻¹,a⁻¹], ![a*b,a⁻¹,b*a⁻¹,b],
    ![a⁻¹*b⁻¹,a,a*b⁻¹,b⁻¹], ![a*b,b⁻¹,a*b⁻¹,a],
    ![b*a⁻¹,a,a*b,b], ![a*b⁻¹,b,a*b,a]]

def A (q : ℝ) (a b : ℂ) (i : Fin 8) : ℂ :=
  ∏ j : Fin 4, (1 - (q : ℂ)⁻¹ * roots a b i j) / (1 - roots a b i j)
def U (a b : ℂ) : Fin 8 → ℂ :=
  ![a*b,a*b,a*b⁻¹,a*b⁻¹,b*a⁻¹,b*a⁻¹,a⁻¹*b⁻¹,a⁻¹*b⁻¹]
def V (a b : ℂ) : Fin 8 → ℂ := ![a,b,a,b⁻¹,b,a⁻¹,b⁻¹,a⁻¹]

theorem U_eq (a b : ℂ) : U a b = weylU a b := by simp [U, weylU]
theorem V_eq (a b : ℂ) : V a b = weylV a b := by simp [V, weylV]
theorem A_eq (q : ℝ) (hq : 0 ≤ q) (a b : ℂ) (i : Fin 8) :
    A q a b i = weylWeights (inverseSqrt q : ℂ) a b i := by
  have hR (z : ℂ) : (1 - (q : ℂ)⁻¹ * z) / (1 - z) =
      rootFactor (inverseSqrt q : ℂ) z := by
    rw [rootFactor, inverseSqrt_coe_sq q hq]
  simp only [A, hR]
  fin_cases i <;> simp [roots, weylWeights, Fin.prod_univ_succ, mul_assoc]

theorem roots_regular (a b : ℂ) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (ha₁ : a ≠ 1) (hb₁ : b ≠ 1) (hab : a ≠ b) (hab₁ : a*b ≠ 1)
    (i : Fin 8) (j : Fin 4) : 1 - roots a b i j ≠ 0 := by
  have ha₀ := unit_ne_zero ha
  have hb₀ := unit_ne_zero hb
  intro he
  have he' := sub_eq_zero.mp he
  fin_cases i <;> fin_cases j <;> norm_num [roots] at he'
  all_goals
    field_simp [ha₀, hb₀] at he'
    first | exact ha₁ he' | exact ha₁ he'.symm | exact hb₁ he' |
      exact hb₁ he'.symm | exact hab he' | exact hab he'.symm |
      exact hab₁ he' | exact hab₁ he'.symm

def satake (a b : ℂ) : Fin 4 → ℂ := ![a,a⁻¹,b,b⁻¹]
def N1 (q : ℝ) (a b : ℂ) : ℂ := ∏ i : Fin 4, (1-satake a b i*(q:ℂ)⁻¹)
def N2 (q : ℝ) (a b : ℂ) : ℂ :=
  (1-a*b*(q:ℂ)⁻¹)*(1-a⁻¹*b*(q:ℂ)⁻¹)*
    (1-a*b⁻¹*(q:ℂ)⁻¹)*(1-a⁻¹*b⁻¹*(q:ℂ)⁻¹)
def D1 (q : ℝ) (a b d : ℂ) : ℂ :=
  ∏ i : Fin 4, (1-satake a b i*d*(inverseSqrt q:ℂ))
def D2 (q : ℝ) (a b d : ℂ) : ℂ :=
  ∏ i : Fin 4, (1-satake a b i*d⁻¹*(inverseSqrt q:ℂ))
def E (q : ℝ) (a b d : ℂ) : ℂ :=
  (((1+a)^2*(1+b)^2/(a*b))*(1-(q:ℂ)⁻¹)*N1 q a b*N2 q a b)/
    ((C q:ℂ)*D1 q a b d*D2 q a b d)

theorem D1_eq (q : ℝ) (a b d : ℂ) : D1 q a b d = paperD1 q a b d := rfl
theorem D2_eq (q : ℝ) (a b d : ℂ) : D2 q a b d = paperD2 q a b d := rfl
theorem E_eq (q : ℝ) (a b d : ℂ) : E q a b d = paperE q a b d := by
  simp only [E, C_coe, D1_eq, D2_eq]
  rfl

def matrix {K : Type*} [Field K] (a x y z : K) : Matrix (Fin 4) (Fin 4) K :=
  !![1,0,y,z; 0,a,a*x,a*y; 0,0,a⁻¹,0; 0,0,0,1]

theorem matrix_eq {K : Type*} [Field K] (a x y z : K) : matrix a x y z = g a x y z := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix, g, FourierJacobi.LocalMatrix.D, N, Matrix.mul_apply, Fin.sum_univ_succ]

theorem minor_index_coverage (i j : Fin 4) :
    i < j ↔ ∃ k : Fin 6, indexPairs k = (i,j) := by
  fin_cases i <;> fin_cases j <;> decide

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K]
local notation "qK" => (residueCardinality K : ℝ)

def Phi (a b : ℂ) (p : KernelPoint K) : ℂ :=
  (C qK : ℂ)⁻¹ * ∑ i : Fin 8,
    A qK a b i * (inverseSqrt qK : ℂ) ^ (6*kernelN K p+4*kernelB K p) *
      U a b i ^ kernelN K p * V a b i ^ kernelB K p

omit [MeasurableSpace K] [BorelSpace K] in
theorem Phi_eq (a b : ℂ) (p : KernelPoint K) :
    Phi K a b p = explicitWeylKernel K (inverseSqrt qK : ℂ) a b p := by
  simp only [Phi, C_coe, paperC_eq_poincare qK (Nat.cast_nonneg _),
    A_eq qK (Nat.cast_nonneg _), U_eq, V_eq]
  unfold explicitWeylKernel weylKernelAtIndices
  rfl

omit [MeasurableSpace K] [BorelSpace K] in
theorem minima_finite (p : KernelPoint K) :
    matrixMinimum (localFieldValuation K) (matrix (p.1 : K) p.2.1 p.2.2.1 p.2.2.2) ≠ ⊤ ∧
    matrixMinimum (localFieldValuation K)
      (secondCompound (matrix (p.1 : K) p.2.1 p.2.2.1 p.2.2.2)) ≠ ⊤ := by
  rw [matrix_eq]
  exact actual_minima_finite (localFieldValuation K) p.1 p.2.1 p.2.2.1 p.2.2.2 (Units.ne_zero p.1)

omit [MeasurableSpace K] [BorelSpace K] in
theorem minima_eq (p : KernelPoint K) :
    (kernelEntryIndex K p : WithTop ℤ) =
      matrixMinimum (localFieldValuation K) (matrix (p.1 : K) p.2.1 p.2.2.1 p.2.2.2) ∧
    (kernelMinorIndex K p : WithTop ℤ) = matrixMinimum (localFieldValuation K)
      (secondCompound (matrix (p.1 : K) p.2.1 p.2.2.1 p.2.2.2)) := by
  rw [matrix_eq]
  exact ⟨actualEntryInteger_coe _ _ _ _ _, actualMinorInteger_coe _ _ _ _ _⟩

local instance : BorelSpace Kˣ := coreUnits_borelSpace K

theorem measure_normalizations :
    (additiveHaar K).IsAddHaarMeasure ∧ (paperMultiplicativeHaar K).IsHaarMeasure ∧
    additiveHaar K (𝒪[K] : Set K) = 1 ∧
    paperMultiplicativeHaar K (valuationRingUnits K : Set Kˣ) = ENNReal.ofReal (1-qK⁻¹) := by
  exact ⟨inferInstance, inferInstance, additiveHaar_integers K,
    paperMultiplicativeHaar_valuationRingUnits K⟩

theorem product_measure : paperCoreMeasure K =
    (paperMultiplicativeHaar K).prod ((additiveHaar K).prod (additiveHaar K)) := rfl

def prefactor (q : ℝ) : Fin 3 → ℂ :=
  ![(1-(q:ℂ)⁻¹)⁻¹,(q:ℂ),-(q:ℂ)/(1-(q:ℂ)⁻¹)]
def central (π : Kˣ) : Fin 3 → K := ![0,(π:K)⁻¹,(π:K)^(-2:ℤ)]

omit [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K] in
theorem prefactor_eq (q : ℝ) (r : Fin 3) : prefactor q r = coreIntegralPrefactor q r := by
  fin_cases r <;> simp [prefactor, coreIntegralPrefactor]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [MeasurableSpace K] [BorelSpace K] in
theorem central_eq (π : Kˣ) (r : Fin 3) : central K π r = coreCentral K π r := by
  fin_cases r <;> simp [central, coreCentral]

def f (a b d : ℂ) (T : ℝ) (π : Kˣ) (r : Fin 3) (p : HaarPoint K) : ℂ :=
  d ^ coreScaleExponent K p.1 * (Real.rpow (qK ^ (-coreScaleExponent K p.1)) (3/2) : ℂ) *
    (T : ℂ) ^ kernelHeight K (coreAtCentral K (central K π r) p) *
      Phi K a b (coreAtCentral K (central K π r) p)

omit [MeasurableSpace K] [BorelSpace K] in
theorem f_eq (a b d : ℂ) (T : ℝ) (π : Kˣ) (r : Fin 3) :
    f K a b d T π r = explicitCoreIntegrand K qK a b d T (coreCentral K π r) := by
  funext p
  simp only [f, Phi_eq, central_eq, explicitCoreIntegrand, coreLocalAbs]

def I (a b d : ℂ) (T : ℝ) (π : Kˣ) : ℂ :=
  ∑ r : Fin 3, prefactor qK r * ∫ p, f K a b d T π r p ∂paperCoreMeasure K

theorem I_eq (a b d : ℂ) (T : ℝ) (π : Kˣ) :
    I K a b d T π = paperExplicitHaarCore K a b d T π := by
  simp only [I, prefactor_eq, f_eq]
  rfl

omit [MeasurableSpace K] [BorelSpace K] in
/-- PDF Theorem 1(i): all pointwise inequalities and the explicit norm bound. -/
theorem part_i (a b : ℂ) (hq : 2 < qK) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (p : KernelPoint K) :
    (2 * kernelEntryIndex K p ≤ kernelMinorIndex K p ∧
      kernelMinorIndex K p ≤ kernelEntryIndex K p ∧ kernelEntryIndex K p ≤ 0) ∧
    (0 ≤ kernelN K p ∧ 0 ≤ kernelB K p ∧ 0 ≤ kernelEll K p ∧ 0 ≤ kernelHeight K p) ∧
    kernelEll K p = 2 * kernelN K p ∧ kernelHeight K p = -kernelEntryIndex K p ∧
    ‖Phi K a b p‖ ≤ ((∑ i : Fin 8, ‖A qK a b i‖) / C qK) *
      qK ^ (-3*kernelN K p-2*kernelB K p) := by
  refine ⟨actualInteger_bounds (localFieldValuation K) p.1 p.2.1 p.2.2.1 p.2.2.2,
    kernel_indices_nonnegative K p, rfl, kernel_height_eq K p, ?_⟩
  simpa only [Phi_eq, A_eq qK (Nat.cast_nonneg _), C_eq_poincare qK (Nat.cast_nonneg _)]
    using explicitWeylKernel_q_norm_le K qK (by linarith) a b p ha hb

theorem part_i_measurable (a b : ℂ) :
    Measurable (kernelEntryIndex K) ∧ Measurable (kernelMinorIndex K) ∧
    Measurable (kernelN K) ∧ Measurable (kernelB K) ∧ Measurable (kernelEll K) ∧
    Measurable (kernelHeight K) ∧ Measurable (Phi K a b) := by
  refine ⟨kernelEntryIndex_measurable K, kernelMinorIndex_measurable K,
    kernelN_measurable K, kernelB_measurable K, kernelEll_measurable K,
    kernelHeight_measurable K, ?_⟩
  have he : Phi K a b = explicitWeylKernel K (inverseSqrt qK : ℂ) a b := funext (Phi_eq K a b)
  rw [he]
  exact explicitWeylKernel_measurable K _ _ _

/-- PDF Theorem 1(ii), including measurability and ordinary integrability. -/
theorem part_ii (a b d : ℂ) (T : ℝ) (hq : 2 < qK) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hT₀ : 0 < T) (hT₁ : T ≤ 1) (hd₀ : inverseSqrt qK ≤ ‖d‖) (hd₁ : ‖d‖ ≤ 1)
    (hstrict : T * inverseSqrt qK < ‖d‖) (π : Kˣ)
    (hπ : localFieldValuation K (π : K) = (1 : WithTop ℤ)) (r : Fin 3) :
    Measurable (f K a b d T π r) ∧ Integrable (f K a b d T π r) (paperCoreMeasure K) := by
  rw [f_eq]
  exact ⟨explicitCoreIntegrand_measurable K qK a b d T _,
    explicitCoreIntegrand_integrable K a b d T hq ha hb hT₀ hT₁ hd₀ hd₁ hstrict
      r _ (centralRepresentative_coreCentral K π hπ r)⟩

/-- PDF Theorem 1(iii), stated with the PDF's own definitions. -/
theorem part_iii (a b d : ℂ) (hq : 2 < qK) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hd₀ : inverseSqrt qK < ‖d‖) (hd₁ : ‖d‖ ≤ 1)
    (ha₁ : a ≠ 1) (hb₁ : b ≠ 1) (hab : a ≠ b) (hab₁ : a*b ≠ 1)
    (π : Kˣ) (hπ : localFieldValuation K (π : K) = (1 : WithTop ℤ)) :
    (C qK : ℂ)*D1 qK a b d*D2 qK a b d ≠ 0 ∧
    I K a b d 1 π = E qK a b d ∧
    Tendsto (fun T => I K a b d T π) (𝓝[Set.Ioo 0 1] 1) (𝓝 (I K a b d 1 π)) ∧
    (2/((qK:ℂ)+1)*I K a b d 1 π = 2/((qK:ℂ)+1)*E qK a b d) ∧
    Tendsto (fun T => 2/((qK:ℂ)+1)*I K a b d T π)
      (𝓝[Set.Ioo 0 1] 1) (𝓝 (2/((qK:ℂ)+1)*E qK a b d)) := by
  simp only [C_coe, D1_eq, D2_eq, I_eq, E_eq]
  obtain ⟨_, he, hn, hl⟩ := explicit_haar_core_evaluation K a b d hq ha hb
    hd₀ hd₁ ha₁ hb₁ hab hab₁ π hπ
  have hp := corrected_principal_haar_comparison K a b d hq ha hb
    hd₀ hd₁ ha₁ hb₁ hab hab₁ π hπ
  exact ⟨hn, he, he ▸ hl, hp.1, hp.2⟩

/-- PDF Theorem 1(iv), with no undamped endpoint integrability hypothesis. -/
theorem part_iv (a b ε : ℂ) (hq : 2 < qK) (hε : ε = 1 ∨ ε = -1)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (ha₁ : a ≠ 1) (hb₁ : b ≠ 1) (hab : a ≠ b) (hab₁ : a*b ≠ 1)
    (haε : a ≠ ε) (hbε : b ≠ ε)
    (π : Kˣ) (hπ : localFieldValuation K (π : K) = (1 : WithTop ℤ)) :
    (∀ T ∈ Set.Ioo (0:ℝ) 1, ∀ r : Fin 3,
      Integrable (f K a b (ε*(inverseSqrt qK:ℂ)) T π r) (paperCoreMeasure K)) ∧
    (C qK:ℂ)*D1 qK a b (ε*(inverseSqrt qK:ℂ))*D2 qK a b (ε*(inverseSqrt qK:ℂ)) ≠ 0 ∧
    Tendsto (fun T => (1-ε)/((qK:ℂ)+1)*I K a b (ε*(inverseSqrt qK:ℂ)) T π)
      (𝓝[Set.Ioo 0 1] 1) (𝓝 ((1-ε)/((qK:ℂ)+1)*E qK a b (ε*(inverseSqrt qK:ℂ)))) := by
  simpa only [f_eq, C_coe, D1_eq, D2_eq, I_eq, E_eq] using
    explicit_haar_special_abel K a b ε hq hε ha hb ha₁ hb₁ hab hab₁ haε hbε π hπ

theorem positive_product (a b : ℂ) (T : ℝ) (π : Kˣ) :
    (1-(1:ℂ))/((qK:ℂ)+1)*I K a b (inverseSqrt qK:ℂ) T π = 0 := by simp

theorem positive_limit (a b : ℂ) (π : Kˣ) :
    Tendsto (fun T => (1-(1:ℂ))/((qK:ℂ)+1)*I K a b (inverseSqrt qK:ℂ) T π)
      (𝓝[Set.Ioo 0 1] 1) (𝓝 0) := by
  simpa only [I_eq] using tendsto_haar_special_positive K a b π

end FourierJacobiPdfV1

run_cmd do
  let env ← Lean.getEnv
  let allowed : Array Lean.Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    if (`FourierJacobiPdfV1).isPrefixOf name ||
        (env.getModuleIdxFor? name).isNone then
      if info.isUnsafe || info.isPartial then
        throwError "Unsafe/partial statement-audit declaration: {name}"
      let axs ← Lean.collectAxioms name
      unless (axs.filter (fun a => !allowed.contains a)).isEmpty do
        throwError "Unapproved axiom in statement audit: {name}: {axs}"
      if (`FourierJacobiPdfV1).isPrefixOf name then
        count := count + 1
        Lean.logInfo m!"STATEMENT {name}\nTYPE {info.type}\nAXIOMS {axs}"
  Lean.logInfo m!"PDF statement implication audit passed: {count} named declarations; current-module private helpers also checked."
