import StatementAudit_v1
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Norm
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Topology.Algebra.Group.Units

/-!
# Proofs of the Palomar statement

The public mathematical definitions and four theorem types match Challenge.lean.
Private bridge lemmas connect these concrete definitions to StatementAudit_v1,
which proves the PDF theorem from the full FourierJacobi development.
The final command checks every declaration in this module, including private
helpers, for unsafe/partial definitions and nonstandard transitive axioms.
-/

set_option autoImplicit false
noncomputable section
namespace FourierJacobiPalomar
open MeasureTheory Filter ValuativeRel
open scoped Topology WithZero

/-- The positive inverse square root of q on the asserted range q > 2. -/
def t (q : ℝ) : ℝ := (Real.sqrt q)⁻¹
/-- The degree-four Weyl normalization polynomial. -/
def C (q : ℝ) : ℝ := 1 + 2*q⁻¹ + 2*(q⁻¹)^2 + 2*(q⁻¹)^3 + (q⁻¹)^4
/-- The four roots in each of the eight Weyl terms, with multiplicities. -/
def roots (a b : ℂ) : Fin 8 → Fin 4 → ℂ :=
  ![![b*a⁻¹,b⁻¹,a⁻¹*b⁻¹,a⁻¹], ![a*b⁻¹,a⁻¹,a⁻¹*b⁻¹,b⁻¹],
    ![a⁻¹*b⁻¹,b,b*a⁻¹,a⁻¹], ![a*b,a⁻¹,b*a⁻¹,b],
    ![a⁻¹*b⁻¹,a,a*b⁻¹,b⁻¹], ![a*b,b⁻¹,a*b⁻¹,a],
    ![b*a⁻¹,a,a*b,b], ![a*b⁻¹,b,a*b,a]]
/-- The coefficient of a Weyl term, a product of four root quotients. -/
def A (q : ℝ) (a b : ℂ) (i : Fin 8) : ℂ :=
  ∏ j : Fin 4, (1 - (q : ℂ)⁻¹ * roots a b i j) / (1 - roots a b i j)
/-- The character values raised to the first Cartan index. -/
def U (a b : ℂ) : Fin 8 → ℂ :=
  ![a*b,a*b,a*b⁻¹,a*b⁻¹,b*a⁻¹,b*a⁻¹,a⁻¹*b⁻¹,a⁻¹*b⁻¹]
/-- The character values raised to the second Cartan index. -/
def V (a b : ℂ) : Fin 8 → ℂ := ![a,b,a,b⁻¹,b,a⁻¹,b⁻¹,a⁻¹]
/-- The four Satake parameters, retaining multiplicities. -/
def satake (a b : ℂ) : Fin 4 → ℂ := ![a,a⁻¹,b,b⁻¹]
/-- The first numerator factor of the evaluated rational expression. -/
def N1 (q : ℝ) (a b : ℂ) : ℂ := ∏ i : Fin 4, (1-satake a b i*(q:ℂ)⁻¹)
/-- The four mixed numerator factors. -/
def N2 (q : ℝ) (a b : ℂ) : ℂ :=
  (1-a*b*(q:ℂ)⁻¹)*(1-a⁻¹*b*(q:ℂ)⁻¹)*
    (1-a*b⁻¹*(q:ℂ)⁻¹)*(1-a⁻¹*b⁻¹*(q:ℂ)⁻¹)
/-- The four denominator factors containing d. -/
def D1 (q : ℝ) (a b d : ℂ) : ℂ :=
  ∏ i : Fin 4, (1-satake a b i*d*(t q:ℂ))
/-- The four denominator factors containing the reciprocal of d. -/
def D2 (q : ℝ) (a b d : ℂ) : ℂ :=
  ∏ i : Fin 4, (1-satake a b i*d⁻¹*(t q:ℂ))
/-- The explicitly evaluated core E_q; nonzero denominators are proved below. -/
def E (q : ℝ) (a b d : ℂ) : ℂ :=
  (((1+a)^2*(1+b)^2/(a*b))*(1-(q:ℂ)⁻¹)*N1 q a b*N2 q a b)/
    ((C q:ℂ)*D1 q a b d*D2 q a b d)
/-- The actual 4 by 4 matrix whose entry and minor valuations define the kernel. -/
def matrix {K : Type*} [Field K] (a x y z : K) : Matrix (Fin 4) (Fin 4) K :=
  !![1,0,y,z; 0,a,a*x,a*y; 0,0,a⁻¹,0; 0,0,0,1]
/-- All six increasing pairs of row or column indices. -/
def pairs : Fin 6 → Fin 4 × Fin 4 :=
  ![(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]
/-- The matrix of all 36 two-by-two minors. -/
def minors {K : Type*} [Field K] (M : Matrix (Fin 4) (Fin 4) K) :
    Matrix (Fin 6) (Fin 6) K := fun i j =>
  M (pairs i).1 (pairs j).1 * M (pairs i).2 (pairs j).2 -
    M (pairs i).1 (pairs j).2 * M (pairs i).2 (pairs j).1

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
/-- q is the cardinality of the actual residue field, viewed as a real number. -/
def q : ℝ := (Nat.card 𝓀[K] : ℝ)
local notation "qK" => q K
/-- The canonical additive integer valuation, with value infinity at zero. -/
def valuationInt (x : K) : WithTop ℤ :=
  WithZero.expRecOn
    (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K (ValuativeRel.valuation K x))
    ⊤ (fun n => ((-n : ℤ) : WithTop ℤ))
/-- The minimum valuation of all entries of a finite matrix. -/
def minimum {m n : ℕ} (M : Matrix (Fin m) (Fin n) K) : WithTop ℤ :=
  Finset.univ.inf fun i => Finset.univ.inf fun j => valuationInt K (M i j)
/-- The entry valuation minimum, converted to an integer (zero at infinity).
Infinity never occurs for these matrices, since the (0,0) entry is one. -/
def entry (p : Kˣ × K × K × K) : ℤ :=
  (minimum K (matrix (p.1 : K) p.2.1 p.2.2.1 p.2.2.2)).untopD 0
/-- The minor valuation minimum. Infinity never occurs: the minor on rows
(0,3) and columns (0,3) equals one. The default zero only totalizes the map. -/
def minor (p : Kˣ × K × K × K) : ℤ :=
  (minimum K (minors (matrix (p.1 : K) p.2.1 p.2.2.1 p.2.2.2))).untopD 0
/-- The first intrinsic Cartan index (half the even index ell). -/
def n (p : Kˣ × K × K × K) : ℤ := entry K p - minor K p
/-- The second intrinsic Cartan index. -/
def B (p : Kˣ × K × K × K) : ℤ := minor K p - 2*entry K p
/-- The nonnegative height used for Abel damping. -/
def height (p : Kˣ × K × K × K) : ℤ := n K p + B K p
/-- The complete finite Weyl kernel, defined independently of any integral. -/
def Phi (a b : ℂ) (p : Kˣ × K × K × K) : ℂ :=
  (C qK : ℂ)⁻¹ * ∑ i : Fin 8,
    A qK a b i * (t qK : ℂ) ^ (6*n K p+4*B K p) *
      U a b i ^ n K p * V a b i ^ B K p
/-- The additive valuation of a nonzero multiplicative coordinate. -/
def exponent (a : Kˣ) : ℤ := (valuationInt K (a : K)).untopD 0
/-- The three coefficients multiplying the three Haar integrals. -/
def prefactor (q : ℝ) : Fin 3 → ℂ :=
  ![(1-(q:ℂ)⁻¹)⁻¹,(q:ℂ),-(q:ℂ)/(1-(q:ℂ)⁻¹)]
/-- The three central coordinates: zero, inverse uniformizer, inverse square. -/
def central (π : Kˣ) : Fin 3 → K := ![0,(π:K)⁻¹,(π:K)^(-2:ℤ)]
/-- The integrand d^v(a) |a|^(3/2) T^height Phi at a fixed central coordinate. -/
def f (a b d : ℂ) (T : ℝ) (π : Kˣ) (r : Fin 3) (p : Kˣ × K × K) : ℂ :=
  d ^ exponent K p.1 * (Real.rpow (qK ^ (-exponent K p.1)) (3/2) : ℂ) *
    (T : ℂ) ^ height K (p.1,p.2.1,p.2.2,central K π r) *
      Phi K a b (p.1,p.2.1,p.2.2,central K π r)

local instance fieldT2 : T2Space K := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  let := isUniformAddGroup_of_addCommGroup (G := K)
  infer_instance
variable [MeasurableSpace K] [BorelSpace K]
local instance unitsBorel : BorelSpace Kˣ := by
  refine ⟨?_⟩
  change MeasurableSpace.comap (Units.val : Kˣ → K) ‹MeasurableSpace K› = borel Kˣ
  rw [BorelSpace.measurable_eq (α := K)]
  rw [(Units.isEmbedding_val₀ (G₀ := K)).eq_induced, borel_comap]
/-- The compact open valuation ring, used to normalize additive Haar measure. -/
def integersCompact : TopologicalSpace.PositiveCompacts K :=
  ⟨⟨𝒪[K], IsNonarchimedeanLocalField.isCompact_closedBall K 1⟩, by
    rw [(ValuativeRel.valuation K).isOpen_integer.interior_eq]
    exact ⟨0, by simp⟩⟩
/-- The compact open subgroup of valuation-ring units. -/
def unitsCompact : TopologicalSpace.PositiveCompacts Kˣ :=
  ⟨⟨(𝒪[K]).toSubmonoid.units,
    Submonoid.units_isCompact (S := (𝒪[K]).toSubmonoid)
      (IsNonarchimedeanLocalField.isCompact_closedBall K 1)⟩, by
    rw [(Submonoid.isOpen_units (U := (𝒪[K]).toSubmonoid)
      (ValuativeRel.valuation K).isOpen_integer).interior_eq]
    exact ⟨1, (𝒪[K]).toSubmonoid.units.one_mem⟩⟩
/-- Additive Haar measure giving the valuation ring mass one. -/
def additive : Measure K := Measure.addHaarMeasure (integersCompact K)
/-- Multiplicative Haar measure giving valuation-ring units mass 1-q^(-1). -/
def multiplicative : Measure Kˣ :=
  ENNReal.ofReal (1-qK⁻¹) • Measure.haarMeasure (unitsCompact K)
/-- The measure d×a dx dy, with both normalizations explicit above. -/
def coreMeasure : Measure (Kˣ × K × K) :=
  (multiplicative K).prod ((additive K).prod (additive K))
/-- The sum of three prefactored Bochner integrals at the central coordinates. -/
def I (a b d : ℂ) (T : ℝ) (π : Kˣ) : ℂ :=
  ∑ r : Fin 3, prefactor qK r * ∫ p, f K a b d T π r p ∂coreMeasure K


-- Each concrete statement definition is identified with the checked PDF audit.
-- Neither this file nor its imported proof development imports Challenge.
open FourierJacobi.Valuations FourierJacobi.LocalMatrix FourierJacobi.Analysis

private theorem C_eq (q : ℝ) : C q = FourierJacobiPdfV1.C q := rfl
private theorem D1_eq (q : ℝ) (a b d : ℂ) : D1 q a b d = FourierJacobiPdfV1.D1 q a b d := rfl
private theorem D2_eq (q : ℝ) (a b d : ℂ) : D2 q a b d = FourierJacobiPdfV1.D2 q a b d := rfl
private theorem E_eq (q : ℝ) (a b d : ℂ) : E q a b d = FourierJacobiPdfV1.E q a b d := rfl
omit [MeasurableSpace K] [BorelSpace K] in
omit [MeasurableSpace K] [BorelSpace K] in
private theorem q_eq : q K = (FourierJacobi.Measure.residueCardinality K : ℝ) := rfl
private theorem t_eq (q : ℝ) : t q = FourierJacobi.Algebra.inverseSqrt q := rfl

omit [MeasurableSpace K] [BorelSpace K] in
private theorem entry_eq (p : Kˣ × K × K × K) : entry K p = kernelEntryIndex K p := by
  change (matrixMinimum (localFieldValuation K)
    (FourierJacobiPdfV1.matrix (p.1 : K) p.2.1 p.2.2.1 p.2.2.2)).untopD 0 = _
  rw [FourierJacobiPdfV1.matrix_eq, ← actualEntryInteger_coe]
  rfl

omit [MeasurableSpace K] [BorelSpace K] in
private theorem minor_eq (p : Kˣ × K × K × K) : minor K p = kernelMinorIndex K p := by
  change (matrixMinimum (localFieldValuation K)
    (secondCompound (FourierJacobiPdfV1.matrix (p.1 : K) p.2.1 p.2.2.1 p.2.2.2))).untopD 0 = _
  rw [FourierJacobiPdfV1.matrix_eq, ← actualMinorInteger_coe]
  rfl

omit [MeasurableSpace K] [BorelSpace K] in
private theorem n_eq (p : Kˣ × K × K × K) : n K p = kernelN K p := by
  simp only [n, kernelN, entry_eq, minor_eq]

omit [MeasurableSpace K] [BorelSpace K] in
private theorem B_eq (p : Kˣ × K × K × K) : B K p = kernelB K p := by
  simp only [B, kernelB, entry_eq, minor_eq]

omit [MeasurableSpace K] [BorelSpace K] in
private theorem height_eq (p : Kˣ × K × K × K) : height K p = kernelHeight K p := by
  simp only [height, kernelHeight, n_eq, B_eq]

omit [MeasurableSpace K] [BorelSpace K] in
private theorem Phi_eq (a b : ℂ) (p : Kˣ × K × K × K) :
    Phi K a b p = FourierJacobiPdfV1.Phi K a b p := by
  simp only [Phi, n_eq, B_eq]
  rfl

omit [MeasurableSpace K] [BorelSpace K] in
private theorem exponent_eq (a : Kˣ) : exponent K a = coreScaleExponent K a := by
  change (localFieldValuation K (a : K)).untopD 0 = _
  rw [← coreScaleExponent_coe]
  rfl

private theorem coreMeasure_eq : coreMeasure K = paperCoreMeasure K := rfl

omit [MeasurableSpace K] [BorelSpace K] in
private theorem f_eq (a b d : ℂ) (T : ℝ) (π : Kˣ) (r : Fin 3) :
    f K a b d T π r = FourierJacobiPdfV1.f K a b d T π r := by
  funext p
  simp only [f, exponent_eq, height_eq, Phi_eq]
  rfl

private theorem I_eq (a b d : ℂ) (T : ℝ) (π : Kˣ) :
    I K a b d T π = FourierJacobiPdfV1.I K a b d T π := by
  simp only [I, f_eq, coreMeasure_eq]
  rfl

/-- The constructed measures really are Haar measures with the source's
additive and multiplicative normalizations. -/
theorem measure_normalizations :
    (additive K).IsAddHaarMeasure ∧ (multiplicative K).IsHaarMeasure ∧
    additive K (𝒪[K] : Set K) = 1 ∧
    multiplicative K ((𝒪[K]).toSubmonoid.units : Set Kˣ) = ENNReal.ofReal (1-qK⁻¹) := by
  exact FourierJacobiPdfV1.measure_normalizations K

/-- Each of the three genuine integrands is measurable and Bochner integrable
for 0 < T ≤ 1, t ≤ |d| ≤ 1, T*t < |d|. This includes the undamped interior. -/
theorem integrability (a b d : ℂ) (T : ℝ) (hq : 2 < qK) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hT₀ : 0 < T) (hT₁ : T ≤ 1) (hd₀ : t qK ≤ ‖d‖) (hd₁ : ‖d‖ ≤ 1)
    (hstrict : T * t qK < ‖d‖) (π : Kˣ)
    (hπ : valuationInt K (π : K) = (1 : WithTop ℤ)) (r : Fin 3) :
    Measurable (f K a b d T π r) ∧ Integrable (f K a b d T π r) (coreMeasure K) := by
  simpa only [f_eq, coreMeasure_eq] using
    FourierJacobiPdfV1.part_ii K a b d T hq ha hb hT₀ hT₁ hd₀ hd₁ hstrict π hπ r

/-- For regular unitary a,b and t < |d| ≤ 1: the denominator is nonzero,
I_1 = E_q, and I_T tends to I_1 as T approaches one from within (0,1).
The same evaluation and limit include the principal factor 2/(q+1). -/
theorem principal_evaluation (a b d : ℂ) (hq : 2 < qK) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hd₀ : t qK < ‖d‖) (hd₁ : ‖d‖ ≤ 1)
    (ha₁ : a ≠ 1) (hb₁ : b ≠ 1) (hab : a ≠ b) (hab₁ : a*b ≠ 1)
    (π : Kˣ) (hπ : valuationInt K (π : K) = (1 : WithTop ℤ)) :
    (C qK : ℂ)*D1 qK a b d*D2 qK a b d ≠ 0 ∧
    I K a b d 1 π = E qK a b d ∧
    Tendsto (fun T => I K a b d T π) (𝓝[Set.Ioo 0 1] 1) (𝓝 (I K a b d 1 π)) ∧
    (2/((qK:ℂ)+1)*I K a b d 1 π = 2/((qK:ℂ)+1)*E qK a b d) ∧
    Tendsto (fun T => 2/((qK:ℂ)+1)*I K a b d T π)
      (𝓝[Set.Ioo 0 1] 1) (𝓝 (2/((qK:ℂ)+1)*E qK a b d)) := by
  simpa only [I_eq, C_eq, D1_eq, D2_eq, E_eq, q_eq] using
    FourierJacobiPdfV1.part_iii K a b d hq ha hb hd₀ hd₁ ha₁ hb₁ hab hab₁ π hπ

/-- At d = ε*t, ε = ±1: damped integrability, a nonzero denominator,
and convergence of the entire product (1-ε)/(q+1)*I_T to the corresponding
rational value. No ordinary undamped endpoint integral is asserted. -/
theorem special_abel_limit (a b ε : ℂ) (hq : 2 < qK) (hε : ε = 1 ∨ ε = -1)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (ha₁ : a ≠ 1) (hb₁ : b ≠ 1) (hab : a ≠ b) (hab₁ : a*b ≠ 1)
    (haε : a ≠ ε) (hbε : b ≠ ε)
    (π : Kˣ) (hπ : valuationInt K (π : K) = (1 : WithTop ℤ)) :
    (∀ T ∈ Set.Ioo (0:ℝ) 1, ∀ r : Fin 3,
      Integrable (f K a b (ε*(t qK:ℂ)) T π r) (coreMeasure K)) ∧
    (C qK:ℂ)*D1 qK a b (ε*(t qK:ℂ))*D2 qK a b (ε*(t qK:ℂ)) ≠ 0 ∧
    Tendsto (fun T => (1-ε)/((qK:ℂ)+1)*I K a b (ε*(t qK:ℂ)) T π)
      (𝓝[Set.Ioo 0 1] 1) (𝓝 ((1-ε)/((qK:ℂ)+1)*E qK a b (ε*(t qK:ℂ)))) := by
  simpa only [f_eq, coreMeasure_eq, I_eq, C_eq, D1_eq, D2_eq, E_eq, q_eq, t_eq] using
    FourierJacobiPdfV1.part_iv K a b ε hq hε ha hb ha₁ hb₁ hab hab₁ haε hbε π hπ

end FourierJacobiPalomar


run_cmd do
  let env ← Lean.getEnv
  let allowed : Array Lean.Name := #[`propext, `Classical.choice, `Quot.sound]
  if env.header.moduleNames.contains `Challenge then
    throwError "Solution must never import Challenge"
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    if (env.getModuleIdxFor? name).isNone then
      if info.isUnsafe || info.isPartial then
        throwError "Unsafe or partial Solution declaration: {name}"
      let axioms ← Lean.collectAxioms name
      unless (axioms.filter fun ax => !allowed.contains ax).isEmpty do
        throwError "Unapproved Solution axiom in {name}: {axioms}"
      count := count + 1
  for name in #[`FourierJacobiPalomar.measure_normalizations,
      `FourierJacobiPalomar.integrability, `FourierJacobiPalomar.principal_evaluation,
      `FourierJacobiPalomar.special_abel_limit] do
    unless (env.find? name).isSome do
      throwError "Missing Palomar theorem: {name}"
    let axioms ← Lean.collectAxioms name
    Lean.logInfo m!"PALOMAR THEOREM {name}: {axioms}"
  Lean.logInfo m!"Palomar Solution axiom/safety audit passed: {count} declarations."
