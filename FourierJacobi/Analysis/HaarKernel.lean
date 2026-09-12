import FourierJacobi.Analysis.ExplicitKernel
import FourierJacobi.Measure.PaperMultiplicativeHaar
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Independently defined explicit-kernel Haar integrals

These are the three actual local-field Bochner integrals in the brief. Their
integrands are proved measurable. No integrability or evaluation theorem is
asserted here: an integral value must only be used after integrability is proved.
-/

noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory

namespace FourierJacobi.Analysis
open FourierJacobi.Algebra FourierJacobi.Valuations

theorem inverseSqrt_even_zpow (q : ℝ) (hq : 0 ≤ q) (e : ℤ) :
    inverseSqrt q ^ (2 * e) = q ^ (-e) := by
  rw [zpow_mul]
  simp [inverseSqrt_sq hq, zpow_neg]

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The actual finite valuation of the multiplicative coordinate. -/
def coreScaleExponent (a : Kˣ) : ℤ :=
  (localFieldValuation K (a : K)).untop
    ((localFieldValuation_ne_top K (a : K)).mpr (Units.ne_zero a))

@[simp] theorem coreScaleExponent_coe (a : Kˣ) :
    (coreScaleExponent K a : WithTop ℤ) = localFieldValuation K (a : K) :=
  WithTop.coe_untop _ _

/-- The normalized absolute value q^(-v(a)) on the actual field units. -/
def coreLocalAbs (q : ℝ) (a : Kˣ) : ℝ := q ^ (-coreScaleExponent K a)

theorem coreLocalAbs_pos (q : ℝ) (hq : 0 < q) (a : Kˣ) :
    0 < coreLocalAbs K q a := zpow_pos hq _

/-- The majorant q^(-3ℓ/2-2b), with the even Cartan exponent expressed by n=ℓ/2. -/
theorem explicitWeylKernel_q_norm_le (q : ℝ) (hq : 1 < q)
    (a b : ℂ) (p : KernelPoint K) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    ‖explicitWeylKernel K (inverseSqrt q : ℂ) a b p‖ ≤
      ((∑ i : Fin 8, ‖weylWeights (inverseSqrt q : ℂ) a b i‖) /
        poincare (inverseSqrt q)) * q ^ (-3 * kernelN K p - 2 * kernelB K p) := by
  have hn := explicitWeylKernel_norm_le K (inverseSqrt q) a b p
    (inverseSqrt_pos hq).le ha hb
  have he : 3 * kernelEll K p + 4 * kernelB K p =
      2 * (3 * kernelN K p + 2 * kernelB K p) := by unfold kernelEll; ring
  rw [he, inverseSqrt_even_zpow q (by linarith)] at hn
  have he' : -(3 * kernelN K p + 2 * kernelB K p) =
      -3 * kernelN K p - 2 * kernelB K p := by ring
  simpa only [he'] using hn

abbrev HaarPoint := Kˣ × K × K

def coreAtCentral (z : K) (p : HaarPoint K) : KernelPoint K :=
  (p.1, p.2.1, p.2.2, z)

/-- The actual integrand δ^v(a)|a|^(3/2)T^H Ψ, with real-power absolute value. -/
def explicitCoreIntegrand (q : ℝ) (a b d : ℂ) (T : ℝ) (z : K)
    (p : HaarPoint K) : ℂ :=
  d ^ (coreScaleExponent K p.1) *
    (Real.rpow (coreLocalAbs K q p.1) (3 / 2) : ℂ) *
      (T : ℂ) ^ (kernelHeight K (coreAtCentral K z p)) *
        explicitWeylKernel K (inverseSqrt q : ℂ) a b (coreAtCentral K z p)

/-- The three central representatives, with r=0 meaning z=0. -/
def coreCentral (π : Kˣ) (r : Fin 3) : K :=
  if r = 0 then 0 else (π : K) ^ (-(r.val : ℤ))

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
@[simp] theorem coreCentral_zero (π : Kˣ) : coreCentral K π 0 = 0 := by
  simp [coreCentral]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
@[simp] theorem coreCentral_one (π : Kˣ) : coreCentral K π 1 = (π : K)⁻¹ := by
  simp [coreCentral]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
@[simp] theorem coreCentral_two (π : Kˣ) : coreCentral K π 2 = (π : K) ^ (-2 : ℤ) := by
  simp [coreCentral]

/-- Exactly the three Haar prefactors a₀, a₁, a₂ in the brief. -/
def coreIntegralPrefactor (q : ℝ) (r : Fin 3) : ℂ :=
  if r = 0 then (1 - (q : ℂ)⁻¹)⁻¹
  else if r = 1 then (q : ℂ)
  else -(q : ℂ) / (1 - (q : ℂ)⁻¹)

section Measurability
variable [MeasurableSpace K] [BorelSpace K]

/-- The standard measurable structure on field units is its Borel structure. -/
theorem coreUnits_borelSpace : BorelSpace Kˣ := by
  refine ⟨?_⟩
  change MeasurableSpace.comap (Units.val : Kˣ → K) ‹MeasurableSpace K› = borel Kˣ
  rw [BorelSpace.measurable_eq (α := K)]
  rw [(Units.isEmbedding_val₀ (G₀ := K)).eq_induced, borel_comap]

local instance : BorelSpace Kˣ := coreUnits_borelSpace K

theorem coreScaleExponent_measurable : Measurable (coreScaleExponent K) := by
  have ha : Measurable (fun a : Kˣ => (a : K)) := MeasurableSpace.le_map_comap
  have hm := (kernel_localFieldValuation_measurable K).comp ha
  have he : coreScaleExponent K = (fun a : Kˣ =>
      (localFieldValuation K (a : K)).untopA) := by
    funext a
    exact (WithTop.untopA_eq_untop
      ((localFieldValuation_ne_top K (a : K)).mpr (Units.ne_zero a))).symm
  rw [he]
  exact hm.untopA

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [BorelSpace K] in
theorem coreAtCentral_measurable (z : K) : Measurable (coreAtCentral K z) :=
  measurable_fst.prodMk (measurable_snd.fst.prodMk
    (measurable_snd.snd.prodMk measurable_const))

theorem explicitCoreIntegrand_measurable (q : ℝ) (a b d : ℂ) (T : ℝ) (z : K) :
    Measurable (explicitCoreIntegrand K q a b d T z) := by
  have hk : Measurable (fun p : HaarPoint K => coreScaleExponent K p.1) :=
    (coreScaleExponent_measurable K).comp measurable_fst
  have hscale : Measurable (fun n : ℤ =>
      d ^ n * (Real.rpow (q ^ (-n)) (3 / 2) : ℂ)) := measurable_of_countable _
  have hheight := ((measurable_of_countable (fun n : ℤ => (T : ℂ) ^ n)).comp
    (kernelHeight_measurable K)).comp (coreAtCentral_measurable K z)
  exact ((hscale.comp hk).mul hheight).mul
    ((explicitWeylKernel_measurable K (inverseSqrt q : ℂ) a b).comp
      (coreAtCentral_measurable K z))

/-- A measurable, countable family of exact intrinsic Cartan-index fibres. -/
def kernelCartanFiber (n B : ℤ) : Set (KernelPoint K) :=
  {p | kernelN K p = n ∧ kernelB K p = B}

theorem kernelCartanFiber_measurableSet (n B : ℤ) :
    MeasurableSet (kernelCartanFiber K n B) :=
  ((measurableSet_singleton n).preimage (kernelN_measurable K)).inter
    ((measurableSet_singleton B).preimage (kernelB_measurable K))

omit [MeasurableSpace K] [BorelSpace K] in
theorem kernelCartanFiber_disjoint {n B m C : ℤ} (h : (n,B) ≠ (m,C)) :
    Disjoint (kernelCartanFiber K n B) (kernelCartanFiber K m C) := by
  rw [Set.disjoint_left]
  intro p hp hq
  exact h (Prod.ext (hp.1.symm.trans hq.1) (hp.2.symm.trans hq.2))

omit [MeasurableSpace K] [BorelSpace K] in
theorem kernelCartanFiber_exhaustive (p : KernelPoint K) :
    p ∈ kernelCartanFiber K (kernelN K p) (kernelB K p) := ⟨rfl,rfl⟩

omit [MeasurableSpace K] [BorelSpace K] in
theorem kernelCartanFiber_empty_of_negative {n B : ℤ} (h : n < 0 ∨ B < 0) :
    kernelCartanFiber K n B = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  have hn := kernel_indices_nonnegative K p
  change kernelN K p = n ∧ kernelB K p = B at hp
  omega

/-- Independently defined Haar shell integral. Its use as an ordinary integral
value requires the separate, still outstanding integrability theorem. -/
def explicitHaarCoreShell (μ : Measure K) (ν : Measure Kˣ)
    (q : ℝ) (a b d : ℂ) (T : ℝ) (π : Kˣ) (r : Fin 3) : ℂ :=
  coreIntegralPrefactor q r * ∫ p : HaarPoint K,
    explicitCoreIntegrand K q a b d T (coreCentral K π r) p ∂ν.prod (μ.prod μ)

def explicitHaarCore (μ : Measure K) (ν : Measure Kˣ)
    (q : ℝ) (a b d : ℂ) (T : ℝ) (π : Kˣ) : ℂ :=
  ∑ r : Fin 3, explicitHaarCoreShell K μ ν q a b d T π r

/-- Source normalization: actual residue cardinality, additive unit-ball mass
one and multiplicative unit-shell mass 1-q⁻¹. Integrability remains a separate
obligation of the eventual evaluation theorem. -/
def paperExplicitHaarCore (a b d : ℂ) (T : ℝ) (π : Kˣ) : ℂ :=
  explicitHaarCore K (FourierJacobi.Measure.additiveHaar K)
    (FourierJacobi.Measure.paperMultiplicativeHaar K)
    (FourierJacobi.Measure.residueCardinality K : ℝ) a b d T π

end Measurability
end FourierJacobi.Analysis
