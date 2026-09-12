import FourierJacobi.Valuations.LocalMatrix
import FourierJacobi.Measure.IntegerShells
import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Finite integer kernel indices of the actual core matrices

The entry and minor extrema are intrinsic minima of actual matrix entries.
No Cartan decomposition, spherical formula, or integral-to-series identity is
assumed. In particular zero x, y or z and a vanishing determinant are retained.
-/

noncomputable section
namespace FourierJacobi.Valuations
open FourierJacobi.LocalMatrix

variable {K : Type*} [Field K]

/-- The missing upper minor bound for the concrete core matrix. -/
theorem actual_minor_minimum_le_entry (v : AddValuation K (WithTop ℤ))
    (a x y z : K) (ha : a ≠ 0) :
    matrixMinimum v (secondCompound (g a x y z)) ≤ matrixMinimum v (g a x y z) := by
  rw [actual_minor_minimum v a x y z ha, actual_entry_minimum]
  have hz : minorListMinimum v a x y z ≤ v z := by
    obtain ⟨k,hk⟩ := WithTop.ne_top_iff_exists.mp (v.ne_top_iff.mpr ha)
    have hva : v a = (k : WithTop ℤ) := hk.symm
    have hvi : v a⁻¹ = ((-k : ℤ) : WithTop ℤ) := by simp [hva]
    rcases le_total k 0 with h | h
    · have hka : v a ≤ 0 := by rw [hva]; exact_mod_cast h
      have he : v (a*z) ≤ v z := by
        rw [v.map_mul]
        simpa [add_comm] using add_le_add_right hka (v z)
      exact le_trans (by simp [minorListMinimum]) he
    · have hka : v a⁻¹ ≤ 0 := by
        rw [hvi]
        exact_mod_cast neg_nonpos.mpr h
      have he : v (z/a) ≤ v z := by
        rw [div_eq_mul_inv, v.map_mul]
        simpa [add_comm] using add_le_add_left hka (v z)
      exact le_trans (by simp [minorListMinimum]) he
  simp only [entryListMinimum, le_min_iff]
  exact ⟨⟨⟨⟨⟨⟨by simp [minorListMinimum], by simp [minorListMinimum]⟩,
    by simp [minorListMinimum]⟩, by simp [minorListMinimum]⟩,
    by simp [minorListMinimum]⟩, by simp [minorListMinimum]⟩, hz⟩

/-- The finite entry minimum, extracted using its proof of finiteness. -/
def actualEntryInteger (v : AddValuation K (WithTop ℤ)) (a : Kˣ) (x y z : K) : ℤ :=
  (matrixMinimum v (g a x y z)).untop
    (actual_minima_finite v a x y z (Units.ne_zero a)).1

/-- The finite two-by-two-minor minimum, extracted using finiteness. -/
def actualMinorInteger (v : AddValuation K (WithTop ℤ)) (a : Kˣ) (x y z : K) : ℤ :=
  (matrixMinimum v (secondCompound (g a x y z))).untop
    (actual_minima_finite v a x y z (Units.ne_zero a)).2

@[simp] theorem actualEntryInteger_coe (v : AddValuation K (WithTop ℤ))
    (a : Kˣ) (x y z : K) :
    (actualEntryInteger v a x y z : WithTop ℤ) = matrixMinimum v (g a x y z) :=
  WithTop.coe_untop _ _

@[simp] theorem actualMinorInteger_coe (v : AddValuation K (WithTop ℤ))
    (a : Kˣ) (x y z : K) :
    (actualMinorInteger v a x y z : WithTop ℤ) =
      matrixMinimum v (secondCompound (g a x y z)) :=
  WithTop.coe_untop _ _

theorem actualInteger_bounds (v : AddValuation K (WithTop ℤ))
    (a : Kˣ) (x y z : K) :
    2 * actualEntryInteger v a x y z ≤ actualMinorInteger v a x y z ∧
    actualMinorInteger v a x y z ≤ actualEntryInteger v a x y z ∧
    actualEntryInteger v a x y z ≤ 0 := by
  have h1 := twice_entry_minimum_le_minor v (g (a:K) x y z)
  have h2 := actual_minor_minimum_le_entry v (a:K) x y z (Units.ne_zero a)
  have h3 := actual_entry_minimum_le_zero v (a:K) x y z
  rw [← actualEntryInteger_coe v a x y z,
    ← actualMinorInteger_coe v a x y z, ← WithTop.coe_add] at h1
  rw [← actualEntryInteger_coe v a x y z,
    ← actualMinorInteger_coe v a x y z] at h2
  rw [← actualEntryInteger_coe v a x y z] at h3
  have h1' := WithTop.coe_le_coe.mp h1
  have h2' := WithTop.coe_le_coe.mp h2
  have h3' : actualEntryInteger v a x y z ≤ 0 := by exact_mod_cast h3
  exact ⟨by omega, h2', h3'⟩

section LocalField
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

abbrev KernelPoint := Kˣ × K × K × K

def kernelEntryIndex (p : KernelPoint K) : ℤ :=
  actualEntryInteger (localFieldValuation K) p.1 p.2.1 p.2.2.1 p.2.2.2

def kernelMinorIndex (p : KernelPoint K) : ℤ :=
  actualMinorInteger (localFieldValuation K) p.1 p.2.1 p.2.2.1 p.2.2.2

def kernelN (p : KernelPoint K) : ℤ := kernelEntryIndex K p - kernelMinorIndex K p
def kernelB (p : KernelPoint K) : ℤ := kernelMinorIndex K p - 2 * kernelEntryIndex K p
def kernelEll (p : KernelPoint K) : ℤ := 2 * kernelN K p
def kernelHeight (p : KernelPoint K) : ℤ := kernelN K p + kernelB K p

theorem kernel_indices_nonnegative (p : KernelPoint K) :
    0 ≤ kernelN K p ∧ 0 ≤ kernelB K p ∧ 0 ≤ kernelEll K p ∧ 0 ≤ kernelHeight K p := by
  have h := actualInteger_bounds (localFieldValuation K) p.1 p.2.1 p.2.2.1 p.2.2.2
  simp only [kernelEll, kernelHeight, kernelN, kernelB, kernelEntryIndex, kernelMinorIndex]
  omega

theorem kernel_height_eq (p : KernelPoint K) :
    kernelHeight K p = -kernelEntryIndex K p := by
  unfold kernelHeight kernelN kernelB
  ring

theorem kernel_half_ell (p : KernelPoint K) : kernelEll K p / 2 = kernelN K p := by
  unfold kernelEll
  omega

theorem kernel_indices_of_minima (p : KernelPoint K) (r k j h c : ℤ)
    (he : matrixMinimum (localFieldValuation K) (g p.1 p.2.1 p.2.2.1 p.2.2.2) =
      (entryMinimum r k j h : WithTop ℤ))
    (hm : matrixMinimum (localFieldValuation K)
      (secondCompound (g p.1 p.2.1 p.2.2.1 p.2.2.2)) =
        (minorMinimum r k j h c : WithTop ℤ)) :
    (kernelEll K p, kernelB K p) = cartanIndices r k j h c := by
  have he' : kernelEntryIndex K p = entryMinimum r k j h := by
    apply WithTop.coe_injective
    exact (actualEntryInteger_coe _ _ _ _ _).trans he
  have hm' : kernelMinorIndex K p = minorMinimum r k j h c := by
    apply WithTop.coe_injective
    exact (actualMinorInteger_coe _ _ _ _ _).trans hm
  unfold kernelEll kernelN kernelB cartanIndices
  rw [he',hm']
  simp only [Prod.mk.injEq]
  constructor
  · ring
  · trivial

section Measurability
variable [MeasurableSpace K] [BorelSpace K]

local instance kernelField_t2Space : T2Space K := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  let := isUniformAddGroup_of_addCommGroup (G := K)
  infer_instance

local instance kernelField_secondCountable : SecondCountableTopology K := by
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
  infer_instance

/-- Measurability of the normalized valuation, supplied by the actual integer
shell theorem, and used below to measure the actual entry and minor minima. -/
theorem kernel_localFieldValuation_measurable : Measurable (localFieldValuation K) :=
  FourierJacobi.Measure.canonicalValuation_measurable K

theorem kernel_entry_minimum_measurable {α : Type*} [MeasurableSpace α]
    (a x y z : α → K) (ha : Measurable a) (hx : Measurable x)
    (hy : Measurable y) (hz : Measurable z) :
    Measurable (fun p => matrixMinimum (localFieldValuation K)
      (g (a p) (x p) (y p) (z p))) := by
  simp_rw [actual_entry_minimum]
  unfold entryListMinimum
  have hv := kernel_localFieldValuation_measurable K
  have hzero : Measurable (fun _ : α => (0 : WithTop ℤ)) := measurable_const
  have h0 := (hzero.min (hv.comp ha)).min (hv.comp ha.inv)
  have h1 := (h0.min (hv.comp (ha.mul hx))).min (hv.comp hy)
  exact (h1.min (hv.comp (ha.mul hy))).min (hv.comp hz)

theorem kernel_minor_minimum_measurable {α : Type*} [MeasurableSpace α]
    (a x y z : α → K) (ha : Measurable a) (hx : Measurable x)
    (hy : Measurable y) (hz : Measurable z) (ha0 : ∀ p, a p ≠ 0) :
    Measurable (fun p => matrixMinimum (localFieldValuation K)
      (secondCompound (g (a p) (x p) (y p) (z p)))) := by
  have he : (fun p => matrixMinimum (localFieldValuation K)
      (secondCompound (g (a p) (x p) (y p) (z p)))) =
      (fun p => minorListMinimum (localFieldValuation K) (a p) (x p) (y p) (z p)) :=
    funext fun p => actual_minor_minimum _ _ _ _ _ (ha0 p)
  rw [he]
  unfold minorListMinimum
  have hv := kernel_localFieldValuation_measurable K
  have hzero : Measurable (fun _ : α => (0 : WithTop ℤ)) := measurable_const
  have h0 := (hzero.min (hv.comp ha)).min (hv.comp ha.inv)
  have h1 := (h0.min (hv.comp (ha.mul hx))).min (hv.comp hy)
  have h2 := (h1.min (hv.comp (ha.mul hy))).min (hv.comp (ha.mul hz))
  exact (h2.min (hv.comp (hz.div ha))).min
    (hv.comp (ha.mul ((hy.pow_const 2).sub (hx.mul hz))))

theorem kernelEntryIndex_measurable : Measurable (kernelEntryIndex K) := by
  have ha : Measurable (fun p : KernelPoint K => (p.1 : K)) :=
    (show Measurable (fun a : Kˣ => (a : K)) from MeasurableSpace.le_map_comap).comp
      measurable_fst
  have hm := kernel_entry_minimum_measurable K
    (fun p : KernelPoint K => (p.1 : K)) (fun p => p.2.1)
    (fun p => p.2.2.1) (fun p => p.2.2.2)
    ha measurable_snd.fst measurable_snd.snd.fst measurable_snd.snd.snd
  have he : kernelEntryIndex K = (fun p : KernelPoint K =>
      (matrixMinimum (localFieldValuation K) (g p.1 p.2.1 p.2.2.1 p.2.2.2)).untopA) := by
    funext p
    exact (WithTop.untopA_eq_untop
      (actual_minima_finite _ _ _ _ _ (Units.ne_zero p.1)).1).symm
  rw [he]
  exact hm.untopA

theorem kernelMinorIndex_measurable : Measurable (kernelMinorIndex K) := by
  have ha : Measurable (fun p : KernelPoint K => (p.1 : K)) :=
    (show Measurable (fun a : Kˣ => (a : K)) from MeasurableSpace.le_map_comap).comp
      measurable_fst
  have hm := kernel_minor_minimum_measurable K
    (fun p : KernelPoint K => (p.1 : K)) (fun p => p.2.1)
    (fun p => p.2.2.1) (fun p => p.2.2.2)
    ha measurable_snd.fst measurable_snd.snd.fst measurable_snd.snd.snd
    (fun p => Units.ne_zero p.1)
  have he : kernelMinorIndex K = (fun p : KernelPoint K =>
      (matrixMinimum (localFieldValuation K)
        (secondCompound (g p.1 p.2.1 p.2.2.1 p.2.2.2))).untopA) := by
    funext p
    exact (WithTop.untopA_eq_untop
      (actual_minima_finite _ _ _ _ _ (Units.ne_zero p.1)).2).symm
  rw [he]
  exact hm.untopA

theorem kernelN_measurable : Measurable (kernelN K) :=
  (kernelEntryIndex_measurable K).sub (kernelMinorIndex_measurable K)

theorem kernelB_measurable : Measurable (kernelB K) :=
  (kernelMinorIndex_measurable K).sub ((kernelEntryIndex_measurable K).const_mul 2)

theorem kernelEll_measurable : Measurable (kernelEll K) :=
  (kernelN_measurable K).const_mul 2

theorem kernelHeight_measurable : Measurable (kernelHeight K) :=
  (kernelN_measurable K).add (kernelB_measurable K)

end Measurability

end LocalField
end FourierJacobi.Valuations
