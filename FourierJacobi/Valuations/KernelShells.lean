import FourierJacobi.Valuations.KernelIndices

/-!
# Actual kernel indices on the valuation shells of the master lattice

The shell hypotheses specify actual canonical field valuations, including the
actual collision ratio when the two determinant terms have equal valuation.
No matrix-minimum, integration, or spherical-coefficient identity is assumed.
-/

noncomputable section
namespace FourierJacobi.Valuations
open FourierJacobi.LocalMatrix

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The complete intrinsic index data at a specified integer-table point. -/
def KernelShellCoordinates (p : KernelPoint K) (r k j h c : ℤ) : Prop :=
  kernelEntryIndex K p = entryMinimum r k j h ∧
  kernelMinorIndex K p = minorMinimum r k j h c ∧
  kernelEll K p = (cartanIndices r k j h c).1 ∧
  kernelN K p = (cartanIndices r k j h c).1 / 2 ∧
  kernelB K p = (cartanIndices r k j h c).2 ∧
  kernelHeight K p = (cartanIndices r k j h c).1 / 2 +
    (cartanIndices r k j h c).2 ∧
  kernelHeight K p = -entryMinimum r k j h

theorem kernelShellCoordinates_of_minima (p : KernelPoint K) (r k j h c : ℤ)
    (he : matrixMinimum (localFieldValuation K) (g p.1 p.2.1 p.2.2.1 p.2.2.2) =
      (entryMinimum r k j h : WithTop ℤ))
    (hm : matrixMinimum (localFieldValuation K)
      (secondCompound (g p.1 p.2.1 p.2.2.1 p.2.2.2)) =
        (minorMinimum r k j h c : WithTop ℤ)) :
    KernelShellCoordinates K p r k j h c := by
  have he' : kernelEntryIndex K p = entryMinimum r k j h := by
    apply WithTop.coe_injective
    exact (actualEntryInteger_coe _ _ _ _ _).trans he
  have hm' : kernelMinorIndex K p = minorMinimum r k j h c := by
    apply WithTop.coe_injective
    exact (actualMinorInteger_coe _ _ _ _ _).trans hm
  have hcartan := kernel_indices_of_minima K p r k j h c he hm
  have hell : kernelEll K p = (cartanIndices r k j h c).1 := congrArg Prod.fst hcartan
  have hb : kernelB K p = (cartanIndices r k j h c).2 := congrArg Prod.snd hcartan
  have hn : kernelN K p = (cartanIndices r k j h c).1 / 2 := by
    rw [← hell, kernel_half_ell]
  refine ⟨he', hm', hell, hn, hb, ?_, ?_⟩
  · unfold kernelHeight
    rw [hn, hb]
  · rw [kernel_height_eq, he']

/-- At r=0 the actual central coordinate is zero and there is no collision depth. -/
theorem kernelShellCoordinates_zero (a : Kˣ) (x y : K) (k j h : ℤ)
    (hk : localFieldValuation K (a : K) = (k : WithTop ℤ))
    (hj : localFieldValuation K x = (j : WithTop ℤ))
    (hh : localFieldValuation K y = (h : WithTop ℤ)) :
    KernelShellCoordinates K (a,x,y,0) 0 k j h 0 := by
  apply kernelShellCoordinates_of_minima K (a,x,y,0) 0 k j h 0
  · exact actual_entry_minimum_integer_zero (localFieldValuation K) (a:K) x y k j h
      hk hj hh
  · exact actual_minor_minimum_integer_zero (localFieldValuation K) (a:K) x y k j h 0
      hk hj hh (Units.ne_zero a)

/-- At r≠0 the actual collision ratio determines the cancellation-depth input.
Off the collision locus the implication is vacuous and the index is independent
of c; the master measure weight separately forces c=0 there. -/
theorem kernelShellCoordinates_nonzero (a : Kˣ) (x y z : K)
    (r k j h : ℤ) (c : ℕ) (hr : r ≠ 0)
    (hk : localFieldValuation K (a : K) = (k : WithTop ℤ))
    (hj : localFieldValuation K x = (j : WithTop ℤ))
    (hh : localFieldValuation K y = (h : WithTop ℤ))
    (hz : localFieldValuation K z = ((-r : ℤ) : WithTop ℤ))
    (hc : 2*h = j-r → localFieldValuation K (y^2/(x*z)-1) = ((c:ℤ) : WithTop ℤ)) :
    KernelShellCoordinates K (a,x,y,z) r k j h c := by
  obtain ⟨he,hm⟩ := actual_minima_integer_nonzero (localFieldValuation K)
    (a:K) x y z r k j h c hr hk hj hh hz hc
  exact kernelShellCoordinates_of_minima K (a,x,y,z) r k j h c he hm

/-- The finite actual shell/collision hypotheses really exclude zero coordinates
and determinant zero; the discarded sets have not been assigned finite values. -/
theorem kernelShell_nonzero_locus (x y z : K) (r j h : ℤ) (c : ℕ)
    (hj : localFieldValuation K x = (j : WithTop ℤ))
    (hh : localFieldValuation K y = (h : WithTop ℤ))
    (hz : localFieldValuation K z = ((-r : ℤ) : WithTop ℤ))
    (hc : 2*h = j-r → localFieldValuation K (y^2/(x*z)-1) = ((c:ℤ) : WithTop ℤ)) :
    x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 ∧ y^2-x*z ≠ 0 := by
  have hd := actual_determinant_valuation (localFieldValuation K) x y z r j h c
    hj hh hz hc
  exact ⟨nonzero_of_integer_valuation _ _ _ hj,
    nonzero_of_integer_valuation _ _ _ hh, nonzero_of_integer_valuation _ _ _ hz,
    nonzero_of_integer_valuation _ _ _ hd⟩

end FourierJacobi.Valuations
