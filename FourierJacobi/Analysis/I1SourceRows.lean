import FourierJacobi.Analysis.I1Assembly

/-! One HasSum declaration for each of the fifteen restored source rows.
The two parity rows use the explicit disjoint sum of their checked cells. -/
noncomputable section
namespace FourierJacobi.Analysis
open FourierJacobi.Algebra
set_option linter.unusedSimpArgs false

theorem hasSum_i1_source_case1 (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hq0 : q ≠ 0) (hq1 : q-1 ≠ 0)
    (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    HasSum (fun p : I1Cell 0 => masterTerm q t d U V T 1 p.val)
      (regionTerms t d (T*U) (T*V) 10) := by
  have hs := hasSum_i1r1_master q t d U V T ht hq0 hq1 hqt h
  rw [i1r1_value_eq q t d U V T ht hd hqt h] at hs
  exact hs

theorem hasSum_i1_source_case2 (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hq0 : q ≠ 0) (hq1 : q-1 ≠ 0)
    (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    HasSum (fun p : I1Cell 1 => masterTerm q t d U V T 1 p.val)
      (regionTerms t d (T*U) (T*V) 11) := by
  have hs := hasSum_i1r2_master q t d U V T ht hq0 hq1 hqt h
  rw [i1r2_value_eq q t d U V T ht hd hqt h] at hs
  exact hs

theorem hasSum_i1_source_case3a (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hq0 : q ≠ 0) (hq1 : q-1 ≠ 0)
    (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    HasSum (Sum.elim (fun p : I1Cell 2 => masterTerm q t d U V T 1 p.val)
        (fun p : I1Cell 3 => masterTerm q t d U V T 1 p.val))
      (regionTerms t d (T*U) (T*V) 12) := by
  have h1 := hasSum_i1r3ae_master q t d U V T ht hq0 hq1 hqt h
  have h2 := hasSum_i1r3ao_master q t d U V T ht hq0 hq1 hqt h
  rw [i1r3ae_value_eq q t d U V T ht hd hqt h] at h1
  rw [i1r3ao_value_eq q t d U V T ht hd hqt h] at h2
  have hs := h1.sum (f := (Sum.elim (fun p : I1Cell 2 => masterTerm q t d U V T 1 p.val)
        (fun p : I1Cell 3 => masterTerm q t d U V T 1 p.val))) h2
  convert hs using 1
  change regionTerm12 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4) = _
  unfold regionTerm12
  simp only [pow_one]
  ring

theorem hasSum_i1_source_case3b (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hq0 : q ≠ 0) (hq1 : q-1 ≠ 0)
    (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    HasSum (fun p : I1Cell 4 => masterTerm q t d U V T 1 p.val)
      (regionTerms t d (T*U) (T*V) 13) := by
  have hs := hasSum_i1r3b_master q t d U V T ht hq0 hq1 hqt h
  rw [i1r3b_value_eq q t d U V T ht hd hqt h] at hs
  exact hs

theorem hasSum_i1_source_case3c (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hq0 : q ≠ 0) (hq1 : q-1 ≠ 0)
    (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    HasSum (fun p : I1Cell 5 => masterTerm q t d U V T 1 p.val)
      (regionTerms t d (T*U) (T*V) 14) := by
  have hs := hasSum_i1r3c_master q t d U V T ht hq0 hq1 hqt h
  rw [i1r3c_value_eq q t d U V T ht hd hqt h] at hs
  exact hs

theorem hasSum_i1_source_case4 (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hq0 : q ≠ 0) (hq1 : q-1 ≠ 0)
    (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    HasSum (fun p : I1Cell 6 => masterTerm q t d U V T 1 p.val)
      (regionTerms t d (T*U) (T*V) 15) := by
  have hs := hasSum_i1r4_master q t d U V T ht hq0 hq1 hqt h
  rw [i1r4_value_eq q t d U V T ht hd hqt h] at hs
  exact hs

theorem hasSum_i1_source_case5 (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hq0 : q ≠ 0) (hq1 : q-1 ≠ 0)
    (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    HasSum (fun p : I1Cell 7 => masterTerm q t d U V T 1 p.val)
      (regionTerms t d (T*U) (T*V) 16) := by
  have hs := hasSum_i1r5_master q t d U V T ht hq0 hq1 hqt h
  rw [i1r5_value_eq q t d U V T ht hd hqt h] at hs
  exact hs

theorem hasSum_i1_source_case6a (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hq0 : q ≠ 0) (hq1 : q-1 ≠ 0)
    (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    HasSum (fun p : I1Cell 8 => masterTerm q t d U V T 1 p.val)
      (regionTerms t d (T*U) (T*V) 17) := by
  have hs := hasSum_i1r6a_master q t d U V T ht hq0 hq1 hqt h
  rw [i1r6a_value_eq q t d U V T ht hd hqt h] at hs
  exact hs

theorem hasSum_i1_source_case6b (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hq0 : q ≠ 0) (hq1 : q-1 ≠ 0)
    (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    HasSum (fun p : I1Cell 9 => masterTerm q t d U V T 1 p.val)
      (regionTerms t d (T*U) (T*V) 18) := by
  have hs := hasSum_i1r6b_master q t d U V T ht hq0 hq1 hqt h
  rw [i1r6b_value_eq q t d U V T ht hd hqt h] at hs
  exact hs

theorem hasSum_i1_source_case7 (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hq0 : q ≠ 0) (hq1 : q-1 ≠ 0)
    (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    HasSum (fun p : I1Cell 10 => masterTerm q t d U V T 1 p.val)
      (regionTerms t d (T*U) (T*V) 19) := by
  have hs := hasSum_i1r7_master q t d U V T ht hq0 hq1 hqt h
  rw [i1r7_value_eq q t d U V T ht hd hqt h] at hs
  exact hs

theorem hasSum_i1_source_case8a (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hq0 : q ≠ 0) (hq1 : q-1 ≠ 0)
    (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    HasSum (Sum.elim (fun p : I1Cell 11 => masterTerm q t d U V T 1 p.val)
        (fun p : I1Cell 12 => masterTerm q t d U V T 1 p.val))
      (regionTerms t d (T*U) (T*V) 20) := by
  have h1 := hasSum_i1r8ae_master q t d U V T ht hq0 hq1 hqt h
  have h2 := hasSum_i1r8ao_master q t d U V T ht hq0 hq1 hqt h
  rw [i1r8ae_value_eq q t d U V T ht hd hqt h] at h1
  rw [i1r8ao_value_eq q t d U V T ht hd hqt h] at h2
  have hs := h1.sum (f := (Sum.elim (fun p : I1Cell 11 => masterTerm q t d U V T 1 p.val)
        (fun p : I1Cell 12 => masterTerm q t d U V T 1 p.val))) h2
  convert hs using 1
  change regionTerm20 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4) = _
  unfold regionTerm20
  simp only [pow_one]
  ring

theorem hasSum_i1_source_case8b (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hq0 : q ≠ 0) (hq1 : q-1 ≠ 0)
    (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    HasSum (fun p : I1Cell 13 => masterTerm q t d U V T 1 p.val)
      (regionTerms t d (T*U) (T*V) 21) := by
  have hs := hasSum_i1r8b_master q t d U V T ht hq0 hq1 hqt h
  rw [i1r8b_value_eq q t d U V T ht hd hqt h] at hs
  exact hs

theorem hasSum_i1_source_case8c (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hq0 : q ≠ 0) (hq1 : q-1 ≠ 0)
    (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    HasSum (fun p : I1Cell 14 => masterTerm q t d U V T 1 p.val)
      (regionTerms t d (T*U) (T*V) 22) := by
  have hs := hasSum_i1r8c_master q t d U V T ht hq0 hq1 hqt h
  rw [i1r8c_value_eq q t d U V T ht hd hqt h] at hs
  exact hs

theorem hasSum_i1_source_case9 (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hq0 : q ≠ 0) (hq1 : q-1 ≠ 0)
    (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    HasSum (fun p : I1Cell 15 => masterTerm q t d U V T 1 p.val)
      (regionTerms t d (T*U) (T*V) 23) := by
  have hs := hasSum_i1r9_master q t d U V T ht hq0 hq1 hqt h
  rw [i1r9_value_eq q t d U V T ht hd hqt h] at hs
  exact hs

theorem hasSum_i1_source_case10 (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hq0 : q ≠ 0) (hq1 : q-1 ≠ 0)
    (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    HasSum (fun p : I1Cell 16 => masterTerm q t d U V T 1 p.val)
      (regionTerms t d (T*U) (T*V) 24) := by
  have hs := hasSum_i1r10_master q t d U V T ht hq0 hq1 hqt h
  rw [i1r10_value_eq q t d U V T ht hd hqt h] at hs
  exact hs

end FourierJacobi.Analysis
