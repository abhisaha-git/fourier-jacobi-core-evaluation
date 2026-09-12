import FourierJacobi.Analysis.LatticeCore
import FourierJacobi.Analysis.PaperDomain

/-!
Evaluation and Abel limits of the independently defined infinite series.
The undamped core is evaluated before its principal prefactor is applied.
The special theorem concerns the whole signed product and never asserts an
ordinary endpoint sum at delta = ±t.
-/

noncomputable section
namespace FourierJacobi.Analysis
open FourierJacobi.Algebra Filter
open scoped Topology
set_option maxHeartbeats 4000000

theorem summable_norm_lattice_damped (q T : ℝ) (a b d : ℂ) (hq : 2 < q)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hT₀ : 0 < T) (hT₁ : T < 1)
    (hd₀ : inverseSqrt q ≤ ‖d‖) (hd₁ : ‖d‖ ≤ 1) :
    Summable (fun p : Fin 8 × Fin 3 × LatticeIndex =>
      ‖weightedLatticeTerm q a b d T p‖) := by
  apply summable_norm_weightedLatticeTerm q T a b d hq ha hb hT₀.le hT₁.le hd₀ hd₁
  have ht := inverseSqrt_pos (show 1 < q by linarith)
  nlinarith

theorem summable_norm_lattice_undamped (q : ℝ) (a b d : ℂ) (hq : 2 < q)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hd₀ : inverseSqrt q < ‖d‖) (hd₁ : ‖d‖ ≤ 1) :
    Summable (fun p : Fin 8 × Fin 3 × LatticeIndex =>
      ‖weightedLatticeTerm q a b d 1 p‖) := by
  apply summable_norm_weightedLatticeTerm q 1 a b d hq ha hb (by norm_num)
    (by norm_num) hd₀.le hd₁
  simpa only [one_mul] using hd₀

/-- The principal core evaluation, with no prefactor. This is a theorem
about the infinite lattice definition, not a definition by a rational value. -/
theorem latticeCore_eq_paperE (q : ℝ) (a b d : ℂ) (hq : 2 < q)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hd₀ : inverseSqrt q < ‖d‖) (hd₁ : ‖d‖ ≤ 1)
    (ha₁ : a ≠ 1) (hb₁ : b ≠ 1) (hab : a ≠ b) (hab₁ : a * b ≠ 1) :
    latticeCore q a b d 1 = paperE q a b d := by
  have hq' : 1 < q := by linarith
  rw [latticeCore_eq_dampedRational q 1 a b d hq ha hb (by norm_num)
    (by norm_num) hd₀.le hd₁ (by simpa only [one_mul] using hd₀)]
  rw [dampedRational_one, paperE_eq_closedCore q (by linarith)]
  exact finiteCore_eq_closedCore _ _ _ _
    (finiteRegular_interior (inverseSqrt_pos hq') (inverseSqrt_lt_one hq')
      ha hb hd₀ hd₁ ha₁ hb₁ hab hab₁)

/-- Abel convergence is proved by domination of the actual master summand
by its summable undamped norm, independently of finite rational continuity. -/
theorem tendsto_latticeCore_undamped (q : ℝ) (a b d : ℂ) (hq : 2 < q)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hd₀ : inverseSqrt q < ‖d‖) (hd₁ : ‖d‖ ≤ 1) :
    Tendsto (latticeCore q a b d) (𝓝[Set.Ioo 0 1] 1)
      (𝓝 (latticeCore q a b d 1)) := by
  have hq' : 1 < q := by linarith
  obtain ⟨ht, hq0, hq1, hq2, hqt⟩ := natural_master_parameters hq
  have hd : d ≠ 0 := norm_pos_iff.mp (lt_trans (inverseSqrt_pos hq') hd₀)
  unfold latticeCore
  apply Filter.Tendsto.div_const
  apply tendsto_finsetSum
  intro i _
  apply Filter.Tendsto.const_mul
  apply tendsto_finsetSum
  intro r _
  have h := geometricRange_undamped (inverseSqrt_pos hq') (inverseSqrt_lt_one hq')
    hd₀ hd₁ (weylU_unitary ha hb i) (weylV_unitary ha hb i)
  simpa only [Complex.ofReal_one] using
    tendsto_master_sum_of_summable (q : ℂ) (inverseSqrt q : ℂ) d
      (weylU a b i) (weylV a b i) (r.val : ℤ)
      (summable_norm_central_master (q : ℂ) (inverseSqrt q : ℂ) d
        (weylU a b i) (weylV a b i) 1 ht hd hq0 hq1 hq2 hqt h r)

theorem tendsto_latticeCore_paperE (q : ℝ) (a b d : ℂ) (hq : 2 < q)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hd₀ : inverseSqrt q < ‖d‖) (hd₁ : ‖d‖ ≤ 1)
    (ha₁ : a ≠ 1) (hb₁ : b ≠ 1) (hab : a ≠ b) (hab₁ : a * b ≠ 1) :
    Tendsto (latticeCore q a b d) (𝓝[Set.Ioo 0 1] 1)
      (𝓝 (paperE q a b d)) := by
  rw [← latticeCore_eq_paperE q a b d hq ha hb hd₀ hd₁ ha₁ hb₁ hab hab₁]
  exact tendsto_latticeCore_undamped q a b d hq ha hb hd₀ hd₁

/-- Corrected principal comparison at the series scope. The required
factor 2/(q+1) multiplies both the Abel limit and E_q. -/
theorem corrected_principal_lattice_comparison (q : ℝ) (a b d : ℂ) (hq : 2 < q)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hd₀ : inverseSqrt q < ‖d‖) (hd₁ : ‖d‖ ≤ 1)
    (ha₁ : a ≠ 1) (hb₁ : b ≠ 1) (hab : a ≠ b) (hab₁ : a * b ≠ 1) :
    (2 / ((q : ℂ) + 1) * latticeCore q a b d 1 =
      2 / ((q : ℂ) + 1) * paperE q a b d) ∧
    Tendsto (fun T => 2 / ((q : ℂ) + 1) * latticeCore q a b d T)
      (𝓝[Set.Ioo 0 1] 1) (𝓝 (2 / ((q : ℂ) + 1) * paperE q a b d)) := by
  exact ⟨congrArg (fun z => 2 / ((q : ℂ) + 1) * z)
    (latticeCore_eq_paperE q a b d hq ha hb hd₀ hd₁ ha₁ hb₁ hab hab₁),
    (tendsto_latticeCore_paperE q a b d hq ha hb hd₀ hd₁ ha₁ hb₁ hab hab₁).const_mul _⟩

theorem tendsto_lattice_special_negative (q : ℝ) (a b : ℂ) (hq : 2 < q)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (ha₁ : a ≠ 1) (hb₁ : b ≠ 1) (hab : a ≠ b) (hab₁ : a * b ≠ 1)
    (haM : a ≠ -1) (hbM : b ≠ -1) :
    Tendsto (fun T => ((1 - (-1 : ℂ)) / ((q : ℂ) + 1)) *
      latticeCore q a b (-(inverseSqrt q : ℂ)) T)
      (𝓝[Set.Ioo 0 1] 1)
      (𝓝 (((1 - (-1 : ℂ)) / ((q : ℂ) + 1)) *
        paperE q a b (-(inverseSqrt q : ℂ)))) := by
  have hq' : 1 < q := by linarith
  have ht := inverseSqrt_pos hq'
  have hn : ‖-(inverseSqrt q : ℂ)‖ = inverseSqrt q := by
    simp [abs_of_pos ht]
  apply (tendsto_dampedRational_special_negative q hq' a b ha hb
    ha₁ hb₁ hab hab₁ haM hbM).congr'
  filter_upwards [self_mem_nhdsWithin] with T hT
  rw [latticeCore_eq_dampedRational q T a b (-(inverseSqrt q : ℂ)) hq ha hb
    hT.1.le hT.2.le (by rw [hn]) (by rw [hn]; exact (inverseSqrt_lt_one hq').le)
    (by rw [hn]; nlinarith [hT.2])]

/-- At epsilon=1 the signed product is identically zero. This proof makes
no claim that the undamped endpoint core exists. -/
theorem tendsto_lattice_special_positive (q : ℝ) (a b : ℂ) :
    Tendsto (fun T => ((1 - (1 : ℂ)) / ((q : ℂ) + 1)) *
      latticeCore q a b (inverseSqrt q : ℂ) T)
      (𝓝[Set.Ioo 0 1] 1) (𝓝 0) :=
  tendsto_positive_zero_product q (latticeCore q a b (inverseSqrt q : ℂ))

/-- Corrected special comparison for the whole product, on the literal
endpoint quotient's regular locus. There is no extra normalization factor. -/
theorem corrected_special_lattice_comparison (q : ℝ) (a b ε : ℂ) (hq : 2 < q)
    (hε : ε = 1 ∨ ε = -1) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (ha₁ : a ≠ 1) (hb₁ : b ≠ 1) (hab : a ≠ b) (hab₁ : a * b ≠ 1)
    (haε : a ≠ ε) (hbε : b ≠ ε) :
    Tendsto (fun T => ((1 - ε) / ((q : ℂ) + 1)) *
      latticeCore q a b (ε * (inverseSqrt q : ℂ)) T)
      (𝓝[Set.Ioo 0 1] 1)
      (𝓝 (((1 - ε) / ((q : ℂ) + 1)) *
        paperE q a b (ε * (inverseSqrt q : ℂ)))) := by
  rcases hε with rfl | rfl
  · simpa only [sub_self, zero_div, zero_mul, one_mul] using
      tendsto_lattice_special_positive q a b
  · simpa only [neg_one_mul] using
      tendsto_lattice_special_negative q a b hq ha hb ha₁ hb₁ hab hab₁ haε hbε

/-- Complete undamped infinite-series evaluation and its Abel convergence,
including norm summability and validity of the literal closed quotient. -/
theorem infinite_lattice_core_evaluation (q : ℝ) (a b d : ℂ) (hq : 2 < q)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hd₀ : inverseSqrt q < ‖d‖) (hd₁ : ‖d‖ ≤ 1)
    (ha₁ : a ≠ 1) (hb₁ : b ≠ 1) (hab : a ≠ b) (hab₁ : a * b ≠ 1) :
    Summable (fun p : Fin 8 × Fin 3 × LatticeIndex =>
      ‖weightedLatticeTerm q a b d 1 p‖) ∧
    HasSum (weightedLatticeTerm q a b d 1) (paperE q a b d) ∧
    paperC q * paperD1 q a b d * paperD2 q a b d ≠ 0 ∧
    Tendsto (latticeCore q a b d) (𝓝[Set.Ioo 0 1] 1) (𝓝 (paperE q a b d)) := by
  have hn := summable_norm_lattice_undamped q a b d hq ha hb hd₀ hd₁
  have he := latticeCore_eq_paperE q a b d hq ha hb hd₀ hd₁ ha₁ hb₁ hab hab₁
  refine ⟨hn, ?_, ?_, tendsto_latticeCore_paperE q a b d hq ha hb
    hd₀ hd₁ ha₁ hb₁ hab hab₁⟩
  · rw [← he]
    exact hasSum_weightedLatticeTerm_of_norm q 1 a b d hn
  · exact paper_denominator_interior_ne_zero q (by linarith) a b d ha hb hd₀ hd₁

/-- The special Abel theorem packages convergence of every damped family,
the literal quotient's nonzero denominator, and the whole signed limit.
It contains no assertion about an ordinary undamped endpoint family. -/
theorem infinite_lattice_special_abel (q : ℝ) (a b ε : ℂ) (hq : 2 < q)
    (hε : ε = 1 ∨ ε = -1) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (ha₁ : a ≠ 1) (hb₁ : b ≠ 1) (hab : a ≠ b) (hab₁ : a * b ≠ 1)
    (haε : a ≠ ε) (hbε : b ≠ ε) :
    (∀ T ∈ Set.Ioo (0 : ℝ) 1,
      Summable (fun p : Fin 8 × Fin 3 × LatticeIndex =>
        ‖weightedLatticeTerm q a b (ε * (inverseSqrt q : ℂ)) T p‖) ∧
      HasSum (weightedLatticeTerm q a b (ε * (inverseSqrt q : ℂ)) T)
        (latticeCore q a b (ε * (inverseSqrt q : ℂ)) T)) ∧
    paperC q * paperD1 q a b (ε * (inverseSqrt q : ℂ)) *
      paperD2 q a b (ε * (inverseSqrt q : ℂ)) ≠ 0 ∧
    Tendsto (fun T => ((1 - ε) / ((q : ℂ) + 1)) *
      latticeCore q a b (ε * (inverseSqrt q : ℂ)) T)
      (𝓝[Set.Ioo 0 1] 1)
      (𝓝 (((1 - ε) / ((q : ℂ) + 1)) *
        paperE q a b (ε * (inverseSqrt q : ℂ)))) := by
  have hq' : 1 < q := by linarith
  refine ⟨?_, paper_denominator_special_ne_zero q hq' a b ε ha hb hε haε hbε,
    corrected_special_lattice_comparison q a b ε hq hε ha hb ha₁ hb₁ hab hab₁ haε hbε⟩
  intro T hT
  have hnε : ‖ε‖ = 1 := by rcases hε with rfl | rfl <;> simp
  have hnd : ‖ε * (inverseSqrt q : ℂ)‖ = inverseSqrt q := by
    simp [hnε, abs_of_pos (inverseSqrt_pos hq')]
  have hn := summable_norm_lattice_damped q T a b (ε * (inverseSqrt q : ℂ))
    hq ha hb hT.1 hT.2 (by rw [hnd]) (by rw [hnd]; exact (inverseSqrt_lt_one hq').le)
  exact ⟨hn, hasSum_weightedLatticeTerm_of_norm q T a b (ε * (inverseSqrt q : ℂ)) hn⟩

end FourierJacobi.Analysis
