import FourierJacobi.Analysis.CoreParameters
import Mathlib.Tactic.FunProp

/-!
Continuity of the finite expression obtained by damping the UNSUMMED row
monomials. Identification with the independent lattice family is a separate
theorem in the assembly. These lemmas alone do not evaluate an infinite sum.
-/

noncomputable section
namespace FourierJacobi.Analysis
open FourierJacobi.Algebra Filter
open scoped Topology

set_option maxHeartbeats 4000000

def dampedRational (t : ℝ) (a b d : ℂ) (T : ℝ) : ℂ :=
  (∑ i : Fin 8, weylWeights (t : ℂ) a b i *
    ∑ ν : Fin 50, regionTerms (t : ℂ) d
      ((T : ℂ) * weylU a b i) ((T : ℂ) * weylV a b i) ν) /
    poincare (t : ℂ)

@[simp] theorem dampedRational_one (t : ℝ) (a b d : ℂ) :
    dampedRational t a b d 1 = finiteCore (t : ℂ) a b d := by
  simp only [dampedRational, finiteCore, Complex.ofReal_one, one_mul]

theorem continuousAt_damped_regionTerm (t d U V : ℂ) (hd : d ≠ 0)
    (h : RegionRegular t d U V) (i : Fin 50) :
    ContinuousAt (fun T : ℝ => regionTerms t d ((T : ℂ) * U) ((T : ℂ) * V) i) 1 := by
  have hp := h.p
  have hn := h.n
  have he := h.e
  have hf := h.f
  have hg := h.g
  have hct : ContinuousAt (fun T : ℝ => (T : ℂ)) 1 :=
    Complex.continuous_ofReal.continuousAt
  fin_cases i
  · change ContinuousAt (fun T : ℝ => regionTerm0 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm0
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm1 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm1
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm2 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm2
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm3 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm3
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm4 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm4
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm5 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm5
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm6 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm6
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm7 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm7
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm8 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm8
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm9 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm9
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm10 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm10
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm11 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm11
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm12 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm12
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm13 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm13
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm14 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm14
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm15 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm15
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm16 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm16
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm17 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm17
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm18 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm18
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm19 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm19
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm20 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm20
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm21 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm21
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm22 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm22
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm23 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm23
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm24 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm24
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm25 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm25
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm26 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm26
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm27 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm27
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm28 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm28
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm29 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm29
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm30 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm30
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm31 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm31
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm32 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm32
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm33 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm33
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm34 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm34
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm35 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm35
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm36 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm36
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm37 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm37
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm38 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm38
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm39 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm39
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm40 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm40
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm41 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm41
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm42 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm42
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm43 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm43
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm44 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm44
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm45 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm45
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm46 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm46
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm47 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm47
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm48 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm48
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm49 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm49
    fun_prop (disch := simp_all)

theorem continuousAt_dampedRational (t : ℝ) (a b d : ℂ)
    (h : FiniteRegular (t : ℂ) a b d) :
    ContinuousAt (dampedRational t a b d) 1 := by
  unfold dampedRational
  apply ContinuousAt.div_const
  apply tendsto_finsetSum
  intro i _
  apply Filter.Tendsto.const_mul
  apply tendsto_finsetSum
  intro j _
  exact (continuousAt_damped_regionTerm (t : ℂ) d (weylU a b i) (weylV a b i)
    h.d_ne_zero (h.rows i) j).tendsto

theorem tendsto_dampedRational (t : ℝ) (a b d : ℂ)
    (h : FiniteRegular (t : ℂ) a b d) :
    Tendsto (dampedRational t a b d) (𝓝[Set.Ioo 0 1] 1)
      (𝓝 (closedCore (t : ℂ) a b d)) := by
  have hc := (continuousAt_dampedRational t a b d h).tendsto.mono_left
    (nhdsWithin_le_nhds (s := Set.Ioo (0 : ℝ) 1))
  simpa only [dampedRational_one, finiteCore_eq_closedCore _ _ _ _ h] using hc

/-- Whole-product zero limit. No convergence of f itself is asserted. -/
theorem tendsto_positive_zero_product (q : ℝ) (f : ℝ → ℂ) :
    Tendsto (fun T => ((1 - (1 : ℂ)) / ((q : ℂ) + 1)) * f T)
      (𝓝[Set.Ioo 0 1] 1) (𝓝 0) := by
  simpa only [sub_self, zero_div, zero_mul] using
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℂ)) (𝓝[Set.Ioo 0 1] 1) (𝓝 0))

theorem tendsto_dampedRational_principal (q : ℝ) (hq : 1 < q) (a b d : ℂ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hd : ‖d‖ = 1)
    (ha₁ : a ≠ 1) (hb₁ : b ≠ 1) (hab : a ≠ b) (hab₁ : a * b ≠ 1) :
    Tendsto (fun T => 2 / ((q : ℂ) + 1) * dampedRational (inverseSqrt q) a b d T)
      (𝓝[Set.Ioo 0 1] 1) (𝓝 (2 / ((q : ℂ) + 1) * paperE q a b d)) := by
  rw [paperE_eq_closedCore q (by linarith)]
  exact (tendsto_dampedRational (inverseSqrt q) a b d
    (finiteRegular_unitary (inverseSqrt_pos hq).le (inverseSqrt_lt_one hq)
      ha hb hd (sub_ne_zero.mpr ha₁) (sub_ne_zero.mpr hb₁)
      (sub_ne_zero.mpr hab) (sub_ne_zero.mpr hab₁))).const_mul _

theorem tendsto_dampedRational_special_negative (q : ℝ) (hq : 1 < q) (a b : ℂ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (ha₁ : a ≠ 1) (hb₁ : b ≠ 1) (hab : a ≠ b) (hab₁ : a * b ≠ 1)
    (haM : a ≠ -1) (hbM : b ≠ -1) :
    Tendsto (fun T => ((1 - (-1 : ℂ)) / ((q : ℂ) + 1)) *
      dampedRational (inverseSqrt q) a b (-(inverseSqrt q : ℂ)) T)
      (𝓝[Set.Ioo 0 1] 1)
      (𝓝 (((1 - (-1 : ℂ)) / ((q : ℂ) + 1)) *
        paperE q a b (-(inverseSqrt q : ℂ)))) := by
  rw [paperE_eq_closedCore q (by linarith)]
  have hA : 1 + a ≠ 0 := by intro he; apply haM; linear_combination he
  have hB : 1 + b ≠ 0 := by intro he; apply hbM; linear_combination he
  exact (tendsto_dampedRational (inverseSqrt q) a b (-(inverseSqrt q : ℂ))
    (finiteRegular_special_negative (inverseSqrt_pos hq) (inverseSqrt_lt_one hq)
      ha hb (sub_ne_zero.mpr ha₁) (sub_ne_zero.mpr hb₁)
      (sub_ne_zero.mpr hab) (sub_ne_zero.mpr hab₁) hA hB)).const_mul _

end FourierJacobi.Analysis
