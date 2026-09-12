import FourierJacobi.Analysis.I1Partition
import FourierJacobi.Analysis.CoreParameters

/-! Complete I1 depth weights, absolute summability, and restored row sums. -/
noncomputable section
namespace FourierJacobi.Analysis
open FourierJacobi.Valuations
open FourierJacobi.Algebra
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

theorem i1_qinv_eq (q t : ℂ) (ht : t ≠ 0) (hqt : q * t ^ 2 = 1) :
    q⁻¹ = t ^ 2 := by
  have he : q = (t ^ 2)⁻¹ := by
    calc
      q = q * (t ^ 2 * (t ^ 2)⁻¹) := by rw [mul_inv_cancel₀ (pow_ne_zero 2 ht), mul_one]
      _ = (t ^ 2)⁻¹ := by rw [← mul_assoc, hqt, one_mul]
  rw [he, inv_inv]

theorem i1_prob0_eq (q t : ℂ) (ht : t ≠ 0) (hqt : q*t^2=1)
    (hz : 1-t^2 ≠ 0) : collisionProbability q 0 = (1-2*t^2)/(1-t^2) := by
  have he : q = (t^2)⁻¹ := by
    rw [← i1_qinv_eq q t ht hqt, inv_inv]
  simp only [collisionProbability, if_true]
  rw [he]
  field_simp [ht,hz]
  <;> ring

theorem i1_summable_norm_prob_tail (q : ℂ) (hq : ‖q⁻¹‖ < 1) :
    Summable (fun c : ℕ => ‖collisionProbability q (c+1)‖) := by
  simpa only [collisionProbability_succ, norm_mul] using
    (geometric_norm_summable q⁻¹ hq).mul_left ‖q⁻¹‖

theorem i1_hasSum_product {ι κ : Type*} (f : ι → ℂ) (g : κ → ℂ)
    (s z : ℂ) (hf : HasSum f s) (hg : HasSum g z)
    (hfn : Summable (fun p => ‖f p‖)) (hgn : Summable (fun p => ‖g p‖)) :
    HasSum (fun p : ι × κ => f p.1 * g p.2) (s*z) := by
  have hs := (hfn.mul_norm hgn).of_norm
  have he := tsum_mul_tsum_of_summable_norm hfn hgn
  rw [hf.tsum_eq,hg.tsum_eq] at he
  exact he.symm ▸ hs.hasSum

theorem i1r1_master_reindexed (q t d U V T : ℂ) (ht : t ≠ 0)
    (hqt : q*t^2=1) (p : I1R1Row × ℕ) :
    masterTerm q t d U V T 1 (i1r1DepthEquiv p).val =
      i1Raw t d U V T p.1.val 0 * collisionWeight q 1 p.1.val.2.1 p.1.val.2.2 p.2 := by
  rw [i1r1DepthEquiv_val]
  unfold masterTerm
  rw [← i1Raw_eq_shell q t d U V T ht hqt]
  have he : i1Raw t d U V T p.1.val (p.2) =
      i1Raw t d U V T p.1.val 0 := by
    unfold i1Raw
    rw [i1r1_cartan, i1r1_cartan]
    
  rw [he]

theorem hasSum_i1r1_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hq0 : q ≠ 0) (hq1 : q-1 ≠ 0)
    (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    HasSum (fun p : I1Cell 0 => masterTerm q t d U V T 1 p.val)
      (((1 - t ^ 2) ^ 3 * d * (T * U) * t) * (1 - d * T * V * t)⁻¹ * (1 - t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hs := hasSum_i1r1_raw t d U V T 0 h.p h.t2 h.t2
  have hn := summable_norm_i1r1_raw t d U V T 0 h.p h.t2 h.t2
  apply i1r1DepthEquiv.hasSum_iff.mp
  convert hasSum_weighted_collision q 1
    (fun p : I1R1Row => p.val.2.1) (fun p : I1R1Row => p.val.2.2)
    (fun p : I1R1Row => i1Raw t d U V T p.val 0) _ hq0 hq1 hq hs hn using 1
  exact funext fun p => i1r1_master_reindexed q t d U V T ht hqt p

theorem summable_norm_i1r1_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    Summable (fun p : I1Cell 0 => ‖masterTerm q t d U V T 1 p.val‖) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hn := summable_norm_i1r1_raw t d U V T 0 h.p h.t2 h.t2
  apply i1r1DepthEquiv.summable_iff.mp
  convert summable_norm_weighted_collision q 1
    (fun p : I1R1Row => p.val.2.1) (fun p : I1R1Row => p.val.2.2)
    (fun p : I1R1Row => i1Raw t d U V T p.val 0) hq hn using 1
  exact funext fun p => congrArg norm (i1r1_master_reindexed q t d U V T ht hqt p)

theorem i1r1_value_eq (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hqt : q*t^2=1)
    (h : GeometricRange t d U V T) :
    (((1 - t ^ 2) ^ 3 * d * (T * U) * t) * (1 - d * T * V * t)⁻¹ * (1 - t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹) = (regionTerm10 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4)) := by
  have hz := norm_one_sub_ne_zero h.t2
  have hp := norm_one_sub_ne_zero h.p
  have hn := norm_one_sub_ne_zero h.n
  have he := norm_one_sub_ne_zero h.e
  have hf := norm_one_sub_ne_zero h.f
  have hg := norm_one_sub_ne_zero h.g
  
  unfold regionTerm10
  simp only [pow_one, mul_assoc] at *
  field_simp [hz,hp,hn,he,hf,hg,ht,hd]
  <;> ring

theorem i1r2_master_reindexed (q t d U V T : ℂ) (ht : t ≠ 0)
    (hqt : q*t^2=1) (p : I1R2Row × ℕ) :
    masterTerm q t d U V T 1 (i1r2DepthEquiv p).val =
      i1Raw t d U V T p.1.val 0 * collisionWeight q 1 p.1.val.2.1 p.1.val.2.2 p.2 := by
  rw [i1r2DepthEquiv_val]
  unfold masterTerm
  rw [← i1Raw_eq_shell q t d U V T ht hqt]
  have he : i1Raw t d U V T p.1.val (p.2) =
      i1Raw t d U V T p.1.val 0 := by
    unfold i1Raw
    rw [i1r2_cartan, i1r2_cartan]
    
  rw [he]

theorem hasSum_i1r2_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hq0 : q ≠ 0) (hq1 : q-1 ≠ 0)
    (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    HasSum (fun p : I1Cell 1 => masterTerm q t d U V T 1 p.val)
      (((1 - t ^ 2) ^ 3 * d * (T * U) * (T * V) * t ^ 3) * (1 - d * T * V * t)⁻¹ * (1 - t ^ 2)⁻¹ * (1 - T * U * t ^ 4)⁻¹) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hs := hasSum_i1r2_raw t d U V T 0 h.p h.t2 h.g
  have hn := summable_norm_i1r2_raw t d U V T 0 h.p h.t2 h.g
  apply i1r2DepthEquiv.hasSum_iff.mp
  convert hasSum_weighted_collision q 1
    (fun p : I1R2Row => p.val.2.1) (fun p : I1R2Row => p.val.2.2)
    (fun p : I1R2Row => i1Raw t d U V T p.val 0) _ hq0 hq1 hq hs hn using 1
  exact funext fun p => i1r2_master_reindexed q t d U V T ht hqt p

theorem summable_norm_i1r2_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    Summable (fun p : I1Cell 1 => ‖masterTerm q t d U V T 1 p.val‖) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hn := summable_norm_i1r2_raw t d U V T 0 h.p h.t2 h.g
  apply i1r2DepthEquiv.summable_iff.mp
  convert summable_norm_weighted_collision q 1
    (fun p : I1R2Row => p.val.2.1) (fun p : I1R2Row => p.val.2.2)
    (fun p : I1R2Row => i1Raw t d U V T p.val 0) hq hn using 1
  exact funext fun p => congrArg norm (i1r2_master_reindexed q t d U V T ht hqt p)

theorem i1r2_value_eq (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hqt : q*t^2=1)
    (h : GeometricRange t d U V T) :
    (((1 - t ^ 2) ^ 3 * d * (T * U) * (T * V) * t ^ 3) * (1 - d * T * V * t)⁻¹ * (1 - t ^ 2)⁻¹ * (1 - T * U * t ^ 4)⁻¹) = (regionTerm11 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4)) := by
  have hz := norm_one_sub_ne_zero h.t2
  have hp := norm_one_sub_ne_zero h.p
  have hn := norm_one_sub_ne_zero h.n
  have he := norm_one_sub_ne_zero h.e
  have hf := norm_one_sub_ne_zero h.f
  have hg := norm_one_sub_ne_zero h.g
  
  unfold regionTerm11
  simp only [pow_one, mul_assoc] at *
  field_simp [hz,hp,hn,he,hf,hg,ht,hd]
  <;> ring

theorem i1r3ae_master_reindexed (q t d U V T : ℂ) (ht : t ≠ 0)
    (hqt : q*t^2=1) (p : I1R3AERow × ℕ) :
    masterTerm q t d U V T 1 (i1r3aeDepthEquiv p).val =
      i1Raw t d U V T p.1.val 0 * collisionWeight q 1 p.1.val.2.1 p.1.val.2.2 p.2 := by
  rw [i1r3aeDepthEquiv_val]
  unfold masterTerm
  rw [← i1Raw_eq_shell q t d U V T ht hqt]
  have he : i1Raw t d U V T p.1.val (p.2) =
      i1Raw t d U V T p.1.val 0 := by
    unfold i1Raw
    rw [i1r3ae_cartan, i1r3ae_cartan]
    
  rw [he]

theorem hasSum_i1r3ae_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hq0 : q ≠ 0) (hq1 : q-1 ≠ 0)
    (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    HasSum (fun p : I1Cell 2 => masterTerm q t d U V T 1 p.val)
      (((1 - t ^ 2) ^ 3 * d * (T * U) * (T * V)^2 * t^3) * (1 - d * T * V * t)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hs := hasSum_i1r3ae_raw t d U V T 0 h.p h.e h.t2
  have hn := summable_norm_i1r3ae_raw t d U V T 0 h.p h.e h.t2
  apply i1r3aeDepthEquiv.hasSum_iff.mp
  convert hasSum_weighted_collision q 1
    (fun p : I1R3AERow => p.val.2.1) (fun p : I1R3AERow => p.val.2.2)
    (fun p : I1R3AERow => i1Raw t d U V T p.val 0) _ hq0 hq1 hq hs hn using 1
  exact funext fun p => i1r3ae_master_reindexed q t d U V T ht hqt p

theorem summable_norm_i1r3ae_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    Summable (fun p : I1Cell 2 => ‖masterTerm q t d U V T 1 p.val‖) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hn := summable_norm_i1r3ae_raw t d U V T 0 h.p h.e h.t2
  apply i1r3aeDepthEquiv.summable_iff.mp
  convert summable_norm_weighted_collision q 1
    (fun p : I1R3AERow => p.val.2.1) (fun p : I1R3AERow => p.val.2.2)
    (fun p : I1R3AERow => i1Raw t d U V T p.val 0) hq hn using 1
  exact funext fun p => congrArg norm (i1r3ae_master_reindexed q t d U V T ht hqt p)

theorem i1r3ae_value_eq (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hqt : q*t^2=1)
    (h : GeometricRange t d U V T) :
    (((1 - t ^ 2) ^ 3 * d * (T * U) * (T * V)^2 * t^3) * (1 - d * T * V * t)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹) = ((1-t^2)^2 * d * (T*U) * (T * V)^2 * t^3 * (1 - d * (T * V) * t)⁻¹ * (1 - (T * V)^2 * t^2)⁻¹) := by
  have hz := norm_one_sub_ne_zero h.t2
  have hp := norm_one_sub_ne_zero h.p
  have hn := norm_one_sub_ne_zero h.n
  have he := norm_one_sub_ne_zero h.e
  have hf := norm_one_sub_ne_zero h.f
  have hg := norm_one_sub_ne_zero h.g
  
  
  simp only [pow_one, mul_assoc] at *
  field_simp [hz,hp,hn,he,hf,hg,ht,hd]
  <;> ring

theorem i1r3ao_master_reindexed (q t d U V T : ℂ) (ht : t ≠ 0)
    (hqt : q*t^2=1) (p : I1R3AORow × ℕ) :
    masterTerm q t d U V T 1 (i1r3aoDepthEquiv p).val =
      i1Raw t d U V T p.1.val 0 * collisionWeight q 1 p.1.val.2.1 p.1.val.2.2 p.2 := by
  rw [i1r3aoDepthEquiv_val]
  unfold masterTerm
  rw [← i1Raw_eq_shell q t d U V T ht hqt]
  have he : i1Raw t d U V T p.1.val (p.2) =
      i1Raw t d U V T p.1.val 0 := by
    unfold i1Raw
    rw [i1r3ao_cartan, i1r3ao_cartan]
    
  rw [he]

theorem hasSum_i1r3ao_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hq0 : q ≠ 0) (hq1 : q-1 ≠ 0)
    (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    HasSum (fun p : I1Cell 3 => masterTerm q t d U V T 1 p.val)
      (((1 - t ^ 2) ^ 3 * d * (T * U) * (T * V) * t^3) * (1 - d * T * V * t)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hs := hasSum_i1r3ao_raw t d U V T 0 h.p h.e h.t2
  have hn := summable_norm_i1r3ao_raw t d U V T 0 h.p h.e h.t2
  apply i1r3aoDepthEquiv.hasSum_iff.mp
  convert hasSum_weighted_collision q 1
    (fun p : I1R3AORow => p.val.2.1) (fun p : I1R3AORow => p.val.2.2)
    (fun p : I1R3AORow => i1Raw t d U V T p.val 0) _ hq0 hq1 hq hs hn using 1
  exact funext fun p => i1r3ao_master_reindexed q t d U V T ht hqt p

theorem summable_norm_i1r3ao_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    Summable (fun p : I1Cell 3 => ‖masterTerm q t d U V T 1 p.val‖) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hn := summable_norm_i1r3ao_raw t d U V T 0 h.p h.e h.t2
  apply i1r3aoDepthEquiv.summable_iff.mp
  convert summable_norm_weighted_collision q 1
    (fun p : I1R3AORow => p.val.2.1) (fun p : I1R3AORow => p.val.2.2)
    (fun p : I1R3AORow => i1Raw t d U V T p.val 0) hq hn using 1
  exact funext fun p => congrArg norm (i1r3ao_master_reindexed q t d U V T ht hqt p)

theorem i1r3ao_value_eq (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hqt : q*t^2=1)
    (h : GeometricRange t d U V T) :
    (((1 - t ^ 2) ^ 3 * d * (T * U) * (T * V) * t^3) * (1 - d * T * V * t)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹) = ((1-t^2)^2 * d * (T*U) * (T * V)^1 * t^3 * (1 - d * (T * V) * t)⁻¹ * (1 - (T * V)^2 * t^2)⁻¹) := by
  have hz := norm_one_sub_ne_zero h.t2
  have hp := norm_one_sub_ne_zero h.p
  have hn := norm_one_sub_ne_zero h.n
  have he := norm_one_sub_ne_zero h.e
  have hf := norm_one_sub_ne_zero h.f
  have hg := norm_one_sub_ne_zero h.g
  
  
  simp only [pow_one, mul_assoc] at *
  field_simp [hz,hp,hn,he,hf,hg,ht,hd]
  <;> ring

theorem i1r3b_master_reindexed (q t d U V T : ℂ) (ht : t ≠ 0)
    (hqt : q*t^2=1) (p : I1R3BRow) :
    masterTerm q t d U V T 1 (i1r3bDepthEquiv p).val =
      i1Raw t d U V T p.val 0 * collisionProbability q 0 := by
  rw [i1r3bDepthEquiv_val]
  unfold masterTerm
  rw [← i1Raw_eq_shell q t d U V T ht hqt]
  have hc : 2*p.val.2.2 = p.val.2.1-1 := p.property.2.2.2
  simp only [collisionWeight, one_ne_zero, hc, ne_eq, not_true_eq_false, false_or, if_false]

theorem hasSum_i1r3b_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hq0 : q ≠ 0) (hq1 : q-1 ≠ 0)
    (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    HasSum (fun p : I1Cell 4 => masterTerm q t d U V T 1 p.val)
      (((1 - t ^ 2) ^ 3 * d * (T * U) * (T * V) * t) * (1 - d * T * V * t)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (collisionProbability q 0)) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hs := hasSum_i1r3b_raw t d U V T h.p h.e
  have hn := summable_norm_i1r3b_raw t d U V T h.p h.e
  apply i1r3bDepthEquiv.hasSum_iff.mp
  convert hs.mul_right (collisionProbability q 0) using 1
  all_goals try rfl
  exact funext fun p => i1r3b_master_reindexed q t d U V T ht hqt p

theorem summable_norm_i1r3b_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    Summable (fun p : I1Cell 4 => ‖masterTerm q t d U V T 1 p.val‖) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hn := summable_norm_i1r3b_raw t d U V T h.p h.e
  apply i1r3bDepthEquiv.summable_iff.mp
  convert hn.mul_right ‖collisionProbability q 0‖ using 1
  all_goals try rfl
  exact funext fun p => by
    simpa only [norm_mul, Function.comp_apply] using
      congrArg norm (i1r3b_master_reindexed q t d U V T ht hqt p)

theorem i1r3b_value_eq (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hqt : q*t^2=1)
    (h : GeometricRange t d U V T) :
    (((1 - t ^ 2) ^ 3 * d * (T * U) * (T * V) * t) * (1 - d * T * V * t)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (collisionProbability q 0)) = (regionTerm13 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4)) := by
  have hz := norm_one_sub_ne_zero h.t2
  have hp := norm_one_sub_ne_zero h.p
  have hn := norm_one_sub_ne_zero h.n
  have he := norm_one_sub_ne_zero h.e
  have hf := norm_one_sub_ne_zero h.f
  have hg := norm_one_sub_ne_zero h.g
  rw [i1_prob0_eq q t ht hqt hz]
  unfold regionTerm13
  simp only [pow_one, mul_assoc] at *
  field_simp [hz,hp,hn,he,hf,hg,ht,hd]
  <;> ring

theorem i1r3c_master_reindexed (q t d U V T : ℂ) (ht : t ≠ 0)
    (hqt : q*t^2=1) (p : I1R3CRow × ℕ) :
    masterTerm q t d U V T 1 (i1r3cDepthEquiv p).val =
      i1Raw t d U V T p.1.val 1 * collisionProbability q (p.2+1) := by
  rw [i1r3cDepthEquiv_val]
  unfold masterTerm
  rw [← i1Raw_eq_shell q t d U V T ht hqt]
  have he : i1Raw t d U V T p.1.val (p.2 + 1) =
      i1Raw t d U V T p.1.val 1 := by
    unfold i1Raw
    rw [i1r3c_cartan, i1r3c_cartan]
    all_goals omega
  rw [he]
  have hc : 2*p.1.val.2.2 = p.1.val.2.1-1 := p.1.property.2.2.2
  simp only [collisionWeight, one_ne_zero, hc, ne_eq, not_true_eq_false, false_or, if_false]

theorem hasSum_i1r3c_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hq0 : q ≠ 0) (hq1 : q-1 ≠ 0)
    (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    HasSum (fun p : I1Cell 5 => masterTerm q t d U V T 1 p.val)
      (((1 - t ^ 2) ^ 3 * d * (T * V)^2 / t) * (1 - d * T * V * t)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (q⁻¹ * (1 - q⁻¹)⁻¹)) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hs := hasSum_i1r3c_raw t d U V T ht 1 (by omega) h.p h.e
  have hn := summable_norm_i1r3c_raw t d U V T ht 1 (by omega) h.p h.e
  apply i1r3cDepthEquiv.hasSum_iff.mp
  have hg := hasSum_collisionProbability_tail q 0 hq
  simp only [Nat.add_zero, zero_add, pow_one] at hg
  convert i1_hasSum_product (fun p : I1R3CRow => i1Raw t d U V T p.val 1)
    (fun c : ℕ => collisionProbability q (c+1)) _ _ hs hg hn
    (i1_summable_norm_prob_tail q hq) using 1
  exact funext fun p => i1r3c_master_reindexed q t d U V T ht hqt p

theorem summable_norm_i1r3c_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    Summable (fun p : I1Cell 5 => ‖masterTerm q t d U V T 1 p.val‖) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hn := summable_norm_i1r3c_raw t d U V T ht 1 (by omega) h.p h.e
  apply i1r3cDepthEquiv.summable_iff.mp
  convert hn.mul_norm (i1_summable_norm_prob_tail q hq) using 1
  exact funext fun p => congrArg norm (i1r3c_master_reindexed q t d U V T ht hqt p)

theorem i1r3c_value_eq (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hqt : q*t^2=1)
    (h : GeometricRange t d U V T) :
    (((1 - t ^ 2) ^ 3 * d * (T * V)^2 / t) * (1 - d * T * V * t)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (q⁻¹ * (1 - q⁻¹)⁻¹)) = (regionTerm14 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4)) := by
  have hz := norm_one_sub_ne_zero h.t2
  have hp := norm_one_sub_ne_zero h.p
  have hn := norm_one_sub_ne_zero h.n
  have he := norm_one_sub_ne_zero h.e
  have hf := norm_one_sub_ne_zero h.f
  have hg := norm_one_sub_ne_zero h.g
  rw [i1_qinv_eq q t ht hqt]
  unfold regionTerm14
  simp only [pow_one, mul_assoc] at *
  field_simp [hz,hp,hn,he,hf,hg,ht,hd]
  <;> ring

theorem i1r4_master_reindexed (q t d U V T : ℂ) (ht : t ≠ 0)
    (hqt : q*t^2=1) (p : I1R4Row × ℕ) :
    masterTerm q t d U V T 1 (i1r4DepthEquiv p).val =
      i1Raw t d U V T p.1.val 0 * collisionWeight q 1 p.1.val.2.1 p.1.val.2.2 p.2 := by
  rw [i1r4DepthEquiv_val]
  unfold masterTerm
  rw [← i1Raw_eq_shell q t d U V T ht hqt]
  have he : i1Raw t d U V T p.1.val (p.2) =
      i1Raw t d U V T p.1.val 0 := by
    unfold i1Raw
    rw [i1r4_cartan, i1r4_cartan]
    
  rw [he]

theorem hasSum_i1r4_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hq0 : q ≠ 0) (hq1 : q-1 ≠ 0)
    (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    HasSum (fun p : I1Cell 6 => masterTerm q t d U V T 1 p.val)
      (((1 - t ^ 2) ^ 3 * d * (T * U)^2 * (T * V) * t^3) * (1 - d * T * V * t)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (1 - T * U * t ^ 2)⁻¹) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hs := hasSum_i1r4_raw t d U V T 0 h.p h.e h.f
  have hn := summable_norm_i1r4_raw t d U V T 0 h.p h.e h.f
  apply i1r4DepthEquiv.hasSum_iff.mp
  convert hasSum_weighted_collision q 1
    (fun p : I1R4Row => p.val.2.1) (fun p : I1R4Row => p.val.2.2)
    (fun p : I1R4Row => i1Raw t d U V T p.val 0) _ hq0 hq1 hq hs hn using 1
  exact funext fun p => i1r4_master_reindexed q t d U V T ht hqt p

theorem summable_norm_i1r4_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    Summable (fun p : I1Cell 6 => ‖masterTerm q t d U V T 1 p.val‖) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hn := summable_norm_i1r4_raw t d U V T 0 h.p h.e h.f
  apply i1r4DepthEquiv.summable_iff.mp
  convert summable_norm_weighted_collision q 1
    (fun p : I1R4Row => p.val.2.1) (fun p : I1R4Row => p.val.2.2)
    (fun p : I1R4Row => i1Raw t d U V T p.val 0) hq hn using 1
  exact funext fun p => congrArg norm (i1r4_master_reindexed q t d U V T ht hqt p)

theorem i1r4_value_eq (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hqt : q*t^2=1)
    (h : GeometricRange t d U V T) :
    (((1 - t ^ 2) ^ 3 * d * (T * U)^2 * (T * V) * t^3) * (1 - d * T * V * t)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (1 - T * U * t ^ 2)⁻¹) = (regionTerm15 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4)) := by
  have hz := norm_one_sub_ne_zero h.t2
  have hp := norm_one_sub_ne_zero h.p
  have hn := norm_one_sub_ne_zero h.n
  have he := norm_one_sub_ne_zero h.e
  have hf := norm_one_sub_ne_zero h.f
  have hg := norm_one_sub_ne_zero h.g
  
  unfold regionTerm15
  simp only [pow_one, mul_assoc] at *
  field_simp [hz,hp,hn,he,hf,hg,ht,hd]
  <;> ring

theorem i1r5_master_reindexed (q t d U V T : ℂ) (ht : t ≠ 0)
    (hqt : q*t^2=1) (p : I1R5Row × ℕ) :
    masterTerm q t d U V T 1 (i1r5DepthEquiv p).val =
      i1Raw t d U V T p.1.val 0 * collisionWeight q 1 p.1.val.2.1 p.1.val.2.2 p.2 := by
  rw [i1r5DepthEquiv_val]
  unfold masterTerm
  rw [← i1Raw_eq_shell q t d U V T ht hqt]
  have he : i1Raw t d U V T p.1.val (p.2) =
      i1Raw t d U V T p.1.val 0 := by
    unfold i1Raw
    rw [i1r5_cartan, i1r5_cartan]
    
  rw [he]

theorem hasSum_i1r5_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hq0 : q ≠ 0) (hq1 : q-1 ≠ 0)
    (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    HasSum (fun p : I1Cell 7 => masterTerm q t d U V T 1 p.val)
      (((1 - t ^ 2) ^ 3 * d * (T * U)^2 * (T * V) * t^5) * (1 - d * T * V * t)⁻¹ * (1 - T * U * t ^ 2)⁻¹ * (1 - T * U * t ^ 4)⁻¹) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hs := hasSum_i1r5_raw t d U V T 0 h.p h.f h.g
  have hn := summable_norm_i1r5_raw t d U V T 0 h.p h.f h.g
  apply i1r5DepthEquiv.hasSum_iff.mp
  convert hasSum_weighted_collision q 1
    (fun p : I1R5Row => p.val.2.1) (fun p : I1R5Row => p.val.2.2)
    (fun p : I1R5Row => i1Raw t d U V T p.val 0) _ hq0 hq1 hq hs hn using 1
  exact funext fun p => i1r5_master_reindexed q t d U V T ht hqt p

theorem summable_norm_i1r5_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    Summable (fun p : I1Cell 7 => ‖masterTerm q t d U V T 1 p.val‖) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hn := summable_norm_i1r5_raw t d U V T 0 h.p h.f h.g
  apply i1r5DepthEquiv.summable_iff.mp
  convert summable_norm_weighted_collision q 1
    (fun p : I1R5Row => p.val.2.1) (fun p : I1R5Row => p.val.2.2)
    (fun p : I1R5Row => i1Raw t d U V T p.val 0) hq hn using 1
  exact funext fun p => congrArg norm (i1r5_master_reindexed q t d U V T ht hqt p)

theorem i1r5_value_eq (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hqt : q*t^2=1)
    (h : GeometricRange t d U V T) :
    (((1 - t ^ 2) ^ 3 * d * (T * U)^2 * (T * V) * t^5) * (1 - d * T * V * t)⁻¹ * (1 - T * U * t ^ 2)⁻¹ * (1 - T * U * t ^ 4)⁻¹) = (regionTerm16 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4)) := by
  have hz := norm_one_sub_ne_zero h.t2
  have hp := norm_one_sub_ne_zero h.p
  have hn := norm_one_sub_ne_zero h.n
  have he := norm_one_sub_ne_zero h.e
  have hf := norm_one_sub_ne_zero h.f
  have hg := norm_one_sub_ne_zero h.g
  
  unfold regionTerm16
  simp only [pow_one, mul_assoc] at *
  field_simp [hz,hp,hn,he,hf,hg,ht,hd]
  <;> ring

theorem i1r6a_master_reindexed (q t d U V T : ℂ) (ht : t ≠ 0)
    (hqt : q*t^2=1) (p : I1R6ARow × ℕ) :
    masterTerm q t d U V T 1 (i1r6aDepthEquiv p).val =
      i1Raw t d U V T p.1.val 0 * collisionWeight q 1 p.1.val.2.1 p.1.val.2.2 p.2 := by
  rw [i1r6aDepthEquiv_val]
  unfold masterTerm
  rw [← i1Raw_eq_shell q t d U V T ht hqt]
  have he : i1Raw t d U V T p.1.val (p.2) =
      i1Raw t d U V T p.1.val 0 := by
    unfold i1Raw
    rw [i1r6a_cartan, i1r6a_cartan]
    
  rw [he]

theorem hasSum_i1r6a_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hq0 : q ≠ 0) (hq1 : q-1 ≠ 0)
    (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    HasSum (fun p : I1Cell 8 => masterTerm q t d U V T 1 p.val)
      (((1 - t ^ 2) ^ 3 * (T * V) * t^2) * (1 - t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hs := hasSum_i1r6a_raw t d U V T 0 h.t2 h.t2
  have hn := summable_norm_i1r6a_raw t d U V T 0 h.t2 h.t2
  apply i1r6aDepthEquiv.hasSum_iff.mp
  convert hasSum_weighted_collision q 1
    (fun p : I1R6ARow => p.val.2.1) (fun p : I1R6ARow => p.val.2.2)
    (fun p : I1R6ARow => i1Raw t d U V T p.val 0) _ hq0 hq1 hq hs hn using 1
  exact funext fun p => i1r6a_master_reindexed q t d U V T ht hqt p

theorem summable_norm_i1r6a_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    Summable (fun p : I1Cell 8 => ‖masterTerm q t d U V T 1 p.val‖) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hn := summable_norm_i1r6a_raw t d U V T 0 h.t2 h.t2
  apply i1r6aDepthEquiv.summable_iff.mp
  convert summable_norm_weighted_collision q 1
    (fun p : I1R6ARow => p.val.2.1) (fun p : I1R6ARow => p.val.2.2)
    (fun p : I1R6ARow => i1Raw t d U V T p.val 0) hq hn using 1
  exact funext fun p => congrArg norm (i1r6a_master_reindexed q t d U V T ht hqt p)

theorem i1r6a_value_eq (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hqt : q*t^2=1)
    (h : GeometricRange t d U V T) :
    (((1 - t ^ 2) ^ 3 * (T * V) * t^2) * (1 - t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹) = (regionTerm17 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4)) := by
  have hz := norm_one_sub_ne_zero h.t2
  have hp := norm_one_sub_ne_zero h.p
  have hn := norm_one_sub_ne_zero h.n
  have he := norm_one_sub_ne_zero h.e
  have hf := norm_one_sub_ne_zero h.f
  have hg := norm_one_sub_ne_zero h.g
  
  unfold regionTerm17
  simp only [pow_one, mul_assoc] at *
  field_simp [hz,hp,hn,he,hf,hg,ht,hd]
  <;> ring

theorem i1r6b_master_reindexed (q t d U V T : ℂ) (ht : t ≠ 0)
    (hqt : q*t^2=1) (p : I1R6BRow × ℕ) :
    masterTerm q t d U V T 1 (i1r6bDepthEquiv p).val =
      i1Raw t d U V T p.1.val 0 * collisionWeight q 1 p.1.val.2.1 p.1.val.2.2 p.2 := by
  rw [i1r6bDepthEquiv_val]
  unfold masterTerm
  rw [← i1Raw_eq_shell q t d U V T ht hqt]
  have he : i1Raw t d U V T p.1.val (p.2) =
      i1Raw t d U V T p.1.val 0 := by
    unfold i1Raw
    rw [i1r6b_cartan, i1r6b_cartan]
    
  rw [he]

theorem hasSum_i1r6b_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hq0 : q ≠ 0) (hq1 : q-1 ≠ 0)
    (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    HasSum (fun p : I1Cell 9 => masterTerm q t d U V T 1 p.val)
      (((1 - t ^ 2) ^ 3 * (T * U) * t / d) * (1 - T * V * t / d)⁻¹ * (1 - t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hs := hasSum_i1r6b_raw t d U V T 0 h.n h.t2 h.t2
  have hn := summable_norm_i1r6b_raw t d U V T 0 h.n h.t2 h.t2
  apply i1r6bDepthEquiv.hasSum_iff.mp
  convert hasSum_weighted_collision q 1
    (fun p : I1R6BRow => p.val.2.1) (fun p : I1R6BRow => p.val.2.2)
    (fun p : I1R6BRow => i1Raw t d U V T p.val 0) _ hq0 hq1 hq hs hn using 1
  exact funext fun p => i1r6b_master_reindexed q t d U V T ht hqt p

theorem summable_norm_i1r6b_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    Summable (fun p : I1Cell 9 => ‖masterTerm q t d U V T 1 p.val‖) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hn := summable_norm_i1r6b_raw t d U V T 0 h.n h.t2 h.t2
  apply i1r6bDepthEquiv.summable_iff.mp
  convert summable_norm_weighted_collision q 1
    (fun p : I1R6BRow => p.val.2.1) (fun p : I1R6BRow => p.val.2.2)
    (fun p : I1R6BRow => i1Raw t d U V T p.val 0) hq hn using 1
  exact funext fun p => congrArg norm (i1r6b_master_reindexed q t d U V T ht hqt p)

theorem i1r6b_value_eq (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hqt : q*t^2=1)
    (h : GeometricRange t d U V T) :
    (((1 - t ^ 2) ^ 3 * (T * U) * t / d) * (1 - T * V * t / d)⁻¹ * (1 - t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹) = (regionTerm18 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4)) := by
  have hz := norm_one_sub_ne_zero h.t2
  have hp := norm_one_sub_ne_zero h.p
  have hn := norm_one_sub_ne_zero h.n
  have he := norm_one_sub_ne_zero h.e
  have hf := norm_one_sub_ne_zero h.f
  have hg := norm_one_sub_ne_zero h.g
  
  unfold regionTerm18
  simp only [pow_one, mul_assoc] at *
  field_simp [hz,hp,hn,he,hf,hg,ht,hd]
  <;> ring

theorem i1r7_master_reindexed (q t d U V T : ℂ) (ht : t ≠ 0)
    (hqt : q*t^2=1) (p : I1R7Row × ℕ) :
    masterTerm q t d U V T 1 (i1r7DepthEquiv p).val =
      i1Raw t d U V T p.1.val 0 * collisionWeight q 1 p.1.val.2.1 p.1.val.2.2 p.2 := by
  rw [i1r7DepthEquiv_val]
  unfold masterTerm
  rw [← i1Raw_eq_shell q t d U V T ht hqt]
  have he : i1Raw t d U V T p.1.val (p.2) =
      i1Raw t d U V T p.1.val 0 := by
    unfold i1Raw
    rw [i1r7_cartan, i1r7_cartan]
    
  rw [he]

theorem hasSum_i1r7_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hq0 : q ≠ 0) (hq1 : q-1 ≠ 0)
    (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    HasSum (fun p : I1Cell 10 => masterTerm q t d U V T 1 p.val)
      (((1 - t ^ 2) ^ 3 * (T * U) * t^2) * (1 - T * V * t / d)⁻¹ * (1 - t ^ 2)⁻¹ * (1 - T * U * t ^ 4)⁻¹) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hs := hasSum_i1r7_raw t d U V T 0 h.n h.t2 h.g
  have hn := summable_norm_i1r7_raw t d U V T 0 h.n h.t2 h.g
  apply i1r7DepthEquiv.hasSum_iff.mp
  convert hasSum_weighted_collision q 1
    (fun p : I1R7Row => p.val.2.1) (fun p : I1R7Row => p.val.2.2)
    (fun p : I1R7Row => i1Raw t d U V T p.val 0) _ hq0 hq1 hq hs hn using 1
  exact funext fun p => i1r7_master_reindexed q t d U V T ht hqt p

theorem summable_norm_i1r7_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    Summable (fun p : I1Cell 10 => ‖masterTerm q t d U V T 1 p.val‖) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hn := summable_norm_i1r7_raw t d U V T 0 h.n h.t2 h.g
  apply i1r7DepthEquiv.summable_iff.mp
  convert summable_norm_weighted_collision q 1
    (fun p : I1R7Row => p.val.2.1) (fun p : I1R7Row => p.val.2.2)
    (fun p : I1R7Row => i1Raw t d U V T p.val 0) hq hn using 1
  exact funext fun p => congrArg norm (i1r7_master_reindexed q t d U V T ht hqt p)

theorem i1r7_value_eq (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hqt : q*t^2=1)
    (h : GeometricRange t d U V T) :
    (((1 - t ^ 2) ^ 3 * (T * U) * t^2) * (1 - T * V * t / d)⁻¹ * (1 - t ^ 2)⁻¹ * (1 - T * U * t ^ 4)⁻¹) = (regionTerm19 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4)) := by
  have hz := norm_one_sub_ne_zero h.t2
  have hp := norm_one_sub_ne_zero h.p
  have hn := norm_one_sub_ne_zero h.n
  have he := norm_one_sub_ne_zero h.e
  have hf := norm_one_sub_ne_zero h.f
  have hg := norm_one_sub_ne_zero h.g
  
  unfold regionTerm19
  simp only [pow_one, mul_assoc] at *
  field_simp [hz,hp,hn,he,hf,hg,ht,hd]
  <;> ring

theorem i1r8ae_master_reindexed (q t d U V T : ℂ) (ht : t ≠ 0)
    (hqt : q*t^2=1) (p : I1R8AERow × ℕ) :
    masterTerm q t d U V T 1 (i1r8aeDepthEquiv p).val =
      i1Raw t d U V T p.1.val 0 * collisionWeight q 1 p.1.val.2.1 p.1.val.2.2 p.2 := by
  rw [i1r8aeDepthEquiv_val]
  unfold masterTerm
  rw [← i1Raw_eq_shell q t d U V T ht hqt]
  have he : i1Raw t d U V T p.1.val (p.2) =
      i1Raw t d U V T p.1.val 0 := by
    unfold i1Raw
    rw [i1r8ae_cartan, i1r8ae_cartan]
    
  rw [he]

theorem hasSum_i1r8ae_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hq0 : q ≠ 0) (hq1 : q-1 ≠ 0)
    (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    HasSum (fun p : I1Cell 11 => masterTerm q t d U V T 1 p.val)
      (((1 - t ^ 2) ^ 3 * (T * U) * (T * V) * t^2) * (1 - T * V * t / d)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hs := hasSum_i1r8ae_raw t d U V T 0 h.n h.e h.t2
  have hn := summable_norm_i1r8ae_raw t d U V T 0 h.n h.e h.t2
  apply i1r8aeDepthEquiv.hasSum_iff.mp
  convert hasSum_weighted_collision q 1
    (fun p : I1R8AERow => p.val.2.1) (fun p : I1R8AERow => p.val.2.2)
    (fun p : I1R8AERow => i1Raw t d U V T p.val 0) _ hq0 hq1 hq hs hn using 1
  exact funext fun p => i1r8ae_master_reindexed q t d U V T ht hqt p

theorem summable_norm_i1r8ae_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    Summable (fun p : I1Cell 11 => ‖masterTerm q t d U V T 1 p.val‖) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hn := summable_norm_i1r8ae_raw t d U V T 0 h.n h.e h.t2
  apply i1r8aeDepthEquiv.summable_iff.mp
  convert summable_norm_weighted_collision q 1
    (fun p : I1R8AERow => p.val.2.1) (fun p : I1R8AERow => p.val.2.2)
    (fun p : I1R8AERow => i1Raw t d U V T p.val 0) hq hn using 1
  exact funext fun p => congrArg norm (i1r8ae_master_reindexed q t d U V T ht hqt p)

theorem i1r8ae_value_eq (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hqt : q*t^2=1)
    (h : GeometricRange t d U V T) :
    (((1 - t ^ 2) ^ 3 * (T * U) * (T * V) * t^2) * (1 - T * V * t / d)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹) = ((1-t^2)^2 * (T*U) * (T * V)^1 * t^2 * (1 - (T * V) * t / d)⁻¹ * (1 - (T * V)^2 * t^2)⁻¹) := by
  have hz := norm_one_sub_ne_zero h.t2
  have hp := norm_one_sub_ne_zero h.p
  have hn := norm_one_sub_ne_zero h.n
  have he := norm_one_sub_ne_zero h.e
  have hf := norm_one_sub_ne_zero h.f
  have hg := norm_one_sub_ne_zero h.g
  
  
  simp only [pow_one, mul_assoc] at *
  field_simp [hz,hp,hn,he,hf,hg,ht,hd]
  <;> ring

theorem i1r8ao_master_reindexed (q t d U V T : ℂ) (ht : t ≠ 0)
    (hqt : q*t^2=1) (p : I1R8AORow × ℕ) :
    masterTerm q t d U V T 1 (i1r8aoDepthEquiv p).val =
      i1Raw t d U V T p.1.val 0 * collisionWeight q 1 p.1.val.2.1 p.1.val.2.2 p.2 := by
  rw [i1r8aoDepthEquiv_val]
  unfold masterTerm
  rw [← i1Raw_eq_shell q t d U V T ht hqt]
  have he : i1Raw t d U V T p.1.val (p.2) =
      i1Raw t d U V T p.1.val 0 := by
    unfold i1Raw
    rw [i1r8ao_cartan, i1r8ao_cartan]
    
  rw [he]

theorem hasSum_i1r8ao_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hq0 : q ≠ 0) (hq1 : q-1 ≠ 0)
    (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    HasSum (fun p : I1Cell 12 => masterTerm q t d U V T 1 p.val)
      (((1 - t ^ 2) ^ 3 * (T * U) * t^2) * (1 - T * V * t / d)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hs := hasSum_i1r8ao_raw t d U V T 0 h.n h.e h.t2
  have hn := summable_norm_i1r8ao_raw t d U V T 0 h.n h.e h.t2
  apply i1r8aoDepthEquiv.hasSum_iff.mp
  convert hasSum_weighted_collision q 1
    (fun p : I1R8AORow => p.val.2.1) (fun p : I1R8AORow => p.val.2.2)
    (fun p : I1R8AORow => i1Raw t d U V T p.val 0) _ hq0 hq1 hq hs hn using 1
  exact funext fun p => i1r8ao_master_reindexed q t d U V T ht hqt p

theorem summable_norm_i1r8ao_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    Summable (fun p : I1Cell 12 => ‖masterTerm q t d U V T 1 p.val‖) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hn := summable_norm_i1r8ao_raw t d U V T 0 h.n h.e h.t2
  apply i1r8aoDepthEquiv.summable_iff.mp
  convert summable_norm_weighted_collision q 1
    (fun p : I1R8AORow => p.val.2.1) (fun p : I1R8AORow => p.val.2.2)
    (fun p : I1R8AORow => i1Raw t d U V T p.val 0) hq hn using 1
  exact funext fun p => congrArg norm (i1r8ao_master_reindexed q t d U V T ht hqt p)

theorem i1r8ao_value_eq (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hqt : q*t^2=1)
    (h : GeometricRange t d U V T) :
    (((1 - t ^ 2) ^ 3 * (T * U) * t^2) * (1 - T * V * t / d)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹) = ((1-t^2)^2 * (T*U) * 1 * t^2 * (1 - (T * V) * t / d)⁻¹ * (1 - (T * V)^2 * t^2)⁻¹) := by
  have hz := norm_one_sub_ne_zero h.t2
  have hp := norm_one_sub_ne_zero h.p
  have hn := norm_one_sub_ne_zero h.n
  have he := norm_one_sub_ne_zero h.e
  have hf := norm_one_sub_ne_zero h.f
  have hg := norm_one_sub_ne_zero h.g
  
  
  simp only [pow_one, mul_assoc] at *
  field_simp [hz,hp,hn,he,hf,hg,ht,hd]
  <;> ring

theorem i1r8b_master_reindexed (q t d U V T : ℂ) (ht : t ≠ 0)
    (hqt : q*t^2=1) (p : I1R8BRow) :
    masterTerm q t d U V T 1 (i1r8bDepthEquiv p).val =
      i1Raw t d U V T p.val 0 * collisionProbability q 0 := by
  rw [i1r8bDepthEquiv_val]
  unfold masterTerm
  rw [← i1Raw_eq_shell q t d U V T ht hqt]
  have hc : 2*p.val.2.2 = p.val.2.1-1 := p.property.2.2.2
  simp only [collisionWeight, one_ne_zero, hc, ne_eq, not_true_eq_false, false_or, if_false]

theorem hasSum_i1r8b_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hq0 : q ≠ 0) (hq1 : q-1 ≠ 0)
    (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    HasSum (fun p : I1Cell 13 => masterTerm q t d U V T 1 p.val)
      (((1 - t ^ 2) ^ 3 * (T * U)) * (1 - T * V * t / d)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (collisionProbability q 0)) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hs := hasSum_i1r8b_raw t d U V T h.n h.e
  have hn := summable_norm_i1r8b_raw t d U V T h.n h.e
  apply i1r8bDepthEquiv.hasSum_iff.mp
  convert hs.mul_right (collisionProbability q 0) using 1
  all_goals try rfl
  exact funext fun p => i1r8b_master_reindexed q t d U V T ht hqt p

theorem summable_norm_i1r8b_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    Summable (fun p : I1Cell 13 => ‖masterTerm q t d U V T 1 p.val‖) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hn := summable_norm_i1r8b_raw t d U V T h.n h.e
  apply i1r8bDepthEquiv.summable_iff.mp
  convert hn.mul_right ‖collisionProbability q 0‖ using 1
  all_goals try rfl
  exact funext fun p => by
    simpa only [norm_mul, Function.comp_apply] using
      congrArg norm (i1r8b_master_reindexed q t d U V T ht hqt p)

theorem i1r8b_value_eq (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hqt : q*t^2=1)
    (h : GeometricRange t d U V T) :
    (((1 - t ^ 2) ^ 3 * (T * U)) * (1 - T * V * t / d)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (collisionProbability q 0)) = (regionTerm21 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4)) := by
  have hz := norm_one_sub_ne_zero h.t2
  have hp := norm_one_sub_ne_zero h.p
  have hn := norm_one_sub_ne_zero h.n
  have he := norm_one_sub_ne_zero h.e
  have hf := norm_one_sub_ne_zero h.f
  have hg := norm_one_sub_ne_zero h.g
  rw [i1_prob0_eq q t ht hqt hz]
  unfold regionTerm21
  simp only [pow_one, mul_assoc] at *
  field_simp [hz,hp,hn,he,hf,hg,ht,hd]
  <;> ring

theorem i1r8c_master_reindexed (q t d U V T : ℂ) (ht : t ≠ 0)
    (hqt : q*t^2=1) (p : I1R8CRow × ℕ) :
    masterTerm q t d U V T 1 (i1r8cDepthEquiv p).val =
      i1Raw t d U V T p.1.val 1 * collisionProbability q (p.2+1) := by
  rw [i1r8cDepthEquiv_val]
  unfold masterTerm
  rw [← i1Raw_eq_shell q t d U V T ht hqt]
  have he : i1Raw t d U V T p.1.val (p.2 + 1) =
      i1Raw t d U V T p.1.val 1 := by
    unfold i1Raw
    rw [i1r8c_cartan, i1r8c_cartan]
    all_goals omega
  rw [he]
  have hc : 2*p.1.val.2.2 = p.1.val.2.1-1 := p.1.property.2.2.2
  simp only [collisionWeight, one_ne_zero, hc, ne_eq, not_true_eq_false, false_or, if_false]

theorem hasSum_i1r8c_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hq0 : q ≠ 0) (hq1 : q-1 ≠ 0)
    (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    HasSum (fun p : I1Cell 14 => masterTerm q t d U V T 1 p.val)
      (((1 - t ^ 2) ^ 3 * (T * V) / t^2) * (1 - T * V * t / d)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (q⁻¹ * (1 - q⁻¹)⁻¹)) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hs := hasSum_i1r8c_raw t d U V T ht 1 (by omega) h.n h.e
  have hn := summable_norm_i1r8c_raw t d U V T ht 1 (by omega) h.n h.e
  apply i1r8cDepthEquiv.hasSum_iff.mp
  have hg := hasSum_collisionProbability_tail q 0 hq
  simp only [Nat.add_zero, zero_add, pow_one] at hg
  convert i1_hasSum_product (fun p : I1R8CRow => i1Raw t d U V T p.val 1)
    (fun c : ℕ => collisionProbability q (c+1)) _ _ hs hg hn
    (i1_summable_norm_prob_tail q hq) using 1
  exact funext fun p => i1r8c_master_reindexed q t d U V T ht hqt p

theorem summable_norm_i1r8c_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    Summable (fun p : I1Cell 14 => ‖masterTerm q t d U V T 1 p.val‖) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hn := summable_norm_i1r8c_raw t d U V T ht 1 (by omega) h.n h.e
  apply i1r8cDepthEquiv.summable_iff.mp
  convert hn.mul_norm (i1_summable_norm_prob_tail q hq) using 1
  exact funext fun p => congrArg norm (i1r8c_master_reindexed q t d U V T ht hqt p)

theorem i1r8c_value_eq (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hqt : q*t^2=1)
    (h : GeometricRange t d U V T) :
    (((1 - t ^ 2) ^ 3 * (T * V) / t^2) * (1 - T * V * t / d)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (q⁻¹ * (1 - q⁻¹)⁻¹)) = (regionTerm22 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4)) := by
  have hz := norm_one_sub_ne_zero h.t2
  have hp := norm_one_sub_ne_zero h.p
  have hn := norm_one_sub_ne_zero h.n
  have he := norm_one_sub_ne_zero h.e
  have hf := norm_one_sub_ne_zero h.f
  have hg := norm_one_sub_ne_zero h.g
  rw [i1_qinv_eq q t ht hqt]
  unfold regionTerm22
  simp only [pow_one, mul_assoc] at *
  field_simp [hz,hp,hn,he,hf,hg,ht,hd]
  <;> ring

theorem i1r9_master_reindexed (q t d U V T : ℂ) (ht : t ≠ 0)
    (hqt : q*t^2=1) (p : I1R9Row × ℕ) :
    masterTerm q t d U V T 1 (i1r9DepthEquiv p).val =
      i1Raw t d U V T p.1.val 0 * collisionWeight q 1 p.1.val.2.1 p.1.val.2.2 p.2 := by
  rw [i1r9DepthEquiv_val]
  unfold masterTerm
  rw [← i1Raw_eq_shell q t d U V T ht hqt]
  have he : i1Raw t d U V T p.1.val (p.2) =
      i1Raw t d U V T p.1.val 0 := by
    unfold i1Raw
    rw [i1r9_cartan, i1r9_cartan]
    
  rw [he]

theorem hasSum_i1r9_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hq0 : q ≠ 0) (hq1 : q-1 ≠ 0)
    (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    HasSum (fun p : I1Cell 15 => masterTerm q t d U V T 1 p.val)
      (((1 - t ^ 2) ^ 3 * (T * U)^2 * t^2) * (1 - T * V * t / d)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (1 - T * U * t ^ 2)⁻¹) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hs := hasSum_i1r9_raw t d U V T 0 h.n h.e h.f
  have hn := summable_norm_i1r9_raw t d U V T 0 h.n h.e h.f
  apply i1r9DepthEquiv.hasSum_iff.mp
  convert hasSum_weighted_collision q 1
    (fun p : I1R9Row => p.val.2.1) (fun p : I1R9Row => p.val.2.2)
    (fun p : I1R9Row => i1Raw t d U V T p.val 0) _ hq0 hq1 hq hs hn using 1
  exact funext fun p => i1r9_master_reindexed q t d U V T ht hqt p

theorem summable_norm_i1r9_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    Summable (fun p : I1Cell 15 => ‖masterTerm q t d U V T 1 p.val‖) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hn := summable_norm_i1r9_raw t d U V T 0 h.n h.e h.f
  apply i1r9DepthEquiv.summable_iff.mp
  convert summable_norm_weighted_collision q 1
    (fun p : I1R9Row => p.val.2.1) (fun p : I1R9Row => p.val.2.2)
    (fun p : I1R9Row => i1Raw t d U V T p.val 0) hq hn using 1
  exact funext fun p => congrArg norm (i1r9_master_reindexed q t d U V T ht hqt p)

theorem i1r9_value_eq (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hqt : q*t^2=1)
    (h : GeometricRange t d U V T) :
    (((1 - t ^ 2) ^ 3 * (T * U)^2 * t^2) * (1 - T * V * t / d)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (1 - T * U * t ^ 2)⁻¹) = (regionTerm23 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4)) := by
  have hz := norm_one_sub_ne_zero h.t2
  have hp := norm_one_sub_ne_zero h.p
  have hn := norm_one_sub_ne_zero h.n
  have he := norm_one_sub_ne_zero h.e
  have hf := norm_one_sub_ne_zero h.f
  have hg := norm_one_sub_ne_zero h.g
  
  unfold regionTerm23
  simp only [pow_one, mul_assoc] at *
  field_simp [hz,hp,hn,he,hf,hg,ht,hd]
  <;> ring

theorem i1r10_master_reindexed (q t d U V T : ℂ) (ht : t ≠ 0)
    (hqt : q*t^2=1) (p : I1R10Row × ℕ) :
    masterTerm q t d U V T 1 (i1r10DepthEquiv p).val =
      i1Raw t d U V T p.1.val 0 * collisionWeight q 1 p.1.val.2.1 p.1.val.2.2 p.2 := by
  rw [i1r10DepthEquiv_val]
  unfold masterTerm
  rw [← i1Raw_eq_shell q t d U V T ht hqt]
  have he : i1Raw t d U V T p.1.val (p.2) =
      i1Raw t d U V T p.1.val 0 := by
    unfold i1Raw
    rw [i1r10_cartan, i1r10_cartan]
    
  rw [he]

theorem hasSum_i1r10_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hq0 : q ≠ 0) (hq1 : q-1 ≠ 0)
    (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    HasSum (fun p : I1Cell 16 => masterTerm q t d U V T 1 p.val)
      (((1 - t ^ 2) ^ 3 * (T * U)^2 * t^4) * (1 - T * V * t / d)⁻¹ * (1 - T * U * t ^ 2)⁻¹ * (1 - T * U * t ^ 4)⁻¹) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hs := hasSum_i1r10_raw t d U V T 0 h.n h.f h.g
  have hn := summable_norm_i1r10_raw t d U V T 0 h.n h.f h.g
  apply i1r10DepthEquiv.hasSum_iff.mp
  convert hasSum_weighted_collision q 1
    (fun p : I1R10Row => p.val.2.1) (fun p : I1R10Row => p.val.2.2)
    (fun p : I1R10Row => i1Raw t d U V T p.val 0) _ hq0 hq1 hq hs hn using 1
  exact funext fun p => i1r10_master_reindexed q t d U V T ht hqt p

theorem summable_norm_i1r10_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    Summable (fun p : I1Cell 16 => ‖masterTerm q t d U V T 1 p.val‖) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hn := summable_norm_i1r10_raw t d U V T 0 h.n h.f h.g
  apply i1r10DepthEquiv.summable_iff.mp
  convert summable_norm_weighted_collision q 1
    (fun p : I1R10Row => p.val.2.1) (fun p : I1R10Row => p.val.2.2)
    (fun p : I1R10Row => i1Raw t d U V T p.val 0) hq hn using 1
  exact funext fun p => congrArg norm (i1r10_master_reindexed q t d U V T ht hqt p)

theorem i1r10_value_eq (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hqt : q*t^2=1)
    (h : GeometricRange t d U V T) :
    (((1 - t ^ 2) ^ 3 * (T * U)^2 * t^4) * (1 - T * V * t / d)⁻¹ * (1 - T * U * t ^ 2)⁻¹ * (1 - T * U * t ^ 4)⁻¹) = (regionTerm24 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4)) := by
  have hz := norm_one_sub_ne_zero h.t2
  have hp := norm_one_sub_ne_zero h.p
  have hn := norm_one_sub_ne_zero h.n
  have he := norm_one_sub_ne_zero h.e
  have hf := norm_one_sub_ne_zero h.f
  have hg := norm_one_sub_ne_zero h.g
  
  unfold regionTerm24
  simp only [pow_one, mul_assoc] at *
  field_simp [hz,hp,hn,he,hf,hg,ht,hd]
  <;> ring

def i1CellValue (q t d U V T : ℂ) : Fin 17 → ℂ :=
  ![((1 - t ^ 2) ^ 3 * d * (T * U) * t) * (1 - d * T * V * t)⁻¹ * (1 - t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹,
    ((1 - t ^ 2) ^ 3 * d * (T * U) * (T * V) * t ^ 3) * (1 - d * T * V * t)⁻¹ * (1 - t ^ 2)⁻¹ * (1 - T * U * t ^ 4)⁻¹,
    ((1 - t ^ 2) ^ 3 * d * (T * U) * (T * V)^2 * t^3) * (1 - d * T * V * t)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹,
    ((1 - t ^ 2) ^ 3 * d * (T * U) * (T * V) * t^3) * (1 - d * T * V * t)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹,
    ((1 - t ^ 2) ^ 3 * d * (T * U) * (T * V) * t) * (1 - d * T * V * t)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (collisionProbability q 0),
    ((1 - t ^ 2) ^ 3 * d * (T * V)^2 / t) * (1 - d * T * V * t)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (q⁻¹ * (1 - q⁻¹)⁻¹),
    ((1 - t ^ 2) ^ 3 * d * (T * U)^2 * (T * V) * t^3) * (1 - d * T * V * t)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (1 - T * U * t ^ 2)⁻¹,
    ((1 - t ^ 2) ^ 3 * d * (T * U)^2 * (T * V) * t^5) * (1 - d * T * V * t)⁻¹ * (1 - T * U * t ^ 2)⁻¹ * (1 - T * U * t ^ 4)⁻¹,
    ((1 - t ^ 2) ^ 3 * (T * V) * t^2) * (1 - t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹,
    ((1 - t ^ 2) ^ 3 * (T * U) * t / d) * (1 - T * V * t / d)⁻¹ * (1 - t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹,
    ((1 - t ^ 2) ^ 3 * (T * U) * t^2) * (1 - T * V * t / d)⁻¹ * (1 - t ^ 2)⁻¹ * (1 - T * U * t ^ 4)⁻¹,
    ((1 - t ^ 2) ^ 3 * (T * U) * (T * V) * t^2) * (1 - T * V * t / d)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹,
    ((1 - t ^ 2) ^ 3 * (T * U) * t^2) * (1 - T * V * t / d)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹,
    ((1 - t ^ 2) ^ 3 * (T * U)) * (1 - T * V * t / d)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (collisionProbability q 0),
    ((1 - t ^ 2) ^ 3 * (T * V) / t^2) * (1 - T * V * t / d)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (q⁻¹ * (1 - q⁻¹)⁻¹),
    ((1 - t ^ 2) ^ 3 * (T * U)^2 * t^2) * (1 - T * V * t / d)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (1 - T * U * t ^ 2)⁻¹,
    ((1 - t ^ 2) ^ 3 * (T * U)^2 * t^4) * (1 - T * V * t / d)⁻¹ * (1 - T * U * t ^ 2)⁻¹ * (1 - T * U * t ^ 4)⁻¹]

theorem hasSum_i1_cell (q t d U V T : ℂ)
    (ht : t ≠ 0) (hq0 : q ≠ 0) (hq1 : q-1 ≠ 0)
    (hqt : q*t^2=1) (h : GeometricRange t d U V T) (i : Fin 17) :
    HasSum (fun p : I1Cell i => masterTerm q t d U V T 1 p.val)
      (i1CellValue q t d U V T i) := by
  fin_cases i
  · exact hasSum_i1r1_master q t d U V T ht hq0 hq1 hqt h
  · exact hasSum_i1r2_master q t d U V T ht hq0 hq1 hqt h
  · exact hasSum_i1r3ae_master q t d U V T ht hq0 hq1 hqt h
  · exact hasSum_i1r3ao_master q t d U V T ht hq0 hq1 hqt h
  · exact hasSum_i1r3b_master q t d U V T ht hq0 hq1 hqt h
  · exact hasSum_i1r3c_master q t d U V T ht hq0 hq1 hqt h
  · exact hasSum_i1r4_master q t d U V T ht hq0 hq1 hqt h
  · exact hasSum_i1r5_master q t d U V T ht hq0 hq1 hqt h
  · exact hasSum_i1r6a_master q t d U V T ht hq0 hq1 hqt h
  · exact hasSum_i1r6b_master q t d U V T ht hq0 hq1 hqt h
  · exact hasSum_i1r7_master q t d U V T ht hq0 hq1 hqt h
  · exact hasSum_i1r8ae_master q t d U V T ht hq0 hq1 hqt h
  · exact hasSum_i1r8ao_master q t d U V T ht hq0 hq1 hqt h
  · exact hasSum_i1r8b_master q t d U V T ht hq0 hq1 hqt h
  · exact hasSum_i1r8c_master q t d U V T ht hq0 hq1 hqt h
  · exact hasSum_i1r9_master q t d U V T ht hq0 hq1 hqt h
  · exact hasSum_i1r10_master q t d U V T ht hq0 hq1 hqt h

theorem summable_norm_i1_cell (q t d U V T : ℂ)
    (ht : t ≠ 0) (hqt : q*t^2=1) (h : GeometricRange t d U V T) (i : Fin 17) :
    Summable (fun p : I1Cell i => ‖masterTerm q t d U V T 1 p.val‖) := by
  fin_cases i
  · exact summable_norm_i1r1_master q t d U V T ht hqt h
  · exact summable_norm_i1r2_master q t d U V T ht hqt h
  · exact summable_norm_i1r3ae_master q t d U V T ht hqt h
  · exact summable_norm_i1r3ao_master q t d U V T ht hqt h
  · exact summable_norm_i1r3b_master q t d U V T ht hqt h
  · exact summable_norm_i1r3c_master q t d U V T ht hqt h
  · exact summable_norm_i1r4_master q t d U V T ht hqt h
  · exact summable_norm_i1r5_master q t d U V T ht hqt h
  · exact summable_norm_i1r6a_master q t d U V T ht hqt h
  · exact summable_norm_i1r6b_master q t d U V T ht hqt h
  · exact summable_norm_i1r7_master q t d U V T ht hqt h
  · exact summable_norm_i1r8ae_master q t d U V T ht hqt h
  · exact summable_norm_i1r8ao_master q t d U V T ht hqt h
  · exact summable_norm_i1r8b_master q t d U V T ht hqt h
  · exact summable_norm_i1r8c_master q t d U V T ht hqt h
  · exact summable_norm_i1r9_master q t d U V T ht hqt h
  · exact summable_norm_i1r10_master q t d U V T ht hqt h

/-- Absolute summability of the actual complete I1 lattice, before rearrangement. -/
theorem summable_norm_i1_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    Summable (fun p : LatticeIndex => ‖masterTerm q t d U V T 1 p‖) := by
  apply i1PartitionEquiv.summable_iff.mp
  apply (summable_sigma_of_nonneg (fun p => norm_nonneg _)).mpr
  exact ⟨summable_norm_i1_cell q t d U V T ht hqt h, (hasSum_fintype _).summable⟩

theorem hasSum_i1_master_cells (q t d U V T : ℂ)
    (ht : t ≠ 0) (hq0 : q ≠ 0) (hq1 : q-1 ≠ 0)
    (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    HasSum (masterTerm q t d U V T 1) (∑ i : Fin 17, i1CellValue q t d U V T i) := by
  have hs := (summable_norm_i1_master q t d U V T ht hqt h).of_norm
  apply i1PartitionEquiv.hasSum_iff.mp
  exact (hasSum_fintype (i1CellValue q t d U V T)).sigma_of_hasSum
    (hasSum_i1_cell q t d U V T ht hq0 hq1 hqt h)
    (i1PartitionEquiv.summable_iff.mpr hs)

def i1CellSimplified (t d U V T : ℂ) : Fin 17 → ℂ :=
  ![regionTerm10 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm11 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    (1-t^2)^2 * d * (T*U) * (T * V)^2 * t^3 * (1 - d * (T * V) * t)⁻¹ * (1 - (T * V)^2 * t^2)⁻¹,
    (1-t^2)^2 * d * (T*U) * (T * V)^1 * t^3 * (1 - d * (T * V) * t)⁻¹ * (1 - (T * V)^2 * t^2)⁻¹,
    regionTerm13 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm14 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm15 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm16 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm17 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm18 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm19 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    (1-t^2)^2 * (T*U) * (T * V)^1 * t^2 * (1 - (T * V) * t / d)⁻¹ * (1 - (T * V)^2 * t^2)⁻¹,
    (1-t^2)^2 * (T*U) * 1 * t^2 * (1 - (T * V) * t / d)⁻¹ * (1 - (T * V)^2 * t^2)⁻¹,
    regionTerm21 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm22 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm23 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm24 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4)]

def i1StoredRows (t d U V T : ℂ) : Fin 15 → ℂ :=
  ![regionTerm10 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm11 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm12 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm13 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm14 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm15 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm16 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm17 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm18 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm19 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm20 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm21 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm22 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm23 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm24 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4)]

theorem i1StoredRows_eq_regionTerms (t d U V T : ℂ) (i : Fin 15) :
    i1StoredRows t d U V T i =
      regionTerms t d (T*U) (T*V) ⟨10+i.val, by omega⟩ := by
  fin_cases i <;> rfl

theorem i1CellValue_eq_simplified (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hqt : q*t^2=1)
    (h : GeometricRange t d U V T) (i : Fin 17) :
    i1CellValue q t d U V T i = i1CellSimplified t d U V T i := by
  fin_cases i
  · exact i1r1_value_eq q t d U V T ht hd hqt h
  · exact i1r2_value_eq q t d U V T ht hd hqt h
  · exact i1r3ae_value_eq q t d U V T ht hd hqt h
  · exact i1r3ao_value_eq q t d U V T ht hd hqt h
  · exact i1r3b_value_eq q t d U V T ht hd hqt h
  · exact i1r3c_value_eq q t d U V T ht hd hqt h
  · exact i1r4_value_eq q t d U V T ht hd hqt h
  · exact i1r5_value_eq q t d U V T ht hd hqt h
  · exact i1r6a_value_eq q t d U V T ht hd hqt h
  · exact i1r6b_value_eq q t d U V T ht hd hqt h
  · exact i1r7_value_eq q t d U V T ht hd hqt h
  · exact i1r8ae_value_eq q t d U V T ht hd hqt h
  · exact i1r8ao_value_eq q t d U V T ht hd hqt h
  · exact i1r8b_value_eq q t d U V T ht hd hqt h
  · exact i1r8c_value_eq q t d U V T ht hd hqt h
  · exact i1r9_value_eq q t d U V T ht hd hqt h
  · exact i1r10_value_eq q t d U V T ht hd hqt h

theorem i1CellSimplified_sum (t d U V T : ℂ) :
    (∑ i : Fin 17, i1CellSimplified t d U V T i) =
      ∑ i : Fin 15, i1StoredRows t d U V T i := by
  simp only [i1CellSimplified, i1StoredRows, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]
  unfold regionTerm10 regionTerm11 regionTerm12 regionTerm13 regionTerm14 regionTerm15 regionTerm16 regionTerm17 regionTerm18 regionTerm19 regionTerm20 regionTerm21 regionTerm22 regionTerm23 regionTerm24
  simp only [pow_one]
  ring

theorem i1CellValue_sum_eq_regions (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hqt : q*t^2=1)
    (h : GeometricRange t d U V T) :
    (∑ i : Fin 17, i1CellValue q t d U V T i) =
      ∑ i : Fin 15, regionTerms t d (T*U) (T*V) ⟨10+i.val, by omega⟩ := by
  calc
    _ = ∑ i : Fin 17, i1CellSimplified t d U V T i := by
      apply Finset.sum_congr rfl
      intro i hi
      exact i1CellValue_eq_simplified q t d U V T ht hd hqt h i
    _ = ∑ i : Fin 15, i1StoredRows t d U V T i := i1CellSimplified_sum t d U V T
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      exact i1StoredRows_eq_regionTerms t d U V T i

/-- The complete infinite I1 master lattice equals the exact stored fifteen
restored row fractions. Absolute summability was established before this
partition and parity recombination. Damping remains in each unsummed term. -/
theorem hasSum_i1_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hq0 : q ≠ 0) (hq1 : q-1 ≠ 0)
    (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    HasSum (masterTerm q t d U V T 1)
      (∑ i : Fin 15, regionTerms t d (T*U) (T*V) ⟨10+i.val, by omega⟩) := by
  rw [← i1CellValue_sum_eq_regions q t d U V T ht hd hqt h]
  exact hasSum_i1_master_cells q t d U V T ht hq0 hq1 hqt h

theorem i1_basic_nonzero (q t : ℂ) (hqt : q*t^2=1) (hz : ‖t^2‖<1) :
    t ≠ 0 ∧ q ≠ 0 ∧ q-1 ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro ht
    simp [ht] at hqt
  · intro hq
    simp [hq] at hqt
  · intro hq
    have he : q = 1 := sub_eq_zero.mp hq
    have he' : t^2=1 := by simpa only [he,one_mul] using hqt
    rw [he',norm_one] at hz
    exact (lt_irrefl (1 : ℝ)) hz

/-- All auxiliary nonzero q/t hypotheses follow from the independent
normalization equation and the convergent parameter range. -/
theorem hasSum_i1_master_of_geometricRange (q t d U V T : ℂ)
    (hd : d ≠ 0) (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    HasSum (masterTerm q t d U V T 1)
      (∑ i : Fin 15, regionTerms t d (T*U) (T*V) ⟨10+i.val, by omega⟩) := by
  obtain ⟨ht,hq0,hq1⟩ := i1_basic_nonzero q t hqt h.t2
  exact hasSum_i1_master q t d U V T ht hd hq0 hq1 hqt h

/-- Natural real damping and unitary monomial hypotheses. The strict
inequality T*t < ‖δ‖ covers damped endpoint and undamped interior cases. -/
theorem i1_master_of_bounds (q t T : ℝ) (d U V : ℂ)
    (hqt : q*t^2=1) (ht0 : 0<t) (ht1 : t<1) (hT0 : 0≤T) (hT1 : T≤1)
    (hdlo : t≤‖d‖) (hdhi : ‖d‖≤1) (hstrict : T*t<‖d‖)
    (hU : ‖U‖=1) (hV : ‖V‖=1) :
    Summable (fun p : LatticeIndex => ‖masterTerm (q:ℂ) (t:ℂ) d U V (T:ℂ) 1 p‖) ∧
    HasSum (masterTerm (q:ℂ) (t:ℂ) d U V (T:ℂ) 1)
      (∑ i : Fin 15, regionTerms (t:ℂ) d ((T:ℂ)*U) ((T:ℂ)*V) ⟨10+i.val, by omega⟩) := by
  have h := geometricRange_of_bounds ht0 ht1 hT0 hT1 hdlo hdhi hstrict hU hV
  have he : (q:ℂ)*(t:ℂ)^2=1 := by exact_mod_cast hqt
  have ht : (t:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ht0
  have hd : d ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le ht0 hdlo)
  exact ⟨summable_norm_i1_master q t d U V T ht he h,
    hasSum_i1_master_of_geometricRange q t d U V T hd he h⟩

end FourierJacobi.Analysis
