/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Volume of thin cones about the kernel of a linear form

For a continuous linear form `ψ` on a finite-dimensional real normed space `E` and `t ≥ 0`, the
vectors `v` with `|ψ v| ≤ t ‖v‖` form a closed cone about the kernel of `ψ`. For an additive Haar
measure `μ` on `E`, the part of this cone in the closed ball of radius `R > 0` has measure
`R ^ dim E` times the measure of its part in the closed unit ball. When `ψ ≠ 0` the kernel is a
proper subspace, hence `μ`-null, and the measure of the part of the cone in the closed unit ball
tends to zero as `t → 0⁺`.

## Main results

* `TauCeti.addHaar_closedBall_inter_setOf_abs_le_mul_norm`: scaling the part of the cone in a
  closed ball centred at `0`.
* `TauCeti.tendsto_addHaar_closedBall_inter_setOf_abs_le_mul_norm`: the part of the cone in the
  closed unit ball has measure tending to zero as `t → 0⁺`, for a nonzero form.
-/

public section

open Filter Metric MeasureTheory Set
open scoped ENNReal Topology Pointwise

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- The part of the cone `{v | |ψ v| ≤ t ‖v‖}` in the closed ball of radius `R > 0` is the
dilation by `R` of its part in the closed unit ball, so its measure is `R ^ dim E` times that
of the latter. -/
theorem addHaar_closedBall_inter_setOf_abs_le_mul_norm (ψ : E →L[ℝ] ℝ) (t : ℝ) {R : ℝ}
    (hR : 0 < R) :
    μ (closedBall (0 : E) R ∩ {v | |ψ v| ≤ t * ‖v‖}) =
      ENNReal.ofReal (R ^ Module.finrank ℝ E) *
        μ (closedBall (0 : E) 1 ∩ {v | |ψ v| ≤ t * ‖v‖}) := by
  have hset : closedBall (0 : E) R ∩ {v | |ψ v| ≤ t * ‖v‖} =
      R • (closedBall (0 : E) 1 ∩ {v | |ψ v| ≤ t * ‖v‖}) := by
    ext v
    rw [mem_smul_set_iff_inv_smul_mem₀ hR.ne']
    simp only [mem_inter_iff, mem_ofPred_eq, mem_closedBall_zero_iff, map_smul, smul_eq_mul,
      norm_smul, Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos hR]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨by rw [inv_mul_le_iff₀ hR]; linarith, ?_⟩
      rw [mul_left_comm]
      exact mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr hR.le)
    · rintro ⟨h1, h2⟩
      refine ⟨by rw [inv_mul_le_iff₀ hR] at h1; linarith, ?_⟩
      rw [mul_left_comm] at h2
      exact le_of_mul_le_mul_left h2 (inv_pos.mpr hR)
  rw [hset, Measure.addHaar_smul, abs_of_pos (pow_pos hR _)]

/-- For a nonzero linear form `ψ`, the part of the cone `{v | |ψ v| ≤ t ‖v‖}` in the closed unit
ball has measure tending to zero as `t → 0⁺`: the cones shrink to the kernel of `ψ`, a proper
subspace and hence a null set. -/
theorem tendsto_addHaar_closedBall_inter_setOf_abs_le_mul_norm {ψ : E →L[ℝ] ℝ} (hψ : ψ ≠ 0) :
    Tendsto (fun t : ℝ ↦ μ (closedBall (0 : E) 1 ∩ {v | |ψ v| ≤ t * ‖v‖})) (𝓝[>] 0) (𝓝 0) := by
  set C : ℝ → Set E := fun t ↦ closedBall (0 : E) 1 ∩ {v | |ψ v| ≤ t * ‖v‖}
  have hmono : Monotone C := fun s t hst v hv ↦
    ⟨hv.1, hv.2.trans (mul_le_mul_of_nonneg_right hst (norm_nonneg v))⟩
  -- The sequence of cones of aperture `1 / (n + 1)`.
  have hmeas (n : ℕ) : NullMeasurableSet (C (1 / (n + 1))) μ :=
    (isClosed_closedBall.inter (isClosed_le (by fun_prop) (by fun_prop))).measurableSet
      |>.nullMeasurableSet
  have hanti : Antitone fun n : ℕ ↦ C (1 / (n + 1)) := fun m n hmn ↦ hmono (by gcongr)
  have hfin : μ (C (1 / ((0 : ℕ) + 1))) ≠ ∞ :=
    (measure_mono inter_subset_left).trans_lt measure_closedBall_lt_top |>.ne
  have hlim := tendsto_measure_iInter_atTop hmeas hanti ⟨0, hfin⟩
  set W := LinearMap.ker (ψ : E →ₗ[ℝ] ℝ)
  have hker : ⋂ n : ℕ, C (1 / (n + 1)) ⊆ (W : Set E) := by
    intro v hv
    simp only [mem_iInter] at hv
    simp only [SetLike.mem_coe, W, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
    refine abs_eq_zero.mp (le_antisymm (le_of_forall_pos_le_add fun δ hδ ↦ ?_) (abs_nonneg _))
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
    have hv1 : ‖v‖ ≤ 1 := mem_closedBall_zero_iff.mp (hv n).1
    calc |ψ v| ≤ 1 / (n + 1) * ‖v‖ := (hv n).2
      _ ≤ 1 / (n + 1) * 1 := by gcongr
      _ ≤ 0 + δ := by linarith
  have hker0 : μ (W : Set E) = 0 := by
    refine Measure.addHaar_submodule _ _ fun htop ↦ hψ ?_
    ext v
    have hv : v ∈ W := htop ▸ Submodule.mem_top
    simpa [W] using hv
  rw [measure_mono_null hker hker0] at hlim
  -- Every small aperture is dominated by a term of the sequence.
  refine ENNReal.tendsto_nhds_zero.mpr fun ε hε ↦ ?_
  obtain ⟨n, hn⟩ := (ENNReal.tendsto_nhds_zero.mp hlim ε hε).exists
  filter_upwards [Ioo_mem_nhdsGT (by positivity : (0 : ℝ) < 1 / (n + 1))] with t ht
  exact (measure_mono (hmono ht.2.le)).trans hn

end TauCeti
