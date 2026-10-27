/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.IrwinHall.Basic
public import Mathlib.MeasureTheory.Measure.Support
import TauCeti.Probability.Distributions.Uniform.Support

/-!
# Support of Irwin–Hall laws

A sum of `n > 0` independent unit uniforms has topological support `[0, n]`.
Every interior point is the sum of a constant vector in the interior of the unit cube;
neighborhoods of that vector have positive product measure. Exact support supplies strict
increase of the cdf and uniqueness of its inverse on interior probability levels.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  2nd ed., Wiley (1995), chapter 26.
-/

public section

open MeasureTheory ProbabilityTheory Set Topology

namespace TauCeti.Probability

/-- The support of a positive-order Irwin–Hall law is the whole closed interval `[0, n]`. -/
@[simp]
theorem support_irwinHallMeasure {n : ℕ} (hn : 0 < n) :
    (irwinHallMeasure n).support = Icc 0 (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  apply Subset.antisymm
  · exact Measure.support_subset_of_isClosed isClosed_Icc (ae_mem_Icc_irwinHallMeasure n)
  · have hinter : Ioo 0 (n : ℝ) ⊆ (irwinHallMeasure n).support := by
      intro x hx
      rw [Measure.support_eq_forall_isOpen]
      intro U hxU hU
      have hsum : (∑ _ : Fin n, x / (n : ℝ)) = x := by
        simp [div_eq_mul_inv, mul_left_comm, hnR.ne']
      have hpre : (fun y : Fin n → ℝ ↦ ∑ i, y i) ⁻¹' U ∈
          𝓝 (fun _ : Fin n ↦ x / (n : ℝ)) := by
        apply ContinuousAt.preimage_mem_nhds (by fun_prop)
        simpa only [hsum] using hU.mem_nhds hxU
      obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hpre
      rw [← Fintype.card_fin n, ← map_sum_pi_uniformMeasure_zero_one,
        Measure.map_apply (by fun_prop) hU.measurableSet]
      refine lt_of_lt_of_le ?_ (measure_mono hball)
      rw [Measure.pi_ball _ _ hε]
      apply pos_iff_ne_zero.2
      apply Finset.prod_ne_zero_iff.2
      intro i _
      apply ne_of_gt
      apply (Measure.mem_support_iff_forall _).1 ?_ _ (Metric.ball_mem_nhds _ hε)
      rw [support_uniformMeasure zero_lt_one]
      exact ⟨(div_pos hx.1 hnR).le, ((div_lt_one hnR).2 hx.2).le⟩
    simpa only [closure_Ioo hnR.ne] using
      closure_minimal hinter Measure.isClosed_support

end TauCeti.Probability
