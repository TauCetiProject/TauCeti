/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Topology.MetricSpace.Cauchy

/-!
# Limits of uniformly Cauchy weighted families

A sequence of families in a complete seminormed additive group has a uniform weighted limit
whenever its weighted differences are uniformly Cauchy. The weights may be arbitrary real
numbers; at indices with nonpositive weight any value satisfies the required upper bound.
For nonnegative weights, if each family's weighted norms vanish along the cofinite filter,
the weighted norms of the limit vanish there as well.

## Main results

* `TauCeti.exists_weighted_uniform_limit`: existence of a uniform weighted limit.
* `TauCeti.exists_weighted_coefficient_limit`: preservation of vanishing at infinity.
-/

public section

namespace TauCeti

open Filter
open scoped Topology

/-- A sequence of families that is uniformly Cauchy in the weighted coefficient norms
`‖A k t‖ * w t` has a family `a` approximating it uniformly in these weighted norms; at indices
with positive weight `a t` is the coefficientwise limit. No decay, boundedness or positivity
hypothesis on the weights is needed. -/
theorem exists_weighted_uniform_limit {ι E : Type*}
    [SeminormedAddCommGroup E] [CompleteSpace E] (w : ι → ℝ) (A : ℕ → ι → E)
    (hC : ∀ ε > 0, ∃ N, ∀ k ≥ N, ∀ l ≥ N, ∀ t, ‖A k t - A l t‖ * w t < ε) :
    ∃ a : ι → E, ∀ ε > 0, ∃ N, ∀ k ≥ N, ∀ t, ‖A k t - a t‖ * w t ≤ ε := by
  have hlim : ∀ t, ∃ a : E, 0 < w t → Tendsto (fun k ↦ A k t) atTop (𝓝 a) := fun t ↦ by
    by_cases ht : 0 < w t
    · refine (cauchySeq_tendsto_of_complete ?_).imp fun a ha _ ↦ ha
      refine Metric.cauchySeq_iff.mpr fun ε hε ↦ ?_
      obtain ⟨N, hN⟩ := hC (ε * w t) (mul_pos hε ht)
      exact ⟨N, fun k hk l hl ↦ by
        rw [dist_eq_norm]
        exact lt_of_mul_lt_mul_right (hN k hk l hl t) ht.le⟩
    · exact ⟨0, fun h ↦ absurd h ht⟩
  choose a ha using hlim
  refine ⟨a, fun ε hε ↦ ?_⟩
  obtain ⟨N, hN⟩ := hC ε hε
  refine ⟨N, fun k hk t ↦ ?_⟩
  by_cases ht : 0 < w t
  · exact le_of_tendsto (((tendsto_const_nhds.sub (ha t ht)).norm).mul_const (w t))
      (eventually_atTop.mpr ⟨N, fun l hl ↦ (hN k hk l hl t).le⟩)
  · exact (mul_nonpos_of_nonneg_of_nonpos (norm_nonneg _) (not_lt.mp ht)).trans hε.le

/-- A sequence of families whose weighted norms vanish at infinity and whose weighted differences
are uniformly Cauchy has a limit whose weighted norms vanish at infinity, with uniform weighted
error estimates. The index type is arbitrary and the weights may vanish. -/
theorem exists_weighted_coefficient_limit {ι E : Type*}
    [SeminormedAddCommGroup E] [CompleteSpace E] {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    (A : ℕ → ι → E)
    (hres : ∀ k, Tendsto (fun t ↦ ‖A k t‖ * w t) cofinite (𝓝 0))
    (hC : ∀ ε > 0, ∃ N, ∀ k ≥ N, ∀ l ≥ N, ∀ t,
      ‖A k t - A l t‖ * w t < ε) :
    ∃ a : ι → E,
      Tendsto (fun t ↦ ‖a t‖ * w t) cofinite (𝓝 0) ∧
      ∀ ε > 0, ∃ N, ∀ k ≥ N, ∀ t, ‖A k t - a t‖ * w t ≤ ε := by
  obtain ⟨a, hunif⟩ := exists_weighted_uniform_limit _ A hC
  refine ⟨a, ?_, hunif⟩
  -- A uniform weighted limit again vanishes at infinity.
  refine tendsto_order.mpr ⟨fun b hb ↦ .of_forall fun t ↦
    hb.trans_le (mul_nonneg (norm_nonneg _) (hw t)), fun ε hε ↦ ?_⟩
  obtain ⟨N, hN⟩ := hunif (ε / 2) (half_pos hε)
  filter_upwards [(hres N).eventually (gt_mem_nhds (half_pos hε))] with t ht
  calc
    ‖a t‖ * w t ≤ ‖A N t‖ * w t +
        ‖A N t - a t‖ * w t := by
      rw [← add_mul]
      exact mul_le_mul_of_nonneg_right (norm_le_norm_add_norm_sub _ _) (hw t)
    _ < ε / 2 + ε / 2 := add_lt_add_of_lt_of_le ht (hN N le_rfl t)
    _ = ε := add_halves ε

end TauCeti
