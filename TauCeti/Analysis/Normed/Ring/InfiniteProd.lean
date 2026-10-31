/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Exponential bounds for infinite products in normed rings

For `f` with summable norms, the infinite product `∏' i, (1 + f i)` in a normed commutative ring
has norm at most `exp (∑' i, ‖f i‖)`. Each finite partial product is bounded by
`∏ (1 + ‖f i‖) ≤ exp (∑ ‖f i‖)`, and the bound passes to the limit. This is the estimate used to
bound theta products and Siegel functions on the upper half-plane by elementary functions of
`|q|`.
-/

public section

namespace TauCeti

variable {ι R : Type*} [NormedCommRing R] [NormOneClass R]

/-- In a normed commutative ring, `‖∏' i, (1 + f i)‖ ≤ exp (∑' i, ‖f i‖)` whenever the norms
`‖f i‖` are summable. -/
theorem norm_tprod_one_add_le_exp_tsum {f : ι → R} (hf : Summable fun i ↦ ‖f i‖) :
    ‖∏' i, (1 + f i)‖ ≤ Real.exp (∑' i, ‖f i‖) := by
  by_cases h : Multipliable fun i ↦ 1 + f i
  · refine le_of_tendsto' (Filter.Tendsto.norm h.hasProd) fun s ↦ ?_
    calc ‖∏ i ∈ s, (1 + f i)‖ ≤ ∏ i ∈ s, ‖1 + f i‖ := Finset.norm_prod_le s _
      _ ≤ ∏ i ∈ s, (1 + ‖f i‖) := Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _)
          fun i _ ↦ (norm_add_le _ _).trans_eq (by rw [norm_one])
      _ ≤ Real.exp (∑ i ∈ s, ‖f i‖) := Real.prod_one_add_le_exp_sum s fun _ ↦ norm_nonneg _
      _ ≤ Real.exp (∑' i, ‖f i‖) :=
          Real.exp_le_exp.2 (hf.sum_le_tsum s fun _ _ ↦ norm_nonneg _)
  · rw [tprod_eq_one_of_not_multipliable h, norm_one]
    exact Real.one_le_exp (tsum_nonneg fun _ ↦ norm_nonneg _)

end TauCeti
