/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Continuous

/-!
# The region above a graph in an inner product space

Let `ν ≠ 0` be a vector of a real inner product space `E` and let `γ : E → ℝ` be invariant under
translation along `ν`. Then `{x | γ x < ⟪x, ν⟫}` is the open region above the graph of `γ` over
the hyperplane `ν^⊥`, `{x | γ x ≤ ⟪x, ν⟫}` is the closed region, and `{x | ⟪x, ν⟫ = γ x}` is the
graph itself. This file records how these sets sit relative to each other inside an open set `U`.

* Every point of the closed region in `U` is a limit of points of the open region in `U`,
  approached along `ν` (`TauCeti.setOf_le_inner_inter_subset_closure`).
* If a set `Ω` agrees with the open region on `U`, then the closed region in `U` lies in
  `closure Ω` (`TauCeti.setOf_le_inner_inter_subset_closure_of_inter_eq`); for continuous `γ`,
  conversely, `closure Ω ∩ U` lies in the closed region
  (`TauCeti.closure_inter_subset_setOf_le_inner_of_inter_eq`); and the points of the graph in `U`
  lie on `frontier Ω` (`TauCeti.mem_frontier_of_inner_eq_of_inter_eq`).

These are the facts used when a domain with `C^{k,α}` boundary is described near each boundary
point as the region above a graph.
-/

public section

open Set Filter Topology
open scoped InnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every point of the closed region `{x | γ x ≤ ⟪x, ν⟫}` in an open set `U` is a limit of points of
the open region `{x | γ x < ⟪x, ν⟫}` in `U`, approached along `ν`. -/
theorem setOf_le_inner_inter_subset_closure {U : Set E} {ν : E} {γ : E → ℝ} (hU : IsOpen U)
    (hν : ν ≠ 0) (hγν : ∀ x (t : ℝ), γ (x + t • ν) = γ x) :
    {x | γ x ≤ ⟪x, ν⟫_ℝ} ∩ U ⊆ closure ({x | γ x < ⟪x, ν⟫_ℝ} ∩ U) := by
  intro y ⟨hy, hyU⟩
  have ht : Tendsto (fun t : ℝ => y + t • ν) (𝓝[>] 0) (𝓝 y) :=
    tendsto_nhdsWithin_of_tendsto_nhds
      ((continuous_const.add (continuous_id.smul continuous_const)).tendsto' 0 y (by simp))
  refine mem_closure_of_tendsto ht ?_
  filter_upwards [ht.eventually (hU.mem_nhds hyU), self_mem_nhdsWithin] with t htU ht0
  refine ⟨?_, htU⟩
  have hpos : 0 < t * ‖ν‖ ^ 2 := mul_pos ht0 (by positivity)
  have hlt : γ y < ⟪y, ν⟫_ℝ + t * ‖ν‖ ^ 2 := hy.trans_lt (lt_add_of_pos_right _ hpos)
  simpa only [mem_ofPred_eq, hγν, inner_add_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq] using hlt

/-- If `Ω` agrees on an open set `U` with the region `{x | γ x < ⟪x, ν⟫}` above the graph of `γ`,
then the closed region `{x | γ x ≤ ⟪x, ν⟫}` in `U` lies in the closure of `Ω`. -/
theorem setOf_le_inner_inter_subset_closure_of_inter_eq {Ω U : Set E} {ν : E} {γ : E → ℝ}
    (hU : IsOpen U) (hΩU : Ω ∩ U = {x | γ x < ⟪x, ν⟫_ℝ} ∩ U) (hν : ν ≠ 0)
    (hγν : ∀ x (t : ℝ), γ (x + t • ν) = γ x) :
    {x | γ x ≤ ⟪x, ν⟫_ℝ} ∩ U ⊆ closure Ω := by
  refine (setOf_le_inner_inter_subset_closure hU hν hγν).trans (closure_mono ?_)
  rw [← hΩU]
  exact inter_subset_left

/-- If `Ω` agrees on an open set `U` with the region `{x | γ x < ⟪x, ν⟫}` above the graph of a
continuous `γ`, then the closure of `Ω` meets `U` inside the closed region `{x | γ x ≤ ⟪x, ν⟫}`. -/
theorem closure_inter_subset_setOf_le_inner_of_inter_eq {Ω U : Set E} {ν : E} {γ : E → ℝ}
    (hU : IsOpen U) (hΩU : Ω ∩ U = {x | γ x < ⟪x, ν⟫_ℝ} ∩ U) (hγ : Continuous γ) :
    closure Ω ∩ U ⊆ {x | γ x ≤ ⟪x, ν⟫_ℝ} := by
  intro x ⟨hx, hxU⟩
  have hx' : x ∈ closure (Ω ∩ U) := by
    rw [inter_comm]
    exact hU.inter_closure ⟨hxU, hx⟩
  rw [hΩU] at hx'
  exact closure_lt_subset_le hγ (continuous_id.inner continuous_const)
    (closure_mono inter_subset_left hx')

/-- If `Ω` agrees on an open set `U` with the region `{x | γ x < ⟪x, ν⟫}` above the graph of `γ`,
then the points of the graph `{x | ⟪x, ν⟫ = γ x}` in `U` lie on the frontier of `Ω`. -/
theorem mem_frontier_of_inner_eq_of_inter_eq {Ω U : Set E} {ν : E} {γ : E → ℝ} (hU : IsOpen U)
    (hΩU : Ω ∩ U = {x | γ x < ⟪x, ν⟫_ℝ} ∩ U) (hν : ν ≠ 0)
    (hγν : ∀ x (t : ℝ), γ (x + t • ν) = γ x) {y : E} (hyU : y ∈ U) (hyγ : ⟪y, ν⟫_ℝ = γ y) :
    y ∈ frontier Ω := by
  refine ⟨setOf_le_inner_inter_subset_closure_of_inter_eq hU hΩU hν hγν ⟨hyγ.ge, hyU⟩,
    fun hyΩ => ?_⟩
  have h : y ∈ {x | γ x < ⟪x, ν⟫_ℝ} ∩ U := by
    rw [← hΩU]
    exact ⟨interior_subset hyΩ, hyU⟩
  exact lt_irrefl _ (h.1.trans_eq hyγ)

end TauCeti
