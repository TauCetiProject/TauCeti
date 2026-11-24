/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Continuous
public import TauCeti.Topology.Order.OrderClosed

/-!
# The closure and frontier of a domain inside a graph patch

Let `ν ≠ 0` be a vector of a real inner product space and `γ` a function invariant under translation
along `ν`. The region `{z | γ z < ⟪z, ν⟫}` lies above the graph `{z | ⟪z, ν⟫ = γ z}` of a function
over the hyperplane `ν^⊥`. A domain `Ω` has a *graph patch* on an open set `U` when

`U ∩ Ω = U ∩ {z | γ z < ⟪z, ν⟫}`,

which is how a domain with `C^k` boundary is described near a boundary point. Inside such a patch:

* every point on or above the graph lies in the closure of `Ω`
  (`TauCeti.inter_setOf_le_inner_subset_closure`); no regularity of `γ` is needed, since such a
  point `y` is the limit of the points `y + t ν`, `t > 0`, which lie strictly above it;
* if `γ` is continuous on `U`, the closure of `Ω` is the closed region `{z | γ z ≤ ⟪z, ν⟫}`
  (`TauCeti.inter_closure_eq_inter_setOf_le_inner`), and the frontier of `Ω` is the graph
  `{z | ⟪z, ν⟫ = γ z}` (`TauCeti.inter_frontier_eq_inter_setOf_inner_eq`); `Ω` need not be open,
  since the patch makes `U ∩ Ω` open.
-/

public section

open Set Filter Topology
open scoped InnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {U Ω : Set E} {ν : E}
  {γ : E → ℝ}

/-- Inside a graph patch `U ∩ Ω = U ∩ {z | γ z < ⟪z, ν⟫}` on an open set `U`, with `γ` invariant
along `ν ≠ 0`, every point on or above the graph of `γ` lies in the closure of `Ω`: such a point
`y` is the limit of the points `y + t ν`, `t > 0`, which lie strictly above it. -/
theorem inter_setOf_le_inner_subset_closure (hU : IsOpen U) (hν : ν ≠ 0)
    (hγν : ∀ z (t : ℝ), γ (z + t • ν) = γ z) (hΩ : U ∩ Ω = U ∩ {z | γ z < ⟪z, ν⟫_ℝ}) :
    U ∩ {z | γ z ≤ ⟪z, ν⟫_ℝ} ⊆ closure Ω := by
  rintro y ⟨hy, hle : γ y ≤ ⟪y, ν⟫_ℝ⟩
  -- Approach `y` along `ν` from above.
  have ht : Tendsto (fun t : ℝ => y + t • ν) (𝓝[>] 0) (𝓝 y) := by
    have h0 : Tendsto (fun t : ℝ => y + t • ν) (𝓝 0) (𝓝 (y + (0 : ℝ) • ν)) :=
      (continuous_const.add (continuous_id.smul continuous_const)).tendsto 0
    rw [zero_smul, add_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto ht ?_
  filter_upwards [ht (hU.mem_nhds hy), self_mem_nhdsWithin] with t htU htpos
  have hmem : y + t • ν ∈ U ∩ Ω := by
    rw [hΩ]
    refine ⟨htU, ?_⟩
    rw [mem_ofPred_eq, hγν, inner_add_left, real_inner_smul_left]
    have hνν : 0 < ⟪ν, ν⟫_ℝ := real_inner_self_pos.2 hν
    have ht0 : (0 : ℝ) < t := htpos
    linarith [mul_pos ht0 hνν]
  exact hmem.2

/-- Inside a graph patch `U ∩ Ω = U ∩ {z | γ z < ⟪z, ν⟫}` on an open set `U`, with `γ` continuous
on `U` and invariant along `ν ≠ 0`, the closure of `Ω` is the closed region on or above the graph
of `γ`. -/
theorem inter_closure_eq_inter_setOf_le_inner (hU : IsOpen U) (hν : ν ≠ 0)
    (hγ : ContinuousOn γ U) (hγν : ∀ z (t : ℝ), γ (z + t • ν) = γ z)
    (hΩ : U ∩ Ω = U ∩ {z | γ z < ⟪z, ν⟫_ℝ}) :
    U ∩ closure Ω = U ∩ {z | γ z ≤ ⟪z, ν⟫_ℝ} :=
  Subset.antisymm
    (fun _ hy => ⟨hy.1, inter_closure_subset_setOf_le hU hγ
      (continuous_id.inner continuous_const).continuousOn hΩ hy⟩)
    (fun _ hy => ⟨hy.1, inter_setOf_le_inner_subset_closure hU hν hγν hΩ hy⟩)

/-- Inside a graph patch `U ∩ Ω = U ∩ {z | γ z < ⟪z, ν⟫}` on an open set `U`, with `γ` continuous
on `U` and invariant along `ν ≠ 0`, the frontier of `Ω` is the graph of `γ`. -/
theorem inter_frontier_eq_inter_setOf_inner_eq (hU : IsOpen U) (hν : ν ≠ 0)
    (hγ : ContinuousOn γ U) (hγν : ∀ z (t : ℝ), γ (z + t • ν) = γ z)
    (hΩ : U ∩ Ω = U ∩ {z | γ z < ⟪z, ν⟫_ℝ}) :
    U ∩ frontier Ω = U ∩ {z | ⟪z, ν⟫_ℝ = γ z} := by
  have hcl := Set.ext_iff.1 (inter_closure_eq_inter_setOf_le_inner hU hν hγ hγν hΩ)
  -- The patch makes `U ∩ Ω` open, so its points are interior points of `Ω`.
  have hUΩ : IsOpen (U ∩ Ω) := by
    have hf : ContinuousOn (fun z => ⟪z, ν⟫_ℝ - γ z) U :=
      (continuous_id.inner continuous_const).continuousOn.sub hγ
    have := hf.isOpen_inter_preimage hU (isOpen_Ioi (a := (0 : ℝ)))
    rwa [hΩ, show {z | γ z < ⟪z, ν⟫_ℝ} = (fun z => ⟪z, ν⟫_ℝ - γ z) ⁻¹' Ioi 0 by
      ext; simp [sub_pos]]
  ext y
  constructor
  · rintro ⟨hy, hycl, hynΩ⟩
    have hle : γ y ≤ ⟪y, ν⟫_ℝ := ((hcl y).1 ⟨hy, hycl⟩).2
    -- A point of `U` strictly above the graph lies in the interior of `Ω`.
    refine ⟨hy, le_antisymm (not_lt.1 fun hlt => hynΩ ?_) hle⟩
    have hyΩ : y ∈ U ∩ Ω := hΩ ▸ ⟨hy, hlt⟩
    exact interior_maximal inter_subset_right hUΩ hyΩ
  · rintro ⟨hy, heq⟩
    refine ⟨hy, ((hcl y).2 ⟨hy, heq.ge⟩).2, fun hyΩ => ?_⟩
    -- A point of `U ∩ Ω` lies strictly above the graph.
    exact (((Set.ext_iff.1 hΩ y).1 ⟨hy, interior_subset hyΩ⟩).2 : γ y < ⟪y, ν⟫_ℝ).ne heq.symm

end TauCeti
