/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Uniform local properties and norm bounds over compact parameter sets

This file records a uniform local boundedness consequence of continuity over a compact family.
Such bounds provide constant dominating functions for compact-parameter integration.
It also gives a norm-ball version of the tube lemma for properties near a compact fiber.

## Main declarations

* `IsCompact.exists_pos_forall_norm_lt`: a property holding near each point of `{0} × K`
  holds on a uniform norm-ball times `K`.
* `IsCompact.exists_eventually_norm_le`: a function continuous at every point of a compact fiber
  is uniformly bounded on nearby fibers, which remain in any open set containing the original
  fiber.
* `TauCeti.exists_nonneg_forall_notMem_norm_lt`: in a compact space covered by open sets `U` and
  `V`, the coordinates of the points of `U` outside `V` are bounded.
-/

public section

open Filter Set
open scoped Topology

variable {X P H : Type*} [TopologicalSpace X] [TopologicalSpace P] [SeminormedAddGroup H]

/-- A property holding near every point of `{0} × K`, with `K` compact, holds uniformly on
the product of a sufficiently small norm-ball about zero with `K`. -/
theorem IsCompact.exists_pos_forall_norm_lt {K : Set P} (hK : IsCompact K)
    {Q : H → P → Prop} (hQ : ∀ y ∈ K, ∀ᶠ z in 𝓝 ((0 : H), y), Q z.1 z.2) :
    ∃ r > 0, ∀ ⦃x : H⦄, ‖x‖ < r → ∀ y ∈ K, Q x y := by
  simpa using Metric.eventually_nhds_iff.1 (hK.eventually_forall_of_forall_eventually hQ)

/-- A function continuous at every point of `{x₀} × K`, with `K` compact, is uniformly bounded
on `{x} × K` for `x` near `x₀`. These nearby fibers also lie in any open set `W` containing
the original fiber. -/
theorem IsCompact.exists_eventually_norm_le {K : Set P} (hK : IsCompact K)
    {W : Set (X × P)} {F : X × P → H} {x₀ : X} (hW : IsOpen W)
    (hF : ∀ y ∈ K, ContinuousAt F (x₀, y)) (hx₀ : ∀ y ∈ K, (x₀, y) ∈ W) :
    ∃ C, ∀ᶠ x in 𝓝 x₀, ∀ y ∈ K, (x, y) ∈ W ∧ ‖F (x, y)‖ ≤ C := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn fun y hy ↦
    ((hF y hy).comp (Continuous.prodMk_right x₀).continuousAt).continuousWithinAt
  refine ⟨C + 1, hK.eventually_forall_of_forall_eventually fun y hy ↦ ?_⟩
  filter_upwards [hW.eventually_mem (hx₀ y hy),
    (hF y hy).norm.eventually_lt_const ((hC y hy).trans_lt (lt_add_one C))] with z hzW hz
  exact ⟨hzW, hz.le⟩

namespace TauCeti

/-- In a compact space covered by open sets `U` and `V`, the points of `U` outside `V` have
bounded coordinates in any homeomorphism `eU : U ≃ₜ H` with a seminormed group. -/
theorem exists_nonneg_forall_notMem_norm_lt [CompactSpace X] {U V : Set X} (hV : IsOpen V)
    (hUV : U ∪ V = univ) (eU : U ≃ₜ H) : ∃ R, 0 ≤ R ∧ ∀ x : U, (x : X) ∉ V → ‖eU x‖ < R := by
  have hK : IsCompact ((↑) ⁻¹' Vᶜ : Set U) := by
    rw [Subtype.isCompact_iff, Subtype.image_preimage_coe,
      inter_eq_right.2 fun x hx ↦ (eq_univ_iff_forall.1 hUV x).resolve_right hx]
    exact hV.isClosed_compl.isCompact
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn eU.continuous.continuousOn
  exact ⟨max C 0 + 1, by positivity, fun x hx ↦ (hC x hx).trans_lt (by linarith [le_max_left C 0])⟩

end TauCeti
