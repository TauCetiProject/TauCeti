/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Uniform local norm bounds over compact parameter sets

This file records a uniform local boundedness consequence of continuity over a compact family.
Such bounds provide constant dominating functions for compact-parameter integration.

## Main declarations

* `IsCompact.exists_eventually_norm_le`: a function continuous at every point of a compact fiber
  is uniformly bounded on nearby fibers, which remain in any open set containing the original
  fiber.
-/

public section

open Filter Set
open scoped Topology

variable {X P H : Type*} [TopologicalSpace X] [TopologicalSpace P] [SeminormedAddGroup H]

/-- A function continuous at every point of `{x₀} × K`, with `K` compact, is uniformly bounded
on `{x} × K` for `x` near `x₀`. These nearby fibers also lie in any open set `W` containing
the original fiber. -/
theorem IsCompact.exists_eventually_norm_le {K : Set P} (hK : IsCompact K)
    {W : Set (X × P)} {F : X × P → H} {x₀ : X} (hW : IsOpen W)
    (hF : ∀ y ∈ K, ContinuousAt F (x₀, y)) (hx₀ : ∀ y ∈ K, (x₀, y) ∈ W) :
    ∃ C, ∀ᶠ x in 𝓝 x₀, ∀ y ∈ K, (x, y) ∈ W ∧ ‖F (x, y)‖ ≤ C := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (fun y hy ↦
    (hF y hy).comp_continuousWithinAt
      (continuous_const.prodMk continuous_id).continuousWithinAt)
  refine ⟨C + 1, ?_⟩
  apply hK.eventually_forall_of_forall_eventually
  intro y hy
  have hlt : ∀ᶠ z in 𝓝 (x₀, y), ‖F z‖ < C + 1 :=
    (hF y hy).norm.eventually_lt_const ((hC y hy).trans_lt (lt_add_one C))
  exact ((hW.eventually_mem (hx₀ y hy)).and hlt).mono fun _ hz ↦ ⟨hz.1, hz.2.le⟩
