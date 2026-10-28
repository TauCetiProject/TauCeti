/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic
public import Mathlib.Topology.UniformSpace.Equicontinuity

/-!
# Equicontinuous families of linear maps

This file records general consequences of equicontinuity for families of linear maps between
topological modules.
-/

public section

open Filter Topology Uniformity

namespace TauCeti

variable {ι A M N : Type*} [Semiring A] [AddCommMonoid M] [TopologicalSpace M] [Module A M]
  [AddCommGroup N] [UniformSpace N] [IsUniformAddGroup N] [Module A N]

/-- An equicontinuous family of linear maps sends some common neighbourhood of zero into any
given neighbourhood of zero. -/
theorem equicontinuousAt_eventually_forall_apply_mem {φ : ι → M →ₗ[A] N}
    (hφ : EquicontinuousAt (fun i ↦ ⇑(φ i)) 0) {W : Set N} (hW : W ∈ 𝓝 0) :
    ∀ᶠ m in 𝓝 (0 : M), ∀ i, φ i m ∈ W := by
  have hU : {p : N × N | p.2 - p.1 ∈ W} ∈ 𝓤 N := by
    rw [uniformity_eq_comap_nhds_zero N]
    exact preimage_mem_comap hW
  filter_upwards [hφ _ hU] with m hm i
  simpa using hm i

end TauCeti
