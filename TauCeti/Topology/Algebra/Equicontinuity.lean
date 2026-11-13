/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.UniformSpace.Equicontinuity

/-!
# Equicontinuous families of zero-preserving maps

This file records consequences of equicontinuity at `0` for families of maps that send `0` to
`0`, such as linear maps between topological modules or additive group homomorphisms.
-/

public section

open Topology

variable {ι F M N : Type*} [TopologicalSpace M] [Zero M] [UniformSpace N] [Zero N]
  [FunLike F M N] [ZeroHomClass F M N]

/-- A family of zero-preserving maps that is equicontinuous at `0` sends some common
neighbourhood of zero into any given neighbourhood of zero. -/
theorem EquicontinuousAt.eventually_forall_apply_mem {φ : ι → F}
    (hφ : EquicontinuousAt (fun i ↦ ⇑(φ i)) 0) {W : Set N} (hW : W ∈ 𝓝 0) :
    ∀ᶠ m in 𝓝 (0 : M), ∀ i, φ i m ∈ W := by
  -- The entourage of pairs whose second entry lies in `W` whenever the first one is `0`.
  filter_upwards [hφ _ (mem_nhds_uniformity_iff_right.mp hW)] with m hm i
  exact hm i (map_zero (φ i))
