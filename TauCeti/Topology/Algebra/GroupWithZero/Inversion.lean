/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.GroupWithZero

/-!
# Inversion on the nonzero elements of a topological group with zero

The value of `Homeomorph.inv₀` coerces to inversion in the ambient group with zero.
-/

public section

/-- The underlying value of inversion on the nonzero subtype is the ambient inverse. -/
@[simp] theorem Homeomorph.coe_inv₀_apply {G₀ : Type*} [GroupWithZero G₀] [TopologicalSpace G₀]
    [ContinuousInv₀ G₀] (x : {g : G₀ // g ≠ 0}) : (Homeomorph.inv₀ G₀ x : G₀) = (x : G₀)⁻¹ :=
  (rfl)
