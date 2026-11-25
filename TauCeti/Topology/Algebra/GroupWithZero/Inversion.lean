/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.GroupWithZero

/-!
# Inversion on the nonzero elements of a group with zero

The value of Mathlib's inversion homeomorphism in the ambient group with zero is the
multiplicative inverse.
-/

public section

/-- Coercing the image of a nonzero element under the inversion homeomorphism gives its inverse. -/
@[simp] theorem Homeomorph.coe_inv₀_apply {G₀ : Type*} [GroupWithZero G₀] [TopologicalSpace G₀]
    [ContinuousInv₀ G₀] (x : {g : G₀ // g ≠ 0}) : (Homeomorph.inv₀ G₀ x : G₀) = (x : G₀)⁻¹ :=
  (rfl)
