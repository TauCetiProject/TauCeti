/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Continuous.Basic

/-!
# Basic facts about continuous representations

This file records elementary identities for Mathlib's `ContRepresentation` that hold for any
group, without topology on the group or measure theory.

## Main results

* `ContRepresentation.comp_inv_self`: the action operator of `g` composed with that of `g⁻¹` is
  the identity.
-/

public section

namespace ContRepresentation

/-- An action operator composed with the action of the inverse group element is the identity. -/
theorem comp_inv_self {R G V : Type*} [Ring R] [Group G] [AddCommGroup V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [Module R V] (ρ : ContRepresentation R G V) (g : G) :
    (ρ g).comp (ρ g⁻¹) = ContinuousLinearMap.id R V := by
  rw [← ContinuousLinearMap.mul_def, ← map_mul, mul_inv_cancel, map_one]
  rfl

end ContRepresentation
