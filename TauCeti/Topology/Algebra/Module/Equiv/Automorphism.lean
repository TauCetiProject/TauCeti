/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Topology.Algebra.Group.Defs

/-!
# Continuous homomorphisms into the automorphisms of a normed space

In the group `ContinuousLinearEquiv.automorphismGroup` of continuous linear automorphisms of a
space, the inverse of `e` is `e.symm`. So along a group homomorphism `τ` from a topological group
the inverses `(τ g).symm = τ g⁻¹` vary continuously in the operator norm as soon as the
automorphisms `τ g` do (`MonoidHom.continuous_coe_symm`). This is the continuity of a linear
representation of a topological group on a normed space, in the operator norm, together with that
of the inverse operators.
-/

public section

namespace MonoidHom

variable {G 𝕜 E : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Along a group homomorphism into the continuous linear automorphisms of a normed space, the
inverse automorphisms depend continuously on the group element in the operator norm whenever the
automorphisms do. -/
theorem continuous_coe_symm (τ : G →* (E ≃L[𝕜] E)) (hτ : Continuous fun g ↦ (τ g : E →L[𝕜] E)) :
    Continuous fun g ↦ ((τ g).symm : E →L[𝕜] E) :=
  -- In `ContinuousLinearEquiv.automorphismGroup` the inverse of `e` is `e.symm` by definition.
  (hτ.comp continuous_inv).congr fun g ↦ by rw [Function.comp_apply, map_inv]; rfl

end MonoidHom
