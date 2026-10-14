/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ContinuousAffineEquiv

/-!
# Forgetting invertibility of continuous affine equivalences

The continuous affine map underlying an equivalence has the same linear part, viewed as a
linear map. This identifies the linear parts used for differentiation and change of variables.
-/

public section

namespace ContinuousAffineEquiv

variable {R P Q V W : Type*} [Ring R]
  [AddCommGroup V] [Module R V] [AddTorsor V P] [TopologicalSpace P]
  [AddCommGroup W] [Module R W] [AddTorsor W Q] [TopologicalSpace Q]

/-- Forgetting invertibility preserves the linear part of a continuous affine equivalence. -/
@[simp]
theorem toContinuousAffineMap_linear (A : P ≃ᴬ[R] Q) :
    A.toContinuousAffineMap.linear = A.linear.toLinearMap := by
  rw [toContinuousAffineMap_toAffineMap, AffineEquiv.linear_toAffineMap]

end ContinuousAffineEquiv
