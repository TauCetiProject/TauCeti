/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.LinearAlgebra.Prod

/-!
# Reflecting one coordinate of a product

The norm of a product `E × F` is the maximum of the coordinate norms, so negating the first
coordinate is a linear isometry equivalence `LinearIsometryEquiv.negFst`. On `ℝ × ℝ` this is the
reflection `(s, t) ↦ (-s, t)` exchanging the two ends of a strip or cylinder, which transports
results proved at the end `s → ∞` to the end `s → -∞`. Precomposition with it preserves operator
norms by Mathlib's `ContinuousLinearMap.opNorm_comp_linearIsometryEquiv`.

## Main definitions

* `LinearIsometryEquiv.negFst`: the reflection `(x, y) ↦ (-x, y)` of `E × F`.
-/

public section

namespace LinearIsometryEquiv

variable (R E F : Type*) [Semiring R] [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
  [Module R E] [Module R F]

/-- The reflection `(x, y) ↦ (-x, y)` of `E × F`, negating the first coordinate, as a linear
isometry equivalence. -/
def negFst : E × F ≃ₗᵢ[R] E × F where
  toLinearEquiv := (LinearEquiv.neg R).prodCongr (LinearEquiv.refl R F)
  norm_map' z := by simp [Prod.norm_def]

@[simp]
theorem negFst_apply (z : E × F) : negFst R E F z = (-z.1, z.2) := (rfl)

theorem coe_negFst : ⇑(negFst R E F) = Prod.map Neg.neg id := (rfl)

/-- The reflection `negFst` is an involution. -/
@[simp]
theorem symm_negFst : (negFst R E F).symm = negFst R E F := by
  ext z <;> rfl

end LinearIsometryEquiv
