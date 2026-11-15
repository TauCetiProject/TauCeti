/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.ContinuousMap.Algebra

/-!
# The exponential of a bounded continuous function

The exponential of a bounded continuous function with values in a complete normed `ℚ`-algebra
is computed pointwise (`BoundedContinuousFunction.exp_apply`). This is the bounded continuous
analogue of `Pi.coe_exp`.
-/

public section

open scoped BoundedContinuousFunction
open NormedSpace

namespace BoundedContinuousFunction

variable {α : Type*} [TopologicalSpace α]

/-- The exponential of a bounded continuous function with values in a complete normed
`ℚ`-algebra is computed pointwise. -/
@[simp]
theorem exp_apply {R : Type*} [NormedRing R] [NormedAlgebra ℚ R] [CompleteSpace R]
    (g : α →ᵇ R) (x : α) : exp g x = exp (g x) :=
  -- The coercion of the composite ring homomorphism is definitionally evaluation at `x`.
  map_exp (((Pi.evalRingHom (fun _ : α => R) x).comp ContinuousMap.coeFnRingHom).comp
    (toContinuousMapₐ ℚ : (α →ᵇ R) →ₐ[ℚ] C(α, R)).toRingHom) (continuous_eval_const x) g

end BoundedContinuousFunction
