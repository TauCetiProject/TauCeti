/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Uniform ultrametric bounds on tensor products

For a linear map into an ultrametric seminormed group, a uniform bound on pure tensors
extends to the whole tensor product. This gives estimates on dual tensor products
without choosing a norm on either source module.
-/

public section

open TensorProduct

namespace LinearMap

variable {R E M N : Type*} [CommSemiring R] [SeminormedAddCommGroup E] [Module R E]
  [IsUltrametricDist E] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

/-- A bound on pure tensors bounds a linear map on the entire tensor product. -/
theorem norm_apply_le_of_tmul (f : M ⊗[R] N →ₗ[R] E) {r : ℝ}
    (h : ∀ m n, ‖f (m ⊗ₜ[R] n)‖ ≤ r) (x : M ⊗[R] N) : ‖f x‖ ≤ r := by
  induction x with
  | tmul m n => exact h m n
  | add x y hx hy =>
    simpa only [map_add] using (IsUltrametricDist.norm_add_le_max (f x) (f y)).trans
      (max_le hx hy)

end LinearMap
