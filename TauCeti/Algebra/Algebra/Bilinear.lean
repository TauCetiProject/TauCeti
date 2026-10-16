/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Equivariance of tensor multiplication

The multiplication map `LinearMap.mul' R A : A ⊗[R] A → A` intertwines left multiplication on
the first tensor factor with left multiplication on `A`, and right multiplication on the second
tensor factor with right multiplication on `A`.  These identities show, for instance, that the
kernel of multiplication is stable under the outer bimodule actions.
-/

public section

open scoped TensorProduct

namespace TauCeti

namespace LinearMap

variable {R A : Type*} [CommSemiring R] [NonUnitalSemiring A] [Module R A]
  [SMulCommClass R A A] [IsScalarTower R A A]

/-- Multiplication `A ⊗ A → A` turns left multiplication on the first factor into left
multiplication. -/
theorem mul'_rTensor_mulLeft (a : A) (t : A ⊗[R] A) :
    LinearMap.mul' R A ((LinearMap.mulLeft R a).rTensor A t) =
      a * LinearMap.mul' R A t := by
  induction t using TensorProduct.inductionOn with
  | tmul x y => simp [mul_assoc]
  | add x y hx hy => simp only [map_add, hx, hy, mul_add]

/-- Multiplication `A ⊗ A → A` turns right multiplication on the second factor into right
multiplication. -/
theorem mul'_lTensor_mulRight (a : A) (t : A ⊗[R] A) :
    LinearMap.mul' R A ((LinearMap.mulRight R a).lTensor A t) =
      LinearMap.mul' R A t * a := by
  induction t using TensorProduct.inductionOn with
  | tmul x y => simp [mul_assoc]
  | add x y hx hy => simp only [map_add, hx, hy, add_mul]

end LinearMap

end TauCeti
