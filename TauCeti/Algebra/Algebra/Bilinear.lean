/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Module.Equiv.Opposite
public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Equivariance of tensor multiplication

The multiplication map `LinearMap.mul' R A : A ⊗[R] A → A` intertwines left multiplication on
the first tensor factor with left multiplication on `A`, and right multiplication on the second
tensor factor with right multiplication on `A`.  These identities show, for instance, that the
kernel of multiplication is stable under the outer bimodule actions.

The multiplication map `TauCeti.LinearMap.mulUnop' R A : A ⊗[R] Aᵐᵒᵖ → A`, `a ⊗ bᵒᵖ ↦ a b`,
is the variant with the second factor read in the opposite algebra.

Left multiplication `Algebra.lmul R A` is the action map `Algebra.lsmul R R A` of `A` on itself
regarded as a module over itself (`TauCeti.Algebra.lmul_eq_lsmul`), so results about the trace or
action of an arbitrary module specialise to the regular module.
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

variable (R A) in
/-- Multiplication `A ⊗ Aᵐᵒᵖ → A`, `a ⊗ bᵒᵖ ↦ a b`. -/
noncomputable def mulUnop' : A ⊗[R] Aᵐᵒᵖ →ₗ[R] A :=
  LinearMap.mul' R A ∘ₗ
    TensorProduct.map LinearMap.id (MulOpposite.opLinearEquiv R).symm.toLinearMap

/-- `TauCeti.LinearMap.mulUnop'` on elementary tensors. -/
@[simp]
theorem mulUnop'_tmul (a : A) (b : Aᵐᵒᵖ) : mulUnop' R A (a ⊗ₜ b) = a * b.unop :=
  (rfl)

end LinearMap

namespace Algebra

variable (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]

/-- Left multiplication `L_a` is the action of `a` on `A` regarded as a module over itself. -/
theorem lmul_eq_lsmul : Algebra.lmul R A = Algebra.lsmul R R A := by
  ext a z
  rw [Algebra.coe_lmul_eq_mul, LinearMap.mul_apply', Algebra.lsmul_apply, smul_eq_mul]

end Algebra

end TauCeti
