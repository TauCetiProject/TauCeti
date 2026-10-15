/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Free

/-!
# Multiplying pure tensors in `A ⊗[K] B`

Multiplication formulas and anticommutation criteria for `A ⊗[K] B` over a commutative
semiring. The anticommutation criteria need only nonunital, nonassociative semirings whose
multiplication is bilinear over `K`. The formulas for multiplication by `a ⊗ₜ 1` use a
`K`-algebra `A` and a possibly nonassociative semiring `B` with `K`-bilinear multiplication.

## Main results

* `Algebra.TensorProduct.tmul_one_mul_eq_smul`: multiplying on the left by `a ⊗ₜ 1` is the left
  `A`-module action on `A ⊗[K] B`.
* `Algebra.TensorProduct.basis_repr_mul_tmul_one`: multiplying on the right by `a ⊗ₜ 1` multiplies
  each coordinate against `Algebra.TensorProduct.basis` by `a` on the right.
* `Algebra.TensorProduct.tmul_anticommute_of_left` and
  `Algebra.TensorProduct.tmul_anticommute_of_right`: pure tensors anticommute when the factors
  on one side anticommute and the factors on the other side commute.
-/

public section

open scoped TensorProduct

namespace Algebra.TensorProduct

variable {K A B ι : Type*} [CommSemiring K]

section NonUnitalNonAssocSemiring

variable [NonUnitalNonAssocSemiring A] [Module K A] [SMulCommClass K A A] [IsScalarTower K A A]
  [NonUnitalNonAssocSemiring B] [Module K B] [SMulCommClass K B B] [IsScalarTower K B B]

/-- Pure tensors anticommute when their left factors anticommute and right factors commute. -/
theorem tmul_anticommute_of_left {x x' : A} {y y' : B}
    (hx : x * x' + x' * x = 0) (hy : Commute y y') :
    x ⊗ₜ[K] y * x' ⊗ₜ y' + x' ⊗ₜ y' * x ⊗ₜ y = 0 := by
  simp only [tmul_mul_tmul, hy.eq, ← TensorProduct.add_tmul, hx, TensorProduct.zero_tmul]

/-- Pure tensors anticommute when their left factors commute and right factors anticommute. -/
theorem tmul_anticommute_of_right {x x' : A} {y y' : B}
    (hx : Commute x x') (hy : y * y' + y' * y = 0) :
    x ⊗ₜ[K] y * x' ⊗ₜ y' + x' ⊗ₜ y' * x ⊗ₜ y = 0 := by
  simp only [tmul_mul_tmul, hx.eq, ← TensorProduct.tmul_add, hy, TensorProduct.tmul_zero]

end NonUnitalNonAssocSemiring

section Semiring

variable [Semiring A] [Algebra K A]
  [NonAssocSemiring B] [Module K B] [SMulCommClass K B B] [IsScalarTower K B B]

/-- Left multiplication by `a ⊗ₜ 1` on `A ⊗[K] B` is the left `A`-module action, the one that
`Algebra.TensorProduct.basis` is a basis for. This identifies `a ⊗ₜ 1` with `a • 1` in
`smul_one_mul`, and does not require `A` to be commutative. -/
@[simp]
theorem tmul_one_mul_eq_smul (a : A) (x : A ⊗[K] B) :
    (a ⊗ₜ[K] (1 : B)) * x = a • x := by
  simpa [one_def, TensorProduct.smul_tmul'] using smul_one_mul a x

variable (𝓑 : Module.Basis ι K B)

/-- Multiplying by `a ⊗ₜ 1` on the right multiplies each coordinate of `x` by `a` on the right.

Unlike the left-handed `Algebra.TensorProduct.tmul_one_mul_eq_smul` this is not an instance of the
generic scalar-action API, since right multiplication is not the module action
`Algebra.TensorProduct.basis` is a basis for. -/
@[simp]
theorem basis_repr_mul_tmul_one (a : A) (x : A ⊗[K] B) (j : ι) :
    (basis A 𝓑).repr (x * (a ⊗ₜ[K] (1 : B))) j = (basis A 𝓑).repr x j * a := by
  induction x using TensorProduct.inductionOn with
  | tmul a' b => simp [mul_assoc, ← Algebra.commutes]
  | add x y hx hy => simp [add_mul, hx, hy]

end Semiring

end Algebra.TensorProduct
