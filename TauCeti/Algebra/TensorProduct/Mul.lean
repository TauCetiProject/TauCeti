/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Free

/-!
# Multiplying by `a ⊗ₜ 1` in `A ⊗[K] B`

Two formulas for multiplication by a pure tensor `a ⊗ₜ 1` in an algebra tensor product, one on
each side. Both are general facts about `A ⊗[K] B` over a commutative semiring: neither needs `A`
or `B` to be central, simple, or even a ring.

## Main results

* `Algebra.TensorProduct.tmul_one_mul_eq_smul`: multiplying on the left by `a ⊗ₜ 1` is the left
  `A`-module action on `A ⊗[K] B`.
* `Algebra.TensorProduct.basis_repr_mul_tmul_one`: multiplying on the right by `a ⊗ₜ 1` multiplies
  each coordinate against `Algebra.TensorProduct.basis` by `a` on the right.

Both are declared into Mathlib's root `Algebra.TensorProduct` namespace, which houses the algebra
tensor product's multiplicative API, rather than into a `TauCeti.`-prefixed copy of it. (The
underlying type is the root `TensorProduct`; `Algebra.TensorProduct` is where its algebra
structure and the lemmas about it live.)
-/

public section

open scoped TensorProduct

namespace TauCeti

variable {K A B ι : Type*} [CommSemiring K] [Semiring A] [Semiring B] [Algebra K A] [Algebra K B]

/-- Left multiplication by `a ⊗ₜ 1` on `A ⊗[K] B` is the left `A`-module action, the one that
`Algebra.TensorProduct.basis` is a basis for.

This is Mathlib's `smul_one_mul`, available because `Algebra.TensorProduct.isScalarTower_right`
makes `A ⊗[K] B` a scalar tower over `A`; all this adds is the identification of `a • 1` with
`a ⊗ₜ 1`. (`Algebra.smul_def` is not available here: `A` is not assumed commutative, so there is no
`Algebra A (A ⊗[K] B)` instance.) -/
@[simp]
theorem _root_.Algebra.TensorProduct.tmul_one_mul_eq_smul (a : A) (x : A ⊗[K] B) :
    (a ⊗ₜ[K] (1 : B)) * x = a • x := by
  rw [← smul_one_mul a x, Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul,
    mul_one]

variable (𝓑 : Module.Basis ι K B)

/-- Multiplying by `a ⊗ₜ 1` on the right multiplies each coordinate of `x` by `a` on the right.

Unlike the left-handed `Algebra.TensorProduct.tmul_one_mul_eq_smul` this is not an instance of the
generic scalar-action API, since right multiplication is not the module action
`Algebra.TensorProduct.basis` is a basis for. -/
@[simp]
theorem _root_.Algebra.TensorProduct.basis_repr_mul_tmul_one (a : A) (x : A ⊗[K] B) (j : ι) :
    (Algebra.TensorProduct.basis A 𝓑).repr (x * (a ⊗ₜ[K] (1 : B))) j =
      (Algebra.TensorProduct.basis A 𝓑).repr x j * a := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a' b =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, Algebra.TensorProduct.basis_repr_tmul,
      Algebra.TensorProduct.basis_repr_tmul]
    simp only [Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul]
    rw [mul_assoc, mul_assoc, Algebra.commutes]
  | add x y hx hy => rw [add_mul, map_add, Finsupp.add_apply, hx, hy, map_add, Finsupp.add_apply,
      add_mul]

end TauCeti
