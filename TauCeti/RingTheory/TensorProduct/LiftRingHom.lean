/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Ring homomorphisms out of a tensor product of commutative algebras

For commutative `R`-algebras `A` and `B`, the tensor product `A ⊗[R] B` is the pushout of
`A ← R → B` in commutative rings. Mathlib's `Algebra.TensorProduct.productMap` expresses this
universal property for algebra homomorphisms into an `R`-algebra, and
`Algebra.TensorProduct.ringHom_ext` is its uniqueness half for ring homomorphisms. This file
supplies the existence half for ring homomorphisms: ring homomorphisms `x : A →+* T` and
`y : B →+* T` into a commutative ring `T` which agree on `R` induce `a ⊗ b ↦ x a * y b`, with no
`R`-algebra structure on `T` involved. This is the form needed when `T` already carries an
`R`-algebra structure which `x` and `y` do not respect, for instance when `T` is itself a tensor
product over `R` and `x` twists the first factor by a ring automorphism.

## Main definitions

* `Algebra.TensorProduct.liftRingHom x y h`: the ring homomorphism `a ⊗ b ↦ x a * y b`.
-/

public section

open TensorProduct

namespace Algebra.TensorProduct

variable {R A B T : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] [CommSemiring B]
  [Algebra R B] [CommSemiring T]

/-- The ring homomorphism `A ⊗[R] B →+* T`, `a ⊗ b ↦ x a * y b`, induced by ring homomorphisms
`x : A →+* T` and `y : B →+* T` which agree on `R`. Unlike `Algebra.TensorProduct.productMap`, no
`R`-algebra structure on `T` is involved. -/
noncomputable def liftRingHom (x : A →+* T) (y : B →+* T)
    (h : x.comp (algebraMap R A) = y.comp (algebraMap R B)) : A ⊗[R] B →+* T :=
  letI : Algebra R T := (x.comp (algebraMap R A)).toAlgebra
  (productMap (R := R) { x with commutes' := fun _ ↦ rfl }
    { y with commutes' := fun r ↦ congr($h r).symm }).toRingHom

variable (x : A →+* T) (y : B →+* T) (h : x.comp (algebraMap R A) = y.comp (algebraMap R B))

@[simp]
theorem liftRingHom_tmul (a : A) (b : B) : liftRingHom x y h (a ⊗ₜ b) = x a * y b := by
  simp [liftRingHom]

@[simp]
theorem liftRingHom_comp_includeLeftRingHom :
    (liftRingHom x y h).comp includeLeftRingHom = x := by
  ext a
  simp

@[simp]
theorem liftRingHom_comp_includeRight :
    (liftRingHom x y h).comp (includeRight : B →ₐ[R] A ⊗[R] B) = y := by
  ext b
  simp

end Algebra.TensorProduct
