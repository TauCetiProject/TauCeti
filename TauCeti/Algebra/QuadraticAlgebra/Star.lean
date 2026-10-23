/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Basic

/-!
# The quadratic involution as an algebra automorphism

The quadratic involution `star` of `QuadraticAlgebra R a b`, sending `x + yω` to
`(x + by) - yω`, fixes `R`. This file bundles it as an `R`-algebra automorphism
`QuadraticAlgebra.starAe`, the form in which it enters Galois-theoretic statements such as
`NumberField.ComplexEmbedding.IsConj`.
-/

public section

namespace QuadraticAlgebra

variable {R : Type*} [CommRing R] {a b : R}

/-- The quadratic involution `star` of `QuadraticAlgebra R a b` as an `R`-algebra
automorphism. -/
def starAe : QuadraticAlgebra R a b ≃ₐ[R] QuadraticAlgebra R a b :=
  AlgEquiv.ofRingEquiv (f := starRingAut) fun r => by ext <;> simp

@[simp] theorem starAe_apply (z : QuadraticAlgebra R a b) : starAe z = star z := (rfl)

@[simp] theorem starAe_symm : (starAe : QuadraticAlgebra R a b ≃ₐ[R] _).symm = starAe := (rfl)

end QuadraticAlgebra
