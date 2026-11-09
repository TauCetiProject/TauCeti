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
`(x + by) - yω`, fixes `R`. Mathlib bundles it as the `R`-algebra automorphism
`QuadraticAlgebra.starAlgEquiv`. This file records that the bundled automorphism is its own
inverse.
-/

public section

namespace QuadraticAlgebra

variable {R : Type*} [CommRing R] {a b : R}

/-- The quadratic involution as an algebra automorphism is its own inverse. -/
@[simp] theorem starAlgEquiv_symm :
    (starAlgEquiv : QuadraticAlgebra R a b ≃ₐ[R] _).symm = starAlgEquiv := by
  apply AlgEquiv.ext
  intro z
  rw [starAlgEquiv_symm_apply, starAlgEquiv_apply]

end QuadraticAlgebra
