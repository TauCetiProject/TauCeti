/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Basic

import Mathlib.Tactic.LinearCombination

/-!
# The quadratic involution as an algebra automorphism

The quadratic involution `star` of `QuadraticAlgebra R a b`, sending `x + yω` to
`(x + by) - yω`, fixes `R`. Mathlib bundles it as the `R`-algebra automorphism
`QuadraticAlgebra.starAlgEquiv`. This file records that the bundled automorphism is its own
inverse, and that when `QuadraticAlgebra R a b` has no zero divisors (for instance the quadratic
field `K(√r)` over a field `K`, for `r` not a square), the identity and conjugation are its only
`R`-algebra endomorphisms (`QuadraticAlgebra.algHom_eq_id_or_eq_starAlgEquiv`).
-/

public section

namespace QuadraticAlgebra

variable {R : Type*} [CommRing R] {a b : R}

/-- The quadratic involution as an algebra automorphism is its own inverse. -/
@[simp] theorem starAlgEquiv_symm :
    (starAlgEquiv : QuadraticAlgebra R a b ≃ₐ[R] _).symm = starAlgEquiv :=
  AlgEquiv.ext fun _ ↦ by simp

/-- If `QuadraticAlgebra R a b` has no zero divisors, an `R`-algebra endomorphism of it is the
identity or conjugation: it sends `ω` to a root of `X ^ 2 - b X - a`, and the roots of this
polynomial are `ω` and `star ω = b - ω`. -/
theorem algHom_eq_id_or_eq_starAlgEquiv [NoZeroDivisors (QuadraticAlgebra R a b)]
    (f : QuadraticAlgebra R a b →ₐ[R] QuadraticAlgebra R a b) :
    f = AlgHom.id R _ ∨ f = (starAlgEquiv : QuadraticAlgebra R a b ≃ₐ[R] _).toAlgHom := by
  have hω := omega_mul_omega_eq_algebraMap (a := a) (b := b)
  -- `f ω` satisfies the same quadratic equation as `ω`.
  have hfω : f ω * f ω = algebraMap R _ a + algebraMap R _ b * f ω := by
    rw [← map_mul, hω]
    simp
  -- The other root of `X ^ 2 - b X - a`.
  have hstar : star (ω : QuadraticAlgebra R a b) = algebraMap R _ b - ω := by ext <;> simp
  -- Hence `f ω` is `ω` or `star ω`.
  have hf : (f ω - ω) * (f ω - star ω) = 0 := by
    rw [hstar]
    linear_combination hfω - hω
  rcases mul_eq_zero.mp hf with h | h
  · exact .inl (algHom_ext (sub_eq_zero.mp h))
  · exact .inr (algHom_ext (by simpa [sub_eq_zero] using h))

end QuadraticAlgebra
