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
`QuadraticAlgebra.starAlgEquiv`. This file records that it sends `ω` to `b - ω`, that the bundled
automorphism is its own inverse, and that two `R`-algebra maps from `QuadraticAlgebra R a b` into a
commutative `R`-algebra without zero divisors agree up to conjugation.

## Main results

* `QuadraticAlgebra.star_omega`: `star ω = b - ω`.
* `QuadraticAlgebra.algHom_eq_or_eq_comp_starAlgEquiv_of_noZeroDivisors`: two `R`-algebra maps
  from `QuadraticAlgebra R a b` into a commutative `R`-algebra without zero divisors agree, or
  agree after precomposing one of them with conjugation.
* `QuadraticAlgebra.algHom_eq_id_or_eq_starAlgEquiv`: when `QuadraticAlgebra R a b` has no zero
  divisors (for instance the quadratic field `K(√r)` over a field `K`, for `r` not a square), the
  identity and conjugation are its only `R`-algebra endomorphisms.
-/

public section

namespace QuadraticAlgebra

variable {R : Type*} [CommRing R] {a b : R}

/-- Conjugation sends the generator `ω` to the conjugate root `b - ω` of `X ^ 2 - b X - a`, which
may coincide with `ω`. -/
@[simp] theorem star_omega : star (ω : QuadraticAlgebra R a b) = algebraMap R _ b - ω := by
  rw [star_eq, trace_omega]

/-- The quadratic involution as an algebra automorphism is its own inverse. -/
@[simp] theorem starAlgEquiv_symm :
    (starAlgEquiv : QuadraticAlgebra R a b ≃ₐ[R] _).symm = starAlgEquiv :=
  AlgEquiv.ext fun _ ↦ by simp

/-- Two `R`-algebra maps from `QuadraticAlgebra R a b` into a commutative `R`-algebra without
zero divisors are equal, or equal after precomposing one of them with conjugation. -/
theorem algHom_eq_or_eq_comp_starAlgEquiv_of_noZeroDivisors {B : Type*} [CommRing B]
    [Algebra R B] [NoZeroDivisors B] (f g : QuadraticAlgebra R a b →ₐ[R] B) :
    f = g ∨ f = g.comp (starAlgEquiv : QuadraticAlgebra R a b ≃ₐ[R] _).toAlgHom := by
  -- `f ω` and `g ω` are both roots of `X ^ 2 - b X - a`.
  have hf : f ω * f ω = algebraMap R B a + algebraMap R B b * f ω := by
    simpa [Algebra.smul_def] using (lift.symm f).property
  have hg : g ω * g ω = algebraMap R B a + algebraMap R B b * g ω := by
    simpa [Algebra.smul_def] using (lift.symm g).property
  have h : (f ω - g ω) * (f ω - g (star ω)) = 0 := by
    rw [star_omega, map_sub, AlgHom.commutes]
    linear_combination hf - hg
  rcases mul_eq_zero.mp h with h | h
  · exact .inl (algHom_ext (sub_eq_zero.mp h))
  · exact .inr (algHom_ext (by simpa using sub_eq_zero.mp h))

/-- If `QuadraticAlgebra R a b` has no zero divisors, an `R`-algebra endomorphism of it is the
identity or conjugation. -/
theorem algHom_eq_id_or_eq_starAlgEquiv [NoZeroDivisors (QuadraticAlgebra R a b)]
    (f : QuadraticAlgebra R a b →ₐ[R] QuadraticAlgebra R a b) :
    f = AlgHom.id R _ ∨ f = (starAlgEquiv : QuadraticAlgebra R a b ≃ₐ[R] _).toAlgHom := by
  simpa only [AlgHom.id_comp] using
    algHom_eq_or_eq_comp_starAlgEquiv_of_noZeroDivisors f (AlgHom.id R _)

end QuadraticAlgebra
