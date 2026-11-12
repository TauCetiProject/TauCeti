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
inverse, and that over a field `K` and for `r` not a square, the identity and conjugation are the
only `K`-algebra endomorphisms of the quadratic field `K(√r)`
(`QuadraticAlgebra.algHom_eq_id_or_eq_starAlgEquiv`).
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

section Field

variable {K : Type*} [Field K] {r : K}

/-- Over a field, an algebra endomorphism of the quadratic field `K(√r)`, for `r` not a square,
is the identity or conjugation: it sends `ω` to a square root of `r`, hence to `ω` or `-ω`. -/
theorem algHom_eq_id_or_eq_starAlgEquiv [Fact (¬IsSquare r)]
    (f : QuadraticAlgebra K r 0 →ₐ[K] QuadraticAlgebra K r 0) :
    f = AlgHom.id K _ ∨ f = (starAlgEquiv : QuadraticAlgebra K r 0 ≃ₐ[K] _).toAlgHom := by
  have hω : (ω : QuadraticAlgebra K r 0) * ω = algebraMap K _ r := by
    simp [omega_mul_omega_eq_algebraMap]
  have hf : f ω * f ω = ω * ω := by rw [← map_mul, hω, AlgHom.commutes]
  rcases mul_self_eq_mul_self_iff.mp hf with h | h
  · exact .inl (algHom_ext h)
  · refine .inr (algHom_ext ?_)
    rw [h]
    ext <;> simp

end Field

end QuadraticAlgebra
