/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.TraceFunctional.Radical
public import Mathlib.Algebra.Star.Module
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic

/-!
# Sesquilinear trace forms

A linear functional on a star algebra defines the sesquilinear form
`(x, y) ↦ τ (star x * y)`, conjugate-linear in the first variable. If the functional preserves
star, this form is Hermitian. If it is also tracial, its multiplication-pairing radical is
star-stable and equals the kernel of the sesquilinear form. No positivity is assumed: these
facts apply before deciding whether a trace gives a Hilbert space after quotient and completion.

## References

* D. Penneys, *Unitary Quantum Symmetries Lite*, Chapter 4, for sesquilinear trace forms and
  trace radicals of Temperley–Lieb algebras.
-/

public section

namespace LinearMap

section Semiring

variable {R A : Type*} [CommSemiring R] [StarRing R] [Semiring A] [StarRing A]
  [Algebra R A] [StarModule R A]

/-- The sesquilinear form of a linear functional on a star algebra, conjugate-linear in the
first argument. Hermitian symmetry requires that the functional preserve star. -/
def traceSesqForm (τ : A →ₗ[R] R) : A →ₗ⋆[R] A →ₗ[R] R :=
  ((LinearMap.mul R A).compr₂ τ).comp (starLinearEquiv R).toLinearMap

/-- Evaluation of the sesquilinear trace form. -/
@[simp]
theorem traceSesqForm_apply (τ : A →ₗ[R] R) (x y : A) :
    τ.traceSesqForm x y = τ (star x * y) := (rfl)

/-- A star-preserving functional has a Hermitian sesquilinear trace form. Traciality is not
needed for this symmetry. -/
theorem traceSesqForm_isSymm (τ : A →ₗ[R] R) (hstar : ∀ x, τ (star x) = star (τ x)) :
    τ.traceSesqForm.IsSymm := by
  constructor
  intro x y
  simp only [traceSesqForm_apply, starRingEnd_apply, ← hstar, star_mul, star_star]

end Semiring

variable {R A : Type*} [CommRing R] [StarRing R] [Ring A] [StarRing A] [Algebra R A]

/-- The multiplication-pairing radical of a star-preserving trace is stable under star. -/
theorem star_mem_traceRadical_iff (τ : A →ₗ[R] R)
    (hτ : ∀ x y, τ (x * y) = τ (y * x)) (hstar : ∀ x, τ (star x) = star (τ x)) {x : A} :
    star x ∈ τ.traceRadical hτ ↔ x ∈ τ.traceRadical hτ := by
  have hmem {a : A} (ha : a ∈ τ.traceRadical hτ) : star a ∈ τ.traceRadical hτ := by
    rw [mem_traceRadical] at ha ⊢
    intro y
    rw [hτ, ← star_star y, ← star_mul, hstar, ha, star_zero]
  exact ⟨fun hx ↦ by simpa only [star_star] using hmem hx, hmem⟩

/-- For a star-preserving trace, the left kernel of its sesquilinear form is the underlying
coefficient submodule of its multiplication-pairing radical. -/
theorem ker_traceSesqForm [StarModule R A] (τ : A →ₗ[R] R)
    (hτ : ∀ x y, τ (x * y) = τ (y * x)) (hstar : ∀ x, τ (star x) = star (τ x)) :
    ker τ.traceSesqForm = (τ.traceRadical hτ).restrictScalars R := by
  ext x
  rw [mem_ker, LinearMap.ext_iff, Submodule.restrictScalars_mem,
    ← τ.star_mem_traceRadical_iff hτ hstar, mem_traceRadical]
  simp [traceSesqForm_apply]

end LinearMap
