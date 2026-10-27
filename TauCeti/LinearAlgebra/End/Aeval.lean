/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Polynomials in intertwined endomorphisms

A (semi)linear map `f` intertwining two endomorphisms `g` and `g₂` intertwines every polynomial
in them: polynomial evaluation at `g₂` after `f` agrees with `f` after evaluation at `g`, with the
coefficients transported along the ring homomorphism of `f`. This extends Mathlib's
`Module.End.commute_pow_left_of_commute` from powers to polynomials.
-/

public section

open Polynomial

namespace Module.End

variable {R M M₂ : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M₂]

/-- A semilinear map intertwining two endomorphisms intertwines every polynomial in them, with
coefficients transported along the ring homomorphism. -/
theorem aeval_map_comp_of_comp_eq {R₂ : Type*} [CommSemiring R₂] [Module R₂ M₂] {σ : R →+* R₂}
    {f : M →ₛₗ[σ] M₂} {g : End R M} {g₂ : End R₂ M₂} (h : g₂.comp f = f.comp g) (p : R[X]) :
    (aeval g₂ (p.map σ)).comp f = f.comp (aeval g p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [Polynomial.map_add, LinearMap.add_comp, LinearMap.comp_add, hp, hq]
  | monomial n a =>
    ext x
    have hn := LinearMap.congr_fun (commute_pow_left_of_commute h n) x
    simp only [LinearMap.comp_apply] at hn
    simp [aeval_monomial, Algebra.algebraMap_eq_smul_one, hn]

/-- A linear map intertwining two endomorphisms intertwines every polynomial in them. -/
theorem aeval_comp_of_comp_eq [Module R M₂] {f : M →ₗ[R] M₂} {g : End R M} {g₂ : End R M₂}
    (h : g₂.comp f = f.comp g) (p : R[X]) : (aeval g₂ p).comp f = f.comp (aeval g p) := by
  simpa using aeval_map_comp_of_comp_eq h p

end Module.End
