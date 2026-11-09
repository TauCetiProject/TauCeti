/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.Coprime.Basic

/-!
# Polynomials in intertwined endomorphisms

A (semi)linear map `f` intertwining two endomorphisms `g` and `g₂` intertwines every polynomial
in them: polynomial evaluation at `g₂` after `f` agrees with `f` after evaluation at `g`, with the
coefficients transported along the ring homomorphism of `f`. This extends Mathlib's
`Module.End.commute_pow_left_of_commute` from powers to polynomials, and generalizes
`Polynomial.aeval_comp_eq_comp_aeval` from linear to semilinear maps.

When `g` and `g₂` are annihilated by coprime polynomials, a linear map intertwining them is zero
(`Module.End.eq_zero_of_comp_eq_of_isCoprime`), so the Sylvester operator `f ↦ g₂ ∘ f - f ∘ g`
is injective. On finite-dimensional vector spaces such polynomials exist exactly when `g` and `g₂`
have no common eigenvalue in an algebraic closure.
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

/-- **Intertwiners of coprime endomorphisms vanish.** If an endomorphism `g` of `M` is annihilated
by `q` and an endomorphism `g₂` of `M₂` is annihilated by `p`, with `p` and `q` coprime, then the
only linear map `f : M → M₂` with `g₂ ∘ f = f ∘ g` is zero. -/
theorem eq_zero_of_comp_eq_of_isCoprime [Module R M₂] {f : M →ₗ[R] M₂} {g : End R M}
    {g₂ : End R M₂} (h : g₂ ∘ₗ f = f ∘ₗ g) {p q : R[X]} (hpq : IsCoprime p q)
    (hp : aeval g₂ p = 0) (hq : aeval g q = 0) : f = 0 := by
  obtain ⟨a, b, hab⟩ := hpq
  have hqf : aeval g₂ q ∘ₗ f = 0 := by
    simpa [hq] using aeval_map_comp_of_comp_eq (σ := RingHom.id R) h q
  have hb : aeval g₂ b * aeval g₂ q = 1 := by
    simpa [hp] using congrArg (aeval g₂) hab
  rw [← LinearMap.id_comp f, ← one_eq_id, ← hb, mul_eq_comp, LinearMap.comp_assoc, hqf,
    LinearMap.comp_zero]

end Module.End
