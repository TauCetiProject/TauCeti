/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.Basic

/-!
# Quadratic expressions in modules

Congruence and linear-map evaluation for a three-term quadratic expression.
-/

public section

namespace TauCeti

/-- Equal coefficients give equal quadratic expressions. -/
theorem quadraticPolynomial_congr
    {A M : Type*} [Semiring A] [AddCommMonoid M] [Module A M]
    {x₀ x₁ x₂ y₀ y₁ y₂ : M} (t : A)
    (h₀ : x₀ = y₀) (h₁ : x₁ = y₁) (h₂ : x₂ = y₂) :
    x₀ + t • x₁ + t ^ 2 • x₂ = y₀ + t • y₁ + t ^ 2 • y₂ := by
  subst y₀
  subst y₁
  subst y₂
  rfl

end TauCeti

namespace LinearMap

/-- A linear map commutes with evaluation of a quadratic expression. -/
theorem map_quadraticPolynomial
    {A M N : Type*} [Semiring A] [AddCommMonoid M] [Module A M]
    [AddCommMonoid N] [Module A N] (f : M →ₗ[A] N) (t : A) (x₀ x₁ x₂ : M) :
    f (x₀ + t • x₁ + t ^ 2 • x₂) =
      f x₀ + t • f x₁ + t ^ 2 • f x₂ := by
  rw [map_add, map_add, map_smul, map_smul]

end LinearMap
