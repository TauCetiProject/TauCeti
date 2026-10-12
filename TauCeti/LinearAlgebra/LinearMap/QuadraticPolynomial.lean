/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.Defs

/-!
# Quadratic expressions and semilinear maps

Three-term expressions of the form `x₀ + t • x₁ + t ^ 2 • x₂` occur in root-exponential actions.
The lemmas here preserve these formulas under coefficientwise equality and semilinear maps,
allowing root-exponential expressions to be compared after changing modules or scalars.
-/

public section

namespace TauCeti

/-- Equal coefficients give equal quadratic expressions. -/
theorem quadraticPolynomial_congr
    {A M : Type*} [Pow A ℕ] [Add M] [SMul A M]
    {x₀ x₁ x₂ y₀ y₁ y₂ : M} (t : A)
    (h₀ : x₀ = y₀) (h₁ : x₁ = y₁) (h₂ : x₂ = y₂) :
    x₀ + t • x₁ + t ^ 2 • x₂ = y₀ + t • y₁ + t ^ 2 • y₂ := by
  rw [h₀, h₁, h₂]

end TauCeti

namespace LinearMap

/-- A semilinear map carries a quadratic expression to the corresponding expression with
the scalar mapped through its ring homomorphism. -/
theorem map_quadraticPolynomial
    {A B M N : Type*} [Semiring A] [Semiring B]
    [AddCommMonoid M] [Module A M] [AddCommMonoid N] [Module B N]
    {σ : A →+* B} (f : M →ₛₗ[σ] N) (t : A) (x₀ x₁ x₂ : M) :
    f (x₀ + t • x₁ + t ^ 2 • x₂) =
      f x₀ + σ t • f x₁ + (σ t) ^ 2 • f x₂ := by
  simp only [map_add, LinearMap.map_smulₛₗ, map_pow]

end LinearMap
