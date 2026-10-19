/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
public import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Trailing coefficients under injective coefficient maps

An injective coefficient map preserves the support of a polynomial, hence its trailing degree
and trailing coefficient. These identities allow projection data involving the lowest nonzero
coefficient to be transported without assuming that the constant coefficient is nonzero.
-/

public section

namespace TauCeti

variable {R S : Type*} [Semiring R] [Semiring S] {φ : R →+* S} {p : Polynomial R}

/-- An injective coefficient map preserves the trailing degree, including for zero. -/
@[simp]
theorem trailingDegree_map_eq_of_injective (hφ : Function.Injective φ) :
    (p.map φ).trailingDegree = p.trailingDegree := by
  exact congrArg (fun s : Finset ℕ ↦ s.min) (Polynomial.support_map_of_injective p hφ)

/-- An injective coefficient map preserves the natural trailing degree, including for zero. -/
@[simp]
theorem natTrailingDegree_map_eq_of_injective (hφ : Function.Injective φ) :
    (p.map φ).natTrailingDegree = p.natTrailingDegree := by
  rw [Polynomial.natTrailingDegree, trailingDegree_map_eq_of_injective hφ]
  rfl

/-- The trailing coefficient commutes with an injective coefficient map. -/
@[simp]
theorem trailingCoeff_map_of_injective (hφ : Function.Injective φ) :
    (p.map φ).trailingCoeff = φ p.trailingCoeff := by
  rw [Polynomial.trailingCoeff, natTrailingDegree_map_eq_of_injective hφ, Polynomial.coeff_map]
  rfl

end TauCeti
