/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Complex conjugation generates the real Galois group

Mathlib classifies real algebra homomorphisms of `ℂ` as the identity or conjugation. Here that
classification is expressed as the generator condition used by cyclic group cohomology. The
quadratic-extension instance makes the Galois structure of `ℂ/ℝ` available to that API.
-/

public section

namespace TauCeti

/-- The complex numbers form a quadratic extension of the reals. -/
instance instIsQuadraticExtensionRealComplex : Algebra.IsQuadraticExtension ℝ ℂ :=
  ⟨Complex.finrank_real_complex⟩

/-- Every real algebra automorphism of `ℂ` is a power of complex conjugation. -/
theorem mem_zpowers_conjAe (σ : ℂ ≃ₐ[ℝ] ℂ) : σ ∈ Subgroup.zpowers Complex.conjAe := by
  rcases Complex.real_algHom_eq_id_or_conj σ.toAlgHom with h | h
  · have hσ : σ = 1 := AlgEquiv.coe_toAlgHom_injective h
    rw [hσ]
    exact Subgroup.one_mem _
  · have hσ : σ = Complex.conjAe := AlgEquiv.coe_toAlgHom_injective h
    rw [hσ]
    exact Subgroup.mem_zpowers _

end TauCeti
