/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Ring.Action.ConjAct
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Outer automorphisms of an algebra

Conjugation by units gives a normal subgroup of the algebra automorphism group.
The quotient is the group of outer algebra automorphisms. In particular, an action
whose multiplication law holds only up to inner conjugation becomes an ordinary
action in this quotient, as happens for the endomorphism algebra in Clifford theory.

The inner subgroup uses Mathlib's `MulSemiringAction.toAlgAut` for the conjugation
action of `ConjAct Aˣ`; the quotient uses the native `QuotientGroup` construction.
-/

public section

namespace TauCeti

variable (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]

/-- The subgroup of algebra automorphisms given by conjugation by units. -/
def innerAlgAut : Subgroup (A ≃ₐ[R] A) :=
  ((MulSemiringAction.toAlgAut (ConjAct Aˣ) R A).comp
    ConjAct.toConjAct.toMonoidHom).range

/-- An algebra automorphism is inner exactly when a unit implements it on every element. -/
theorem mem_innerAlgAut_iff (φ : A ≃ₐ[R] A) :
    φ ∈ innerAlgAut R A ↔
      ∃ u : Aˣ, ∀ x : A, φ x = (u : A) * x * (↑u⁻¹ : A) := by
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨u, fun x ↦ by simp [ConjAct.units_smul_def]⟩
  · rintro ⟨u, hu⟩
    refine ⟨u, AlgEquiv.ext fun x ↦ ?_⟩
    simpa [ConjAct.units_smul_def] using (hu x).symm

/-- Conjugating an inner algebra automorphism by an algebra automorphism is inner. -/
instance innerAlgAut_normal : (innerAlgAut R A).Normal where
  conj_mem φ hφ ψ := by
    obtain ⟨u, hu⟩ := (mem_innerAlgAut_iff R A φ).mp hφ
    refine (mem_innerAlgAut_iff R A _).mpr ⟨Units.map ψ.toMonoidHom u, fun x ↦ ?_⟩
    simp [AlgEquiv.mul_apply, hu]

/-- The group of algebra automorphisms modulo conjugations by units. -/
abbrev OuterAlgAut := (A ≃ₐ[R] A) ⧸ innerAlgAut R A

end TauCeti
