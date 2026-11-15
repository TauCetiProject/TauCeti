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
# Inner and outer automorphisms of an algebra

Conjugation by units defines a group homomorphism `Units.conjAlgEquiv R : Aˣ →* (A ≃ₐ[R] A)` into
the `R`-algebra automorphisms of any `R`-algebra `A`. Its range `TauCeti.innerAlgAut R A` of inner
algebra automorphisms is normal in `A ≃ₐ[R] A`, and the quotient `TauCeti.OuterAlgAut R A` is the
group of outer algebra automorphisms. In particular, an action whose multiplication law holds only
up to inner conjugation becomes an ordinary action in this quotient, as happens for the
endomorphism algebra in Clifford theory.

`Units.conjAlgEquiv` uses Mathlib's `MulSemiringAction.toAlgAut` for the conjugation action of
`ConjAct Aˣ`; the quotient uses the native `QuotientGroup` construction.

## Main definitions

* `Units.conjAlgEquiv`: conjugation of an `R`-algebra `A` by units as a group homomorphism
  `Aˣ →* (A ≃ₐ[R] A)`.
* `TauCeti.innerAlgAut`: the normal subgroup `(Units.conjAlgEquiv R).range` of inner algebra
  automorphisms of `A`.
* `TauCeti.OuterAlgAut`: the group of outer algebra automorphisms `(A ≃ₐ[R] A) ⧸ innerAlgAut R A`.

## References

* N. Bourbaki, *Algebra I, Chapters 1--3*, Chapter III, §1.
* C. W. Curtis and I. Reiner, *Methods of Representation Theory*, Vol. I, §11.
-/

public section

namespace Units

variable (R : Type*) {A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

/-- Conjugation of an `R`-algebra by units, `u ↦ (x ↦ u * x * u⁻¹)`, as a group homomorphism into
`A ≃ₐ[R] A`. -/
def conjAlgEquiv : Aˣ →* (A ≃ₐ[R] A) :=
  (MulSemiringAction.toAlgAut (ConjAct Aˣ) R A).comp ConjAct.toConjAct.toMonoidHom

/-- Applying `Units.conjAlgEquiv` conjugates by `u`. -/
@[simp]
theorem conjAlgEquiv_apply (u : Aˣ) (x : A) :
    Units.conjAlgEquiv R u x = (u : A) * x * (↑u⁻¹ : A) := by
  simp [conjAlgEquiv, ConjAct.units_smul_def]

end Units

namespace TauCeti

variable (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]

/-- The subgroup of algebra automorphisms given by conjugation by units. -/
def innerAlgAut : Subgroup (A ≃ₐ[R] A) :=
  (Units.conjAlgEquiv R).range

/-- Conjugation by a unit is an inner algebra automorphism. -/
@[simp]
theorem conjAlgEquiv_mem_innerAlgAut {A : Type*} [Semiring A] [Algebra R A] (u : Aˣ) :
    Units.conjAlgEquiv R u ∈ innerAlgAut R A :=
  ⟨u, rfl⟩

/-- An algebra automorphism is inner exactly when a unit implements it on every element. -/
theorem mem_innerAlgAut_iff (φ : A ≃ₐ[R] A) :
    φ ∈ innerAlgAut R A ↔
      ∃ u : Aˣ, ∀ x : A, φ x = (u : A) * x * (↑u⁻¹ : A) := by
  simp [innerAlgAut, AlgEquiv.ext_iff, eq_comm]

/-- Conjugating an inner algebra automorphism by an algebra automorphism is inner. -/
instance innerAlgAut_normal : (innerAlgAut R A).Normal where
  conj_mem φ hφ ψ := by
    obtain ⟨u, hu⟩ := (mem_innerAlgAut_iff R A φ).mp hφ
    refine (mem_innerAlgAut_iff R A _).mpr ⟨Units.map ψ.toMonoidHom u, fun x ↦ ?_⟩
    simp [AlgEquiv.mul_apply, hu]

/-- The group of algebra automorphisms modulo conjugations by units. -/
abbrev OuterAlgAut := (A ≃ₐ[R] A) ⧸ innerAlgAut R A

end TauCeti
