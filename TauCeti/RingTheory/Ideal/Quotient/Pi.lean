/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Componentwise quotient maps of products

For a family of `R₁`-algebras `A j` and two-sided ideals `I j ≤ J j` of `A j`, the quotient maps
`A j ⧸ I j → A j ⧸ J j` assemble into an `R₁`-algebra map `∏ j, A j ⧸ I j → ∏ j, A j ⧸ J j`,
which is surjective. This is the product version of Mathlib's `Ideal.Quotient.factorₐ`.

For ideals `I i` of a ring `A` and exponents `n i`, the factors of `∏ i, A ⧸ I i ^ n i` with
`n i = 0` are zero, so restricting to the factors with `n i ≠ 0` is a linear bijection.

## Main declarations

* `TauCeti.Ideal.Quotient.piFactorₐ`: the componentwise quotient map.
* `TauCeti.Ideal.Quotient.piFactorₐ_surjective`: it is surjective.
* `TauCeti.Ideal.Quotient.bijective_pi_restrict_pow`: dropping the factors `A ⧸ I ^ 0 = 0` from
  `∏ i, A ⧸ I i ^ n i` is a linear bijection.
-/

public section

namespace TauCeti

namespace Ideal.Quotient

section piFactorₐ

variable (R₁ : Type*) {ι : Type*} {A : ι → Type*} [CommSemiring R₁] [∀ j, Ring (A j)]
  [∀ j, Algebra R₁ (A j)] {I J : (j : ι) → Ideal (A j)} [∀ j, (I j).IsTwoSided]
  [∀ j, (J j).IsTwoSided]

/-- The componentwise quotient map `∏ j, A j ⧸ I j → ∏ j, A j ⧸ J j` for ideals `I j ≤ J j`. -/
def piFactorₐ (hle : ∀ j, I j ≤ J j) : ((j : ι) → A j ⧸ I j) →ₐ[R₁] ((j : ι) → A j ⧸ J j) :=
  AlgHom.pi fun j ↦ (Ideal.Quotient.factorₐ R₁ (hle j)).comp (Pi.evalAlgHom R₁ _ j)

/-- Each component of `piFactorₐ` is the quotient map `A j ⧸ I j → A j ⧸ J j`. -/
@[simp]
theorem piFactorₐ_apply (hle : ∀ j, I j ≤ J j) (x : (j : ι) → A j ⧸ I j) (j : ι) :
    piFactorₐ R₁ hle x j = Ideal.Quotient.factor (hle j) (x j) :=
  (rfl)

/-- The componentwise quotient map is surjective. -/
theorem piFactorₐ_surjective (hle : ∀ j, I j ≤ J j) :
    Function.Surjective (piFactorₐ R₁ hle) :=
  -- `piFactorₐ R₁ hle` is definitionally `Pi.map` of the factor maps, as in `piFactorₐ_apply`.
  Function.Surjective.piMap fun j ↦ Ideal.Quotient.factor_surjective (hle j)

end piFactorₐ

/-- Dropping the factors with exponent zero from `∏ᵢ A ⧸ Iᵢ ^ nᵢ` is bijective, as those factors
are `A ⧸ A = 0`. -/
theorem bijective_pi_restrict_pow {A ι : Type*} [Ring A] (I : ι → Ideal A) (n : ι → ℕ) :
    Function.Bijective (LinearMap.pi fun y : {i // n i ≠ 0} ↦ LinearMap.proj y.val :
      (∀ i, A ⧸ I i ^ n i) →ₗ[A] ∀ y : {i // n i ≠ 0}, A ⧸ I y ^ n y) := by
  classical
  refine ⟨fun x x' hxx' ↦ funext fun i ↦ ?_, fun y ↦ ?_⟩
  · by_cases hi : n i = 0
    · have : Subsingleton (A ⧸ I i ^ n i) := Ideal.Quotient.subsingleton_iff.mpr (by simp [hi])
      exact Subsingleton.elim _ _
    · exact congr_fun hxx' ⟨i, hi⟩
  · refine ⟨fun i ↦ if hi : n i = 0 then 0 else y ⟨i, hi⟩, funext fun i ↦ ?_⟩
    simp only [LinearMap.pi_apply, LinearMap.proj_apply, i.property, ↓reduceDIte]

end Ideal.Quotient

end TauCeti
