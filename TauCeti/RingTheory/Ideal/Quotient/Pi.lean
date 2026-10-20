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

For families of two-sided ideals `I j ≤ J j` of an `R₁`-algebra `A`, the quotient maps
`A ⧸ I j → A ⧸ J j` assemble into an `R₁`-algebra map `∏ j, A ⧸ I j → ∏ j, A ⧸ J j`, which is
surjective. This is the product version of Mathlib's `Ideal.Quotient.factorₐ`.

## Main declarations

* `TauCeti.Ideal.Quotient.piFactorₐ`: the componentwise quotient map.
* `TauCeti.Ideal.Quotient.piFactorₐ_surjective`: it is surjective.
-/

public section

namespace TauCeti

namespace Ideal.Quotient

variable (R₁ : Type*) {A : Type*} [CommSemiring R₁] [Ring A] [Algebra R₁ A] {ι : Type*}
  {I J : ι → Ideal A} [∀ j, (I j).IsTwoSided] [∀ j, (J j).IsTwoSided]

/-- The componentwise quotient map `∏ j, A ⧸ I j → ∏ j, A ⧸ J j` for ideals `I j ≤ J j`. -/
@[expose]
def piFactorₐ (hle : ∀ j, I j ≤ J j) : ((j : ι) → A ⧸ I j) →ₐ[R₁] ((j : ι) → A ⧸ J j) :=
  AlgHom.pi fun j ↦ (Ideal.Quotient.factorₐ R₁ (hle j)).comp (Pi.evalAlgHom R₁ _ j)

/-- Each component of `piFactorₐ` is the quotient map `A ⧸ I j → A ⧸ J j`. -/
@[simp]
theorem piFactorₐ_apply (hle : ∀ j, I j ≤ J j) (x : (j : ι) → A ⧸ I j) (j : ι) :
    piFactorₐ R₁ hle x j = Ideal.Quotient.factor (hle j) (x j) :=
  rfl

/-- The componentwise quotient map is surjective. -/
theorem piFactorₐ_surjective (hle : ∀ j, I j ≤ J j) :
    Function.Surjective (piFactorₐ R₁ hle) := fun y ↦
  ⟨fun j ↦ (Ideal.Quotient.factor_surjective (hle j) (y j)).choose,
    funext fun j ↦ (Ideal.Quotient.factor_surjective (hle j) (y j)).choose_spec⟩

end Ideal.Quotient

end TauCeti
