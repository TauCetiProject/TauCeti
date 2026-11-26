/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Commutator
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Unipotent automorphisms of a biproduct are stably commutators

In a preadditive category with binary biproducts, the unipotent automorphism
`Biprod.unipotentLower r` of `X₁ ⊞ X₂`, `(x₁, x₂) ↦ (x₁ + r x₂, x₂)`, need not be a commutator of
automorphisms of `X₁ ⊞ X₂`. After adding a second copy of `X₂` it is one: on
`(X₁ ⊞ X₂) ⊞ X₂` it is the commutator of the automorphism adding `r` of the third summand to the
first and of the automorphism adding the second summand to the third. In matrix language this is
the elementary commutator identity `e₁₂(r) = ⁅e₁₃(r), e₃₂(1)⁆`, the categorical form of the step
of Whitehead's lemma used to show that unipotent automorphisms die in `K`-groups presented by
automorphisms.

## Main results

* `CategoryTheory.Biprod.unipotentLower_biprod_eq_commutatorElement`: the automorphism
  `Biprod.unipotentLower r ⊞ 𝟙` of `(X₁ ⊞ X₂) ⊞ X₂` is a commutator in `Aut ((X₁ ⊞ X₂) ⊞ X₂)`.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter III,
  Lemma 1.3.2 (the commutator identity for elementary matrices) and Whitehead's Lemma 1.3.3.
-/

public section

namespace CategoryTheory.Biprod

open CategoryTheory.Limits
open scoped commutatorElement

variable {C : Type*} [Category* C] [Preadditive C] [HasBinaryBiproducts C]

/-- After adding a second copy of `X₂`, the unipotent automorphism
`(x₁, x₂) ↦ (x₁ + r x₂, x₂)` of `X₁ ⊞ X₂` becomes the commutator of the automorphisms
`(w, x₃) ↦ (w + inl (r x₃), x₃)` and `(w, x₃) ↦ (w, x₃ + snd w)` of `(X₁ ⊞ X₂) ⊞ X₂`: the
identity `e₁₂(r) = ⁅e₁₃(r), e₃₂(1)⁆` for elementary matrices. -/
theorem unipotentLower_biprod_eq_commutatorElement {X₁ X₂ : C} (r : X₂ ⟶ X₁) :
    Aut.of (biprod.mapIso (Biprod.unipotentLower r) (Iso.refl X₂)) =
      ⁅Aut.of (Biprod.unipotentLower (r ≫ biprod.inl : X₂ ⟶ X₁ ⊞ X₂)),
        Aut.of (Biprod.unipotentUpper (biprod.snd : X₁ ⊞ X₂ ⟶ X₂))⁆ := by
  ext : 2
  simp only [commutatorElement_def, Aut.mul_asIso, Aut.inv_asIso, Iso.trans_hom, Iso.symm_hom,
    biprod.mapIso_hom, Iso.refl_hom, Biprod.unipotentUpper_hom, Biprod.unipotentUpper_inv,
    Biprod.unipotentLower_hom, Biprod.unipotentLower_inv]
  ext <;> simp [Biprod.ofComponents]

end CategoryTheory.Biprod
