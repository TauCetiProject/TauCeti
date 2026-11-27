/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.EpiMono

/-!
# Isomorphisms and split epi–mono composites

If `f ≫ g` and `g ≫ h` are isomorphisms, then `g` is an isomorphism: the second composite makes
`g` a split monomorphism and the first makes it a split epimorphism. This is the core of the
two-out-of-six property of isomorphisms, and is how a homotopy equivalence is shown to induce
isomorphisms on a homotopy-invariant functor.

A composite of an epimorphism and a monomorphism has an inner inverse exactly when both
factors split.
-/

public section

namespace CategoryTheory.IsIso

variable {C : Type*} [Category* C] {W X Y Z : C}

/-- If `f ≫ g` and `g ≫ h` are isomorphisms, then so is `g`. -/
theorem of_isIso_comp_of_isIso_comp {f : W ⟶ X} {g : X ⟶ Y} {h : Y ⟶ Z} (_ : IsIso (f ≫ g))
    (_ : IsIso (g ≫ h)) : IsIso g :=
  have : IsSplitMono g := .mk' ⟨h ≫ inv (g ≫ h), by rw [← Category.assoc, hom_inv_id]⟩
  have : IsSplitEpi g := .mk' ⟨inv (f ≫ g) ≫ f, by rw [Category.assoc, inv_hom_id]⟩
  isIso_of_mono_of_isSplitEpi g

end CategoryTheory.IsIso

open CategoryTheory

/-- The composite of an epimorphism and a monomorphism has an inner inverse exactly when both
factors split. -/
theorem Quiver.Hom.exists_comp_comp_eq_self_iff_isSplitEpi_and_isSplitMono
    {C : Type*} [Category* C] {X I Y : C} (p : X ⟶ I) (i : I ⟶ Y) [Epi p] [Mono i] :
    (∃ g : Y ⟶ X, (p ≫ i) ≫ g ≫ (p ≫ i) = p ≫ i) ↔ IsSplitEpi p ∧ IsSplitMono i := by
  constructor
  · rintro ⟨g, hg⟩
    have h : i ≫ g ≫ p = 𝟙 I := by
      apply (cancel_epi p).mp
      apply (cancel_mono i).mp
      simpa only [Category.assoc, Category.comp_id, Category.id_comp] using hg
    exact ⟨.mk' ⟨i ≫ g, by simpa only [Category.assoc] using h⟩, .mk' ⟨g ≫ p, h⟩⟩
  · rintro ⟨hp, hi⟩
    exact ⟨retraction i ≫ section_ p, by simp⟩
