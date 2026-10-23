/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Preadditive.Schur
public import Mathlib.CategoryTheory.Simple

/-!
# Finite semisimple categories

An abelian category is finite semisimple when every object is isomorphic to a finite biproduct of
simple objects. This file introduces that property and proves that it is invariant under
equivalence of categories.

The decomposition condition is independent of a choice of coefficient field. Linearity and
finite-dimensionality of morphism spaces are separate hypotheses when they are needed.

## Main results

* `TauCeti.IsFiniteSemisimpleCategory`: every object is a finite biproduct of simple objects.
* `TauCeti.IsFiniteSemisimpleCategory.of_equivalence`: transport finite semisimplicity across an
  equivalence.
* `TauCeti.isSplitMono_of_nonzero_from_simple`: a nonzero morphism out of a simple object is a
  split monomorphism.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v v' u u'

/-- An abelian category is finite semisimple if every object is isomorphic to a finite biproduct
of simple objects. -/
class IsFiniteSemisimpleCategory (C : Type u) [Category.{v} C] [Abelian C] : Prop where
  /-- Every object is isomorphic to a finite biproduct of simple objects. -/
  exists_biproduct_simples : ∀ X : C, ∃ (ι : Type) (_ : Fintype ι) (f : ι → C)
    (_ : ∀ i, Simple (f i)) (_ : HasBiproduct f), Nonempty (X ≅ ⨁ f)

namespace IsFiniteSemisimpleCategory

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]

/-- Finite semisimplicity is preserved by an equivalence of abelian categories. -/
theorem of_equivalence (e : C ≌ D) [IsFiniteSemisimpleCategory C] :
    IsFiniteSemisimpleCategory D where
  exists_biproduct_simples X := by
    obtain ⟨ι, hι, f, hf, hbf, ⟨i⟩⟩ :=
      exists_biproduct_simples (e.inverse.obj X)
    let _ := hι
    let _ : ∀ j, Simple (f j) := hf
    let _ := hbf
    let _ : HasFiniteBiproducts D := Abelian.hasFiniteBiproducts
    refine ⟨ι, inferInstance, fun j ↦ e.functor.obj (f j), fun j ↦ ?_, inferInstance, ?_⟩
    · exact CategoryTheory.simple_obj e.functor (f j)
    · have := preservesBiproduct_of_preservesProduct e.functor (f := f)
      exact ⟨(e.counitIso.app X).symm ≪≫ e.functor.mapIso i ≪≫ e.functor.mapBiproduct f⟩

/-- Equivalent abelian categories are finite semisimple simultaneously. -/
theorem iff_of_equivalence (e : C ≌ D) :
    IsFiniteSemisimpleCategory C ↔ IsFiniteSemisimpleCategory D := by
  constructor
  · intro h
    let _ := h
    exact of_equivalence e
  · intro h
    let _ := h
    exact of_equivalence e.symm

end IsFiniteSemisimpleCategory

/-- In a finite semisimple category, a nonzero morphism out of a simple object is a split
monomorphism. -/
theorem isSplitMono_of_nonzero_from_simple {C : Type u} [Category.{v} C] [Abelian C]
    [IsFiniteSemisimpleCategory C] {S Z : C} [Simple S] {f : S ⟶ Z} (hf : f ≠ 0) :
    IsSplitMono f := by
  obtain ⟨ι, hι, g, hg, hbg, ⟨e⟩⟩ := IsFiniteSemisimpleCategory.exists_biproduct_simples Z
  -- Some component of `f` in a decomposition of `Z` into simple objects is nonzero, hence an
  -- isomorphism by Schur's lemma.
  obtain ⟨i, hi⟩ : ∃ i, f ≫ e.hom ≫ biproduct.π g i ≠ 0 := by
    by_contra! h
    exact hf <| (cancel_mono e.hom).1 <| biproduct.hom_ext _ _ fun i ↦ by simpa using h i
  have := isIso_of_hom_simple hi
  exact IsSplitMono.mk' ⟨e.hom ≫ biproduct.π g i ≫ inv (f ≫ e.hom ≫ biproduct.π g i), by
    simpa only [Category.assoc] using IsIso.hom_inv_id (f ≫ e.hom ≫ biproduct.π g i)⟩

end TauCeti
