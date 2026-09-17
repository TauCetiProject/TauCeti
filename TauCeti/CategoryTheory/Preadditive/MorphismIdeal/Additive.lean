/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.MorphismIdeal.Basic

/-!
# Additive structure of morphism-ideal quotients

Quotienting an additive category by a two-sided morphism ideal preserves zero objects and
finite biproducts. These instances allow the quotient to be used as an additive category, not
just as a category with additive hom groups. The quotient functor preserves these biproducts
by Mathlib's `Functor.preservesFiniteBiproductsOfAdditive`; its standard biproduct comparison
isomorphisms therefore apply without a separate choice of sums in the quotient.

An object becomes zero precisely when its identity belongs to the ideal. A morphism becomes
invertible precisely when it admits a two-sided inverse modulo the ideal. These criteria are
useful for stable categories, where zero objects and isomorphisms need not lift to zero objects
and isomorphisms in the original category.

The constructions reuse Mathlib's `Functor.hasZeroObject_of_additive`,
`Functor.hasFiniteProducts_of_additive_of_essSurj`, and biproduct preservation API.

## References

* M. Auslander, I. Reiten, S. Smalø, *Representation Theory of Artin Algebras*,
  Chapter IV, Section 1.
* D. Happel, *Triangulated Categories in the Representation Theory of Finite Dimensional
  Algebras*, Section I.2.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

namespace MorphismIdeal

variable {C : Type u} [Category.{v} C] [Preadditive C] (I : MorphismIdeal C)

/-- A quotient by a morphism ideal has a zero object whenever the original category does. -/
instance [HasZeroObject C] : HasZeroObject I.Quotient :=
  Functor.hasZeroObject_of_additive I.quotientFunctor

/-- Finite biproducts descend to the quotient by a morphism ideal. -/
noncomputable instance [HasFiniteBiproducts C] : HasFiniteBiproducts I.Quotient := by
  let := Functor.hasFiniteProducts_of_additive_of_essSurj I.quotientFunctor
  exact HasFiniteBiproducts.of_hasFiniteProducts

/-- Binary biproducts descend even without a zero object in the original category. -/
noncomputable instance [HasBinaryBiproducts C] : HasBinaryBiproducts I.Quotient where
  has_binary_biproduct X Y := by
    obtain ⟨X⟩ := X
    obtain ⟨Y⟩ := Y
    let := preservesBinaryBiproducts_of_preservesBiproducts I.quotientFunctor
    exact Functor.hasBinaryBiproduct_of_preserves I.quotientFunctor X Y

/-- An object becomes zero in the quotient exactly when its identity belongs to the ideal. -/
@[simp]
theorem isZero_quotientFunctor_obj_iff (X : C) :
    IsZero (I.quotientFunctor.obj X) ↔ 𝟙 X ∈ I.hom X X := by
  rw [IsZero.iff_id_eq_zero, ← I.quotientFunctor.map_id,
    I.quotientFunctor_map_eq_zero_iff]

/-- A morphism is invertible in the quotient exactly when it has a two-sided inverse modulo
the ideal. The lift of the inverse need not be invertible in the original category. -/
theorem isIso_quotientFunctor_map_iff {X Y : C} (f : X ⟶ Y) :
    IsIso (I.quotientFunctor.map f) ↔
      ∃ g : Y ⟶ X, f ≫ g - 𝟙 X ∈ I.hom X X ∧ g ≫ f - 𝟙 Y ∈ I.hom Y Y := by
  constructor
  · intro hf
    obtain ⟨g, hg⟩ := I.quotientFunctor.map_surjective (inv (I.quotientFunctor.map f))
    refine ⟨g, ?_, ?_⟩
    · rw [← I.quotientFunctor_map_eq_iff, I.quotientFunctor.map_comp, hg,
        I.quotientFunctor.map_id]
      exact IsIso.hom_inv_id _
    · rw [← I.quotientFunctor_map_eq_iff, I.quotientFunctor.map_comp, hg,
        I.quotientFunctor.map_id]
      exact IsIso.inv_hom_id _
  · rintro ⟨g, hfg, hgf⟩
    refine ⟨⟨I.quotientFunctor.map g, ?_, ?_⟩⟩
    · rw [← I.quotientFunctor.map_comp, ← I.quotientFunctor.map_id]
      exact I.quotientFunctor_map_eq_iff.mpr hfg
    · rw [← I.quotientFunctor.map_comp, ← I.quotientFunctor.map_id]
      exact I.quotientFunctor_map_eq_iff.mpr hgf

end MorphismIdeal

end TauCeti
