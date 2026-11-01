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
public import TauCeti.CategoryTheory.Abelian.Injective.Basic
public import TauCeti.CategoryTheory.Limits.Shapes.Biproduct
public import TauCeti.CategoryTheory.Preadditive.Injective.Basic

/-!
# Finite semisimple categories

An abelian category is finite semisimple when every object is isomorphic to a finite biproduct of
simple objects. This file introduces that property and proves that it is invariant under
equivalence of categories. In a finite semisimple category every object is injective, so every
monomorphism splits: a monomorphism out of a simple object splits by Schur's lemma, and a finite
biproduct of injective objects is injective.

The decomposition condition is independent of a choice of coefficient field. Linearity and
finite-dimensionality of morphism spaces are separate hypotheses when they are needed.

## Main results

* `TauCeti.IsFiniteSemisimpleCategory`: every object is a finite biproduct of simple objects.
* `TauCeti.IsFiniteSemisimpleCategory.of_equivalence`: transport finite semisimplicity across an
  equivalence.
* `TauCeti.IsFiniteSemisimpleCategory.exists_biproduct_simples_of_isZero`,
  `TauCeti.IsFiniteSemisimpleCategory.exists_biproduct_simples_of_simple` and
  `TauCeti.IsFiniteSemisimpleCategory.exists_biproduct_simples_biprod`: zero objects and simple
  objects are finite biproducts of simple objects, and such decompositions combine along `⊞`.
* `TauCeti.isSplitMono_of_nonzero_from_simple`: a nonzero morphism out of a simple object is a
  split monomorphism.
* `TauCeti.IsFiniteSemisimpleCategory.injective`: every object of a finite semisimple category is
  injective.
* `TauCeti.IsFiniteSemisimpleCategory.splitMonoCategory`: every monomorphism of a finite
  semisimple category splits.
* `TauCeti.natTrans_ext_of_simple`: a natural transformation out of an additive functor is
  determined by its components at the simple objects.
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

/-- A zero object is the biproduct of the empty family of simple objects. -/
theorem exists_biproduct_simples_of_isZero {X : C} (hX : IsZero X) :
    ∃ (ι : Type) (_ : Fintype ι) (f : ι → C) (_ : ∀ i, Simple (f i)) (_ : HasBiproduct f),
      Nonempty (X ≅ ⨁ f) := by
  let _ : HasFiniteBiproducts C := Abelian.hasFiniteBiproducts
  refine ⟨Empty, inferInstance, Empty.elim, fun i ↦ i.elim, inferInstance, ⟨hX.iso ?_⟩⟩
  exact (IsZero.iff_id_eq_zero _).2 (biproduct.hom_ext _ _ fun i ↦ i.elim)

/-- A simple object is the biproduct of the family consisting of itself. -/
theorem exists_biproduct_simples_of_simple (X : C) [Simple X] :
    ∃ (ι : Type) (_ : Fintype ι) (f : ι → C) (_ : ∀ i, Simple (f i)) (_ : HasBiproduct f),
      Nonempty (X ≅ ⨁ f) := by
  let _ : HasFiniteBiproducts C := Abelian.hasFiniteBiproducts
  exact ⟨Unit, inferInstance, fun _ ↦ X, fun _ ↦ inferInstance, inferInstance,
    ⟨(biproductUniqueIso fun _ : Unit ↦ X).symm⟩⟩

/-- Decompositions of `X` and `Y` into finite biproducts of simple objects combine to one of
`X ⊞ Y`. -/
theorem exists_biproduct_simples_biprod {X Y : C}
    (hX : ∃ (ι : Type) (_ : Fintype ι) (f : ι → C) (_ : ∀ i, Simple (f i)) (_ : HasBiproduct f),
      Nonempty (X ≅ ⨁ f))
    (hY : ∃ (ι : Type) (_ : Fintype ι) (f : ι → C) (_ : ∀ i, Simple (f i)) (_ : HasBiproduct f),
      Nonempty (Y ≅ ⨁ f)) :
    ∃ (ι : Type) (_ : Fintype ι) (f : ι → C) (_ : ∀ i, Simple (f i)) (_ : HasBiproduct f),
      Nonempty (X ⊞ Y ≅ ⨁ f) := by
  obtain ⟨ι, hι, f, hf, hbf, ⟨e⟩⟩ := hX
  obtain ⟨κ, hκ, g, hg, hbg, ⟨d⟩⟩ := hY
  let _ : HasFiniteBiproducts C := Abelian.hasFiniteBiproducts
  refine ⟨ι ⊕ κ, inferInstance, Sum.elim f g, fun | .inl i => hf i | .inr j => hg j,
    inferInstance, ⟨biprod.mapIso e d ≪≫ (biproductSumIso f g).symm⟩⟩

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

namespace IsFiniteSemisimpleCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [IsFiniteSemisimpleCategory C]

/-- Every object of a finite semisimple category is injective. -/
instance injective (X : C) : Injective X := by
  obtain ⟨ι, hι, f, hf, hbf, ⟨e⟩⟩ := exists_biproduct_simples X
  -- A monomorphism out of a simple object is nonzero, hence split.
  have (i : ι) : Injective (f i) := by
    have := hf i
    exact (injective_iff_forall_isSplitMono _).2 fun Y g _ ↦
      isSplitMono_of_nonzero_from_simple fun hg ↦
        Simple.not_isZero (f i) (IsZero.of_mono_eq_zero g hg)
  exact Injective.of_iso e.symm inferInstance

/-- Every monomorphism of a finite semisimple category splits. -/
instance splitMonoCategory : SplitMonoCategory C :=
  ⟨fun f _ ↦ (injective_iff_forall_isSplitMono _).1 inferInstance f⟩

end IsFiniteSemisimpleCategory

/-- In a finite semisimple category, a natural transformation out of an additive functor is
determined by its components at the simple objects. -/
theorem natTrans_ext_of_simple {C : Type u} [Category.{v} C] [Abelian C]
    [IsFiniteSemisimpleCategory C] {D : Type u'} [Category.{v'} D] [Preadditive D]
    {F G : C ⥤ D} [F.Additive] {α β : F ⟶ G} (h : ∀ (X : C) [Simple X], α.app X = β.app X) :
    α = β := by
  ext X
  obtain ⟨ι, hι, f, hf, hbf, ⟨e⟩⟩ := IsFiniteSemisimpleCategory.exists_biproduct_simples X
  -- The images of the inclusions of the summands of `⨁ f` are jointly epimorphic.
  have key : α.app (⨁ f) = β.app (⨁ f) := by
    rw [← Category.id_comp (α.app _), ← Category.id_comp (β.app _), ← F.map_id,
      ← biproduct.total, F.map_sum, Preadditive.sum_comp, Preadditive.sum_comp]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [F.map_comp, Category.assoc, Category.assoc, α.naturality, β.naturality, h]
  rw [← cancel_mono (G.map e.hom), ← α.naturality, ← β.naturality, key]

end TauCeti
