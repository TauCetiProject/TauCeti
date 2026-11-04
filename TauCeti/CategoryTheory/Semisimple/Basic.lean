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
* `TauCeti.isSplitMono_of_nonzero_from_simple` and `TauCeti.isSplitEpi_of_nonzero_to_simple`: a
  nonzero morphism out of (resp. into) a simple object is a split monomorphism (resp. split
  epimorphism).
* `TauCeti.exists_nonzero_from_simple_iff_exists_nonzero_to_simple`: a simple object maps
  nontrivially to an object exactly when the object maps nontrivially to it.
* `TauCeti.biproduct_ι_comp_inv_ne_zero`: the inclusion of a simple summand is nonzero.
* `TauCeti.exists_simple_hom_ne_zero`: a nonzero object receives a nonzero morphism from a simple
  object.
* `CategoryTheory.Functor.hom_ext_of_simple`: a morphism out of the image of an object under an
  additive functor is determined by its composites with the images of morphisms from simple
  objects.
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

/-- In a finite semisimple category, a nonzero morphism into a simple object is a split
epimorphism. -/
theorem isSplitEpi_of_nonzero_to_simple {C : Type u} [Category.{v} C] [Abelian C]
    [IsFiniteSemisimpleCategory C] {S Y : C} [Simple S] {g : Y ⟶ S} (hg : g ≠ 0) :
    IsSplitEpi g := by
  obtain ⟨ι, hι, a, ha, hba, ⟨e⟩⟩ := IsFiniteSemisimpleCategory.exists_biproduct_simples Y
  -- Some summand in a decomposition of `Y` into simple objects maps nontrivially to `S`, hence
  -- isomorphically by Schur's lemma.
  obtain ⟨i, hi⟩ : ∃ i, biproduct.ι a i ≫ e.inv ≫ g ≠ 0 := by
    by_contra! h
    exact hg <| (cancel_epi e.inv).1 <| biproduct.hom_ext' _ _ fun i ↦ by simpa using h i
  have := isIso_of_hom_simple hi
  exact IsSplitEpi.mk' ⟨inv (biproduct.ι a i ≫ e.inv ≫ g) ≫ biproduct.ι a i ≫ e.inv,
    by simp only [Category.assoc, IsIso.inv_hom_id]⟩

/-- In a finite semisimple category, a simple object maps nontrivially to an object exactly when
the object maps nontrivially to it. -/
theorem exists_nonzero_from_simple_iff_exists_nonzero_to_simple {C : Type u} [Category.{v} C]
    [Abelian C] [IsFiniteSemisimpleCategory C] {S Y : C} [Simple S] :
    (∃ f : S ⟶ Y, f ≠ 0) ↔ ∃ g : Y ⟶ S, g ≠ 0 := by
  constructor
  · rintro ⟨f, hf⟩
    have := isSplitMono_of_nonzero_from_simple hf
    exact ⟨retraction f, fun h ↦ CategoryTheory.id_ne_zero S (by rw [← IsSplitMono.id f, h,
      comp_zero])⟩
  · rintro ⟨g, hg⟩
    have := isSplitEpi_of_nonzero_to_simple hg
    exact ⟨section_ g, fun h ↦ CategoryTheory.id_ne_zero S (by rw [← IsSplitEpi.id g, h,
      zero_comp])⟩

/-- The inclusion of a simple summand into an object decomposed as a biproduct is nonzero. -/
theorem biproduct_ι_comp_inv_ne_zero {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    {ι : Type*} {a : ι → C} [HasBiproduct a] {Y : C} (e : Y ≅ ⨁ a) (i : ι) [Simple (a i)] :
    biproduct.ι a i ≫ e.inv ≠ 0 := fun h ↦
  CategoryTheory.id_ne_zero (a i) (by simpa using h =≫ (e.hom ≫ biproduct.π a i))

/-- In a finite semisimple category, a nonzero object receives a nonzero morphism from a simple
object: the inclusion of a summand of a decomposition into simple objects. -/
theorem exists_simple_hom_ne_zero {C : Type u} [Category.{v} C] [Abelian C]
    [IsFiniteSemisimpleCategory C] {Y : C} (hY : ¬IsZero Y) :
    ∃ (S : C) (_ : Simple S) (f : S ⟶ Y), f ≠ 0 := by
  obtain ⟨ι, hι, a, ha, hba, ⟨e⟩⟩ := IsFiniteSemisimpleCategory.exists_biproduct_simples Y
  obtain ⟨i⟩ : Nonempty ι := by
    by_contra h
    have : IsEmpty ι := not_nonempty_iff.mp h
    exact hY (((IsZero.iff_id_eq_zero _).2 (by ext i; exact isEmptyElim i)).of_iso e)
  exact ⟨a i, ha i, _, biproduct_ι_comp_inv_ne_zero e i⟩

/-- In a finite semisimple category, the images under an additive functor of the morphisms from
simple objects into `X` are jointly epimorphic: two morphisms out of `F.obj X` agreeing after
precomposition with every `F.map s`, for `s : S ⟶ X` with `S` simple, are equal. -/
theorem _root_.CategoryTheory.Functor.hom_ext_of_simple {C : Type u} [Category.{v} C] [Abelian C]
    [IsFiniteSemisimpleCategory C] {D : Type u'} [Category.{v'} D] [Preadditive D]
    (F : C ⥤ D) [F.Additive] {X : C} {Z : D} {f g : F.obj X ⟶ Z}
    (h : ∀ (S : C) [Simple S] (s : S ⟶ X), F.map s ≫ f = F.map s ≫ g) : f = g := by
  obtain ⟨ι, hι, a, ha, hba, ⟨e⟩⟩ := IsFiniteSemisimpleCategory.exists_biproduct_simples X
  -- The identity of `X` is the sum of the composites through the summands of `⨁ a`.
  have hX : 𝟙 X = ∑ i, (e.hom ≫ biproduct.π a i) ≫ biproduct.ι a i ≫ e.inv :=
    calc 𝟙 X = e.hom ≫ (∑ i, biproduct.π a i ≫ biproduct.ι a i) ≫ e.inv := by
          rw [biproduct.total, Category.id_comp, e.hom_inv_id]
      _ = _ := by simp only [Preadditive.sum_comp, Preadditive.comp_sum, Category.assoc]
  rw [← Category.id_comp f, ← Category.id_comp g, ← F.map_id, hX, F.map_sum,
    Preadditive.sum_comp, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [F.map_comp, Category.assoc, Category.assoc, h]

/-- In a finite semisimple category, a natural transformation out of an additive functor is
determined by its components at the simple objects. -/
theorem natTrans_ext_of_simple {C : Type u} [Category.{v} C] [Abelian C]
    [IsFiniteSemisimpleCategory C] {D : Type u'} [Category.{v'} D] [Preadditive D]
    {F G : C ⥤ D} [F.Additive] {α β : F ⟶ G} (h : ∀ (X : C) [Simple X], α.app X = β.app X) :
    α = β := by
  ext X
  refine F.hom_ext_of_simple fun S _ s ↦ ?_
  rw [α.naturality, β.naturality, h]

end TauCeti
