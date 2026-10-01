/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Prod
public import TauCeti.CategoryTheory.Exact.Product
public import TauCeti.CategoryTheory.GrothendieckGroup.Exact

/-!
# Grothendieck groups of product categories

This file identifies the split Grothendieck group of a product of additive categories with the
product of their split Grothendieck groups. It also identifies the exact Grothendieck group of
the componentwise exact structure with the product of the two exact Grothendieck groups. Both
equivalences are characterised on object classes and are natural in the relevant functors.

## Main definitions

* `TauCeti.SplitK0.prodEquiv`: the canonical equivalence
  `SplitK0 (C × D) ≃+ SplitK0 C × SplitK0 D`.
* `TauCeti.ExactK0.prodEquiv`: the canonical equivalence
  `ExactK0 (E.prod E') ≃+ ExactK0 E × ExactK0 E'`.

## Main results

* `TauCeti.SplitK0.prodEquiv_apply`: the forward map is induced by the two projections.
* `TauCeti.SplitK0.prodEquiv_symm_apply`: the inverse is the sum of the two zero-section maps.
* `TauCeti.SplitK0.prodEquiv_of`: the equivalence sends `[(X, Y)]` to `([X], [Y])`.
* `TauCeti.SplitK0.prodEquiv_naturality`: the equivalence is natural in additive functors.
* `TauCeti.ExactK0.prodEquiv_naturality`: the exact equivalence is natural in
  conflation-exact functors.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits ZeroObject

universe w w' w₁ w₂ v v' v₁ v₂ u u' u₁ u₂

namespace SplitK0

section Product

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] [EssentiallySmall.{w} C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
  [HasBinaryBiproducts D] [EssentiallySmall.{w'} D]

private lemma of_eq_of_components (X : C × D) :
    (of X : SplitK0 (C × D)) = of (X.1, 0) + of (0, X.2) := by
  rw [← of_biprod]
  exact of_congr (prod.biprodComponentsIso X).symm

/-- Split `K₀` takes a product of additive categories to the product of their split
Grothendieck groups. -/
noncomputable def prodEquiv : SplitK0 (C × D) ≃+ SplitK0 C × SplitK0 D :=
  AddEquiv.ofProdCoprod
    (map (CategoryTheory.Prod.fst C D)) (map (CategoryTheory.Prod.snd C D))
    (map (CategoryTheory.Prod.sectL C (0 : D)))
    (map (CategoryTheory.Prod.sectR (0 : C) D))
    (by apply hom_ext; intro X; simpa using (of_eq_of_components X).symm)
    (by apply hom_ext; simp) (by apply hom_ext; simp)
    (by apply hom_ext; simp) (by apply hom_ext; simp)

/-- The forward product equivalence is induced by the two projection functors. -/
@[simp]
lemma prodEquiv_apply (x : SplitK0 (C × D)) :
    prodEquiv x =
      (map (CategoryTheory.Prod.fst C D) x, map (CategoryTheory.Prod.snd C D) x) := by
  simp [prodEquiv]

/-- The inverse product equivalence is the sum of the maps induced by inserting a zero object in
each coordinate. -/
lemma prodEquiv_symm_apply (x : SplitK0 C × SplitK0 D) :
    (prodEquiv (C := C) (D := D)).symm x =
      map (CategoryTheory.Prod.sectL C (0 : D)) x.1 +
        map (CategoryTheory.Prod.sectR (0 : C) D) x.2 := by
  simp [prodEquiv]

/-- The product equivalence sends an object class to the pair of its component classes. -/
lemma prodEquiv_of (X : C × D) : prodEquiv (of X) = (of X.1, of X.2) := by
  simp [prodEquiv_apply]

/-- The inverse product equivalence sends a pair of object classes to the class of the paired
object. -/
@[simp]
lemma prodEquiv_symm_of (X : C) (Y : D) :
    (prodEquiv (C := C) (D := D)).symm (of X, of Y) = of (X, Y) := by
  apply (prodEquiv (C := C) (D := D)).injective
  simp

end Product

section Naturality

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Preadditive C₁] [HasZeroObject C₁]
  [HasBinaryBiproducts C₁] [EssentiallySmall.{w₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Preadditive C₂] [HasZeroObject C₂]
  [HasBinaryBiproducts C₂] [EssentiallySmall.{w₂} C₂]
  {D₁ : Type u} [Category.{v} D₁] [Preadditive D₁] [HasZeroObject D₁]
  [HasBinaryBiproducts D₁] [EssentiallySmall.{w} D₁]
  {D₂ : Type u'} [Category.{v'} D₂] [Preadditive D₂] [HasZeroObject D₂]
  [HasBinaryBiproducts D₂] [EssentiallySmall.{w'} D₂]

/-- The split-`K₀` product equivalence is natural in additive functors in both variables. -/
theorem prodEquiv_naturality (F : C₁ ⥤ C₂) (G : D₁ ⥤ D₂) [F.Additive] [G.Additive] :
    (prodEquiv (C := C₂) (D := D₂) : SplitK0 (C₂ × D₂) →+ _).comp (map (F.prod G)) =
      ((map F).prodMap (map G)).comp
        (prodEquiv (C := C₁) (D := D₁) : SplitK0 (C₁ × D₁) →+ _) := by
  apply hom_ext
  intro X
  simp

end Naturality

end SplitK0

namespace ExactK0

section Product

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] [EssentiallySmall.{w} C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
  [HasBinaryBiproducts D] [EssentiallySmall.{w'} D]
  (E : ExactStructure C) (E' : ExactStructure D)

private lemma of_eq_of_components (X : C × D) :
    (of X : ExactK0 (E.prod E')) = of (X.1, 0) + of (0, X.2) := by
  rw [← of_biprod]
  exact of_congr (prod.biprodComponentsIso X).symm

/-- Exact `K₀` takes a componentwise product of exact categories to the product of their exact
Grothendieck groups. -/
noncomputable def prodEquiv : ExactK0 (E.prod E') ≃+ ExactK0 E × ExactK0 E' :=
  AddEquiv.ofProdCoprod
    (map (CategoryTheory.Prod.fst C D) (ExactStructure.isConflationExact_fst_prod E E'))
    (map (CategoryTheory.Prod.snd C D) (ExactStructure.isConflationExact_snd_prod E E'))
    (map (CategoryTheory.Prod.sectL C (0 : D))
      (ExactStructure.isConflationExact_sectL_prod E E'))
    (map (CategoryTheory.Prod.sectR (0 : C) D)
      (ExactStructure.isConflationExact_sectR_prod E E'))
    (by apply hom_ext; intro X; simpa using (of_eq_of_components E E' X).symm)
    (by apply hom_ext; simp) (by apply hom_ext; simp)
    (by apply hom_ext; simp) (by apply hom_ext; simp)

/-- The forward exact-`K₀` product equivalence is induced by the two projection functors. -/
@[simp]
lemma prodEquiv_apply (x : ExactK0 (E.prod E')) :
    prodEquiv E E' x =
      (map (CategoryTheory.Prod.fst C D) (ExactStructure.isConflationExact_fst_prod E E') x,
        map (CategoryTheory.Prod.snd C D) (ExactStructure.isConflationExact_snd_prod E E') x) := by
  simp [prodEquiv]

/-- The inverse exact-`K₀` product equivalence is the sum of the maps induced by the two zero
sections. -/
lemma prodEquiv_symm_apply (x : ExactK0 E × ExactK0 E') :
    (prodEquiv E E').symm x =
      map (CategoryTheory.Prod.sectL C (0 : D))
          (ExactStructure.isConflationExact_sectL_prod E E') x.1 +
        map (CategoryTheory.Prod.sectR (0 : C) D)
          (ExactStructure.isConflationExact_sectR_prod E E') x.2 := by
  simp [prodEquiv]

/-- The exact-`K₀` product equivalence sends an object class to the pair of its component
classes. -/
lemma prodEquiv_of (X : C × D) : prodEquiv E E' (of X) = (of X.1, of X.2) := by
  simp

/-- The inverse exact-`K₀` product equivalence sends a pair of object classes to the class of
the paired object. -/
@[simp]
lemma prodEquiv_symm_of (X : C) (Y : D) :
    (prodEquiv E E').symm (of X, of Y) = of (X, Y) := by
  apply (prodEquiv E E').injective
  simp

end Product

section Naturality

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Preadditive C₁] [HasZeroObject C₁]
  [HasBinaryBiproducts C₁] [EssentiallySmall.{w₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Preadditive C₂] [HasZeroObject C₂]
  [HasBinaryBiproducts C₂] [EssentiallySmall.{w₂} C₂]
  {D₁ : Type u} [Category.{v} D₁] [Preadditive D₁] [HasZeroObject D₁]
  [HasBinaryBiproducts D₁] [EssentiallySmall.{w} D₁]
  {D₂ : Type u'} [Category.{v'} D₂] [Preadditive D₂] [HasZeroObject D₂]
  [HasBinaryBiproducts D₂] [EssentiallySmall.{w'} D₂]
  {E₁ : ExactStructure C₁} {E₂ : ExactStructure C₂}
  {E₁' : ExactStructure D₁} {E₂' : ExactStructure D₂}

/-- The exact-`K₀` product equivalence is natural in conflation-exact functors in both
variables. -/
theorem prodEquiv_naturality (F : C₁ ⥤ C₂) (G : D₁ ⥤ D₂) [F.Additive] [G.Additive]
    (hF : E₁.IsConflationExact E₂ F) (hG : E₁'.IsConflationExact E₂' G) :
    (prodEquiv E₂ E₂' : ExactK0 (E₂.prod E₂') →+ _).comp
        (map (F.prod G) (hF.prod hG)) =
      ((map F hF).prodMap (map G hG)).comp
        (prodEquiv E₁ E₁' : ExactK0 (E₁.prod E₁') →+ _) := by
  apply hom_ext
  intro X
  simp

end Naturality

end ExactK0

end TauCeti
