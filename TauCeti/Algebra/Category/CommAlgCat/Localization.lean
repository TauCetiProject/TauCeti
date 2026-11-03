/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Localizations as filtered colimits of principal localizations

For a submonoid `M` of a commutative ring `R`, invert the product of each finite subset of
`M`. Inclusion of finite subsets gives a filtered diagram of principal localizations, whose
colimit is any localization of `R` at `M`. This presentation lets properties stable under
filtered colimits pass from principal localizations to arbitrary localizations.

The construction uses the universal property of localization, through Mathlib's
`IsLocalization.liftAlgHom` and `IsLocalization.algHom_subsingleton`.
-/

public section

open CategoryTheory Limits

universe u

namespace Submonoid

open CommAlgCat

variable {R : Type u} [CommRing R] (M : Submonoid R)

/-- Morphisms from a localization are unique as morphisms of algebras over the base ring. -/
theorem isLocalization_hom_ext {A B : CommAlgCat.{u} R} [IsLocalization M A]
    (f g : A ⟶ B) : f = g :=
  hom_ext ((IsLocalization.algHom_subsingleton (S := A) (P := B) M).elim _ _)

/-- The diagram which inverts the product of a finite set of denominators. -/
noncomputable def localizationAwayDiagram : Finset M ⥤ CommAlgCat.{u} R where
  obj s := .of R (Localization.Away (∏ x ∈ s, (x : R)))
  map {s t} h := ofHom <| IsLocalization.Away.liftAlgHom (∏ x ∈ s, (x : R))
    (f := Algebra.ofId R (Localization.Away (∏ x ∈ t, (x : R))))
    (IsLocalization.Away.isUnit_of_dvd _
      (Finset.prod_dvd_prod_of_subset s t (fun x : M ↦ (x : R)) (leOfHom h)))
  map_id s := (Submonoid.powers (∏ x ∈ s, (x : R))).isLocalization_hom_ext _ _
  map_comp {s _ _} _ _ := (Submonoid.powers (∏ x ∈ s, (x : R))).isLocalization_hom_ext _ _

/-- Each stage of the principal-localization diagram is the expected localization algebra. -/
@[simp]
theorem localizationAwayDiagram_obj (s : Finset M) :
    (localizationAwayDiagram M).obj s = .of R (Localization.Away (∏ x ∈ s, (x : R))) := (rfl)

variable (S : Type u) [CommRing S] [Algebra R S] [IsLocalization M S]

/-- The canonical cocone from principal localizations to a localization at all denominators. -/
noncomputable def localizationAwayCocone : Cocone (localizationAwayDiagram M) where
  pt := .of R S
  ι :=
    { app := fun s ↦ ofHom <| IsLocalization.Away.liftAlgHom (∏ x ∈ s, (x : R))
        (f := Algebra.ofId R S)
        (by
          rw [Algebra.ofId_apply, map_prod]
          exact IsUnit.prod_iff.mpr fun x _ ↦ IsLocalization.map_units S x)
      naturality := fun s t h ↦
        (Submonoid.powers (∏ x ∈ s, (x : R))).isLocalization_hom_ext
          (A := .of R (Localization.Away (∏ x ∈ s, (x : R)))) _ _ }

/-- The localization cocone has the specified localization algebra as its apex. -/
@[simp]
theorem localizationAwayCocone_pt : (localizationAwayCocone M S).pt = .of R S := (rfl)

/-- Every localization is the filtered colimit of principal localizations indexed by finite
sets of denominators. No finite generation, domain or Noetherian hypothesis is required. -/
noncomputable def localizationAwayCoconeIsColimit : IsColimit (localizationAwayCocone M S) := by
  classical
  refine
    { desc := fun c ↦ ofHom <| IsLocalization.liftAlgHom (M := M)
        (f := Algebra.ofId R c.pt) (fun x ↦ ?_)
      fac := fun c s ↦ ?_
      uniq := fun c m hm ↦ ?_ }
  · have hx : IsUnit (algebraMap R (Localization.Away (∏ y ∈ ({x} : Finset M), (y : R))) x) := by
      simpa using IsLocalization.Away.algebraMap_isUnit
        (S := Localization.Away (∏ y ∈ ({x} : Finset M), (y : R)))
        (∏ y ∈ ({x} : Finset M), (y : R))
    let f : Localization.Away (∏ y ∈ ({x} : Finset M), (y : R)) →ₐ[R] c.pt :=
      (c.ι.app {x}).hom
    simpa only [Algebra.ofId_apply, AlgHom.commutes] using hx.map f
  · exact (Submonoid.powers (∏ x ∈ s, (x : R))).isLocalization_hom_ext
      (A := .of R (Localization.Away (∏ x ∈ s, (x : R)))) _ _
  · exact M.isLocalization_hom_ext (A := .of R S) _ _

end Submonoid
