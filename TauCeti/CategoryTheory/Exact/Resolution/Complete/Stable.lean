/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory
public import TauCeti.CategoryTheory.Exact.Resolution.Complete.Comparison

/-!
# The stable category as a homotopy category of complete resolutions

Let `E` be a Frobenius exact structure on `C`. Inside the homotopy category `K(C)` of
`ℤ`-indexed cochain complexes, consider the complexes homotopy equivalent to the spliced complex
of a complete resolution, that is, to an acyclic complex (relative to `E`) of projective-injective
objects: `K_ac(P)`. This
file proves that the stable category `E.ProjectiveStableCategory` is equivalent to `K_ac(P)`.

The functor sends an object to its complete resolution and a morphism `f` to the homotopy class
of the lift of `f`. It is well defined on the stable category because a morphism factoring through
a projective-injective object lifts to a null-homotopic map. It is faithful by the converse of
that criterion. It is full because every map between complete resolutions restricts to a
morphism of the objects of cycles in degree zero (`CompleteResolution.cyclesMap`), of which it is
a lift. It is essentially surjective because complete resolutions are unique up to homotopy.

The equivalence is the first half of the realization of an algebraic triangulated category as a
full subcategory of a homotopy category; its compatibility with the triangulations is separate.

## Main definitions

* `TauCeti.ExactStructure.completeResolutionComplex`: the complexes homotopy equivalent to the
  spliced complex of a complete resolution, as an object property of the homotopy category.
* `TauCeti.ExactStructure.CompleteResolutionHomotopyCategory`: the corresponding full subcategory
  `K_ac(P)`.
* `TauCeti.ExactStructure.IsFrobenius.completeResolutionFunctor`: the additive functor sending an
  object to the homotopy class of its complete resolution.
* `TauCeti.ExactStructure.IsFrobenius.stableEquivCompleteResolutionHomotopyCategory`:
  the equivalence between the stable category and `K_ac(P)`.

## References

* Ragnar-Olaf Buchweitz, *Maximal Cohen–Macaulay Modules and Tate Cohomology*, Section 4, for
  the equivalence between the stable category and the homotopy category of complete
  resolutions.
* Bernhard Keller, *Chain complexes and stable categories*, Manuscripta Mathematica **67**
  (1990), 379--417, for Frobenius categories and their stable categories as homotopy categories.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]

namespace ExactStructure

variable (E : ExactStructure C)

/-- The complexes homotopy equivalent to the spliced complex of a complete resolution of `E`, as
an object property of the homotopy category `K(C)`: the closure under isomorphism of the spliced
complexes. These are the complexes homotopy equivalent to complexes of projective-injective
objects that are acyclic relative to `E`. -/
def completeResolutionComplex : ObjectProperty (HomotopyCategory C (ComplexShape.up ℤ)) :=
  (ObjectProperty.ofObj fun r : E.CompleteResolution ↦
    (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj r.complex).isoClosure

instance : E.completeResolutionComplex.IsClosedUnderIsomorphisms := by
  unfold completeResolutionComplex
  infer_instance

theorem completeResolutionComplex_iff (K : HomotopyCategory C (ComplexShape.up ℤ)) :
    E.completeResolutionComplex K ↔ ∃ r : E.CompleteResolution,
      Nonempty (K ≅ (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj r.complex) := by
  simp only [completeResolutionComplex, ObjectProperty.prop_isoClosure_iff,
    ObjectProperty.ofObj_iff]
  exact ⟨fun ⟨_, ⟨r, rfl⟩, e⟩ ↦ ⟨r, e⟩, fun ⟨r, e⟩ ↦ ⟨_, ⟨r, rfl⟩, e⟩⟩

/-- The spliced complex of a complete resolution satisfies `completeResolutionComplex`. -/
theorem completeResolutionComplex_quotient_obj (r : E.CompleteResolution) :
    E.completeResolutionComplex ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj r.complex) :=
  ObjectProperty.le_isoClosure _ _ (ObjectProperty.ofObj_apply _ r)

/-- The homotopy category `K_ac(P)` of the complexes homotopy equivalent to the spliced complex of
a complete resolution, as a full subcategory of `K(C)`. -/
abbrev CompleteResolutionHomotopyCategory := E.completeResolutionComplex.FullSubcategory

namespace IsFrobenius

variable {E} (hE : E.IsFrobenius)

/-- The lift of a morphism along the chosen complete resolutions of its source and target. -/
noncomputable def liftMap {X Y : C} (f : X ⟶ Y) :
    (hE.completeResolution X).complex ⟶ (hE.completeResolution Y).complex :=
  CompleteResolution.lift _ _
    ((hE.completeResolutionIso X).hom ≫ f ≫ (hE.completeResolutionIso Y).inv)

@[reassoc (attr := simp)]
theorem ι_liftMap_f_zero {X Y : C} (f : X ⟶ Y) :
    (hE.completeResolution X).ι 0 ≫ (hE.liftMap f).f 0 =
      ((hE.completeResolutionIso X).hom ≫ f ≫ (hE.completeResolutionIso Y).inv) ≫
        (hE.completeResolution Y).ι 0 :=
  CompleteResolution.ι_lift_f_zero _ _ _

/-- The functor sending an object to the homotopy class of its complete resolution, and a
morphism to the homotopy class of its lift. -/
noncomputable def completeResolutionFunctor :
    C ⥤ HomotopyCategory C (ComplexShape.up ℤ) where
  obj X := (HomotopyCategory.quotient C _).obj (hE.completeResolution X).complex
  map f := (HomotopyCategory.quotient C _).map (hE.liftMap f)
  map_id X := by
    rw [← (HomotopyCategory.quotient C _).map_id]
    exact HomotopyCategory.eq_of_homotopy _ _
      (CompleteResolution.liftHomotopy (𝟙 _) _ _ (by simp) (by simp))
  map_comp {X Y Z} f g := by
    rw [← (HomotopyCategory.quotient C _).map_comp]
    exact HomotopyCategory.eq_of_homotopy _ _ (CompleteResolution.liftHomotopy
      ((hE.completeResolutionIso X).hom ≫ (f ≫ g) ≫ (hE.completeResolutionIso Z).inv) _ _
      (by simp) (by simp))

theorem completeResolutionFunctor_obj (X : C) :
    hE.completeResolutionFunctor.obj X =
      (HomotopyCategory.quotient C _).obj (hE.completeResolution X).complex :=
  (rfl)

/-- The functor on morphisms, transported along `completeResolutionFunctor_obj`. -/
theorem completeResolutionFunctor_map {X Y : C} (f : X ⟶ Y) :
    hE.completeResolutionFunctor.map f = eqToHom (hE.completeResolutionFunctor_obj X) ≫
      (HomotopyCategory.quotient C _).map (hE.liftMap f) ≫
        eqToHom (hE.completeResolutionFunctor_obj Y).symm :=
  (conj_eqToHom_iff_heq _ _ (hE.completeResolutionFunctor_obj X)
    (hE.completeResolutionFunctor_obj Y)).2 HEq.rfl

/-- The functor on morphisms, without transport: private, since its statement unfolds the
objects of the functor. -/
private theorem map_eq {X Y : C} (f : X ⟶ Y) :
    hE.completeResolutionFunctor.map f = (HomotopyCategory.quotient C _).map (hE.liftMap f) :=
  (rfl)

instance : hE.completeResolutionFunctor.Additive where
  map_add {X Y f g} := by
    rw [map_eq, map_eq, map_eq]
    exact (HomotopyCategory.eq_of_homotopy _ _ (CompleteResolution.liftHomotopy
      ((hE.completeResolutionIso X).hom ≫ (f + g) ≫ (hE.completeResolutionIso Y).inv) _ _
      (by simp) (by simp [Preadditive.comp_add, Preadditive.add_comp]))).trans
      ((HomotopyCategory.quotient C _).map_add)

/-- A morphism factoring through a relative projective has a null-homotopic lift, so the functor
kills the ideal defining the stable category. -/
theorem projectiveStableIdeal_le_kerIdeal :
    E.projectiveStableIdeal ≤ hE.completeResolutionFunctor.kerIdeal := by
  intro X Y f hf
  rw [hE.projectiveStableIdeal_eq_factorIdeal, ObjectProperty.mem_factorIdeal_iff] at hf
  have hf' : E.projectiveInjective.FactorsThrough
      ((hE.completeResolutionIso X).hom ≫ f ≫ (hE.completeResolutionIso Y).inv) := by
    simpa only [Category.assoc] using
      (hf.comp_left (hE.completeResolutionIso X).hom).comp_right (hE.completeResolutionIso Y).inv
  rw [Functor.mem_kerIdeal_hom, map_eq]
  exact (HomotopyCategory.quotient_map_eq_zero_iff _).2
    ⟨CompleteResolution.liftHomotopyZero _ (hE.ι_liftMap_f_zero f) hf'⟩

/-- The functor from the stable category to the homotopy category. -/
noncomputable abbrev stableToHomotopyCategory :
    E.ProjectiveStableCategory ⥤ HomotopyCategory C (ComplexShape.up ℤ) :=
  E.projectiveStableIdeal.lift hE.completeResolutionFunctor hE.projectiveStableIdeal_le_kerIdeal

/-- The functor from the stable category to `K_ac(P)`. -/
noncomputable def stableToCompleteResolutionHomotopyCategory :
    E.ProjectiveStableCategory ⥤ E.CompleteResolutionHomotopyCategory :=
  E.completeResolutionComplex.lift hE.stableToHomotopyCategory
    fun X ↦ E.completeResolutionComplex_quotient_obj (hE.completeResolution X.as)

instance : hE.stableToCompleteResolutionHomotopyCategory.Additive := by
  unfold stableToCompleteResolutionHomotopyCategory
  infer_instance

/-- The functor to `K_ac(P)` followed by the inclusion into `K(C)` is the functor to `K(C)`. -/
noncomputable def stableToCompleteResolutionHomotopyCategoryCompιIso :
    hE.stableToCompleteResolutionHomotopyCategory ⋙ E.completeResolutionComplex.ι ≅
      hE.stableToHomotopyCategory :=
  ObjectProperty.liftCompιIso _ _ _

/-- On the image of a morphism of `C`, the functor to `K_ac(P)` is the homotopy class of its
lift. -/
private theorem stableToCompleteResolutionHomotopyCategory_map_hom {X Y : C} (f : X ⟶ Y) :
    (hE.stableToCompleteResolutionHomotopyCategory.map (E.projectiveStableFunctor.map f)).hom =
      hE.completeResolutionFunctor.map f := by
  rw [stableToCompleteResolutionHomotopyCategory, ObjectProperty.lift_map_hom]
  exact CategoryTheory.Quotient.lift_map_functor_map _ _ _ f

instance : hE.stableToCompleteResolutionHomotopyCategory.Full where
  map_surjective {X Y} g := by
    obtain ⟨φ, hφ⟩ := (HomotopyCategory.quotient C _).map_surjective g.hom
    let f₀ := (hE.completeResolutionIso X.as).inv ≫ CompleteResolution.cyclesMap φ ≫
      (hE.completeResolutionIso Y.as).hom
    refine ⟨E.projectiveStableFunctor.map f₀, ObjectProperty.hom_ext _ ?_⟩
    rw [stableToCompleteResolutionHomotopyCategory_map_hom, map_eq, ← hφ]
    exact HomotopyCategory.eq_of_homotopy _ _
      (CompleteResolution.liftHomotopy (CompleteResolution.cyclesMap φ) _ _
        (by simp [f₀]) (by simp))

instance : hE.stableToCompleteResolutionHomotopyCategory.Faithful where
  map_injective {X Y} f₁ f₂ h := by
    obtain ⟨g₁, rfl⟩ := E.projectiveStableIdeal.quotientFunctor.map_surjective f₁
    obtain ⟨g₂, rfl⟩ := E.projectiveStableIdeal.quotientFunctor.map_surjective f₂
    have h' := E.completeResolutionComplex.ι.congr_map h
    rw [ObjectProperty.ι_map, ObjectProperty.ι_map,
      stableToCompleteResolutionHomotopyCategory_map_hom,
      stableToCompleteResolutionHomotopyCategory_map_hom, map_eq, map_eq] at h'
    have H := Homotopy.equivSubZero (HomotopyCategory.homotopyOfEq _ _ h')
    have hfac := CompleteResolution.factorsThrough_of_homotopy
      (f := ((hE.completeResolutionIso X.as).hom ≫ (g₁ - g₂) ≫
        (hE.completeResolutionIso Y.as).inv))
      (by simp [Preadditive.comp_sub, Preadditive.sub_comp]) H
    rw [MorphismIdeal.quotientFunctor_map_eq_iff, mem_projectiveStableIdeal_iff,
      ← hE.projectiveInjective_eq_isProjective]
    simpa using (hfac.comp_left (hE.completeResolutionIso X.as).inv).comp_right
      (hE.completeResolutionIso Y.as).hom

instance : hE.stableToCompleteResolutionHomotopyCategory.EssSurj where
  mem_essImage K := by
    obtain ⟨r, ⟨e⟩⟩ := (E.completeResolutionComplex_iff _).mp K.property
    refine ⟨E.projectiveStableFunctor.obj (r.Z 0), ⟨ObjectProperty.isoMk _ ?_⟩⟩
    exact HomotopyCategory.isoOfHomotopyEquiv
      (CompleteResolution.homotopyEquiv _ _ (hE.completeResolutionIso (r.Z 0))) ≪≫ e.symm

instance : hE.stableToCompleteResolutionHomotopyCategory.IsEquivalence where

/-- **The stable category of a Frobenius exact category is equivalent to the homotopy category of
its complete resolutions**: the complexes homotopy equivalent to acyclic complexes (relative to
`E`) of projective-injective objects. -/
noncomputable def stableEquivCompleteResolutionHomotopyCategory :
    E.ProjectiveStableCategory ≌ E.CompleteResolutionHomotopyCategory :=
  hE.stableToCompleteResolutionHomotopyCategory.asEquivalence

/-- The functor of the stable equivalence is the complete-resolution functor into `K_ac(P)`. -/
@[simp]
theorem stableEquivCompleteResolutionHomotopyCategory_functor :
    hE.stableEquivCompleteResolutionHomotopyCategory.functor =
      hE.stableToCompleteResolutionHomotopyCategory :=
  (rfl)

end IsFrobenius

end ExactStructure

end TauCeti
