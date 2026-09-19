/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Stable.Basic

/-!
# Suspension on a Frobenius stable category

Let `E` be a Frobenius exact structure. For every object `X`, choose a conflation

`X ⟶ I(X) ⟶ ΣX`

with injective middle term. A morphism `f : X ⟶ Y` extends to a map `I(X) ⟶ I(Y)`, hence
induces a map `ΣX ⟶ ΣY`. Neither extension is unique in the original category, but any
two choices differ by a morphism through an injective, which is projective under the Frobenius
hypothesis. The induced map is therefore canonical in the projective stable quotient.

This file carries out that construction and obtains the additive suspension endofunctor of the
stable category. The loop functor and the proof that the two are quasi-inverse are developed
separately.

## Main definitions

* `TauCeti.ExactStructure.IsFrobenius.suspensionPresentation`: the chosen injective conflation.
* `TauCeti.ExactStructure.IsFrobenius.suspensionObj`: its cokernel term `ΣX`.
* `TauCeti.ExactStructure.IsFrobenius.suspensionMap`: a chosen induced map before quotienting.
* `TauCeti.ExactStructure.IsFrobenius.stableSuspension`: the additive suspension endofunctor of
  the projective stable category.

## References

* Dieter Happel, *Triangulated Categories in the Representation Theory of Finite Dimensional
  Algebras*, Chapter I, Section 2.
* Bernhard Keller, *Chain complexes and stable categories*, Manuscripta Mathematica **67**
  (1990), 379–417, Section 1.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C]

namespace ExactStructure.IsFrobenius

variable {E : ExactStructure C} (hE : E.IsFrobenius)

/-- The chosen conflation `X ⟶ I(X) ⟶ ΣX` used to construct suspension. -/
noncomputable def suspensionPresentation (X : C) : E.InjectivePresentation X :=
  hE.enoughInjectives.injectivePresentation X

/-- The chosen injective object in the suspension presentation of `X`. -/
noncomputable abbrev suspensionInjective (X : C) : C :=
  (hE.suspensionPresentation X).I

/-- The suspension object `ΣX`, defined as the third term of the chosen injective conflation. -/
noncomputable abbrev suspensionObj (X : C) : C :=
  (hE.suspensionPresentation X).K

/-- The inflation `X ⟶ I(X)` in the chosen suspension presentation. -/
noncomputable abbrev suspensionInflation (X : C) : X ⟶ hE.suspensionInjective X :=
  (hE.suspensionPresentation X).i

/-- The deflation `I(X) ⟶ ΣX` in the chosen suspension presentation. -/
noncomputable abbrev suspensionDeflation (X : C) :
    hE.suspensionInjective X ⟶ hE.suspensionObj X :=
  (hE.suspensionPresentation X).p

/-- The middle map between chosen injective presentations extending `f : X ⟶ Y`. -/
noncomputable def suspensionMiddleMap {X Y : C} (f : X ⟶ Y) :
    hE.suspensionInjective X ⟶ hE.suspensionInjective Y :=
  (hE.suspensionPresentation Y).isInjective.factorThru
    (E.isInflation_f (hE.suspensionPresentation X).conflation)
    (f ≫ hE.suspensionInflation Y)

/-- The chosen middle map extends `f` across the suspension inflations. -/
@[reassoc (attr := simp)]
theorem suspensionInflation_comp_suspensionMiddleMap {X Y : C} (f : X ⟶ Y) :
    hE.suspensionInflation X ≫ hE.suspensionMiddleMap f =
      f ≫ hE.suspensionInflation Y :=
  (hE.suspensionPresentation Y).isInjective.comp_factorThru
    (E.isInflation_f (hE.suspensionPresentation X).conflation)
    (f ≫ hE.suspensionInflation Y)

/-- The map `Σf : ΣX ⟶ ΣY` induced by a chosen extension between injective
presentations. Its image in the stable quotient is independent of the chosen extension. -/
noncomputable def suspensionMap {X Y : C} (f : X ⟶ Y) :
    hE.suspensionObj X ⟶ hE.suspensionObj Y :=
  (E.isKernelCokernelPair _ (hE.suspensionPresentation X).conflation).desc
    (hE.suspensionMiddleMap f ≫ hE.suspensionDeflation Y) (by
      rw [← Category.assoc, hE.suspensionInflation_comp_suspensionMiddleMap,
        Category.assoc, (hE.suspensionPresentation Y).zero, comp_zero])

/-- The induced suspension map makes the square on the two deflations commute. -/
@[reassoc (attr := simp)]
theorem suspensionDeflation_comp_suspensionMap {X Y : C} (f : X ⟶ Y) :
    hE.suspensionDeflation X ≫ hE.suspensionMap f =
      hE.suspensionMiddleMap f ≫ hE.suspensionDeflation Y :=
  (E.isKernelCokernelPair _ (hE.suspensionPresentation X).conflation).g_desc _ _

/-- Any pair of maps between the chosen suspension presentations inducing `f` gives the same
morphism as `suspensionMap f` after passing to the stable quotient. -/
theorem projectiveStableFunctor_map_suspensionMap_eq {X Y : C} (f : X ⟶ Y)
    (a : hE.suspensionInjective X ⟶ hE.suspensionInjective Y)
    (g : hE.suspensionObj X ⟶ hE.suspensionObj Y)
    (ha : hE.suspensionInflation X ≫ a = f ≫ hE.suspensionInflation Y)
    (hg : hE.suspensionDeflation X ≫ g = a ≫ hE.suspensionDeflation Y) :
    E.projectiveStableFunctor.map (hE.suspensionMap f) =
      E.projectiveStableFunctor.map g := by
  rw [MorphismIdeal.quotientFunctor_map_eq_iff,
    ExactStructure.mem_projectiveStableIdeal_iff]
  let b := hE.suspensionMiddleMap f - a
  have hb : hE.suspensionInflation X ≫ b = 0 := by
    rw [Preadditive.comp_sub, hE.suspensionInflation_comp_suspensionMiddleMap, ha, sub_self]
  let t := (E.isKernelCokernelPair _
    (hE.suspensionPresentation X).conflation).desc b hb
  have ht : hE.suspensionDeflation X ≫ t = b :=
    (E.isKernelCokernelPair _
      (hE.suspensionPresentation X).conflation).g_desc b hb
  have hdiff : hE.suspensionMap f - g = t ≫ hE.suspensionDeflation Y := by
    have := (E.isKernelCokernelPair _
      (hE.suspensionPresentation X).conflation).epi_g
    rw [← cancel_epi (hE.suspensionDeflation X)]
    calc
      hE.suspensionDeflation X ≫ (hE.suspensionMap f - g) =
          hE.suspensionMiddleMap f ≫ hE.suspensionDeflation Y -
            a ≫ hE.suspensionDeflation Y := by
              rw [Preadditive.comp_sub, hE.suspensionDeflation_comp_suspensionMap, hg]
      _ = b ≫ hE.suspensionDeflation Y := by rw [Preadditive.sub_comp]
      _ = hE.suspensionDeflation X ≫ (t ≫ hE.suspensionDeflation Y) := by
        rw [← Category.assoc, ht]
  rw [hdiff]
  exact ObjectProperty.factorsThrough_comp E.isProjective
    ((hE.projective_iff_injective _).mpr
      (hE.suspensionPresentation Y).isInjective) t (hE.suspensionDeflation Y)

/-- Suspension from the exact category to its stable quotient. Functoriality holds in the
quotient because different lifts between injective presentations differ through an injective. -/
public noncomputable def suspensionToStable : C ⥤ E.ProjectiveStableCategory where
  obj X := E.projectiveStableFunctor.obj (hE.suspensionObj X)
  map f := E.projectiveStableFunctor.map (hE.suspensionMap f)
  map_id X := by
    simpa using hE.projectiveStableFunctor_map_suspensionMap_eq (f := 𝟙 X)
      (𝟙 (hE.suspensionInjective X)) (𝟙 (hE.suspensionObj X)) (by simp) (by simp)
  map_comp f g := by
    simpa using hE.projectiveStableFunctor_map_suspensionMap_eq (f := f ≫ g)
      (hE.suspensionMiddleMap f ≫ hE.suspensionMiddleMap g)
      (hE.suspensionMap f ≫ hE.suspensionMap g) (by simp) (by simp)

/-- Suspension to the stable quotient sends `X` to the image of `ΣX`. -/
@[simp]
public theorem suspensionToStable_obj (X : C) :
    hE.suspensionToStable.obj X =
      E.projectiveStableFunctor.obj (hE.suspensionObj X) :=
  (rfl)

/-- Suspension to the stable quotient sends `f` to the image of the chosen `suspensionMap`. -/
@[simp]
public theorem suspensionToStable_map {X Y : C} (f : X ⟶ Y) :
    hE.suspensionToStable.map f =
      eqToHom (hE.suspensionToStable_obj X) ≫
        E.projectiveStableFunctor.map (hE.suspensionMap f) ≫
          eqToHom (hE.suspensionToStable_obj Y).symm :=
  (conj_eqToHom_iff_heq _ _ (hE.suspensionToStable_obj X)
    (hE.suspensionToStable_obj Y)).2 HEq.rfl

public noncomputable instance suspensionToStable_additive : (hE.suspensionToStable).Additive where
  map_add := by
    intro X Y f g
    rw [hE.suspensionToStable_map (f + g), hE.suspensionToStable_map f,
      hE.suspensionToStable_map g, ← Preadditive.comp_add, ← Preadditive.add_comp]
    rw [hE.projectiveStableFunctor_map_suspensionMap_eq (f := f + g)
      (hE.suspensionMiddleMap f + hE.suspensionMiddleMap g)
      (hE.suspensionMap f + hE.suspensionMap g) (by simp) (by simp)]
    simp only [Functor.map_add]

/-- The suspension of a projective object is projective. Thus suspension sends every object
killed by the stable quotient to another object killed by it. -/
theorem isProjective_suspensionObj {X : C} (hX : E.isProjective X) :
    E.isProjective (hE.suspensionObj X) := by
  let s := E.splittingOfInjective (hE.suspensionPresentation X).conflation
    ((hE.projective_iff_injective X).mp hX)
  exact E.isProjective.prop_of_retract
    ⟨s.s, hE.suspensionDeflation X, s.s_g⟩
    ((hE.projective_iff_injective _).mpr
      (hE.suspensionPresentation X).isInjective)

/-- The functor from the exact category to the stable category kills the projective stable ideal,
so it descends to an endofunctor of the stable category. -/
theorem suspensionToStable_kills_projectiveStableIdeal :
    E.projectiveStableIdeal ≤ (hE.suspensionToStable).kerIdeal := by
  intro X Y f hf
  rw [Functor.mem_kerIdeal_hom]
  obtain ⟨P, hP, i, p, rfl⟩ := (ObjectProperty.factorsThrough_iff E.isProjective _).mp
    ((ExactStructure.mem_projectiveStableIdeal_iff E).mp hf)
  rw [Functor.map_comp]
  have hzero : IsZero ((hE.suspensionToStable).obj P) :=
    (ExactStructure.isZero_projectiveStableFunctor_obj_iff E _).mpr
      (hE.isProjective_suspensionObj hP)
  rw [hzero.eq_of_tgt ((hE.suspensionToStable).map i) 0, zero_comp]

/-- The additive suspension endofunctor on the stable category of a Frobenius exact structure. -/
public noncomputable def stableSuspension :
    E.ProjectiveStableCategory ⥤ E.ProjectiveStableCategory :=
  E.projectiveStableIdeal.lift hE.suspensionToStable
    hE.suspensionToStable_kills_projectiveStableIdeal

/-- On objects represented by `X`, stable suspension is represented by `ΣX`. -/
@[simp]
public theorem stableSuspension_obj_projectiveStableFunctor_obj (X : C) :
    hE.stableSuspension.obj (E.projectiveStableFunctor.obj X) =
      E.projectiveStableFunctor.obj (hE.suspensionObj X) :=
  by
    simp only [stableSuspension, CategoryTheory.Quotient.lift_obj_functor_obj,
      hE.suspensionToStable_obj]

/-- On represented morphisms, stable suspension is induced by the chosen `suspensionMap`. -/
@[simp]
public theorem stableSuspension_map_projectiveStableFunctor_map {X Y : C} (f : X ⟶ Y) :
    hE.stableSuspension.map (E.projectiveStableFunctor.map f) =
      eqToHom (hE.stableSuspension_obj_projectiveStableFunctor_obj X) ≫
        E.projectiveStableFunctor.map (hE.suspensionMap f) ≫
          eqToHom (hE.stableSuspension_obj_projectiveStableFunctor_obj Y).symm :=
  (conj_eqToHom_iff_heq _ _
    (hE.stableSuspension_obj_projectiveStableFunctor_obj X)
    (hE.stableSuspension_obj_projectiveStableFunctor_obj Y)).2 HEq.rfl

end ExactStructure.IsFrobenius

end TauCeti
