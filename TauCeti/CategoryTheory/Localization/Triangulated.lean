/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Localization.Triangulated

/-!
# Triangulated localizations: equivalences and induced functors

An equivalence of categories `F : C ⥤ D` is a localization functor for the class of
isomorphisms of `C`. This class admits a left calculus of fractions, and, when `C` is
pretriangulated, it is compatible with the triangulation. Consequently Mathlib's construction
`CategoryTheory.Triangulated.Localization.pretriangulated` applies to `F`: if `D` carries a
shift by `ℤ` for which `F` commutes with the shifts, then `D` is pretriangulated, with
distinguished triangles the triangles isomorphic to images of distinguished triangles of `C`,
`F` is a triangle functor, and `D` is triangulated as soon as `C` is
(`CategoryTheory.Triangulated.Localization.isTriangulated`).

This is the transport used for homotopy categories that are identified with the stable
category of a Frobenius exact category: Happel's triangulation of the stable category is
transported along the identification, after the shift of the homotopy category has been
matched with stable suspension.

A localizer morphism whose underlying functor is a triangle functor induces a functor between
triangulated localizations of its source and target; this induced functor is again a triangle
functor. Comparison functors between Verdier quotients arise this way.

## Main results

* `TauCeti.instHasLeftCalculusOfFractionsIsomorphisms`: the isomorphisms admit a left calculus
  of fractions.
* `TauCeti.instIsCompatibleWithShiftIsomorphisms`: the isomorphisms are compatible with every
  shift by an additive group.
* `TauCeti.instIsCompatibleWithTriangulationIsomorphisms`: in a pretriangulated category, the
  isomorphisms are compatible with the triangulation.
* `TauCeti.instIsLocalizationIsomorphisms`: an equivalence is a localization functor for the
  isomorphisms of its source.
* `CategoryTheory.LocalizerMorphism.isTriangulated_localizedFunctor`: the functor induced on
  triangulated localizations by a localizer morphism whose underlying functor is a triangle
  functor is a triangle functor.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

variable {C : Type*} [Category* C]

/-- The isomorphisms of a category admit a left calculus of fractions: a right fraction
`s⁻¹ ≫ f` with `s` an isomorphism is the left fraction `(inv s ≫ f) ≫ (𝟙)⁻¹`. -/
instance instHasLeftCalculusOfFractionsIsomorphisms :
    (MorphismProperty.isomorphisms C).HasLeftCalculusOfFractions where
  exists_leftFraction _ _ φ :=
    have := φ.hs
    ⟨MorphismProperty.LeftFraction.mk (inv φ.s ≫ φ.f) (𝟙 _)
      (MorphismProperty.isomorphisms.infer_property _), by simp⟩
  ext _ _ _ f₁ f₂ s hs h :=
    have := hs
    ⟨_, 𝟙 _, MorphismProperty.isomorphisms.infer_property _, by
      simpa using (cancel_epi s).1 h⟩

/-- An equivalence of categories is a localization functor for the isomorphisms of its source. -/
instance instIsLocalizationIsomorphisms {D : Type*} [Category* D] (F : C ⥤ D) [F.IsEquivalence] :
    F.IsLocalization (MorphismProperty.isomorphisms C) :=
  Functor.IsLocalization.of_isEquivalence F _ le_rfl

/-- The isomorphisms of a category are compatible with every shift by an additive group: a
morphism is an isomorphism exactly when its shift is. -/
instance instIsCompatibleWithShiftIsomorphisms (A : Type*) [AddGroup A] [HasShift C A] :
    (MorphismProperty.isomorphisms C).IsCompatibleWithShift A where
  condition a := by
    ext X Y f
    simp only [MorphismProperty.inverseImage_iff, MorphismProperty.isomorphisms.iff]
    exact ⟨fun _ ↦ isIso_of_reflects_iso f (shiftFunctor C a), fun _ ↦ inferInstance⟩

variable [HasShift C ℤ] [Preadditive C] [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]

/-- In a pretriangulated category, the isomorphisms are compatible with the triangulation: a
morphism of distinguished triangles whose first two components are isomorphisms can be
completed by an isomorphism. -/
instance instIsCompatibleWithTriangulationIsomorphisms :
    (MorphismProperty.isomorphisms C).IsCompatibleWithTriangulation where
  compatible_with_triangulation T₁ T₂ hT₁ hT₂ a b ha hb comm := by
    obtain ⟨c, hc₂, hc₃⟩ :=
      complete_distinguished_triangle_morphism T₁ T₂ hT₁ hT₂ a b comm
    exact ⟨c, isIso₃_of_isIso₁₂ (Triangle.homMk _ _ a b c comm hc₂ hc₃) hT₁ hT₂ ha hb, hc₂, hc₃⟩

end TauCeti

namespace CategoryTheory.LocalizerMorphism

open Limits

variable {C₁ C₂ D₁ D₂ : Type*} [Category* C₁] [Category* C₂] [Category* D₁] [Category* D₂]
  [HasZeroObject C₁] [HasZeroObject C₂] [HasZeroObject D₁] [HasZeroObject D₂]
  [Preadditive C₁] [Preadditive C₂] [Preadditive D₁] [Preadditive D₂]
  [HasShift C₁ ℤ] [HasShift C₂ ℤ] [HasShift D₁ ℤ] [HasShift D₂ ℤ]
  [∀ n : ℤ, (shiftFunctor C₁ n).Additive] [∀ n : ℤ, (shiftFunctor C₂ n).Additive]
  [∀ n : ℤ, (shiftFunctor D₁ n).Additive] [∀ n : ℤ, (shiftFunctor D₂ n).Additive]
  [Pretriangulated C₁] [Pretriangulated C₂] [Pretriangulated D₁] [Pretriangulated D₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}
  [W₁.IsCompatibleWithShift ℤ] [W₂.IsCompatibleWithShift ℤ] [W₁.HasLeftCalculusOfFractions]
  (Φ : LocalizerMorphism W₁ W₂) [Φ.functor.CommShift ℤ] [Φ.functor.IsTriangulated]
  (L₁ : C₁ ⥤ D₁) [L₁.IsLocalization W₁] [L₁.CommShift ℤ] [L₁.IsTriangulated]
  (L₂ : C₂ ⥤ D₂) [L₂.IsLocalization W₂] [L₂.CommShift ℤ] [L₂.IsTriangulated]

/-- The functor induced on triangulated localizations by a localizer morphism whose underlying
functor is a triangle functor is itself a triangle functor. -/
instance isTriangulated_localizedFunctor : (Φ.localizedFunctor L₁ L₂).IsTriangulated := by
  have := Localization.essSurj_mapArrow L₁ W₁
  have := Φ.natTransCommShift_hom (M := ℤ) L₁ L₂ (Φ.localizedFunctor L₁ L₂) (CatCommSq.iso ..)
  exact Functor.isTriangulated_of_precomp_iso (CatCommSq.iso Φ.functor L₁ L₂ _).symm

end CategoryTheory.LocalizerMorphism
