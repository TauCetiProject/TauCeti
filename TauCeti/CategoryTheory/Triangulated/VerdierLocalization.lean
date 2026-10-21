/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Localization.CalculusOfFractions.Preadditive
public import Mathlib.CategoryTheory.Localization.Triangulated
public import Mathlib.CategoryTheory.Shift.Localization
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import TauCeti.CategoryTheory.ObjectProperty.Retract

/-!
# Verdier localizations: kernels and comparison functors

Let `C` be a pretriangulated category and `P` a class of objects. Mathlib's Verdier localization
inverts the class `P.trW` of morphisms whose cone satisfies `P`. This file records the
elementary facts relating `P` to the localization and to triangle functors, and the comparison
functors between two Verdier localizations.

* A triangle functor `F` inverts `P.trW` exactly when it sends every object of `P` to zero.
  Together with the localization universal property, this says that the Verdier quotient by `P`
  is the universal triangulated category in which the objects of `P` vanish.
* In a triangulated category, an object becomes zero in the Verdier quotient by a thick
  triangulated subcategory `P` exactly when it belongs to `P`.
* The zero objects of a pretriangulated category form a thick triangulated subcategory, so the
  objects killed by a triangle functor do as well.
* A localizer morphism given by a triangle functor induces a triangle functor on triangulated
  localizations. For `P ≤ Q` the identity functor is such a localizer morphism from `P.trW` to
  `Q.trW`, and so induces a comparison triangle functor between the Verdier quotients by `P`
  and by `Q`, compatible with the two localization functors up to natural isomorphism.

## Main definitions

* `CategoryTheory.ObjectProperty.trWLocalizerMorphismOfLE`: the identity functor, as a localizer
  morphism from `P.trW` to `Q.trW` when `P ≤ Q`.

## Main results

* `CategoryTheory.ObjectProperty.trW_isInvertedBy_iff`: a triangle functor inverts `P.trW` if and
  only if it kills `P`.
* `CategoryTheory.ObjectProperty.TrWLocalization.isZero_obj_iff`: the kernel of the Verdier
  localization at a thick triangulated subcategory `P` is `P`.
* `CategoryTheory.LocalizerMorphism.isTriangulated_localizedFunctor`: the functor induced on
  triangulated localizations by a triangulated localizer morphism is a triangle functor.

## References

* J.-L. Verdier, *Des catégories dérivées des catégories abéliennes*, Astérisque **239** (1996),
  Chapitre II, §2.
* A. Neeman, *Triangulated categories*, Annals of Mathematics Studies 148, Princeton University
  Press (2001), Chapter 2.
-/

public section

namespace CategoryTheory

open Limits Pretriangulated ZeroObject

namespace ObjectProperty

variable {C : Type*} [Category* C] [HasZeroObject C] [Preadditive C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] (P : ObjectProperty C)

/-- The zero objects of a pretriangulated category form a triangulated subcategory. -/
instance : ObjectProperty.IsTriangulated (IsZero (C := C)) where
  isStableUnderShiftBy a := ⟨fun _ hX ↦ (shiftFunctor C a).map_isZero hX⟩
  toIsTriangulatedClosed₂ := .mk' fun T hT h₁ h₃ ↦ Triangle.isZero₂_of_isZero₁₃ T hT h₁ h₃

/-- A triangle functor inverts the morphisms whose cone lies in `P` if and only if it sends every
object of `P` to a zero object. With the localization universal property, this identifies the
triangle functors that factor through the Verdier quotient by `P`. -/
theorem trW_isInvertedBy_iff {E : Type*} [Category* E] [HasZeroObject E] [Preadditive E]
    [HasShift E ℤ] [∀ n : ℤ, (shiftFunctor E n).Additive] [Pretriangulated E]
    (F : C ⥤ E) [F.CommShift ℤ] [F.IsTriangulated] :
    P.trW.IsInvertedBy F ↔ ∀ X, P X → IsZero (F.obj X) := by
  refine ⟨fun hF X hX ↦ ?_, fun hF X Y f ⟨Z, g, h, hT, hZ⟩ ↦
    (Triangle.isZero₃_iff_isIso₁ _ (F.map_distinguished _ hT)).1 (hF Z hZ)⟩
  have : IsIso (F.map (0 : 0 ⟶ X)) := hF _ (trW.mk P (contractible_distinguished₁ X) hX)
  exact (F.map_isZero (isZero_zero C)).of_iso (asIso (F.map (0 : 0 ⟶ X))).symm

namespace TrWLocalization

variable {D : Type*} [Category* D] (L : C ⥤ D) [L.IsLocalization P.trW] [HasZeroMorphisms D]
  [L.PreservesZeroMorphisms]

include P in
/-- An object of `P` becomes zero in the Verdier localization at `P`. -/
theorem isZero_obj {X : C} (hX : P X) : IsZero (L.obj X) := by
  have : IsIso (L.map (0 : 0 ⟶ X)) :=
    Localization.inverts L P.trW _ (trW.mk P (contractible_distinguished₁ X) hX)
  exact (L.map_isZero (isZero_zero C)).of_iso (asIso (L.map (0 : 0 ⟶ X))).symm

include P in
/-- **The kernel of the Verdier localization.** If `P` is a thick triangulated subcategory of a
triangulated category, an object becomes zero in the Verdier localization at `P` if and only if
it belongs to `P`. -/
theorem isZero_obj_iff [IsTriangulated C] [P.IsTriangulated] [P.IsStableUnderRetracts]
    (X : C) : IsZero (L.obj X) ↔ P X := by
  refine ⟨fun hX ↦ ?_, isZero_obj P L⟩
  -- Some `s : X ⟶ Z` in `P.trW` satisfies `𝟙 X ≫ s = 0 ≫ s`, so `s = 0`. The cone of the zero
  -- morphism `X ⟶ Z` is `Z ⊞ X⟦1⟧`, so `X⟦1⟧` is a retract of an object of `P`.
  obtain ⟨Z, s, hs, hs0⟩ := (MorphismProperty.map_eq_iff_postcomp L P.trW (𝟙 X) 0).1
    (by rw [L.map_zero]; exact hX.eq_of_src _ _)
  rw [Category.id_comp, zero_comp] at hs0
  obtain ⟨W, g, h, hT, hW⟩ := hs
  obtain ⟨e, -, -⟩ := exists_iso_binaryBiproduct_of_distTriang _ (rot_of_distTriang _ hT)
    (by subst hs0; exact neg_eq_zero.2 ((shiftFunctor C (1 : ℤ)).map_zero X Z))
  have hX₁ : P (Triangle.mk s g h).rotate.obj₃ := P.prop_of_retract
    { i := biprod.inr ≫ e.inv
      r := e.hom ≫ biprod.snd
      retract := by simp } hW
  exact (P.prop_shift_iff_of_isStableUnderShift X (1 : ℤ)).1 hX₁

end TrWLocalization

variable {P} {Q : ObjectProperty C}

/-- For `P ≤ Q`, the identity functor of `C`, as a morphism of localizers from the morphisms with
cone in `P` to the morphisms with cone in `Q`. It induces the comparison functor from the
Verdier quotient by `P` to the Verdier quotient by `Q`. -/
def trWLocalizerMorphismOfLE (h : P ≤ Q) : LocalizerMorphism P.trW Q.trW where
  functor := 𝟭 C
  map := trW_monotone h

/-- The localizer morphism `trWLocalizerMorphismOfLE h` is given by the identity functor. -/
@[simp]
theorem trWLocalizerMorphismOfLE_functor (h : P ≤ Q) :
    (trWLocalizerMorphismOfLE h).functor = 𝟭 C :=
  (rfl)

/-- The identity functor underlying `trWLocalizerMorphismOfLE h` commutes with the shift. -/
instance (h : P ≤ Q) : (trWLocalizerMorphismOfLE h).functor.CommShift ℤ :=
  inferInstanceAs ((𝟭 C).CommShift ℤ)

/-- The identity functor underlying `trWLocalizerMorphismOfLE h` is a triangle functor. -/
instance (h : P ≤ Q) : (trWLocalizerMorphismOfLE h).functor.IsTriangulated :=
  inferInstanceAs (𝟭 C).IsTriangulated

end ObjectProperty

namespace LocalizerMorphism

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

end LocalizerMorphism

end CategoryTheory
