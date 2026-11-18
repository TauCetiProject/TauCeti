/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives

/-!
# Absoluteness of derived functors constructed from derivability structures

When a localizer morphism `Φ : LocalizerMorphism W₁ W₂` is a left (or right) derivability
structure and `h : Φ.Derives F` holds for `F : C₂ ⥤ H`, any left (or right) derived functor of
`F` is *absolute*: postcomposing with an arbitrary functor `G : H ⥤ H'` preserves `Φ.Derives`
(via `CategoryTheory.MorphismProperty.IsInvertedBy.of_comp`) and sends derived functors of `F` to
derived functors of `F ⋙ G`
(`CategoryTheory.LocalizerMorphism.Derives.isLeftDerivedFunctor_comp` and
`CategoryTheory.LocalizerMorphism.Derives.isRightDerivedFunctor_comp`).

The comparison natural transformations match the hypotheses of
`CategoryTheory.Adjunction.derived`, so an adjunction whose left adjoint is derived via a left
derivability structure and whose right adjoint is derived via a right derivability structure (or by
inverting weak equivalences) descends directly to an adjunction on the localized categories.

This extends Joël Riou's `Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives`.

## References

* [Bruno Kahn and Georges Maltsiniotis, *Structures de dérivabilité*][KahnMaltsiniotis2008]
* [Georges Maltsiniotis, *Le théorème de Quillen, d'adjonction des foncteurs dérivés,
  revisité*][Maltsiniotis2007]
-/

public section

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

namespace CategoryTheory

variable {C₁ : Type u₁} {C₂ : Type u₂} {H : Type u₃} {D₂ : Type u₄} {H' : Type u₅}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} H] [Category.{v₄} D₂] [Category.{v₅} H']
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}

namespace LocalizerMorphism.Derives

variable {Φ : LocalizerMorphism W₁ W₂} {F : C₂ ⥤ H} (h : Φ.Derives F) (G : H ⥤ H')

section Right

variable [Φ.IsRightDerivabilityStructure] {L₂ : C₂ ⥤ D₂} [L₂.IsLocalization W₂]
  {RF : D₂ ⥤ H} (α : F ⟶ L₂ ⋙ RF) [RF.IsRightDerivedFunctor α W₂]

include h in
/-- A right derived functor obtained from a right derivability structure is absolute: its
composite with any functor `G : H ⥤ H'` is a right derived functor of `F ⋙ G`. -/
lemma isRightDerivedFunctor_comp :
    (RF ⋙ G).IsRightDerivedFunctor
      (Functor.whiskerRight α G ≫ (Functor.associator L₂ RF G).hom) W₂ := by
  have h' : Φ.Derives (F ⋙ G) := MorphismProperty.IsInvertedBy.of_comp W₁ (Φ.functor ⋙ F) h G
  refine h'.isRightDerivedFunctor_of_isIso _ fun X₁ ↦ ?_
  have : IsIso (α.app (Φ.functor.obj X₁)) := h.isIso_of_isRightDerivedFunctor α X₁
  dsimp
  rw [Category.comp_id]
  infer_instance

end Right

section Left

variable [Φ.IsLeftDerivabilityStructure] {L₂ : C₂ ⥤ D₂} [L₂.IsLocalization W₂]
  {LF : D₂ ⥤ H} (α : L₂ ⋙ LF ⟶ F) [LF.IsLeftDerivedFunctor α W₂]

include h in
/-- A left derived functor obtained from a left derivability structure is absolute: its
composite with any functor `G : H ⥤ H'` is a left derived functor of `F ⋙ G`. -/
lemma isLeftDerivedFunctor_comp :
    (LF ⋙ G).IsLeftDerivedFunctor
      ((Functor.associator L₂ LF G).inv ≫ Functor.whiskerRight α G) W₂ := by
  have h' : Φ.Derives (F ⋙ G) := MorphismProperty.IsInvertedBy.of_comp W₁ (Φ.functor ⋙ F) h G
  refine h'.isLeftDerivedFunctor_of_isIso _ fun X₁ ↦ ?_
  have : IsIso (α.app (Φ.functor.obj X₁)) := h.isIso' α X₁
  dsimp
  rw [Category.id_comp]
  infer_instance

end Left

end LocalizerMorphism.Derives

end CategoryTheory
