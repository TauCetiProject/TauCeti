/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence

/-!
# Evaluating the short complex of diagrams associated to a diagram of short complexes

Mathlib's `CategoryTheory.ShortComplex.functorEquivalence` identifies the category of short
complexes in `J ⥤ C` with the functor category `J ⥤ ShortComplex C`. This file packages the
component at `j : J` of its counit on `F : J ⥤ ShortComplex C` as the isomorphism
`ShortComplex.diagramEvaluationIso F j` from
`((functorEquivalence J C).inverse.obj F).map ((evaluation J C).obj j)` to `F.obj j`, together
with its `@[simp]` component lemmas (`τ₁`, `τ₂`, `τ₃`) and naturality in `j`.
-/

public section

namespace CategoryTheory.ShortComplex

variable {C J : Type*} [Category* C] [Limits.HasZeroMorphisms C] [Category* J]

/-- Evaluating the short complex of diagrams attached to `F : J ⥤ ShortComplex C` at `j` gives
back `F.obj j`. This is the component at `j` of the counit of `ShortComplex.functorEquivalence`,
stated with the evaluated short complex as its source so that later composites are well typed. -/
def diagramEvaluationIso (F : J ⥤ ShortComplex C) (j : J) :
    ((functorEquivalence J C).inverse.obj F).map ((evaluation J C).obj j) ≅ F.obj j :=
  ((functorEquivalence J C).counitIso.app F).app j

/-- The first component of the forward morphism of `ShortComplex.diagramEvaluationIso` is the
identity. -/
@[simp]
theorem diagramEvaluationIso_hom_τ₁ (F : J ⥤ ShortComplex C) (j : J) :
    (diagramEvaluationIso F j).hom.τ₁ = 𝟙 (F.obj j).X₁ := by rfl

/-- The second component of the forward morphism of `ShortComplex.diagramEvaluationIso` is the
identity. -/
@[simp]
theorem diagramEvaluationIso_hom_τ₂ (F : J ⥤ ShortComplex C) (j : J) :
    (diagramEvaluationIso F j).hom.τ₂ = 𝟙 (F.obj j).X₂ := by rfl

/-- The third component of the forward morphism of `ShortComplex.diagramEvaluationIso` is the
identity. -/
@[simp]
theorem diagramEvaluationIso_hom_τ₃ (F : J ⥤ ShortComplex C) (j : J) :
    (diagramEvaluationIso F j).hom.τ₃ = 𝟙 (F.obj j).X₃ := by rfl

/-- The first component of the inverse morphism of `ShortComplex.diagramEvaluationIso` is the
identity. -/
@[simp]
theorem diagramEvaluationIso_inv_τ₁ (F : J ⥤ ShortComplex C) (j : J) :
    (diagramEvaluationIso F j).inv.τ₁ = 𝟙 (F.obj j).X₁ := by rfl

/-- The second component of the inverse morphism of `ShortComplex.diagramEvaluationIso` is the
identity. -/
@[simp]
theorem diagramEvaluationIso_inv_τ₂ (F : J ⥤ ShortComplex C) (j : J) :
    (diagramEvaluationIso F j).inv.τ₂ = 𝟙 (F.obj j).X₂ := by rfl

/-- The third component of the inverse morphism of `ShortComplex.diagramEvaluationIso` is the
identity. -/
@[simp]
theorem diagramEvaluationIso_inv_τ₃ (F : J ⥤ ShortComplex C) (j : J) :
    (diagramEvaluationIso F j).inv.τ₃ = 𝟙 (F.obj j).X₃ := by rfl

/-- Naturality of the forward morphism of `ShortComplex.diagramEvaluationIso`. -/
@[reassoc]
theorem diagramEvaluationIso_hom_naturality (F : J ⥤ ShortComplex C) {X Y : J} (f : X ⟶ Y) :
    ((functorEquivalence J C).inverse.obj F).mapNatTrans ((evaluation J C).map f) ≫
        (diagramEvaluationIso F Y).hom =
      (diagramEvaluationIso F X).hom ≫ F.map f :=
  ((functorEquivalence J C).counitIso.app F).hom.naturality f

/-- Naturality of the inverse morphism of `ShortComplex.diagramEvaluationIso`. -/
@[reassoc]
theorem diagramEvaluationIso_inv_naturality (F : J ⥤ ShortComplex C) {X Y : J} (f : X ⟶ Y) :
    F.map f ≫ (diagramEvaluationIso F Y).inv =
      (diagramEvaluationIso F X).inv ≫
        ((functorEquivalence J C).inverse.obj F).mapNatTrans ((evaluation J C).map f) := by
  rw [Iso.comp_inv_eq, Category.assoc, diagramEvaluationIso_hom_naturality, Iso.inv_hom_id_assoc]

end CategoryTheory.ShortComplex
