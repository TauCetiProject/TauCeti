/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.BifunctorAssociator

/-!
# Naturality of the totalized bifunctor associator

The associator on homological complexes is natural in all three inputs. This
comparison is needed to identify composition of the totalized tensor functors
in the graded bimodule action.

This extends Joël Riou's construction in `Mathlib.Algebra.Homology.BifunctorAssociator`,
using `HomologicalComplex.mapBifunctorAssociator` and its summand-inclusion equations.
-/

public section
noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace TauCeti.HomologicalComplex

universe u₁ u₂ u₃ u₁₂ u₂₃ u₄ v₁ v₂ v₃ v₁₂ v₂₃ v₄
variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃}
  {C₁₂ : Type u₁₂} {C₂₃ : Type u₂₃} {C₄ : Type u₄}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃]
  [Category.{v₁₂} C₁₂] [Category.{v₂₃} C₂₃] [Category.{v₄} C₄]
  [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [HasZeroMorphisms C₃]
  [Preadditive C₁₂] [Preadditive C₂₃] [Preadditive C₄]
  {F₁₂ : C₁ ⥤ C₂ ⥤ C₁₂} {G : C₁₂ ⥤ C₃ ⥤ C₄}
  {F : C₁ ⥤ C₂₃ ⥤ C₄} {G₂₃ : C₂ ⥤ C₃ ⥤ C₂₃}
  [F₁₂.PreservesZeroMorphisms] [∀ X, (F₁₂.obj X).PreservesZeroMorphisms]
  [G.Additive] [∀ X, (G.obj X).PreservesZeroMorphisms]
  [G₂₃.PreservesZeroMorphisms] [∀ X, (G₂₃.obj X).PreservesZeroMorphisms]
  [F.PreservesZeroMorphisms] [∀ X, (F.obj X).Additive]
  (associator : bifunctorComp₁₂ F₁₂ G ≅ bifunctorComp₂₃ F G₂₃)
  {ι₁ ι₂ ι₃ ι₁₂ ι₂₃ ι₄ : Type*}
  [DecidableEq ι₁₂] [DecidableEq ι₂₃] [DecidableEq ι₄]
  {c₁ : ComplexShape ι₁} {c₂ : ComplexShape ι₂} {c₃ : ComplexShape ι₃}
  (c₁₂ : ComplexShape ι₁₂) (c₂₃ : ComplexShape ι₂₃) (c₄ : ComplexShape ι₄)
  [TotalComplexShape c₁ c₂ c₁₂] [TotalComplexShape c₁₂ c₃ c₄]
  [TotalComplexShape c₂ c₃ c₂₃] [TotalComplexShape c₁ c₂₃ c₄]
  [ComplexShape.Associative c₁ c₂ c₃ c₁₂ c₂₃ c₄]
  {K₁ L₁ : HomologicalComplex C₁ c₁} {K₂ L₂ : HomologicalComplex C₂ c₂}
  {K₃ L₃ : HomologicalComplex C₃ c₃}
  [HasMapBifunctor K₁ K₂ F₁₂ c₁₂] [HasMapBifunctor L₁ L₂ F₁₂ c₁₂]
  [HasMapBifunctor K₂ K₃ G₂₃ c₂₃] [HasMapBifunctor L₂ L₃ G₂₃ c₂₃]
  [HasMapBifunctor (mapBifunctor K₁ K₂ F₁₂ c₁₂) K₃ G c₄]
  [HasMapBifunctor (mapBifunctor L₁ L₂ F₁₂ c₁₂) L₃ G c₄]
  [HasMapBifunctor K₁ (mapBifunctor K₂ K₃ G₂₃ c₂₃) F c₄]
  [HasMapBifunctor L₁ (mapBifunctor L₂ L₃ G₂₃ c₂₃) F c₄]

private theorem ι_map₁₂ (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂) (f₃ : K₃ ⟶ L₃)
    (p : ι₁) (q : ι₂) (r : ι₃) (j : ι₄) (h : ComplexShape.r c₁ c₂ c₃ c₁₂ c₄
      (p, q, r) = j) :
    mapBifunctor₁₂.ι F₁₂ G K₁ K₂ K₃ c₁₂ c₄ p q r j h ≫
        (mapBifunctorMap (mapBifunctorMap f₁ f₂ F₁₂ c₁₂) f₃ G c₄).f j =
      (G.map ((F₁₂.map (f₁.f p)).app (K₂.X q) ≫
          (F₁₂.obj (L₁.X p)).map (f₂.f q))).app (K₃.X r) ≫
        (G.obj ((F₁₂.obj (L₁.X p)).obj (L₂.X q))).map (f₃.f r) ≫
          mapBifunctor₁₂.ι F₁₂ G L₁ L₂ L₃ c₁₂ c₄ p q r j h := by
  rw [mapBifunctor₁₂.ι_eq F₁₂ G K₁ K₂ K₃ c₁₂ c₄ p q r
      (ComplexShape.π c₁ c₂ c₁₂ (p, q)) j rfl
      (by rw [← h]; rfl),
    Category.assoc, ι_mapBifunctorMap]
  rw [← NatTrans.comp_app_assoc, ← G.map_comp, ι_mapBifunctorMap]
  simp only [Functor.map_comp, NatTrans.comp_app, Category.assoc]
  rw [← NatTrans.naturality_assoc,
    ← mapBifunctor₁₂.ι_eq F₁₂ G L₁ L₂ L₃ c₁₂ c₄ p q r
      (ComplexShape.π c₁ c₂ c₁₂ (p, q)) j rfl
      (by rw [← h]; rfl)]

omit [DecidableEq ι₁₂] in
private theorem ι_map₂₃ (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂) (f₃ : K₃ ⟶ L₃)
    (p : ι₁) (q : ι₂) (r : ι₃) (j : ι₄) (h : ComplexShape.r c₁ c₂ c₃ c₁₂ c₄
      (p, q, r) = j) :
    mapBifunctor₂₃.ι F G₂₃ K₁ K₂ K₃ c₁₂ c₂₃ c₄ p q r j h ≫
        (mapBifunctorMap f₁ (mapBifunctorMap f₂ f₃ G₂₃ c₂₃) F c₄).f j =
      (F.map (f₁.f p)).app ((G₂₃.obj (K₂.X q)).obj (K₃.X r)) ≫
        (F.obj (L₁.X p)).map ((G₂₃.map (f₂.f q)).app (K₃.X r) ≫
          (G₂₃.obj (L₂.X q)).map (f₃.f r)) ≫
            mapBifunctor₂₃.ι F G₂₃ L₁ L₂ L₃ c₁₂ c₂₃ c₄ p q r j h := by
  rw [mapBifunctor₂₃.ι_eq F G₂₃ K₁ K₂ K₃ c₁₂ c₂₃ c₄
      p q r (ComplexShape.π c₂ c₃ c₂₃ (q, r)) j rfl
      (by rw [← ComplexShape.assoc c₁ c₂ c₃ c₁₂ c₂₃ c₄]; exact h),
    Category.assoc, ι_mapBifunctorMap]
  rw [NatTrans.naturality_assoc, ← Functor.map_comp_assoc, ι_mapBifunctorMap]
  simp only [Functor.map_comp, Category.assoc]
  rw [← mapBifunctor₂₃.ι_eq F G₂₃ L₁ L₂ L₃ c₁₂ c₂₃ c₄
      p q r (ComplexShape.π c₂ c₃ c₂₃ (q, r)) j rfl
      (by rw [← ComplexShape.assoc c₁ c₂ c₃ c₁₂ c₂₃ c₄]; exact h)]

variable
  [HasGoodTrifunctor₁₂Obj F₁₂ G K₁ K₂ K₃ c₁₂ c₄]
  [HasGoodTrifunctor₁₂Obj F₁₂ G L₁ L₂ L₃ c₁₂ c₄]
  [HasGoodTrifunctor₂₃Obj F G₂₃ K₁ K₂ K₃ c₁₂ c₂₃ c₄]
  [HasGoodTrifunctor₂₃Obj F G₂₃ L₁ L₂ L₃ c₁₂ c₂₃ c₄]

/-- The totalized associator is natural in all three complexes. -/
@[reassoc]
theorem mapBifunctorAssociator_naturality
    (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂) (f₃ : K₃ ⟶ L₃) :
    mapBifunctorMap (mapBifunctorMap f₁ f₂ F₁₂ c₁₂) f₃ G c₄ ≫
        (mapBifunctorAssociator associator L₁ L₂ L₃ c₁₂ c₂₃ c₄).hom =
      (mapBifunctorAssociator associator K₁ K₂ K₃ c₁₂ c₂₃ c₄).hom ≫
        mapBifunctorMap f₁ (mapBifunctorMap f₂ f₃ G₂₃ c₂₃) F c₄ := by
  ext j : 1
  simp only [comp_f, mapBifunctorAssociator, Hom.isoOfComponents_hom_f]
  apply mapBifunctor₁₂.hom_ext
  intro p q r h
  rw [← Category.assoc, ι_map₁₂]
  simp only [Category.assoc]
  rw [ι_mapBifunctorAssociatorX_hom, ι_mapBifunctorAssociatorX_hom_assoc, ι_map₂₃]
  have h₁ := NatTrans.naturality_app_app associator.hom (f₁.f p) (K₂.X q) (K₃.X r)
  have h₂ := NatTrans.naturality_app (associator.hom.app (L₁.X p)) (K₃.X r) (f₂.f q)
  have h₃ := ((associator.hom.app (L₁.X p)).app (L₂.X q)).naturality (f₃.f r)
  dsimp at h₁ h₂ h₃
  simp only [Functor.map_comp, NatTrans.comp_app, Category.assoc]
  rw [reassoc_of% h₃, reassoc_of% h₂, reassoc_of% h₁]

/-- The inverse totalized associator is natural in all three complexes. -/
@[reassoc]
theorem mapBifunctorAssociator_inv_naturality
    (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂) (f₃ : K₃ ⟶ L₃) :
    mapBifunctorMap f₁ (mapBifunctorMap f₂ f₃ G₂₃ c₂₃) F c₄ ≫
        (mapBifunctorAssociator associator L₁ L₂ L₃ c₁₂ c₂₃ c₄).inv =
      (mapBifunctorAssociator associator K₁ K₂ K₃ c₁₂ c₂₃ c₄).inv ≫
        mapBifunctorMap (mapBifunctorMap f₁ f₂ F₁₂ c₁₂) f₃ G c₄ := by
  rw [← cancel_mono
    (mapBifunctorAssociator associator L₁ L₂ L₃ c₁₂ c₂₃ c₄).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    mapBifunctorAssociator_naturality, Iso.inv_hom_id_assoc]

end TauCeti.HomologicalComplex
