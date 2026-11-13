/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.BifunctorAssociator

/-!
# Naturality of the totalized bifunctor associator

The associator `HomologicalComplex.mapBifunctorAssociator` on totalized triple complexes is
natural in all three inputs. This comparison is needed to identify composition of the totalized
tensor functors in the graded bimodule action.

On the way, `mapBifunctor₁₂.ι_mapBifunctorMap` and `mapBifunctor₂₃.ι_mapBifunctorMap` compute
the maps of totalized triple complexes induced by three morphisms of complexes on each summand.

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

/-- The map on totalized triple complexes induced by `f₁`, `f₂` and `f₃`, restricted to the
summand of `mapBifunctor (mapBifunctor K₁ K₂ F₁₂ c₁₂) K₃ G c₄` indexed by `(p, q, r)`. -/
@[reassoc (attr := simp)]
theorem mapBifunctor₁₂.ι_mapBifunctorMap (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂) (f₃ : K₃ ⟶ L₃)
    (p : ι₁) (q : ι₂) (r : ι₃) (j : ι₄)
    (h : ComplexShape.r c₁ c₂ c₃ c₁₂ c₄ (p, q, r) = j) :
    mapBifunctor₁₂.ι F₁₂ G K₁ K₂ K₃ c₁₂ c₄ p q r j h ≫
        (mapBifunctorMap (mapBifunctorMap f₁ f₂ F₁₂ c₁₂) f₃ G c₄).f j =
      (G.map ((F₁₂.map (f₁.f p)).app (K₂.X q))).app (K₃.X r) ≫
        (G.map ((F₁₂.obj (L₁.X p)).map (f₂.f q))).app (K₃.X r) ≫
          (G.obj ((F₁₂.obj (L₁.X p)).obj (L₂.X q))).map (f₃.f r) ≫
            mapBifunctor₁₂.ι F₁₂ G L₁ L₂ L₃ c₁₂ c₄ p q r j h := by
  rw [mapBifunctor₁₂.ι_eq F₁₂ G K₁ K₂ K₃ c₁₂ c₄ p q r _ j rfl (by rw [← h]; rfl),
    mapBifunctor₁₂.ι_eq F₁₂ G L₁ L₂ L₃ c₁₂ c₄ p q r _ j rfl (by rw [← h]; rfl)]
  simp only [Category.assoc, ← NatTrans.comp_app_assoc, ← G.map_comp,
    _root_.HomologicalComplex.ι_mapBifunctorMap]
  simp

omit [DecidableEq ι₁₂] in
/-- The map on totalized triple complexes induced by `f₁`, `f₂` and `f₃`, restricted to the
summand of `mapBifunctor K₁ (mapBifunctor K₂ K₃ G₂₃ c₂₃) F c₄` indexed by `(p, q, r)`. -/
@[reassoc (attr := simp)]
theorem mapBifunctor₂₃.ι_mapBifunctorMap (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂) (f₃ : K₃ ⟶ L₃)
    (p : ι₁) (q : ι₂) (r : ι₃) (j : ι₄)
    (h : ComplexShape.r c₁ c₂ c₃ c₁₂ c₄ (p, q, r) = j) :
    mapBifunctor₂₃.ι F G₂₃ K₁ K₂ K₃ c₁₂ c₂₃ c₄ p q r j h ≫
        (mapBifunctorMap f₁ (mapBifunctorMap f₂ f₃ G₂₃ c₂₃) F c₄).f j =
      (F.map (f₁.f p)).app ((G₂₃.obj (K₂.X q)).obj (K₃.X r)) ≫
        (F.obj (L₁.X p)).map ((G₂₃.map (f₂.f q)).app (K₃.X r)) ≫
          (F.obj (L₁.X p)).map ((G₂₃.obj (L₂.X q)).map (f₃.f r)) ≫
            mapBifunctor₂₃.ι F G₂₃ L₁ L₂ L₃ c₁₂ c₂₃ c₄ p q r j h := by
  rw [mapBifunctor₂₃.ι_eq F G₂₃ K₁ K₂ K₃ c₁₂ c₂₃ c₄ p q r _ j rfl
      (by rw [← ComplexShape.assoc c₁ c₂ c₃ c₁₂ c₂₃ c₄]; exact h),
    mapBifunctor₂₃.ι_eq F G₂₃ L₁ L₂ L₃ c₁₂ c₂₃ c₄ p q r _ j rfl
      (by rw [← ComplexShape.assoc c₁ c₂ c₃ c₁₂ c₂₃ c₄]; exact h)]
  simp [← Functor.map_comp_assoc, -Functor.map_comp]

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
  apply mapBifunctor₁₂.hom_ext
  intro p q r h
  have h₁ := NatTrans.naturality_app_app associator.hom (f₁.f p) (K₂.X q) (K₃.X r)
  have h₂ := NatTrans.naturality_app (associator.hom.app (L₁.X p)) (K₃.X r) (f₂.f q)
  dsimp at h₁ h₂
  simp [mapBifunctorAssociator, reassoc_of% h₁, reassoc_of% h₂]

/-- The inverse totalized associator is natural in all three complexes. -/
@[reassoc]
theorem mapBifunctorAssociator_inv_naturality
    (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂) (f₃ : K₃ ⟶ L₃) :
    mapBifunctorMap f₁ (mapBifunctorMap f₂ f₃ G₂₃ c₂₃) F c₄ ≫
        (mapBifunctorAssociator associator L₁ L₂ L₃ c₁₂ c₂₃ c₄).inv =
      (mapBifunctorAssociator associator K₁ K₂ K₃ c₁₂ c₂₃ c₄).inv ≫
        mapBifunctorMap (mapBifunctorMap f₁ f₂ F₁₂ c₁₂) f₃ G c₄ := by
  simp [Iso.comp_inv_eq, mapBifunctorAssociator_naturality]

end TauCeti.HomologicalComplex
