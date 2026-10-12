/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.BifunctorAssociator

/-!
# Naturality of the totalized bifunctor associator

The associator on cochain complexes is natural in all three inputs. This
comparison is needed to identify composition of the totalized tensor functors
in the graded bimodule action.
-/

public section
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

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
  {K₁ L₁ : CochainComplex C₁ ℤ} {K₂ L₂ : CochainComplex C₂ ℤ}
  {K₃ L₃ : CochainComplex C₃ ℤ}
  [∀ (K : CochainComplex C₁ ℤ) (L : CochainComplex C₂ ℤ),
    HasMapBifunctor K L F₁₂ (.up ℤ)]
  [∀ (K : CochainComplex C₁₂ ℤ) (L : CochainComplex C₃ ℤ),
    HasMapBifunctor K L G (.up ℤ)]
  [∀ (K : CochainComplex C₂ ℤ) (L : CochainComplex C₃ ℤ),
    HasMapBifunctor K L G₂₃ (.up ℤ)]
  [∀ (K : CochainComplex C₁ ℤ) (L : CochainComplex C₂₃ ℤ),
    HasMapBifunctor K L F (.up ℤ)]

private theorem ι_map₁₂ (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂) (f₃ : K₃ ⟶ L₃)
    (p q r j : ℤ) (h : ComplexShape.r (.up ℤ) (.up ℤ) (.up ℤ) (.up ℤ) (.up ℤ)
      (p, q, r) = j) :
    mapBifunctor₁₂.ι F₁₂ G K₁ K₂ K₃ (.up ℤ) (.up ℤ) p q r j h ≫
        (mapBifunctorMap (mapBifunctorMap f₁ f₂ F₁₂ (.up ℤ)) f₃ G (.up ℤ)).f j =
      (G.map ((F₁₂.map (f₁.f p)).app (K₂.X q) ≫
          (F₁₂.obj (L₁.X p)).map (f₂.f q))).app (K₃.X r) ≫
        (G.obj ((F₁₂.obj (L₁.X p)).obj (L₂.X q))).map (f₃.f r) ≫
          mapBifunctor₁₂.ι F₁₂ G L₁ L₂ L₃ (.up ℤ) (.up ℤ) p q r j h := by
  rw [mapBifunctor₁₂.ι_eq F₁₂ G K₁ K₂ K₃ (.up ℤ) (.up ℤ) p q r (p + q) j rfl
      (by rw [← h]; rfl),
    Category.assoc, ι_mapBifunctorMap]
  rw [← NatTrans.comp_app_assoc, ← G.map_comp, ι_mapBifunctorMap]
  simp only [Functor.map_comp, NatTrans.comp_app, Category.assoc]
  rw [← NatTrans.naturality_assoc,
    ← mapBifunctor₁₂.ι_eq F₁₂ G L₁ L₂ L₃ (.up ℤ) (.up ℤ) p q r (p + q) j rfl
      (by rw [← h]; rfl)]

private theorem ι_map₂₃ (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂) (f₃ : K₃ ⟶ L₃)
    (p q r j : ℤ) (h : ComplexShape.r (.up ℤ) (.up ℤ) (.up ℤ) (.up ℤ) (.up ℤ)
      (p, q, r) = j) :
    mapBifunctor₂₃.ι F G₂₃ K₁ K₂ K₃ (.up ℤ) (.up ℤ) (.up ℤ) p q r j h ≫
        (mapBifunctorMap f₁ (mapBifunctorMap f₂ f₃ G₂₃ (.up ℤ)) F (.up ℤ)).f j =
      (F.map (f₁.f p)).app ((G₂₃.obj (K₂.X q)).obj (K₃.X r)) ≫
        (F.obj (L₁.X p)).map ((G₂₃.map (f₂.f q)).app (K₃.X r) ≫
          (G₂₃.obj (L₂.X q)).map (f₃.f r)) ≫
            mapBifunctor₂₃.ι F G₂₃ L₁ L₂ L₃ (.up ℤ) (.up ℤ) (.up ℤ) p q r j h := by
  rw [mapBifunctor₂₃.ι_eq F G₂₃ K₁ K₂ K₃ (.up ℤ) (.up ℤ) (.up ℤ)
      p q r (q + r) j rfl (by dsimp [ComplexShape.r] at h ⊢; omega),
    Category.assoc, ι_mapBifunctorMap]
  rw [NatTrans.naturality_assoc, ← Functor.map_comp_assoc, ι_mapBifunctorMap]
  simp only [Functor.map_comp, Category.assoc]
  rw [← mapBifunctor₂₃.ι_eq F G₂₃ L₁ L₂ L₃ (.up ℤ) (.up ℤ) (.up ℤ)
      p q r (q + r) j rfl (by dsimp [ComplexShape.r] at h ⊢; omega)]

variable
  [∀ (K : CochainComplex C₁ ℤ) (L : CochainComplex C₂ ℤ) (P : CochainComplex C₃ ℤ),
    HasGoodTrifunctor₁₂Obj F₁₂ G K L P (.up ℤ) (.up ℤ)]
  [∀ (K : CochainComplex C₁ ℤ) (L : CochainComplex C₂ ℤ) (P : CochainComplex C₃ ℤ),
    HasGoodTrifunctor₂₃Obj F G₂₃ K L P (.up ℤ) (.up ℤ) (.up ℤ)]

/-- The totalized cochain associator is natural in all three complexes. -/
@[reassoc]
theorem mapCochainBifunctorAssociator_naturality
    (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂) (f₃ : K₃ ⟶ L₃) :
    mapBifunctorMap (mapBifunctorMap f₁ f₂ F₁₂ (.up ℤ)) f₃ G (.up ℤ) ≫
        (mapBifunctorAssociator associator L₁ L₂ L₃ (.up ℤ) (.up ℤ) (.up ℤ)).hom =
      (mapBifunctorAssociator associator K₁ K₂ K₃ (.up ℤ) (.up ℤ) (.up ℤ)).hom ≫
        mapBifunctorMap f₁ (mapBifunctorMap f₂ f₃ G₂₃ (.up ℤ)) F (.up ℤ) := by
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

/-- The inverse totalized cochain associator is natural in all three complexes. -/
@[reassoc]
theorem mapCochainBifunctorAssociator_inv_naturality
    (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂) (f₃ : K₃ ⟶ L₃) :
    mapBifunctorMap f₁ (mapBifunctorMap f₂ f₃ G₂₃ (.up ℤ)) F (.up ℤ) ≫
        (mapBifunctorAssociator associator L₁ L₂ L₃ (.up ℤ) (.up ℤ) (.up ℤ)).inv =
      (mapBifunctorAssociator associator K₁ K₂ K₃ (.up ℤ) (.up ℤ) (.up ℤ)).inv ≫
        mapBifunctorMap (mapBifunctorMap f₁ f₂ F₁₂ (.up ℤ)) f₃ G (.up ℤ) := by
  rw [← cancel_mono
    (mapBifunctorAssociator associator L₁ L₂ L₃ (.up ℤ) (.up ℤ) (.up ℤ)).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    mapCochainBifunctorAssociator_naturality, Iso.inv_hom_id_assoc]

end HomologicalComplex
