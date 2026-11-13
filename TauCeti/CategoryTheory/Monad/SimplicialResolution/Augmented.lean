/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monad.SimplicialResolution.Basic
public import Mathlib.CategoryTheory.Monad.Adjunction
public import Mathlib.AlgebraicTopology.ExtraDegeneracy

/-!
# Augmented comonad resolutions

The counit augments the simplicial resolution of any comonad to the original
object. If the comonad comes from an adjunction, applying the right adjoint gives
an extra degeneracy: the unit inserts an outermost layer. In particular, Mathlib's
`SimplicialObject.Augmented.ExtraDegeneracy.homotopy` contracts the forgotten
resolution onto its augmentation object.

## References

* The Stacks Project, Definition 92.3.1 (Tag 08PM), for the polynomial example.
* Mathlib's `SimplicialObject.Augmented.ExtraDegeneracy` supplies the contraction API.
-/

public noncomputable section

open CategoryTheory Opposite Functor

universe v u

namespace CategoryTheory.Comonad

variable {C : Type u} [Category.{v} C] (G : Comonad C)

-- Keep morphism computation equations named: their dependent categorical carriers
-- need not have a robust simp normal form in importing modules.

/-- Collapse all layers of an iterated comonad with its counit. -/
def resolutionCounit : ∀ n : ℕ, G.resolutionStage n ⟶ 𝟭 C
  | 0 => 𝟙 _
  | n + 1 => whiskerLeft (G.resolutionStage n) G.ε ≫ resolutionCounit n

lemma resolutionCounit_zero_app (X : C) :
    (G.resolutionCounit 0).app X = 𝟙 X := (rfl)

/-- Remove the outermost layer before collapsing the remaining layers. -/
lemma resolutionCounit_succ_app (n : ℕ) (X : C) :
    (G.resolutionCounit (n + 1)).app X =
      G.ε.app ((G.resolutionStage n).obj X) ≫ (G.resolutionCounit n).app X := (rfl)

/-- Collapsing all layers is compatible with a counit in any position. -/
@[reassoc] lemma resolutionFace_comp_resolutionCounit (n : ℕ) (i : Fin (n + 1)) :
    G.resolutionFace n i ≫ G.resolutionCounit n = G.resolutionCounit (n + 1) := by
  induction n with
  | zero =>
    have hi : i = 0 := Fin.eq_zero i
    subst i
    ext X
    simp only [NatTrans.comp_app, resolutionFace_zero_app, resolutionCounit_zero_app,
      resolutionCounit_succ_app]
    dsimp only [resolutionStage, Functor.id_obj]
  | succ n ih =>
    ext X
    induction i using Fin.cases with
    | zero =>
      simp only [NatTrans.comp_app, resolutionFace_zero_app, resolutionCounit_succ_app]
      rfl
    | succ i =>
      simp only [NatTrans.comp_app, resolutionFace_succ_app, resolutionCounit_succ_app]
      dsimp only [resolutionStage, Functor.comp_obj, Functor.id_obj]
      rw [← Category.assoc, G.ε.naturality, Category.assoc]
      exact congrArg (G.ε.app _ ≫ ·) (congr_app (ih i) X)

/-- Duplicating a layer does not change its total collapse. -/
@[reassoc] lemma resolutionDegeneracy_comp_resolutionCounit (n : ℕ) (i : Fin (n + 1)) :
    G.resolutionDegeneracy n i ≫ G.resolutionCounit (n + 2) =
      G.resolutionCounit (n + 1) := by
  rw [← G.resolutionFace_comp_resolutionCounit (n + 1) i.castSucc,
    ← Category.assoc, G.resolutionDegeneracy_comp_resolutionFace_self]
  simp

private lemma resolutionPresentation_map_comp_resolutionCounit
    {a b : SimplexCategoryGenRel} (f : a ⟶ b) :
    (G.resolutionPresentation.map f).unop ≫ G.resolutionCounit (a.len + 1) =
      G.resolutionCounit (b.len + 1) := by
  -- Reassociation crosses the dependent object presentation; `erw` aligns those endpoints.
  induction f using SimplexCategoryGenRel.hom_induction with
  | id =>
    rw [Functor.map_id, CategoryTheory.unop_id]
    exact Category.id_comp _
  | comp_δ f i ih =>
    rw [Functor.map_comp]
    erw [CategoryTheory.unop_comp]
    erw [Category.assoc, ih, resolutionPresentation_map_δ, Quiver.Hom.unop_op]
    exact G.resolutionFace_comp_resolutionCounit _ _
  | comp_σ f i ih =>
    rw [Functor.map_comp]
    erw [CategoryTheory.unop_comp]
    erw [Category.assoc, ih, resolutionPresentation_map_σ, Quiver.Hom.unop_op]
    exact G.resolutionDegeneracy_comp_resolutionCounit _ _

/-- The counit augmentation of the simplicial resolution. -/
def simplicialResolutionAugmentation (X : C) :
    G.simplicialResolution.obj X ⟶ (SimplicialObject.const C).obj X where
  app n := (G.resolutionCounit (n.unop.len + 1)).app X
  naturality {a b} f := by
    -- Translate the presented natural transformation to its objectwise components.
    have h := congr_app (G.resolutionPresentation_map_comp_resolutionCounit
      (SimplexCategoryGenRel.fromSimplexCategory.map f.unop)) X
    dsimp only [simplicialResolution, Functor.flip_obj_map, Functor.leftOp_map,
      Functor.comp_map, Functor.const_obj_map]
    exact h.trans (Category.comp_id _).symm

/-- The augmentation in every degree collapses all comonad layers. -/
lemma simplicialResolutionAugmentation_app (X : C) (n : ℕ) :
    (G.simplicialResolutionAugmentation X).app (op (SimplexCategory.mk n)) =
      (G.resolutionCounit (n + 1)).app X := (rfl)

/-- The degree-zero augmentation is the original comonad counit. -/
lemma simplicialResolutionAugmentation_app_zero (X : C) :
    (G.simplicialResolutionAugmentation X).app (op (SimplexCategory.mk 0)) =
      G.ε.app X := by
  simp only [simplicialResolutionAugmentation_app, resolutionCounit_succ_app,
    resolutionCounit_zero_app]
  dsimp only [resolutionStage, Functor.id_obj]
  exact Category.comp_id _

/-- The simplicial resolution augmented to its original object, functorially.
The body is exposed so its dependent simplicial term carriers compute. -/
@[expose] def augmentedSimplicialResolution : C ⥤ SimplicialObject.Augmented C where
  obj X :=
    { left := G.simplicialResolution.obj X
      right := X
      hom := G.simplicialResolutionAugmentation X }
  map f :=
    { left := G.simplicialResolution.map f
      right := f
      w := by
        ext n
        exact (G.resolutionCounit (n.unop.len + 1)).naturality f }

@[simp] lemma augmentedSimplicialResolution_obj_left (X : C) :
    (G.augmentedSimplicialResolution.obj X).left = G.simplicialResolution.obj X := (rfl)

@[simp] lemma augmentedSimplicialResolution_obj_right (X : C) :
    (G.augmentedSimplicialResolution.obj X).right = X := (rfl)

lemma augmentedSimplicialResolution_obj_hom (X : C) :
    (G.augmentedSimplicialResolution.obj X).hom = G.simplicialResolutionAugmentation X := (rfl)

lemma augmentedSimplicialResolution_map_left {X Y : C} (f : X ⟶ Y) :
    (G.augmentedSimplicialResolution.map f).left = G.simplicialResolution.map f := (rfl)

lemma augmentedSimplicialResolution_map_right {X Y : C} (f : X ⟶ Y) :
    (G.augmentedSimplicialResolution.map f).right = f := (rfl)

end CategoryTheory.Comonad

namespace CategoryTheory.Adjunction

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  {L : C ⥤ D} {U : D ⥤ C} (adj : L ⊣ U)

/-- The unit supplies an extra degeneracy after applying the right adjoint to
the augmented resolution of the induced comonad. -/
def resolutionExtraDegeneracy (X : D) :
    SimplicialObject.Augmented.ExtraDegeneracy
      (((SimplicialObject.Augmented.whiskering D C).obj U).obj
        (adj.toComonad.augmentedSimplicialResolution.obj X)) where
  s' := adj.unit.app (U.obj X)
  s n := adj.unit.app (U.obj ((adj.toComonad.resolutionStage (n + 1)).obj X))
  s'_comp_ε := by
    -- Whiskering presents the degree-zero augmentation as the mapped counit.
    change adj.unit.app (U.obj X) ≫
      (U.map ((adj.toComonad.simplicialResolutionAugmentation X).app
        (op (SimplexCategory.mk 0))) ≫ 𝟙 _) = 𝟙 _
    rw [Category.comp_id, Comonad.simplicialResolutionAugmentation_app_zero]
    exact adj.right_triangle_components X
  s₀_comp_δ₁ := by
    -- Normalize the whiskered face, retaining the original comonad stage carriers.
    change adj.unit.app (U.obj (adj.toComonad.obj X)) ≫
        U.map ((adj.toComonad.simplicialResolution.obj X).δ (n := 0) 1) =
      (U.map ((adj.toComonad.simplicialResolutionAugmentation X).app
        (op (SimplexCategory.mk 0))) ≫ 𝟙 _) ≫ adj.unit.app (U.obj X)
    simp only [Comonad.simplicialResolution_δ, ← Fin.succ_zero_eq_one,
      Comonad.resolutionFace_succ_app, Comonad.resolutionFace_zero_app,
      Comonad.simplicialResolutionAugmentation_app_zero, Category.comp_id]
    exact (adj.unit.naturality (U.map (adj.counit.app X))).symm
  s_comp_δ₀ n := by
    -- The first face evaluates the outer layer inserted by the unit.
    change adj.unit.app (U.obj ((adj.toComonad.resolutionStage (n + 1)).obj X)) ≫
      U.map ((adj.toComonad.simplicialResolution.obj X).δ (n := n) 0) = 𝟙 _
    rw [Comonad.simplicialResolution_δ, Comonad.resolutionFace_zero_app]
    exact adj.right_triangle_components _
  s_comp_δ n i := by
    -- Higher faces are the comonad applied to the preceding face.
    change adj.unit.app (U.obj ((adj.toComonad.resolutionStage (n + 2)).obj X)) ≫
        U.map ((adj.toComonad.simplicialResolution.obj X).δ (n := n + 1) i.succ) =
      U.map ((adj.toComonad.simplicialResolution.obj X).δ (n := n) i) ≫
        adj.unit.app (U.obj ((adj.toComonad.resolutionStage (n + 1)).obj X))
    simp only [Comonad.simplicialResolution_δ, Comonad.resolutionFace_succ_app]
    exact (adj.unit.naturality
      (U.map ((adj.toComonad.resolutionFace (n + 1) i).app X))).symm
  s_comp_σ n i := by
    -- Higher degeneracies are the comonad applied to the preceding degeneracy.
    change adj.unit.app (U.obj ((adj.toComonad.resolutionStage (n + 1)).obj X)) ≫
        U.map ((adj.toComonad.simplicialResolution.obj X).σ (n := n + 1) i.succ) =
      U.map ((adj.toComonad.simplicialResolution.obj X).σ (n := n) i) ≫
        adj.unit.app (U.obj ((adj.toComonad.resolutionStage (n + 2)).obj X))
    simp only [Comonad.simplicialResolution_σ, Comonad.resolutionDegeneracy_succ_app]
    exact (adj.unit.naturality
      (U.map ((adj.toComonad.resolutionDegeneracy n i).app X))).symm

/-- The section in degree minus one is the adjunction unit. -/
lemma resolutionExtraDegeneracy_s' (X : D) :
    (adj.resolutionExtraDegeneracy X).s' = adj.unit.app (U.obj X) := (rfl)

/-- In every simplicial degree, the extra degeneracy is the adjunction unit. -/
lemma resolutionExtraDegeneracy_s (X : D) (n : ℕ) :
    (adj.resolutionExtraDegeneracy X).s n =
      adj.unit.app (U.obj ((adj.toComonad.resolutionStage (n + 1)).obj X)) := (rfl)

end CategoryTheory.Adjunction
