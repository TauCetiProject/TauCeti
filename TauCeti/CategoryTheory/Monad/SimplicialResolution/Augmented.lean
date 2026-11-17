/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monad.SimplicialResolution.Basic
public import Mathlib.CategoryTheory.Monad.Adjunction
public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import TauCeti.AlgebraicTopology.SimplicialObject.Op

/-!
# Augmented comonad resolutions

The counit augments the simplicial resolution of any comonad to the original
object. If the comonad comes from an adjunction, applying the right adjoint gives
an extra degeneracy: the unit inserts an outermost layer. In particular, Mathlib's
`SimplicialObject.Augmented.ExtraDegeneracy.homotopy` contracts the forgotten
resolution onto its augmentation object.

Without applying any functor, a section `f : X ⟶ G X` of the counit at `X` splits the
resolution of `X` itself along its last faces: `G^(n+1) f` inserts an innermost layer
(`CategoryTheory.Comonad.resolutionInnerMap`). Mathlib's extra degeneracies split along the
zeroth faces instead, so this splitting is an extra degeneracy of the resolution reversed by
`CategoryTheory.SimplicialObject.Augmented.opFunctor`
(`CategoryTheory.Comonad.resolutionExtraDegeneracyOfSection`). Free objects `G W` carry such a
section, the comultiplication at `W` (`CategoryTheory.Comonad.freeResolutionExtraDegeneracy`).
This is the comonadic form of the contractibility of resolutions of free objects; see Barr and
Beck, *Homology and standard constructions*, §1.

## References

* The Stacks Project, Definition 92.3.1 (Tag 08PM), for the polynomial example.
* Mathlib's `SimplicialObject.Augmented.ExtraDegeneracy` supplies the contraction API.
* M. Barr and J. Beck, *Homology and standard constructions*, in: Seminar on Triples and
  Categorical Homology Theory, Lecture Notes in Math. 80, Springer (1969), §1.
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

/-- Faces of the augmented resolution are the iterated counits. This is
`simplicialResolution_δ` in the form in which faces of augmented objects appear, for instance in
extra degeneracies, where the simplicial part cannot be rewritten in place. -/
lemma augmentedSimplicialResolution_obj_left_δ (X : C) {n : ℕ} (i : Fin (n + 2)) :
    (G.augmentedSimplicialResolution.obj X).left.δ i = (G.resolutionFace (n + 1) i).app X :=
  G.simplicialResolution_δ X i

/-- Degeneracies of the augmented resolution are the iterated comultiplications, in the form
in which they appear in statements about augmented objects. -/
lemma augmentedSimplicialResolution_obj_left_σ (X : C) {n : ℕ} (i : Fin (n + 1)) :
    (G.augmentedSimplicialResolution.obj X).left.σ i = (G.resolutionDegeneracy n i).app X :=
  G.simplicialResolution_σ X i

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

namespace CategoryTheory.Comonad

variable {C : Type u} [Category.{v} C] (G : Comonad C) {X : C}

/-- Apply `f : X ⟶ G X` beneath `n` layers of the comonad. This is `G^n f`, read as a map
`G^n X ⟶ G^(n+1) X` whose new layer is the innermost one. -/
def resolutionInnerMap (f : X ⟶ G.obj X) :
    ∀ n : ℕ, (G.resolutionStage n).obj X ⟶ (G.resolutionStage (n + 1)).obj X
  | 0 => f
  | n + 1 => G.map (resolutionInnerMap f n)

lemma resolutionInnerMap_zero (f : X ⟶ G.obj X) : G.resolutionInnerMap f 0 = f := (rfl)

lemma resolutionInnerMap_succ (f : X ⟶ G.obj X) (n : ℕ) :
    G.resolutionInnerMap f (n + 1) = G.map (G.resolutionInnerMap f n) := (rfl)

/-- If `f` is a section of the counit at `X`, then the inner map is a section of the last face,
which applies the counit to the innermost layer. -/
@[reassoc] lemma resolutionInnerMap_comp_resolutionFace_last {f : X ⟶ G.obj X}
    (hf : f ≫ G.ε.app X = 𝟙 X) :
    ∀ n : ℕ, G.resolutionInnerMap f n ≫ (G.resolutionFace n (Fin.last n)).app X = 𝟙 _
  | 0 => by
    rw [Fin.last_zero, resolutionFace_zero_app]
    exact hf
  | n + 1 => by
    -- Apply `G` to the previous degree. `Functor.map_comp` cannot be rewritten backwards in the
    -- goal, whose compositions are typed by the stages, so it is applied to the hypothesis.
    have h := congrArg (G : C ⥤ C).map (resolutionInnerMap_comp_resolutionFace_last hf n)
    rw [Functor.map_comp, Functor.map_id] at h
    rw [← Fin.succ_last, resolutionFace_succ_app, G.resolutionInnerMap_succ]
    exact h

/-- The inner map commutes with every face except the last one. -/
@[reassoc] lemma resolutionInnerMap_comp_resolutionFace_castSucc (f : X ⟶ G.obj X) :
    ∀ (n : ℕ) (j : Fin (n + 1)),
      G.resolutionInnerMap f (n + 1) ≫ (G.resolutionFace (n + 1) j.castSucc).app X =
        (G.resolutionFace n j).app X ≫ G.resolutionInnerMap f n
  | 0, j => by
    obtain rfl : j = 0 := Fin.eq_zero j
    rw [Fin.castSucc_zero, resolutionFace_zero_app, resolutionFace_zero_app]
    exact G.ε.naturality f
  | n + 1, j => by
    induction j using Fin.cases with
    | zero =>
      rw [Fin.castSucc_zero, resolutionFace_zero_app, resolutionFace_zero_app,
        G.resolutionInnerMap_succ f (n + 1)]
      exact G.ε.naturality (G.resolutionInnerMap f (n + 1))
    | succ j =>
      have h := congrArg (G : C ⥤ C).map (resolutionInnerMap_comp_resolutionFace_castSucc f n j)
      rw [Functor.map_comp, Functor.map_comp] at h
      rw [← Fin.succ_castSucc, resolutionFace_succ_app, resolutionFace_succ_app,
        G.resolutionInnerMap_succ f (n + 1), G.resolutionInnerMap_succ f n]
      exact h

/-- The inner map commutes with every degeneracy except the last one. -/
@[reassoc] lemma resolutionInnerMap_comp_resolutionDegeneracy_castSucc (f : X ⟶ G.obj X) :
    ∀ (n : ℕ) (j : Fin (n + 1)),
      G.resolutionInnerMap f (n + 1) ≫ (G.resolutionDegeneracy (n + 1) j.castSucc).app X =
        (G.resolutionDegeneracy n j).app X ≫ G.resolutionInnerMap f (n + 2)
  | 0, j => by
    obtain rfl : j = 0 := Fin.eq_zero j
    rw [Fin.castSucc_zero, resolutionDegeneracy_zero_app, resolutionDegeneracy_zero_app]
    exact G.δ.naturality f
  | n + 1, j => by
    induction j using Fin.cases with
    | zero =>
      rw [Fin.castSucc_zero, resolutionDegeneracy_zero_app, resolutionDegeneracy_zero_app,
        G.resolutionInnerMap_succ f (n + 1)]
      exact G.δ.naturality (G.resolutionInnerMap f (n + 1))
    | succ j =>
      have h := congrArg (G : C ⥤ C).map
        (resolutionInnerMap_comp_resolutionDegeneracy_castSucc f n j)
      rw [Functor.map_comp, Functor.map_comp] at h
      rw [← Fin.succ_castSucc, resolutionDegeneracy_succ_app, resolutionDegeneracy_succ_app,
        G.resolutionInnerMap_succ f (n + 1), G.resolutionInnerMap_succ f (n + 2)]
      exact h

/-- A section `f` of the counit at `X` splits the comonad resolution of `X` along its last faces,
with `G^(n+1) f` in degree `n`. Reversing the resolution turns this splitting into an extra
degeneracy in Mathlib's sense, which splits along the zeroth faces. -/
def resolutionExtraDegeneracyOfSection (f : X ⟶ G.obj X) (hf : f ≫ G.ε.app X = 𝟙 X) :
    SimplicialObject.Augmented.ExtraDegeneracy
      (SimplicialObject.Augmented.opFunctor.obj (G.augmentedSimplicialResolution.obj X)) where
  -- Each field rewrites the faces of the reversed resolution to iterated counits at reversed
  -- positions, then closes with an identity of the inner map. The terms of the reversed
  -- resolution are the comonad stages by definition, so `exact` matches their carriers.
  s' := f
  s n := G.resolutionInnerMap f (n + 1)
  s'_comp_ε := by
    rw [SimplicialObject.Augmented.opFunctor_obj_hom_app, augmentedSimplicialResolution_obj_hom,
      simplicialResolutionAugmentation_app_zero]
    exact hf
  s₀_comp_δ₁ := by
    have h := G.resolutionInnerMap_comp_resolutionFace_castSucc f 0 0
    rw [resolutionFace_zero_app] at h
    rw [SimplicialObject.Augmented.opFunctor_obj_hom_app, augmentedSimplicialResolution_obj_hom,
      simplicialResolutionAugmentation_app_zero, SimplicialObject.Augmented.opFunctor_obj_left_δ,
      augmentedSimplicialResolution_obj_left_δ, ← Fin.succ_zero_eq_one, Fin.rev_succ, Fin.rev_zero,
      Fin.last_zero]
    exact h
  s_comp_δ₀ n := by
    rw [SimplicialObject.Augmented.opFunctor_obj_left_δ, augmentedSimplicialResolution_obj_left_δ,
      Fin.rev_zero]
    exact G.resolutionInnerMap_comp_resolutionFace_last hf (n + 1)
  s_comp_δ n i := by
    rw [SimplicialObject.Augmented.opFunctor_obj_left_δ,
      SimplicialObject.Augmented.opFunctor_obj_left_δ, augmentedSimplicialResolution_obj_left_δ,
      augmentedSimplicialResolution_obj_left_δ, Fin.rev_succ]
    exact G.resolutionInnerMap_comp_resolutionFace_castSucc f (n + 1) i.rev
  s_comp_σ n i := by
    rw [SimplicialObject.Augmented.opFunctor_obj_left_σ,
      SimplicialObject.Augmented.opFunctor_obj_left_σ, augmentedSimplicialResolution_obj_left_σ,
      augmentedSimplicialResolution_obj_left_σ, Fin.rev_succ]
    exact G.resolutionInnerMap_comp_resolutionDegeneracy_castSucc f n i.rev

/-- The extra degeneracy built from a section `f` has `f` as its section of the augmentation. -/
lemma resolutionExtraDegeneracyOfSection_s' (f : X ⟶ G.obj X) (hf : f ≫ G.ε.app X = 𝟙 X) :
    (G.resolutionExtraDegeneracyOfSection f hf).s' = f := (rfl)

/-- In degree `n`, the extra degeneracy built from a section `f` is `G^(n+1) f`. -/
lemma resolutionExtraDegeneracyOfSection_s (f : X ⟶ G.obj X) (hf : f ≫ G.ε.app X = 𝟙 X)
    (n : ℕ) : (G.resolutionExtraDegeneracyOfSection f hf).s n = G.resolutionInnerMap f (n + 1) :=
  (rfl)

/-- The reversed resolution of a free object `G W` has an extra degeneracy given by the
comultiplication at `W`, a section of the counit at `G W`: its section of the augmentation is
`δ_W` and its degree `n` map is `G^(n+1) δ_W`. -/
def freeResolutionExtraDegeneracy (W : C) :
    SimplicialObject.Augmented.ExtraDegeneracy
      (SimplicialObject.Augmented.opFunctor.obj (G.augmentedSimplicialResolution.obj (G.obj W))) :=
  G.resolutionExtraDegeneracyOfSection (G.δ.app W) (G.left_counit W)

/-- The extra degeneracy of a free object has the comultiplication as its section of the
augmentation. -/
lemma freeResolutionExtraDegeneracy_s' (W : C) :
    (G.freeResolutionExtraDegeneracy W).s' = G.δ.app W := (rfl)

/-- In degree `n`, the extra degeneracy of a free object `G W` is `G^(n+1) δ_W`. -/
lemma freeResolutionExtraDegeneracy_s (W : C) (n : ℕ) :
    (G.freeResolutionExtraDegeneracy W).s n = G.resolutionInnerMap (G.δ.app W) (n + 1) := (rfl)

end CategoryTheory.Comonad
