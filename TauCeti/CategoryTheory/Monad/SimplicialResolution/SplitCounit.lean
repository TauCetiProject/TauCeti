/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monad.SimplicialResolution.Augmented
public import TauCeti.AlgebraicTopology.SimplicialObject.Op

/-!
# Extra degeneracies of comonad resolutions from sections of the counit

Let `G` be a comonad. If the counit `G X ⟶ X` has a section `a`, then the augmented simplicial
resolution of `X` is contractible. Inserting `a` as the innermost layer, the maps
`G^(n+1) a : G^(n+1) X ⟶ G^(n+2) X` together with `a` form an extra degeneracy that splits the
*last* face, the counit at the innermost position. Reversing the simplicial part along
`SimplexCategory.rev` with `SimplicialObject.Augmented.opFunctor` turns it into Mathlib's
`SimplicialObject.Augmented.ExtraDegeneracy`, which splits the zeroth face:
`Comonad.opResolutionExtraDegeneracy`.

The main case is a free object `G W`, where the comultiplication `G W ⟶ G (G W)` is a section of
the counit: `Comonad.freeOpResolutionExtraDegeneracy`. This expresses the projectivity of free
objects relative to the comonad, the input for the vanishing of comonad cohomology whose first
argument is such an object.

To compare the innermost layer with the outermost one, `Comonad.resolutionStageSuccObjIso` from
`SimplicialResolution.Basic` identifies `G^n (G X)` with `G^(n+1) X`. Through it, the last face
is the counit at the innermost position, and the remaining faces and degeneracies are those of the
resolution of `G X`.

## References

* M. Barr and J. Beck, *Homology and standard constructions*, in *Seminar on Triples and
  Categorical Homology Theory*, Lecture Notes in Math. 80, Springer, 1969, §1.
* A. M. Gainutdinov, J. Haferkamp and C. Schweigert, *Davydov–Yetter cohomology, comonads and
  Ocneanu rigidity*, Adv. Math. 414 (2023), arXiv:1910.06094, Lemma 2.5.
-/

public noncomputable section

open CategoryTheory Opposite Functor

universe v u

namespace CategoryTheory.Comonad

variable {C : Type u} [Category.{v} C] (G : Comonad C)

/-- The faces of the reversed augmented resolution are the counits at reversed positions. -/
lemma opFunctor_augmentedSimplicialResolution_obj_left_δ (X : C) {n : ℕ}
    (i : Fin (n + 2)) :
    (SimplicialObject.Augmented.opFunctor.obj (G.augmentedSimplicialResolution.obj X)).left.δ i =
      (G.resolutionFace (n + 1) i.rev).app X :=
  -- `SimplicialObject.opObjIso` is the identity, so `id_comp` and `comp_id` remove it.
  (SimplicialObject.opFunctor_obj_δ _ i).trans <| (Category.id_comp _).trans <|
    (Category.comp_id _).trans <| G.simplicialResolution_δ X i.rev

/-- The degeneracies of the reversed augmented resolution are the comultiplications at reversed
positions. -/
lemma opFunctor_augmentedSimplicialResolution_obj_left_σ (X : C) {n : ℕ}
    (i : Fin (n + 1)) :
    (SimplicialObject.Augmented.opFunctor.obj (G.augmentedSimplicialResolution.obj X)).left.σ i =
      (G.resolutionDegeneracy n i.rev).app X :=
  -- As for faces, the identity isomorphisms `SimplicialObject.opObjIso` are removed.
  (SimplicialObject.opFunctor_obj_σ _ i).trans <| (Category.id_comp _).trans <|
    (Category.comp_id _).trans <| G.simplicialResolution_σ X i.rev

variable {G} {X : C}

/-- Inserting `f` as the innermost layer, then applying the last face, applies `f ≫ ε`. -/
private lemma map_comp_hom_comp_resolutionFace_last {Y : C} (f : Y ⟶ G.obj X) (n : ℕ) :
    ((G.resolutionStage n).map f ≫ (G.resolutionStageSuccObjIso n X).hom) ≫
        (G.resolutionFace n (Fin.last n)).app X =
      (G.resolutionStage n).map (f ≫ G.ε.app X) := by
  rw [Category.assoc, resolutionStageSuccObjIso_hom_comp_resolutionFace_last, Functor.map_comp]

/-- Inserting `f` as the innermost layer commutes with every face but the last. -/
private lemma map_comp_hom_comp_resolutionFace_castSucc {Y : C} (f : Y ⟶ G.obj X) (n : ℕ)
    (j : Fin (n + 1)) :
    ((G.resolutionStage (n + 1)).map f ≫ (G.resolutionStageSuccObjIso (n + 1) X).hom) ≫
        (G.resolutionFace (n + 1) j.castSucc).app X =
      (G.resolutionFace n j).app Y ≫
        (G.resolutionStage n).map f ≫ (G.resolutionStageSuccObjIso n X).hom := by
  rw [Category.assoc, resolutionStageSuccObjIso_hom_comp_resolutionFace_castSucc,
    NatTrans.naturality_assoc]

/-- Inserting `f` as the innermost layer commutes with every degeneracy but the last. -/
private lemma map_comp_hom_comp_resolutionDegeneracy_castSucc {Y : C} (f : Y ⟶ G.obj X)
    (n : ℕ) (j : Fin (n + 1)) :
    ((G.resolutionStage (n + 1)).map f ≫ (G.resolutionStageSuccObjIso (n + 1) X).hom) ≫
        (G.resolutionDegeneracy (n + 1) j.castSucc).app X =
      (G.resolutionDegeneracy n j).app Y ≫
        (G.resolutionStage (n + 2)).map f ≫ (G.resolutionStageSuccObjIso (n + 2) X).hom := by
  rw [Category.assoc, resolutionStageSuccObjIso_hom_comp_resolutionDegeneracy_castSucc,
    NatTrans.naturality_assoc]

/-- A section `a` of the counit `G X ⟶ X` gives an extra degeneracy of the augmented resolution
of `X`, reversed along `SimplexCategory.rev`. It inserts `a` as the innermost layer: the section of
the augmentation is `a`, and the degree `n` map is `G^(n+1) a`. -/
def opResolutionExtraDegeneracy (a : SplitEpi (G.ε.app X)) :
    SimplicialObject.Augmented.ExtraDegeneracy
      (SimplicialObject.Augmented.opFunctor.obj (G.augmentedSimplicialResolution.obj X)) where
  s' := a.section_
  s n := (G.resolutionStage (n + 1)).map a.section_ ≫ (G.resolutionStageSuccObjIso (n + 1) X).hom
  s'_comp_ε := by
    rw [SimplicialObject.Augmented.opFunctor_obj_hom_app, augmentedSimplicialResolution_obj_hom,
      simplicialResolutionAugmentation_app_zero]
    -- `SimplicialObject.opObjIso` is the identity.
    exact (congrArg (a.section_ ≫ ·) (Category.id_comp _)).trans a.id
  s₀_comp_δ₁ := by
    rw [opFunctor_augmentedSimplicialResolution_obj_left_δ,
      SimplicialObject.Augmented.opFunctor_obj_hom_app, augmentedSimplicialResolution_obj_hom,
      simplicialResolutionAugmentation_app_zero]
    refine (map_comp_hom_comp_resolutionFace_castSucc a.section_ 0 0).trans ?_
    rw [resolutionFace_zero_app, resolutionStageSuccObjIso_zero_hom]
    -- In degree zero, `G^0` is the identity functor, and `SimplicialObject.opObjIso` is the
    -- identity.
    exact (congrArg (G.ε.app X ≫ ·) (Category.comp_id a.section_)).trans
      (congrArg (· ≫ a.section_) (Category.id_comp _).symm)
  s_comp_δ₀ n := by
    rw [opFunctor_augmentedSimplicialResolution_obj_left_δ, Fin.rev_zero]
    exact (map_comp_hom_comp_resolutionFace_last a.section_ (n + 1)).trans
      ((congrArg _ a.id).trans ((G.resolutionStage (n + 1)).map_id X))
  s_comp_δ n i := by
    rw [opFunctor_augmentedSimplicialResolution_obj_left_δ,
      opFunctor_augmentedSimplicialResolution_obj_left_δ, Fin.rev_succ]
    exact map_comp_hom_comp_resolutionFace_castSucc a.section_ (n + 1) i.rev
  s_comp_σ n i := by
    rw [opFunctor_augmentedSimplicialResolution_obj_left_σ,
      opFunctor_augmentedSimplicialResolution_obj_left_σ, Fin.rev_succ]
    exact map_comp_hom_comp_resolutionDegeneracy_castSucc a.section_ n i.rev

/-- The section of the augmentation is the given section of the counit. -/
lemma opResolutionExtraDegeneracy_s' (a : SplitEpi (G.ε.app X)) :
    (opResolutionExtraDegeneracy a).s' = a.section_ := (rfl)

/-- In degree `n`, the extra degeneracy applies `G^(n+1)` to the section of the counit. -/
lemma opResolutionExtraDegeneracy_s (a : SplitEpi (G.ε.app X)) (n : ℕ) :
    (opResolutionExtraDegeneracy a).s n =
      (G.resolutionStage (n + 1)).map a.section_ ≫
        (G.resolutionStageSuccObjIso (n + 1) X).hom := (rfl)

variable (G)

/-- At a free object `G W`, the comultiplication `G W ⟶ G (G W)` is a section of the counit, and
gives an extra degeneracy of the reversed augmented resolution of `G W`. -/
def freeOpResolutionExtraDegeneracy (W : C) :
    SimplicialObject.Augmented.ExtraDegeneracy
      (SimplicialObject.Augmented.opFunctor.obj
        (G.augmentedSimplicialResolution.obj (G.obj W))) :=
  opResolutionExtraDegeneracy ⟨G.δ.app W, G.left_counit W⟩

/-- At a free object, the section of the augmentation is the comultiplication. -/
lemma freeOpResolutionExtraDegeneracy_s' (W : C) :
    (G.freeOpResolutionExtraDegeneracy W).s' = G.δ.app W := (rfl)

/-- At a free object, the extra degeneracy in degree `n` applies `G^(n+1)` to the
comultiplication. -/
lemma freeOpResolutionExtraDegeneracy_s (W : C) (n : ℕ) :
    (G.freeOpResolutionExtraDegeneracy W).s n =
      (G.resolutionStage (n + 1)).map (G.δ.app W) ≫
        (G.resolutionStageSuccObjIso (n + 1) (G.obj W)).hom := (rfl)

end CategoryTheory.Comonad
