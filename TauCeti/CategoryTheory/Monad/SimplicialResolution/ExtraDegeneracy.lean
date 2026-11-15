/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monad.SimplicialResolution.Augmented
public import TauCeti.AlgebraicTopology.SimplicialObject.Op

/-!
# Extra degeneracies of comonad resolutions at split objects

Let `G` be a comonad on `C` and let `a : X ⟶ G X` be a section of the counit, so that
`a ≫ ε_X = 𝟙 X`. Applying `a` beneath all layers gives maps `G^(n+1)(a) : G^(n+1) X ⟶ G^(n+2) X`.
They split the *last* face of the augmented resolution `G^(•+1) X → X` (the counit in the
innermost position), and commute with all other faces and degeneracies by naturality of the
counit and comultiplication. Reversing the resolution with
`SimplicialObject.Augmented.opFunctor` turns them into an extra degeneracy in the sense of
Mathlib's `SimplicialObject.Augmented.ExtraDegeneracy`, with `a` as the section of the
augmentation.

Every free object `G W` is split by the comultiplication `δ_W`, which gives an extra degeneracy
of the reversed resolution of `G W`. This makes precise the projectivity of free objects in
[GHS] Lemma 2.5(1), using the comonad identities as in [BB] §1. Applying a functor and
Mathlib's `ExtraDegeneracy.homotopyEquiv` then contracts the resolution onto its augmentation.

## References

* [M. Barr and J. Beck, *Homology and standard constructions*][BB], §1.
* [A. Gainutdinov, J. Haferkamp and C. Schweigert, *Davydov-Yetter cohomology, comonads and
  Ocneanu rigidity*][GHS], arXiv:1910.06094, Lemma 2.5.
-/

public section

open CategoryTheory Opposite

namespace CategoryTheory.Comonad

universe v u

variable {C : Type u} [Category.{v} C] (G : Comonad C) {X : C} (a : X ⟶ G.obj X)

/-- The map `G^n(a) : G^n X ⟶ G^(n+1) X`, which applies `a` beneath all `n` layers. -/
def resolutionInnerMap : ∀ n : ℕ, (G.resolutionStage n).obj X ⟶ (G.resolutionStage (n + 1)).obj X
  | 0 => a
  | n + 1 => G.map (resolutionInnerMap n)

@[simp] lemma resolutionInnerMap_zero : G.resolutionInnerMap a 0 = a := (rfl)

@[simp] lemma resolutionInnerMap_succ (n : ℕ) :
    G.resolutionInnerMap a (n + 1) = G.map (G.resolutionInnerMap a n) := (rfl)

-- The recursive stages `G^(n+1) X` and `G (G^n X)` agree only definitionally, so the
-- inductive steps below close by `exact` rather than by rewriting with `Functor.map_comp`.

/-- A section of the counit splits the counit in the innermost position. -/
@[reassoc] lemma resolutionInnerMap_comp_resolutionFace_last
    (ha : a ≫ G.ε.app X = 𝟙 X) (n : ℕ) :
    G.resolutionInnerMap a n ≫ (G.resolutionFace n (Fin.last n)).app X = 𝟙 _ := by
  induction n with
  | zero => rwa [Fin.last_zero, resolutionFace_zero_app]
  | succ n ih =>
    rw [resolutionInnerMap_succ, ← Fin.succ_last, resolutionFace_succ_app]
    exact (G.map_comp _ _).symm.trans ((congrArg G.map ih).trans (G.map_id _))

/-- Applying `a` beneath all layers commutes with a counit in any position but the innermost. -/
@[reassoc] lemma resolutionInnerMap_comp_resolutionFace_castSucc (n : ℕ) (i : Fin (n + 1)) :
    G.resolutionInnerMap a (n + 1) ≫ (G.resolutionFace (n + 1) i.castSucc).app X =
      (G.resolutionFace n i).app X ≫ G.resolutionInnerMap a n := by
  induction n with
  | zero =>
    obtain rfl : i = 0 := Fin.eq_zero i
    rw [Fin.castSucc_zero, resolutionFace_zero_app, resolutionFace_zero_app]
    exact G.ε.naturality a
  | succ n ih =>
    induction i using Fin.cases with
    | zero =>
      rw [Fin.castSucc_zero, resolutionFace_zero_app, resolutionFace_zero_app]
      exact G.ε.naturality _
    | succ i =>
      rw [← Fin.succ_castSucc, resolutionFace_succ_app, resolutionFace_succ_app]
      exact (G.map_comp _ _).symm.trans ((congrArg G.map (ih i)).trans (G.map_comp _ _))

/-- Applying `a` beneath all layers commutes with every comultiplication. -/
@[reassoc] lemma resolutionInnerMap_comp_resolutionDegeneracy_castSucc (n : ℕ)
    (i : Fin (n + 1)) :
    G.resolutionInnerMap a (n + 1) ≫ (G.resolutionDegeneracy (n + 1) i.castSucc).app X =
      (G.resolutionDegeneracy n i).app X ≫ G.resolutionInnerMap a (n + 2) := by
  induction n with
  | zero =>
    obtain rfl : i = 0 := Fin.eq_zero i
    rw [Fin.castSucc_zero, resolutionDegeneracy_zero_app, resolutionDegeneracy_zero_app]
    exact G.δ.naturality a
  | succ n ih =>
    induction i using Fin.cases with
    | zero =>
      rw [Fin.castSucc_zero, resolutionDegeneracy_zero_app, resolutionDegeneracy_zero_app]
      exact G.δ.naturality _
    | succ i =>
      rw [← Fin.succ_castSucc, resolutionDegeneracy_succ_app, resolutionDegeneracy_succ_app]
      exact (G.map_comp _ _).symm.trans ((congrArg G.map (ih i)).trans (G.map_comp _ _))

/-- A section `a` of the counit at `X` gives an extra degeneracy of the reversed augmented
resolution of `X`: the section of the augmentation is `a`, and the degree-`n` map is
`G^(n+1)(a)`. -/
def opResolutionExtraDegeneracy (ha : a ≫ G.ε.app X = 𝟙 X) :
    SimplicialObject.Augmented.ExtraDegeneracy
      (SimplicialObject.Augmented.opFunctor.obj (G.augmentedSimplicialResolution.obj X)) where
  s' := a
  s n := G.resolutionInnerMap a (n + 1)
  s'_comp_ε := by
    -- The augmentation in degree zero is the counit.
    rw [SimplicialObject.Augmented.opFunctor_obj_hom_app, augmentedSimplicialResolution_obj_hom,
      simplicialResolutionAugmentation_app_zero]
    exact ha
  s₀_comp_δ₁ := by
    -- The reversed face `δ 1` is the outermost counit.
    rw [SimplicialObject.Augmented.opFunctor_obj_left_δ,
      SimplicialObject.Augmented.opFunctor_obj_hom_app, augmentedSimplicialResolution_obj_hom,
      simplicialResolutionAugmentation_app_zero, augmentedSimplicialResolution_obj_left_δ,
      (by decide : (1 : Fin 2).rev = 0), resolutionFace_zero_app]
    exact G.ε.naturality a
  s_comp_δ₀ n := by
    -- The reversed face `δ 0` is the innermost counit.
    rw [SimplicialObject.Augmented.opFunctor_obj_left_δ, augmentedSimplicialResolution_obj_left_δ,
      Fin.rev_zero]
    exact G.resolutionInnerMap_comp_resolutionFace_last a ha (n + 1)
  s_comp_δ n i := by
    rw [SimplicialObject.Augmented.opFunctor_obj_left_δ,
      SimplicialObject.Augmented.opFunctor_obj_left_δ, augmentedSimplicialResolution_obj_left_δ,
      augmentedSimplicialResolution_obj_left_δ, Fin.rev_succ]
    exact G.resolutionInnerMap_comp_resolutionFace_castSucc a (n + 1) i.rev
  s_comp_σ n i := by
    rw [SimplicialObject.Augmented.opFunctor_obj_left_σ,
      SimplicialObject.Augmented.opFunctor_obj_left_σ, augmentedSimplicialResolution_obj_left_σ,
      augmentedSimplicialResolution_obj_left_σ, Fin.rev_succ]
    exact G.resolutionInnerMap_comp_resolutionDegeneracy_castSucc a n i.rev

lemma opResolutionExtraDegeneracy_s' (ha : a ≫ G.ε.app X = 𝟙 X) :
    (G.opResolutionExtraDegeneracy a ha).s' = a := (rfl)

lemma opResolutionExtraDegeneracy_s (ha : a ≫ G.ε.app X = 𝟙 X) (n : ℕ) :
    (G.opResolutionExtraDegeneracy a ha).s n = G.resolutionInnerMap a (n + 1) := (rfl)

/-- The comultiplication `δ_W` gives an extra degeneracy of the reversed augmented resolution
of the free object `G W`. -/
def freeOpResolutionExtraDegeneracy (W : C) :
    SimplicialObject.Augmented.ExtraDegeneracy
      (SimplicialObject.Augmented.opFunctor.obj
        (G.augmentedSimplicialResolution.obj (G.obj W))) :=
  G.opResolutionExtraDegeneracy (G.δ.app W) (G.left_counit W)

lemma freeOpResolutionExtraDegeneracy_s' (W : C) :
    (G.freeOpResolutionExtraDegeneracy W).s' = G.δ.app W := (rfl)

lemma freeOpResolutionExtraDegeneracy_s (W : C) (n : ℕ) :
    (G.freeOpResolutionExtraDegeneracy W).s n = G.resolutionInnerMap (G.δ.app W) (n + 1) := (rfl)

end CategoryTheory.Comonad
