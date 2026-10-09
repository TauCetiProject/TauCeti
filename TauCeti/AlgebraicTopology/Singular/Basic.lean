/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SingularHomology.Basic

/-!
# Singular chain complexes

This module relates the singular-chain functor to the chain map induced by a map of singular
simplicial sets, and records that multiplication by a natural number is invertible on singular
chains whenever it is invertible on the coefficients.
-/

public section

noncomputable section

open CategoryTheory Limits

universe w v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C] (R : C)

/-- The singular chain complex functor with coefficients in `R` sends a continuous map `f` to the
simplicial chain map induced by the singular simplicial map `TopCat.toSSet.map f`. -/
@[simp]
lemma singularChainComplexFunctor_obj_map {X Y : TopCat.{w}} (f : X ⟶ Y) :
    ((AlgebraicTopology.singularChainComplexFunctor C).obj R).map f =
      SSet.chainComplexMap (TopCat.toSSet.map f) R := rfl

/-- A coefficient morphism acts on singular chains by its simplicial chain map evaluated
at the singular simplicial set. -/
@[simp]
lemma singularChainComplexFunctor_map_app {R R' : C} (g : R ⟶ R') (X : TopCat.{w}) :
    ((AlgebraicTopology.singularChainComplexFunctor C).map g).app X =
      ((SSet.chainComplexFunctor C).map g).app (TopCat.toSSet.obj X) :=
  (rfl)

/-- If multiplication by `d` is invertible on the coefficient object `R`, then it is invertible on
the singular chain complex with coefficients in `R` of every space. -/
lemma isIso_nsmul_id_singularChainComplex (d : ℕ) [IsIso (d • 𝟙 R)] (X : TopCat.{w}) :
    IsIso (d • 𝟙 (((AlgebraicTopology.singularChainComplexFunctor C).obj R).obj X)) := by
  have : ((AlgebraicTopology.singularChainComplexFunctor C).map (d • 𝟙 R)).app X = d • 𝟙 _ := by
    rw [Functor.map_nsmul, CategoryTheory.Functor.map_id, NatTrans.app_nsmul, NatTrans.id_app]
  rw [← this]
  infer_instance

end TauCeti
