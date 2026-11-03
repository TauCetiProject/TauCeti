/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import Mathlib.AlgebraicTopology.SingularHomology.Basic

/-!
# Singular chain complexes

This module relates the singular-chain functor to the chain map induced by a map of singular
simplicial sets, and the singular homology functor to the simplicial homology map it induces.
It also records the degree-zero component of Mathlib's identification of the singular chains of
a totally disconnected space with an alternating constant complex
(`TauCeti.ιChainComplex_singularChainComplexFunctorIsoOfTotallyDisconnectedSpace_hom_f_zero`).
-/

public section

noncomputable section

open CategoryTheory Limits
open scoped Simplicial

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

/-- The singular homology functor with coefficients in `R` sends a continuous map `f` to the
simplicial homology map induced by the singular simplicial map `TopCat.toSSet.map f`. -/
lemma singularHomologyFunctor_obj_map [CategoryWithHomology C] (n : ℕ) {X Y : TopCat.{w}}
    (f : X ⟶ Y) :
    ((AlgebraicTopology.singularHomologyFunctor C n).obj R).map f =
      SSet.homologyMap (TopCat.toSSet.map f) R n := rfl

/-- Mathlib's identification of the singular chains of a totally disconnected space with the
alternating constant complex sends the summand of a singular vertex to the summand of the point
it picks out. -/
@[simp, reassoc]
lemma ιChainComplex_singularChainComplexFunctorIsoOfTotallyDisconnectedSpace_hom_f_zero
    (X : TopCat.{w}) [TotallyDisconnectedSpace X] (σ : (TopCat.toSSet.obj X) _⦋0⦌) :
    (TopCat.toSSet.obj X).ιChainComplex σ ≫
        (AlgebraicTopology.singularChainComplexFunctorIsoOfTotallyDisconnectedSpace
          C R X).hom.f 0 =
      Sigma.ι (fun _ : X ↦ R) (TopCat.toSSetObj₀Equiv σ) := by
  -- Mathlib states no degree-zero formula for this isomorphism. By definition it is the map of
  -- alternating face map complexes induced by `TopCat.toSSetIsoConst`, followed by the identity
  -- identification `alternatingFaceMapComplexConst`.
  change _ ≫ ((AlgebraicTopology.alternatingFaceMapComplex C).map
      (Functor.whiskerRight (TopCat.toSSetIsoConst X).hom (sigmaConst.obj R) ≫
        (Functor.constComp _ _ _).hom)).f 0 ≫ 𝟙 _ = _
  simp only [SSet.ιChainComplex, Functor.map_comp, HomologicalComplex.comp_f,
    AlgebraicTopology.alternatingFaceMapComplex_map_f, Functor.whiskerRight_app,
    sigmaConst_obj_map, Functor.constComp_hom_app]
  refine (congrArg _ ((Category.comp_id _).trans (Category.comp_id _))).trans ?_
  rw [Sigma.ι_comp_map', Category.id_comp]
  -- The constant-set isomorphism evaluates a simplex at an arbitrary point of the topological
  -- `0`-simplex, which is the unique point there.
  exact congrArg _ (congrArg (TopCat.toSSetObjEquiv X _ σ) (Subsingleton.elim _ _))

end TauCeti
