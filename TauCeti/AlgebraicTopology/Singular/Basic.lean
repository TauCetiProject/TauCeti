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
It records restriction along subspace inclusions (`TopCat.chainComplexMap_f_comp_subtypeVal`)
without requiring the small-chain subdivision theory, functoriality `g_* ∘ f_* = (g ∘ f)_*` of
singular homology in continuous maps (`TauCeti.homologyMap_comp_homologyMap`), and that a section
`s` of a map `p` induces a section `p_* ∘ s_* = id` on homology
(`TauCeti.homologyMap_comp_homologyMap_of_comp_eq_id`).
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

/-- Singular homology is functorial in continuous maps: `g_* ∘ f_* = (g ∘ f)_*`. -/
@[reassoc, elementwise nosimp]
theorem homologyMap_comp_homologyMap [CategoryWithHomology C] {X Y Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] (f : C(X, Y)) (g : C(Y, Z))
    (n : ℕ) :
    SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom f)) R n ≫
        SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom g)) R n =
      SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom (g.comp f))) R n := by
  rw [← SSet.homologyMap_comp, ← CategoryTheory.Functor.map_comp, ← TopCat.ofHom_comp]

/-- A section `s` of `p : E → M` induces a section on singular homology: `p_* ∘ s_* = id`. -/
@[reassoc, elementwise]
theorem homologyMap_comp_homologyMap_of_comp_eq_id [CategoryWithHomology C] {E M : Type w}
    [TopologicalSpace E] [TopologicalSpace M] (p : C(E, M)) (s : C(M, E))
    (hs : p.comp s = ContinuousMap.id M) (n : ℕ) :
    SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom s)) R n ≫
        SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom p)) R n = 𝟙 _ := by
  rw [homologyMap_comp_homologyMap, hs, TopCat.ofHom_id, CategoryTheory.Functor.map_id,
    SSet.homologyMap_id]

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
  simp only [sigmaConst_obj_obj, AlgebraicTopology.alternatingFaceMapComplex_obj_X,
    Functor.const_obj_obj, Functor.comp_obj, SSet.ιChainComplex, Functor.map_comp,
    HomologicalComplex.comp_f, AlgebraicTopology.alternatingFaceMapComplex_map_f,
    Functor.whiskerRight_app, sigmaConst_obj_map, Functor.constComp_hom_app, Category.comp_id,
    Sigma.ι_comp_map', Category.id_comp]
  -- The constant-set isomorphism evaluates a simplex at an arbitrary point of the topological
  -- `0`-simplex, which is the unique point there.
  exact congrArg _ (congrArg (TopCat.toSSetObjEquiv X _ σ) (Subsingleton.elim _ _))

end TauCeti

namespace TopCat

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
  {R : C} {X : TopCat.{w}}

/-- Pushing singular chains forward along a map of subspaces of `X` commuting with the inclusions,
and then along the inclusion of the target, is pushing them forward along the inclusion of the
source. The reassociated form restricts a singular cochain of `X` in two steps. -/
@[reassoc]
lemma chainComplexMap_f_comp_subtypeVal {S' T' : Set X} (g : of ↥S' ⟶ of ↥T')
    (hg : ∀ x, (g x : X) = x) (n : ℕ) :
    (SSet.chainComplexMap (toSSet.map g) R).f n ≫
        (SSet.chainComplexMap (toSSet.map (ofHom (ContinuousMap.subtypeVal T'))) R).f n =
      (SSet.chainComplexMap (toSSet.map (ofHom (ContinuousMap.subtypeVal S'))) R).f n := by
  rw [← HomologicalComplex.comp_f, ← Functor.map_comp, ← Functor.map_comp]
  congr 4
  exact TopCat.ext hg

end TopCat
