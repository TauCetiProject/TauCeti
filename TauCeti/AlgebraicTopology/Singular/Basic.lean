/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.AlgebraicTopology.SimplicialSet.Nonempty
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Singular chain complexes

Facet restriction is `ContinuousMap.simplexFace`; `TopCat.toSSetObjEquiv_symm_δ` identifies it
with the actual simplicial face.

This module relates the singular-chain functor to the chain map induced by a map of singular
simplicial sets, and the singular homology functor to the simplicial homology of the singular
simplicial set and the map it induces, also applied to a class
(`TauCeti.singularHomologyFunctor_obj_map_hom_apply`), and likewise for a change of coefficients
(`TauCeti.singularHomologyFunctor_map_app_hom_apply`).
It records restriction along subspace inclusions (`TopCat.chainComplexMap_f_comp_subtypeVal`)
without requiring the small-chain subdivision theory.
It also records the degree-zero component of Mathlib's identification of the singular chains of
a totally disconnected space with an alternating constant complex
(`TauCeti.ιChainComplex_singularChainComplexFunctorIsoOfTotallyDisconnectedSpace_hom_f_zero`),
and the vanishing of the singular homology of the empty space
(`TauCeti.isZero_singularHomology_of_isEmpty`).
Applied to a class, the homology map induced by a composite of continuous maps is the composite of
the homology maps (`ContinuousMap.homologyMap_comp_apply`).
A commuting square of continuous maps gives a commuting square of homology maps
(`TauCeti.homologyMap_toSSet_ofHom_comp_comm`).
-/

public section

noncomputable section

open CategoryTheory Limits
open scoped Simplicial

universe w v u

namespace ContinuousMap

open Convexity

/-- Restrict a continuous singular simplex to its `j`-th facet. -/
def simplexFace {Y : Type*} [TopologicalSpace Y] {n : ℕ}
    (s : C(StdSimplex ℝ (Fin (n + 2)), Y)) (j : Fin (n + 2)) :
    C(StdSimplex ℝ (Fin (n + 1)), Y) :=
  s.comp ⟨StdSimplex.map j.succAbove, by fun_prop⟩

/-- The facet restriction evaluates by the native simplex vertex map. -/
@[simp]
lemma simplexFace_apply {Y : Type*} [TopologicalSpace Y] {n : ℕ}
    (s : C(StdSimplex ℝ (Fin (n + 2)), Y)) (j : Fin (n + 2))
    (x : StdSimplex ℝ (Fin (n + 1))) : s.simplexFace j x = s (x.map j.succAbove) := by
  rfl

/-- Facet restriction commutes with postcomposition of continuous maps. -/
@[simp]
lemma simplexFace_comp {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {n : ℕ}
    (f : C(X, Y)) (s : C(Convexity.StdSimplex ℝ (Fin (n + 2)), X)) (j : Fin (n + 2)) :
    (f.comp s).simplexFace j = f.comp (s.simplexFace j) := by
  rfl

end ContinuousMap

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

/-- The singular homology functor with coefficients in `R` evaluates on a space `X` to the
simplicial homology of its singular simplicial set `TopCat.toSSet.obj X`. -/
lemma singularHomologyFunctor_obj_obj_eq_toSSet_homology [CategoryWithHomology C] (n : ℕ)
    (X : TopCat.{w}) :
    ((AlgebraicTopology.singularHomologyFunctor C n).obj R).obj X =
      (TopCat.toSSet.obj X).homology R n := rfl

/-- The singular homology functor with coefficients in `R` sends a continuous map `f` to the
simplicial homology map induced by the singular simplicial map `TopCat.toSSet.map f`. -/
lemma singularHomologyFunctor_obj_map [CategoryWithHomology C] (n : ℕ) {X Y : TopCat.{w}}
    (f : X ⟶ Y) :
    ((AlgebraicTopology.singularHomologyFunctor C n).obj R).map f =
      SSet.homologyMap (TopCat.toSSet.map f) R n := rfl

/-- The map of the singular homology functor applied to a class `μ` typed in `SSet.homology` of
the singular simplicial set, rewritten as the simplicial homology map. The left side applies a
map out of the homology functor's object to `μ`, which agrees with `SSet.homology` only after
unfolding; the right side is well typed as stated, so later rewrites can match it syntactically. -/
theorem singularHomologyFunctor_obj_map_hom_apply {Λ : Type*} [Ring Λ] (L : ModuleCat.{w} Λ)
    {X Y : TopCat.{w}} (f : X ⟶ Y) {k : ℕ}
    (μ : ((TopCat.toSSet.obj X).homology L k : ModuleCat.{w} Λ)) :
    (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} Λ) k).obj L).map f).hom μ =
      (SSet.homologyMap (TopCat.toSSet.map f) L k).hom μ :=
  (rfl)

/-- A coefficient morphism `g` acts on the singular homology of `X`, applied to a class `μ` typed
in `SSet.homology` of the singular simplicial set, by the homology map of its simplicial chain map.
As for `TauCeti.singularHomologyFunctor_obj_map_hom_apply`, the two sides agree only after
unfolding, and the right side is well typed as stated, so later rewrites can match it
syntactically. -/
theorem singularHomologyFunctor_map_app_hom_apply {Λ : Type*} [Ring Λ] {L L' : ModuleCat.{w} Λ}
    (g : L ⟶ L') (X : TopCat.{w}) {k : ℕ}
    (μ : ((TopCat.toSSet.obj X).homology L k : ModuleCat.{w} Λ)) :
    (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} Λ) k).map g).app X).hom μ =
      (HomologicalComplex.homologyMap
        (((SSet.chainComplexFunctor (ModuleCat.{w} Λ)).map g).app (TopCat.toSSet.obj X)) k).hom μ :=
  (rfl)

/-- A commuting square of continuous maps gives a commuting square of the simplicial homology maps
of the singular simplicial sets. -/
lemma homologyMap_toSSet_ofHom_comp_comm [CategoryWithHomology C] (n : ℕ)
    {X Y Y' Z : Type w} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Y']
    [TopologicalSpace Z] {f : C(X, Y)} {g : C(Y, Z)} {f' : C(X, Y')} {g' : C(Y', Z)}
    (h : g.comp f = g'.comp f') :
    SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom f)) R n ≫
        SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom g)) R n =
      SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom f')) R n ≫
        SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom g')) R n := by
  rw [← SSet.homologyMap_comp, ← SSet.homologyMap_comp, ← Functor.map_comp, ← Functor.map_comp,
    ← TopCat.ofHom_comp, ← TopCat.ofHom_comp, h]

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

/-- **The singular homology of the empty space vanishes** in every degree, for arbitrary
coefficients: there are no singular simplices, so the singular chain complex is zero. -/
theorem isZero_singularHomology_of_isEmpty [CategoryWithHomology C] (X : TopCat.{w}) [IsEmpty X]
    (n : ℕ) : IsZero (((AlgebraicTopology.singularHomologyFunctor C n).obj R).obj X) := by
  have : (TopCat.toSSet.obj X).HasDimensionLT 0 :=
    (SSet.notNonempty_iff_hasDimensionLT_zero _).mp fun ⟨σ⟩ ↦
      isEmptyElim (TopCat.toSSetObj₀Equiv σ)
  exact (HomologicalComplex.homologyFunctor _ _ n).map_isZero
    ((TopCat.toSSet.obj X).isZero_chainComplex R)

end TauCeti

namespace ContinuousMap

variable {X Y Z : Type w} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- The map induced by a composite on singular homology, in the form
`SSet.homologyMap (TopCat.toSSet.map _)`, applied to a class with coefficients in a module. -/
theorem homologyMap_comp_apply (f : C(X, Y)) (g : C(Y, Z)) {Λ : Type*} [Ring Λ]
    (R : ModuleCat.{w} Λ) (n : ℕ)
    (x : ((TopCat.toSSet.obj (TopCat.of X)).homology R n : ModuleCat.{w} Λ)) :
    (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom (g.comp f))) R n).hom x =
      (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom g)) R n).hom
        ((SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom f)) R n).hom x) := by
  rw [← ModuleCat.comp_apply, ← SSet.homologyMap_comp, ← Functor.map_comp, ← TopCat.ofHom_comp]

end ContinuousMap

namespace TopCat

/-- Singular-simplex identification carries the native simplicial face to facet restriction.
Use this general form explicitly; affine simplices retain their existing vertex-map simp form. -/
lemma toSSetObjEquiv_symm_δ {X : TopCat.{w}} {n : ℕ}
    (s : C(Convexity.StdSimplex ℝ (Fin (n + 2)), X)) (j : Fin (n + 2)) :
    (TopCat.toSSet.obj X).δ j ((X.toSSetObjEquiv _).symm s) =
      (X.toSSetObjEquiv _).symm (s.simplexFace j) := by
  -- Native `δ` is the simplicial map of `SimplexCategory.δ`; naturality identifies its map.
  change (TopCat.toSSet.obj X).map (SimplexCategory.δ j).op _ = _
  simpa only [ContinuousMap.simplexFace, SimplexCategory.coe_δ] using
    (TopCat.toSSetObjEquiv_symm_naturality (SimplexCategory.δ j) s)

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
