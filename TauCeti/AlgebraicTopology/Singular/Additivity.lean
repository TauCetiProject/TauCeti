/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.CategoryTheory.Limits.Types.Coproducts
public import Mathlib.Topology.Category.TopCat.Limits.Products
public import Mathlib.Topology.ContinuousMap.Sigma
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Coproduct
public import TauCeti.AlgebraicTopology.SimplicialSet.TopAdj

/-!
# Additivity of singular chains

A singular simplex of a disjoint union `Σ i, X i` has connected domain, so its image lies in a
single summand, and it comes from a singular simplex of that summand in exactly one way.  Hence
the singular simplicial set of a disjoint union is the coproduct of the singular simplicial sets
of the summands, and, since the simplicial chain complex functor preserves colimits, so is the
singular chain complex.

This is the chain-level input to the additivity axiom of Eilenberg--Steenrod, not the axiom
itself: the axiom is a statement about singular *homology*, which needs the further step that
homology commutes with the coproduct of chain complexes and is not proved here.  What the chain
level does supply is that every map in sight is induced by one of the inclusions
`X i ⟶ Σ i, X i`, so the result is a statement about a cofan rather than an unrelated degreewise
decomposition.

## Sources

The informal source is Eilenberg--Steenrod, *Foundations of Algebraic Topology*, Chapters I--III.
The connectedness argument is Mathlib's `ContinuousMap.sigmaCodHomeomorph`, by Yury Kudryashov in
`Mathlib/Topology/ContinuousMap/Sigma`; the singular simplicial set `TopCat.toSSet` and the singular
chain complex `AlgebraicTopology.singularChainComplexFunctor` are by Andrew Yang in
`Mathlib/AlgebraicTopology/SingularHomology/Basic`, building on Joël Riou's `TopCat.toSSet`
adjunction; and the concrete cofan `TopCat.sigmaCofanIsColimit` is by Patrick Massot, Kim
Morrison, Mario Carneiro and Andrew Yang in `Mathlib/Topology/Category/TopCat/Limits/Products`.
-/

public section

noncomputable section

open CategoryTheory Limits Convexity TopCat

universe w v u

namespace TauCeti

variable {ι : Type w} (X : ι → TopCat.{w}) (n : SimplexCategoryᵒᵖ)

/-- In each degree, the singular simplices of a disjoint union of spaces are exactly the singular
simplices of the summands: the topological simplex is connected, so a singular simplex of
`Σ i, X i` comes from a unique summand and a unique singular simplex there. -/
lemma toSSet_map_sigmaι_app_bijective : Function.Bijective
    (fun p : Σ i, (toSSet.obj (X i)).obj n ↦ (toSSet.map (sigmaι X p.1)).app n p.2) := by
  have key : Function.Bijective
      (fun p : Σ i, C(StdSimplex ℝ (Fin (n.unop.len + 1)), X i) ↦
        (ContinuousMap.sigmaMk (X := fun i ↦ ((X i : TopCat.{w}) : Type w)) p.1).comp p.2) := by
    have hcoe : ⇑(ContinuousMap.sigmaCodHomeomorph (StdSimplex ℝ (Fin (n.unop.len + 1)))
        (fun i ↦ ((X i : TopCat.{w}) : Type w))).symm =
        fun p ↦ (ContinuousMap.sigmaMk p.1).comp p.2 :=
      funext fun p ↦ ContinuousMap.sigmaCodHomeomorph_symm_apply _ _ p
    have h := (ContinuousMap.sigmaCodHomeomorph (StdSimplex ℝ (Fin (n.unop.len + 1)))
      (fun i ↦ ((X i : TopCat.{w}) : Type w))).symm.bijective
    rwa [hcoe] at h
  have hfun : (fun p : Σ i, (toSSet.obj (X i)).obj n ↦ (toSSet.map (sigmaι X p.1)).app n p.2) =
      (toSSetObjEquiv (of (Σ i, X i)) n).symm ∘
        (fun p : Σ i, C(StdSimplex ℝ (Fin (n.unop.len + 1)), X i) ↦
          (ContinuousMap.sigmaMk (X := fun i ↦ ((X i : TopCat.{w}) : Type w)) p.1).comp p.2) ∘
        (Equiv.sigmaCongrRight fun i ↦ toSSetObjEquiv (X i) n) := by
    ext ⟨i, x⟩
    rw [Function.comp_apply, Function.comp_apply, Equiv.eq_symm_apply,
      TopCat.toSSetObjEquiv_toSSet_map_app]
    -- `TopCat.sigmaι X i` is assembled by a tactic block out of `Sigma.mk i` and a continuity
    -- proof, so its underlying continuous map is `ContinuousMap.sigmaMk i` by construction;
    -- Mathlib states nothing about that map beyond its definition, so there is no rewrite to
    -- perform.  The `change` puts that identification in the goal, leaving the `rfl` to unfold
    -- `Equiv.sigmaCongrRight` on the right-hand side.
    change (ContinuousMap.sigmaMk i).comp _ = _
    rfl
  rw [hfun]
  exact (Equiv.bijective _).comp (key.comp (Equiv.bijective _))

/-- In each degree, the singular simplices of a disjoint union form the coproduct of the singular
simplices of the summands. -/
def isColimitCofanToSSetObj :
    IsColimit (Cofan.mk ((toSSet.obj (of (Σ i, X i))).obj n)
      (fun i ↦ (toSSet.map (sigmaι X i)).app n) : Cofan fun i ↦ (toSSet.obj (X i)).obj n) :=
  ((Cofan.nonempty_isColimit_iff_bijective_fromSigma _).2
    (toSSet_map_sigmaι_app_bijective X n)).some

/-- The step from the degreewise statement to the functorial one: `TopCat.toSSet` preserves the
coproduct of the single family `X`, because colimits of simplicial sets are computed degreewise.
Only the shape-wide instance below is needed downstream. -/
private instance preservesColimit_discreteFunctor_toSSet :
    PreservesColimit (Discrete.functor X) toSSet.{w} :=
  preservesColimit_of_evaluation _ _ fun n ↦
    preservesColimit_of_preserves_colimit_cocone (sigmaCofanIsColimit X)
      ((isColimitMapCoconeCofanMkEquiv _ _ _).symm (isColimitCofanToSSetObj X n))

/-- The singular simplicial set functor preserves coproducts of families indexed by `ι`. -/
instance : PreservesColimitsOfShape (Discrete ι) toSSet.{w} where
  preservesColimit := preservesColimit_of_iso_diagram _ Discrete.natIsoFunctor.symm

/-- The singular simplicial set of a disjoint union of spaces is the coproduct of the singular
simplicial sets of the summands. -/
def isColimitCofanToSSet :
    IsColimit (Cofan.mk (toSSet.obj (of (Σ i, X i)))
      (fun i ↦ toSSet.map (sigmaι X i)) : Cofan fun i ↦ toSSet.obj (X i)) :=
  isColimitCofanMkObjOfIsColimit toSSet X _ (sigmaCofanIsColimit X)

variable (C : Type u) [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C] (R : C)

/-- The singular chain complex with coefficients in `R` preserves coproducts of families indexed
by `ι`: it is the singular simplicial set functor followed by the simplicial chain complex
functor, and both preserve them. -/
instance : PreservesColimitsOfShape (Discrete ι)
    ((AlgebraicTopology.singularChainComplexFunctor.{w} C).obj R) :=
  inferInstanceAs (PreservesColimitsOfShape (Discrete ι)
    (toSSet.{w} ⋙ (SSet.chainComplexFunctor.{w} C).obj R))

/-- **Additivity of singular chains.** The singular chain complex of a disjoint union of spaces,
with coefficients in `R`, is the coproduct of the singular chain complexes of the summands, with
the inclusions of the summands as the cofan legs. -/
def isColimitCofanSingularChainComplex :
    IsColimit (Cofan.mk
      (((AlgebraicTopology.singularChainComplexFunctor.{w} C).obj R).obj (of (Σ i, X i)))
      (fun i ↦ ((AlgebraicTopology.singularChainComplexFunctor.{w} C).obj R).map (sigmaι X i)) :
      Cofan fun i ↦ ((AlgebraicTopology.singularChainComplexFunctor.{w} C).obj R).obj (X i)) :=
  isColimitCofanMkObjOfIsColimit _ X _ (sigmaCofanIsColimit X)

end TauCeti
