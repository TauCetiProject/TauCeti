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
public import Mathlib.Topology.Sets.Opens
public import TauCeti.Algebra.Homology.ShortComplex.Colimit
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Coproduct
public import TauCeti.AlgebraicTopology.SimplicialSet.TopAdj
public import TauCeti.AlgebraicTopology.Singular.Relative
public import TauCeti.Topology.Category.TopPair
public import TauCeti.Topology.Connected.Basic

/-!
# Additivity of singular chains and singular homology

A singular simplex of a disjoint union `Σ i, X i` has connected domain, so its image lies in a
single summand, and it comes from a singular simplex of that summand in exactly one way.  Hence
the singular simplicial set of a disjoint union is the coproduct of the singular simplicial sets
of the summands, and, since the simplicial chain complex functor preserves colimits, so is the
singular chain complex.

Passing to homology needs one more input: homology commutes with the coproduct of chain
complexes when coproducts are exact in the coefficient category (Grothendieck's axiom AB4, as for
modules over a ring).  Under that hypothesis the singular homology of a disjoint union is the
coproduct of the singular homologies of the summands in every degree.  This is the additivity
axiom of Eilenberg--Steenrod.

The same holds for relative singular chains and relative singular homology of the disjoint union
`TopPair.sigma P = ∐ᵢ (Xᵢ, Aᵢ)` of a family of topological pairs: relative chains are the cokernel
of the map from the chains of the subspace to those of the ambient space, both of which are
additive, and cokernels commute with coproducts.

Every map in sight is induced by one of the inclusions `X i ⟶ Σ i, X i`, so the results are
statements about cofans rather than unrelated degreewise decompositions.

The same holds for a union `⨆ i, s i` of pairwise disjoint open subsets `s i` of a space, with
the inclusions `s i → ⨆ i, s i` as the cofan legs: a singular simplex of the union has connected
image, so it lies in exactly one of the open sets `s i`. This is the form in which additivity
enters inductions over the open subsets of a space.

## Main results

* `TauCeti.isColimitCofanSingularChainComplex`: the singular chain complex of `Σ i, X i` is the
  coproduct of the singular chain complexes of the `X i`.
* `TauCeti.isColimitCofanSingularHomology`: if coproducts indexed by `ι` are exact in the
  coefficient category, the singular homology of `Σ i, X i` in each degree is the coproduct of the
  singular homologies of the `X i`.
* `TauCeti.isColimitCofanSingularChainComplexOpens`,
  `TauCeti.isColimitCofanSingularHomologyOpens`: the same for a union of pairwise disjoint open
  subsets of a space.
* `TopPair.isColimitCofanSingularChainComplex` and `TopPair.isColimitCofanSingularHomology`: the
  same for the relative singular chains and relative singular homology of `∐ᵢ (Xᵢ, Aᵢ)`.
* `TopPair.isColimitCofanSingularHomologyOfIsColimit`: relative singular homology carries every
  coproduct cofan in `TopPair` to a coproduct cofan.

## Sources

The informal source is Eilenberg--Steenrod, *Foundations of Algebraic Topology*, Chapters I--III.
The connectedness argument is Mathlib's `ContinuousMap.sigmaCodHomeomorph`, by Yury Kudryashov in
`Mathlib/Topology/ContinuousMap/Sigma`; the singular simplicial set `TopCat.toSSet` and the singular
chain complex `AlgebraicTopology.singularChainComplexFunctor` are by Andrew Yang in
`Mathlib/AlgebraicTopology/SingularHomology/Basic`, building on Joël Riou's `TopCat.toSSet`
adjunction; and the concrete cofan `TopCat.sigmaCofanIsColimit` is by Patrick Massot, Kim
Morrison, Mario Carneiro and Andrew Yang in `Mathlib/Topology/Category/TopCat/Limits/Products`.
The passage from chains to homology is
`TauCeti.homologicalComplexHomologyFunctor_preservesColimitsOfShape`, in
`TauCeti/Algebra/Homology/ShortComplex/Colimit`, applied with Mathlib's exactness class
`HasExactColimitsOfShape`.  The passage from absolute to relative chains is
`TauCeti.isColimitCofanMkCokernelCofork`, in `TauCeti/CategoryTheory/Limits/Shapes/Products`.
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

section Chains

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

end Chains

section Homology

variable (C : Type u) [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]
  [HasExactColimitsOfShape (Discrete ι) C] (R : C) (k : ℕ)

/-- Singular homology in each degree, with coefficients in `R`, preserves coproducts of families
indexed by `ι` when such coproducts are exact in `C`: it is the singular chain complex followed by
homology, and both preserve them. -/
instance : PreservesColimitsOfShape (Discrete ι)
    ((AlgebraicTopology.singularHomologyFunctor.{w} C k).obj R) := by
  have h : (AlgebraicTopology.singularHomologyFunctor.{w} C k).obj R =
      (AlgebraicTopology.singularChainComplexFunctor.{w} C).obj R ⋙
        HomologicalComplex.homologyFunctor C _ k := by
    rfl
  rw [h]
  infer_instance

/-- **Additivity of singular homology.** If coproducts indexed by `ι` are exact in `C`, then in
every degree the singular homology of a disjoint union of spaces, with coefficients in `R`, is the
coproduct of the singular homologies of the summands, with the maps induced by the inclusions of
the summands as the cofan legs. -/
def isColimitCofanSingularHomology :
    IsColimit (Cofan.mk
      (((AlgebraicTopology.singularHomologyFunctor.{w} C k).obj R).obj (of (Σ i, X i)))
      (fun i ↦ ((AlgebraicTopology.singularHomologyFunctor.{w} C k).obj R).map (sigmaι X i)) :
      Cofan fun i ↦ ((AlgebraicTopology.singularHomologyFunctor.{w} C k).obj R).obj (X i)) :=
  isColimitCofanMkObjOfIsColimit _ X _ (sigmaCofanIsColimit X)

end Homology

section Opens

open Function Set TopologicalSpace

variable {M : Type w} [TopologicalSpace M] (s : ι → Opens M)

/-- In each degree, the singular simplices of a union of pairwise disjoint open sets `s i` are
exactly the singular simplices of the members: the topological simplex is connected, so a
singular simplex of `⨆ i, s i` lies in a unique `s i`, and it comes from a unique singular simplex
there. -/
lemma toSSet_map_inclusion_app_bijective (hs : Pairwise (Disjoint on s)) : Function.Bijective
    (fun p : Σ i, (toSSet.obj (of (s i))).obj n ↦
      (toSSet.map (ofHom ⟨Opens.inclusion (le_iSup s p.1), continuous_inclusion _⟩)).app n
        p.2) := by
  have hs' : Pairwise (Disjoint on fun i ↦ (s i : Set M)) := fun i j hij ↦
    Opens.coe_disjoint.2 (hs hij)
  obtain ⟨x₀⟩ : Nonempty (StdSimplex ℝ (Fin (n.unop.len + 1))) := inferInstance
  refine ⟨?_, fun τ ↦ ?_⟩
  · rintro ⟨i, σ⟩ ⟨j, σ'⟩ h
    have h' (x) : ((toSSetObjEquiv (of (s i)) n σ x : s i) : M) =
        ((toSSetObjEquiv (of (s j)) n σ' x : s j) : M) := by
      have h₁ := congrArg (toSSetObjEquiv (of ↥(⨆ i, s i)) n) h
      dsimp only at h₁
      rw [TopCat.toSSetObjEquiv_toSSet_map_app, TopCat.toSSetObjEquiv_toSSet_map_app] at h₁
      simpa using congrArg (fun f ↦ (f x : M)) h₁
    obtain rfl : i = j := by
      by_contra hij
      exact (hs' hij).ne_of_mem (toSSetObjEquiv _ n σ x₀).2 (toSSetObjEquiv _ n σ' x₀).2 (h' x₀)
    refine Sigma.ext rfl (heq_of_eq ((toSSetObjEquiv (of (s i)) n).injective ?_))
    ext x
    exact h' x
  · let f := toSSetObjEquiv (of ↥(⨆ i, s i)) n τ
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (f x₀).2
    have hrange : range (fun x ↦ (f x : M)) ⊆ s i :=
      (isPreconnected_range (continuous_subtype_val.comp f.continuous)).subset_of_subset_iUnion
        (fun j ↦ (s j).isOpen) hs'
        (by rintro _ ⟨x, rfl⟩; exact mem_iUnion.2 (Opens.mem_iSup.1 (f x).2))
        ⟨_, ⟨x₀, rfl⟩, hi⟩
    refine ⟨⟨i, (toSSetObjEquiv (of (s i)) n).symm
      ⟨fun x ↦ ⟨f x, hrange ⟨x, rfl⟩⟩, by fun_prop⟩⟩, ?_⟩
    apply (toSSetObjEquiv (of ↥(⨆ i, s i)) n).injective
    rw [TopCat.toSSetObjEquiv_toSSet_map_app, Equiv.apply_symm_apply]
    ext x
    simp [f]

/-- The singular simplicial set of a union of pairwise disjoint open sets `s i` is the coproduct
of the singular simplicial sets of the `s i`, with the inclusions as the cofan legs. -/
def isColimitCofanToSSetOpens (hs : Pairwise (Disjoint on s)) :
    IsColimit (Cofan.mk (toSSet.obj (of ↥(⨆ i, s i)))
      (fun i ↦ toSSet.map (ofHom ⟨Opens.inclusion (le_iSup s i), continuous_inclusion _⟩)) :
      Cofan fun i ↦ toSSet.obj (of (s i))) :=
  evaluationJointlyReflectsColimits _ fun n ↦ (isColimitMapCoconeCofanMkEquiv _ _ _).symm
    ((Cofan.nonempty_isColimit_iff_bijective_fromSigma _).2
      (toSSet_map_inclusion_app_bijective n s hs)).some

section Chains

variable (C : Type u) [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C] (R : C)

/-- **Additivity of singular chains over disjoint open sets.** The singular chain complex of a
union of pairwise disjoint open sets `s i`, with coefficients in `R`, is the coproduct of the
singular chain complexes of the `s i`, with the inclusions as the cofan legs. -/
def isColimitCofanSingularChainComplexOpens (hs : Pairwise (Disjoint on s)) :
    IsColimit (Cofan.mk ((toSSet.obj (of ↥(⨆ i, s i))).chainComplex R)
      (fun i ↦ SSet.chainComplexMap
        (toSSet.map (ofHom ⟨Opens.inclusion (le_iSup s i), continuous_inclusion _⟩)) R) :
      Cofan fun i ↦ (toSSet.obj (of (s i))).chainComplex R) :=
  isColimitCofanMkObjOfIsColimit ((SSet.chainComplexFunctor C).obj R) _ _
    (isColimitCofanToSSetOpens s hs)

end Chains

section Homology

variable (C : Type u) [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]
  [HasExactColimitsOfShape (Discrete ι) C] (R : C) (k : ℕ)

/-- **Additivity of singular homology over disjoint open sets.** If coproducts indexed by `ι` are
exact in `C`, then in every degree the singular homology of a union of pairwise disjoint open sets
`s i`, with coefficients in `R`, is the coproduct of the singular homologies of the `s i`, with the
maps induced by the inclusions as the cofan legs. -/
def isColimitCofanSingularHomologyOpens (hs : Pairwise (Disjoint on s)) :
    IsColimit (Cofan.mk ((toSSet.obj (of ↥(⨆ i, s i))).homology R k)
      (fun i ↦ SSet.homologyMap
        (toSSet.map (ofHom ⟨Opens.inclusion (le_iSup s i), continuous_inclusion _⟩)) R k) :
      Cofan fun i ↦ (toSSet.obj (of (s i))).homology R k) :=
  isColimitCofanMkObjOfIsColimit (HomologicalComplex.homologyFunctor C _ k) _ _
    (isColimitCofanSingularChainComplexOpens s C R hs)

end Homology

end Opens

end TauCeti

namespace TopPair

variable {ι : Type w} (P : ι → TopPair.{w})

section Chains

variable (C : Type u) [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C] (R : C)

/-- **Additivity of relative singular chains.** The relative singular chain complex of the
disjoint union `∐ᵢ (Xᵢ, Aᵢ)` of a family of topological pairs, with coefficients in `R`, is the
coproduct of the relative singular chain complexes of the pairs, with the inclusions of the
summands as the cofan legs. -/
def isColimitCofanSingularChainComplex :
    IsColimit (Cofan.mk ((sigma P).singularChainComplex R)
      fun i ↦ singularChainComplexMap (sigmaι P i) R) :=
  -- Relative chains are the cokernels of the maps from subspace chains to ambient chains, and
  -- both of those are additive.
  TauCeti.isColimitCofanMkCokernelCofork
    (fun i ↦ (P i).isColimitCokernelCoforkSingularChainComplex R)
    (TauCeti.isColimitCofanSingularChainComplex (fun i ↦ (P i).snd) C R)
    (TauCeti.isColimitCofanSingularChainComplex (fun i ↦ (P i).fst) C R)
    (fun i ↦ ((Functor.map_comp _ _ _).symm.trans
      ((congrArg ((AlgebraicTopology.singularChainComplexFunctor.{w} C).obj R).map
        (Hom.w (sigmaι P i))).trans (Functor.map_comp _ _ _))))
    ((sigma P).isColimitCokernelCoforkSingularChainComplex R) _
    (fun i ↦ (((SSetPair.chainComplexFunctorπ C).app R).naturality
      (toSSetPair.map (sigmaι P i))).symm)

end Chains

section Homology

variable (C : Type u) [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]
  [HasExactColimitsOfShape (Discrete ι) C] (R : C) (k : ℕ)

/-- **Additivity of relative singular homology.** If coproducts indexed by `ι` are exact in `C`,
then in every degree the relative singular homology of the disjoint union `∐ᵢ (Xᵢ, Aᵢ)` of a
family of topological pairs, with coefficients in `R`, is the coproduct of the relative singular
homologies of the pairs, with the maps induced by the inclusions of the summands as the cofan
legs. -/
def isColimitCofanSingularHomology :
    IsColimit (Cofan.mk ((sigma P).singularHomology R k)
      fun i ↦ TopPair.singularHomologyMap (sigmaι P i) R k) :=
  isColimitCofanMkObjOfIsColimit (HomologicalComplex.homologyFunctor C _ k) _ _
    (isColimitCofanSingularChainComplex P C R)

variable {P} in
/-- **Additivity of relative singular homology along any coproduct of pairs.** If coproducts
indexed by `ι` are exact in `C`, relative singular homology carries every coproduct cofan of
topological pairs, not only the disjoint union `∐ᵢ (Xᵢ, Aᵢ)`, to a coproduct cofan in every
degree. -/
def isColimitCofanSingularHomologyOfIsColimit {c : Cofan P} (hc : IsColimit c) :
    IsColimit (Cofan.mk (c.pt.singularHomology R k)
      fun i ↦ TopPair.singularHomologyMap (c.inj i) R k) :=
  let e := (sigmaCofanIsColimit P).coconePointUniqueUpToIso hc
  IsColimit.ofIsoColimit (isColimitCofanSingularHomology P C R k)
    (Cofan.ext
      { hom := TopPair.singularHomologyMap e.hom R k
        inv := TopPair.singularHomologyMap e.inv R k
        hom_inv_id := by
          rw [← singularHomologyMap_comp, e.hom_inv_id, singularHomologyMap_id]
          rfl
        inv_hom_id := by
          rw [← singularHomologyMap_comp, e.inv_hom_id, singularHomologyMap_id]
          rfl }
      fun i ↦ (singularHomologyMap_comp _ _ _ _).symm.trans
        (congrArg (TopPair.singularHomologyMap · R k)
          ((sigmaCofanIsColimit P).comp_coconePointUniqueUpToIso_hom hc ⟨i⟩)))

end Homology

end TopPair
