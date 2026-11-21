/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
public import TauCeti.Algebra.Category.ModuleCat.AB
public import TauCeti.Algebra.Homology.ShortComplex.Colimit
public import TauCeti.AlgebraicTopology.Singular.Twisted.CompactSupport
public import TauCeti.Topology.Category.TopCat.Subspace

/-!
# Twisted singular homology of a directed union

Let `L` be a local coefficient system on a space `X`, and let `U j` be a directed family of
subsets of a subset `V` of `X` which absorbs the compact subsets of `V`: every compact subset of
`V` lies in some `U j`. A singular simplex has compact image and a twisted chain has finitely many
simplices in its support, so every twisted chain of `V` comes from some `U j`. Twisted singular
chains of the members, with `L` restricted to them, therefore form a colimit cocone with apex the
twisted chains of `V`, and since homology commutes with filtered colimits of modules, twisted
singular homology of `V` is the colimit of the twisted singular homology of the `U j`. This is the
compact-supports property of singular homology with local coefficients; for constant coefficients
it is `TauCeti.isColimitMapCoconeSingularHomology`.

The typical family is the skeleta of a relative CW complex, which absorb its compact subsets;
this gives the twisted homology of an infinite-dimensional complex as a colimit over its skeleta.

The maps `subsetTwistedChainComplexMap` induced by inclusions of subsets are monomorphisms and
compose as the inclusions do (`TauCeti.LocalCoefficientSystem.subsetTwistedChainComplexMap_self`,
`TauCeti.LocalCoefficientSystem.subsetTwistedChainComplexMap_comp_subsetTwistedChainComplexMap`),
so they form the diagram over the family.

For `V = X` the homology statement is
`TauCeti.LocalCoefficientSystem.isColimitSubsetTwistedHomologyCocone`, proved elementwise on
homology classes. Here the colimit is first established for the chain complexes, relative to an
arbitrary subset `V`, which is the form needed for the skeleta of a relative CW complex inside its
ambient space.

## Main definitions and results

* `TauCeti.LocalCoefficientSystem.mono_subsetTwistedChainComplexMap`: the maps induced by
  inclusions of subsets are monomorphisms.
* `TauCeti.LocalCoefficientSystem.exists_subsetTwistedChainComplexMap_f_eq`: every twisted chain
  of `V` comes from a member of a family absorbing the compact subsets of `V`.
* `TauCeti.LocalCoefficientSystem.subsetTwistedChainComplexDiagram`,
  `TauCeti.LocalCoefficientSystem.subsetTwistedChainComplexCocone`: the twisted chain complexes of
  a monotone family of subsets, with the restricted systems, over the twisted chains of `V`.
* `TauCeti.LocalCoefficientSystem.isColimitSubsetTwistedChainComplexCocone`: when the family is
  directed and absorbs the compact subsets of `V`, the twisted chains of `V` are their colimit.
* `TauCeti.LocalCoefficientSystem.isColimitSubsetTwistedHomologyMapCocone`: twisted singular
  homology of `V` is then the colimit of twisted singular homology of the members.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.1, Proposition 2.6, and Section 3.H.
-/

public section

noncomputable section

open CategoryTheory Limits Simplicial

universe u v w

namespace TauCeti.LocalCoefficientSystem

variable {R : Type u} [Ring R] {X : TopCat.{v}} (L : LocalCoefficientSystem.{u, v, max v w} R X)

section Subset

/-- The elementwise form of `subsetTwistedChainComplexMap_twistedChainComplexMap`. -/
lemma twistedChainComplexMap_f_subsetTwistedChainComplexMap_f_apply {A B : Set X} (h : A ⊆ B)
    {n : ℕ} (y : ((pullback (X := TopCat.of ↥A) (ContinuousMap.subtypeVal A)).obj
      L).twistedChainComplex.X n) :
    ((twistedChainComplexMap (TopCat.ofHom (ContinuousMap.subtypeVal B)) L).f n).hom
        (((subsetTwistedChainComplexMap L h).f n).hom y) =
      ((twistedChainComplexMap (TopCat.ofHom (ContinuousMap.subtypeVal A)) L).f n).hom y := by
  rw [← ModuleCat.comp_apply, ← HomologicalComplex.comp_f,
    subsetTwistedChainComplexMap_twistedChainComplexMap]

/-- The map of twisted chains induced by an inclusion of subsets is a monomorphism. -/
instance mono_subsetTwistedChainComplexMap {A B : Set X} (h : A ⊆ B) :
    Mono (subsetTwistedChainComplexMap L h) :=
  mono_of_mono_fac (subsetTwistedChainComplexMap_twistedChainComplexMap L h)

variable {ι : Type*} {U : ι → Set X} {V : Set X} (hUV : ∀ i, U i ⊆ V)
  (hK : ∀ K : Set X, IsCompact K → K ⊆ V → ∃ i, K ⊆ U i)

include hK in
/-- A twisted chain of `V` comes, in each degree, from a member of a family of subsets absorbing
the compact subsets of `V`: the images of the finitely many simplices in its support form a
compact subset of `V`. -/
theorem exists_subsetTwistedChainComplexMap_f_eq {n : ℕ}
    (z : ((pullback (X := TopCat.of ↥V) (ContinuousMap.subtypeVal V)).obj
      L).twistedChainComplex.X n) :
    ∃ i y, ((subsetTwistedChainComplexMap L (hUV i)).f n).hom y = z := by
  classical
  let ιV := twistedChainComplexMap (TopCat.ofHom (ContinuousMap.subtypeVal V)) L
  set z' := (ιV.f n).hom z
  -- The pushforward of `z` to `X` is supported in `V`.
  have hz'V : z' ∈ smallTwistedChains L (fun _ : Unit ↦ V) n := by
    rw [← range_twistedChainComplexMap_subtypeVal_f]
    exact LinearMap.mem_range_self _ z
  -- The union of the images of the simplices in its support is a compact subset of `V`.
  set S := {σ : (TopCat.toSSet.obj X) _⦋n⦌ | (twistedChainComplexCoeff L σ).hom z' ≠ 0}
  have hS : S.Finite := finite_support_twistedChainComplexCoeff L z'
  have hσV (σ) (hσ : σ ∈ S) : Set.range (X.toSSetObjEquiv _ σ) ⊆ V := by
    by_contra h
    refine hσ ((mem_smallTwistedChains_iff L _ z').1 hz'V σ fun hσ' ↦ h ?_)
    obtain ⟨-, h'⟩ := (TopCat.mem_smallSingularSubcomplex_iff X _ σ).1 hσ'
    exact h'
  obtain ⟨i, hi⟩ := hK (⋃ σ ∈ S, Set.range (X.toSSetObjEquiv _ σ))
    (hS.isCompact_biUnion fun σ _ ↦ isCompact_range (X.toSSetObjEquiv _ σ).continuous)
    (Set.iUnion₂_subset hσV)
  -- So it is supported in `U i`, hence comes from a twisted chain of `U i`.
  have hz'U : z' ∈ smallTwistedChains L (fun _ : Unit ↦ U i) n := by
    refine (mem_smallTwistedChains_iff L _ z').2 fun σ hσ ↦ ?_
    by_contra h
    exact hσ ((TopCat.mem_smallSingularSubcomplex_iff X _ σ).2
      ⟨(), (Set.subset_biUnion_of_mem (u := fun σ ↦ Set.range (X.toSSetObjEquiv _ σ))
        (show σ ∈ S from h)).trans hi⟩)
  rw [← range_twistedChainComplexMap_subtypeVal_f] at hz'U
  obtain ⟨y, hy⟩ := hz'U
  refine ⟨i, y, (ModuleCat.mono_iff_injective (ιV.f n)).1 inferInstance ?_⟩
  rw [twistedChainComplexMap_f_subsetTwistedChainComplexMap_f_apply, hy]

end Subset

section Diagram

variable {J : Type*} [Preorder J] {U : J → Set X} (hU : Monotone U)

/-- The twisted chain complexes of the members of a monotone family `U` of subsets of `X`, with
`L` restricted to each member, and the maps induced by the inclusions. -/
@[expose, simps]
def subsetTwistedChainComplexDiagram : J ⥤ ChainComplex (ModuleCat.{max v w} R) ℕ where
  obj j := ((pullback (X := TopCat.of ↥(U j)) (ContinuousMap.subtypeVal (U j))).obj
    L).twistedChainComplex
  map f := subsetTwistedChainComplexMap L (hU f.le)
  map_id j := subsetTwistedChainComplexMap_self L (U j)
  map_comp _ _ := (subsetTwistedChainComplexMap_comp_subsetTwistedChainComplexMap L _ _).symm

variable {V : Set X} (hUV : ∀ j, U j ⊆ V)

/-- The cocone over `subsetTwistedChainComplexDiagram` with apex the twisted chains of a subset
`V` containing every member, with legs the maps induced by the inclusions. -/
@[expose, simps]
def subsetTwistedChainComplexCocone : Cocone (subsetTwistedChainComplexDiagram L hU) where
  pt := ((pullback (X := TopCat.of ↥V) (ContinuousMap.subtypeVal V)).obj L).twistedChainComplex
  ι :=
    { app j := subsetTwistedChainComplexMap L (hUV j)
      naturality _ _ _ :=
        (subsetTwistedChainComplexMap_comp_subsetTwistedChainComplexMap L _ _).trans
          (Category.comp_id _).symm }

end Diagram

section Colimit

variable {J : Type} [Preorder J] [IsDirected J (· ≤ ·)] {U : J → Set X}
  (hU : Monotone U) {V : Set X} (hUV : ∀ j, U j ⊆ V)
  (hK : ∀ K : Set X, IsCompact K → K ⊆ V → ∃ j, K ⊆ U j)

include hK in
/-- **Twisted singular chains have compact supports.** For a monotone directed family `U` of
subsets of `V` absorbing the compact subsets of `V`, the twisted chains of `V` are the colimit of
the twisted chains of the members, with `L` restricted to each. -/
def isColimitSubsetTwistedChainComplexCocone :
    IsColimit (subsetTwistedChainComplexCocone L hU hUV) :=
  HomologicalComplex.isColimitOfEval _ _ fun n ↦ by
    -- Detect the colimit on underlying sets, through abelian groups: the forgetful functor of
    -- modules does not preserve filtered colimits when the ring and the modules live in
    -- different universes, but those of modules to abelian groups and of abelian groups do.
    have : Nonempty J := let ⟨j, _⟩ := hK ∅ isCompact_empty (Set.empty_subset _); ⟨j⟩
    have : PreservesFilteredColimitsOfSize.{0, 0} (forget AddCommGrpCat.{max v w}) :=
      preservesSmallestFilteredColimits_of_preservesFilteredColimits _
    have : ReflectsColimitsOfShape J (forget AddCommGrpCat.{max v w}) :=
      reflectsColimitsOfShape_of_reflectsIsomorphisms
    have : ReflectsColimitsOfShape J (forget₂ (ModuleCat.{max v w} R) AddCommGrpCat.{max v w}) :=
      reflectsColimitsOfShape_of_reflectsIsomorphisms
    refine isColimitOfReflects (forget₂ (ModuleCat.{max v w} R) AddCommGrpCat ⋙ forget _)
      (Types.FilteredColimit.isColimitOf' _ _ (fun z ↦ ?_) fun j y y' h ↦ ⟨j, 𝟙 j, ?_⟩)
    · obtain ⟨j, y, hy⟩ := exists_subsetTwistedChainComplexMap_f_eq L hUV hK z
      exact ⟨j, y, hy.symm⟩
    · -- The legs are injective: followed by the split mono to the chains of `X`, they give the
      -- split mono from the chains of `U j`.
      have : Mono ((subsetTwistedChainComplexMap L (hUV j)).f n) := mono_of_mono_fac (by
        rw [← HomologicalComplex.comp_f, subsetTwistedChainComplexMap_twistedChainComplexMap])
      exact congrArg _ ((ModuleCat.mono_iff_injective _).1 this h)

include hK in
/-- **Twisted singular homology has compact supports.** For a monotone directed family `U` of
subsets of `V` absorbing the compact subsets of `V`, twisted singular homology of `V` is the
colimit of twisted singular homology of the members, with `L` restricted to each. -/
def isColimitSubsetTwistedHomologyMapCocone (k : ℕ) :
    IsColimit ((HomologicalComplex.homologyFunctor _ _ k).mapCocone
      (subsetTwistedChainComplexCocone L hU hUV)) :=
  have : Nonempty J := let ⟨j, _⟩ := hK ∅ isCompact_empty (Set.empty_subset _); ⟨j⟩
  isColimitOfPreserves _ (isColimitSubsetTwistedChainComplexCocone L hU hUV hK)

end Colimit

end TauCeti.LocalCoefficientSystem
