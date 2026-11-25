/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import TauCeti.Algebra.Category.ModuleCat.AB
public import TauCeti.Algebra.Homology.ShortComplex.Colimit
public import TauCeti.AlgebraicTopology.Singular.Twisted.CompactSupport.Basic
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

The maps `subsetTwistedChainComplexMap` induced by inclusions of subsets form the diagram
`TauCeti.LocalCoefficientSystem.subsetTwistedChainComplexDiagram` over the family, whose homology
is `TauCeti.LocalCoefficientSystem.subsetTwistedHomologyFunctor`.

For `V = X` the homology statement is
`TauCeti.LocalCoefficientSystem.isColimitSubsetTwistedHomologyCocone`, proved elementwise on
homology classes. Here the colimit is first established for the chain complexes, relative to an
arbitrary subset `V`, which is the form needed for the skeleta of a relative CW complex inside its
ambient space.

## Main definitions and results

* `TauCeti.LocalCoefficientSystem.exists_subsetTwistedChainComplexMap_f_eq`: every twisted chain
  of `V` comes from a member of a family absorbing the compact subsets of `V`.
* `TauCeti.LocalCoefficientSystem.subsetTwistedChainComplexCocone`: the twisted chain complexes of
  a monotone family of subsets, with the restricted systems, over the twisted chains of `V`.
* `TauCeti.LocalCoefficientSystem.isColimitSubsetTwistedChainComplexCocone`: when the family is
  directed and absorbs the compact subsets of `V`, the twisted chains of `V` are their colimit.
* `TauCeti.LocalCoefficientSystem.isColimitMapCoconeTwistedHomologySubset`: twisted singular
  homology of `V` is then the colimit of twisted singular homology of the members.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.1, Proposition 2.6, and Section 3.H.
-/

public section

noncomputable section

open CategoryTheory Limits Simplicial

universe u v w t

namespace TauCeti.LocalCoefficientSystem

variable {R : Type u} [Ring R] {X : TopCat.{v}} (L : LocalCoefficientSystem.{u, v, max v w} R X)

section Subset

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
  let ιV := twistedChainComplexMap (TopCat.ofHom (ContinuousMap.subtypeVal V)) L
  -- The compact support of the pushforward of `z` to `X` lies in `V`, hence in some `U i`.
  obtain ⟨K, hKc, hKA⟩ :=
    exists_isCompact_forall_subset_iff_mem_range_twistedChainComplexMap_f L ((ιV.f n).hom z)
  obtain ⟨i, hi⟩ := hK K hKc ((hKA V).2 (LinearMap.mem_range_self _ z))
  obtain ⟨y, hy⟩ := (hKA (U i)).1 hi
  refine ⟨i, y, (ModuleCat.mono_iff_injective (ιV.f n)).1 inferInstance ?_⟩
  rw [twistedChainComplexMap_f_subsetTwistedChainComplexMap_f_apply, hy]

end Subset

section Cocone

variable {J : Type*} [Preorder J] {U : J → Set X} (hU : Monotone U) {V : Set X}
  (hUV : ∀ j, U j ⊆ V)

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

end Cocone

section Colimit

variable {J : Type*} [Preorder J] [IsDirectedOrder J] {U : J → Set X}
  (hU : Monotone U) {V : Set X} (hUV : ∀ j, U j ⊆ V)
  (hK : ∀ K : Set X, IsCompact K → K ⊆ V → ∃ j, K ⊆ U j)

include hK in
/-- **Twisted singular chains have compact supports.** For a monotone directed family `U` of
subsets of `V` absorbing the compact subsets of `V`, the twisted chains of `V` are the colimit of
the twisted chains of the members, with `L` restricted to each. -/
def isColimitSubsetTwistedChainComplexCocone :
    IsColimit (subsetTwistedChainComplexCocone L hU hUV) :=
  HomologicalComplex.isColimitOfEval _ _ fun n ↦
    TauCeti.ModuleCat.isColimitOfJointlySurjectiveOfMapEqZero _
      (fun z ↦ exists_subsetTwistedChainComplexMap_f_eq L hUV hK z) fun i x hx ↦ ⟨i, le_rfl, by
        -- The leg at `i` is injective, by `mono_subsetTwistedChainComplexMap_f`.
        obtain rfl : x = 0 :=
          (ModuleCat.mono_iff_injective ((subsetTwistedChainComplexMap L (hUV i)).f n)).1
            inferInstance (hx.trans (map_zero _).symm)
        exact map_zero _⟩

end Colimit

section HomologyColimit

variable {J : Type t} [Preorder J] [IsDirectedOrder J] [UnivLE.{t, max v w}] {U : J → Set X}
  (hU : Monotone U) {V : Set X} (hUV : ∀ j, U j ⊆ V)
  (hK : ∀ K : Set X, IsCompact K → K ⊆ V → ∃ j, K ⊆ U j)

include hK in
/-- **Twisted singular homology has compact supports.** For a monotone directed family `U` of
subsets of `V` absorbing the compact subsets of `V`, twisted singular homology of `V` is the
colimit of twisted singular homology of the members, with `L` restricted to each. The cocone lives
over `subsetTwistedHomologyFunctor L hU k`. -/
def isColimitMapCoconeTwistedHomologySubset (k : ℕ) :
    IsColimit ((HomologicalComplex.homologyFunctor _ _ k).mapCocone
      (subsetTwistedChainComplexCocone L hU hUV)) :=
  have : Nonempty J := let ⟨j, _⟩ := hK ∅ isCompact_empty (Set.empty_subset _); ⟨j⟩
  isColimitOfPreserves _ (isColimitSubsetTwistedChainComplexCocone L hU hUV hK)

end HomologyColimit

end TauCeti.LocalCoefficientSystem
