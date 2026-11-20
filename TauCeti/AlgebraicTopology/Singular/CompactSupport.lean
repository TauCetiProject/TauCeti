/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Sets.Compacts
public import TauCeti.AlgebraicTopology.Singular.DirectedUnion
import TauCeti.Algebra.Category.ModuleCat.FilteredColimits

/-!
# Compact supports of singular homology

Every singular simplex has compact image, so the singular simplicial set and the singular homology
of a topological space `X` are the filtered colimits of those of its compact subsets
`K : Compacts X` (`TopCat.isColimitMapCoconeToSSetCompacts` and
`TauCeti.isColimitMapCoconeSingularHomologyCompacts`). More generally, the same holds for any
monotone family of subsets indexed by a directed preorder whose members absorb every compact subset
(`TauCeti.isColimitMapCoconeToSSetSubset` and `TauCeti.isColimitMapCoconeSingularHomologySubset`).

With coefficients in a module `N`, the colimit statement gives two concrete consequences:

* every singular homology class of `X` is the image of a class of some compact subset `K ⊆ X`
  (`TauCeti.exists_isCompact_singularHomologyMap_subtypeVal_eq`), and in a weakly locally compact
  space it comes from an open subset `U` contained in a compact subset `K`
  (`TauCeti.exists_isOpen_isCompact_singularHomologyMap_subtypeVal_eq`);
* a singular homology class of a compact subset `K ⊆ X` whose image in `X` vanishes already
  vanishes in some compact superset `L ⊇ K`
  (`TauCeti.exists_isCompact_singularHomologyMap_inclusion_eq_zero`).

## Main definitions and results

* `TauCeti.subsetDiagram` and `TauCeti.subsetCocone`: the diagram of subspaces of a monotone family
  and its cocone of inclusions into `X`.
* `TauCeti.isColimitMapCoconeToSSetSubset` and
  `TauCeti.isColimitMapCoconeSingularHomologySubset`: the singular simplicial set and singular
  homology of `X` as filtered colimits over a monotone family absorbing compact sets.
* `TopCat.compactsDiagram` and `TopCat.compactsCocone`: the diagram of compact subsets
  `Compacts X` of `X` and its cocone of inclusions into `X`.
* `TopCat.isColimitMapCoconeToSSetCompacts` and
  `TauCeti.isColimitMapCoconeSingularHomologyCompacts`: Hatcher's Proposition 3.33, expressing
  singular simplices and singular homology as filtered colimits over `Compacts X`.
* `TauCeti.exists_isCompact_singularHomologyMap_subtypeVal_eq` and
  `TauCeti.exists_isCompact_singularHomologyMap_inclusion_eq_zero`: compact support of classes and
  of homological relations in `Hₖ(X; N)`.
* `TauCeti.exists_isOpen_isCompact_singularHomologyMap_subtypeVal_eq`: in a weakly locally compact
  space, every class of `Hₖ(X; N)` comes from an open set contained in a compact set.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, Proposition 3.33, p. 244.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology Topology TopologicalSpace TopCat Set

universe w v u

namespace TauCeti

section SubsetDiagram

variable {X : TopCat.{w}} {J : Type*} [Preorder J] {U : J → Set X}

/-- The subspaces `U j` of a monotone family in `X`, as a functor on the index preorder. -/
-- Exposed so `obj` computes definitionally in morphism types and `@[simps]` elaborates.
@[expose, simps]
def subsetDiagram (hU : Monotone U) : J ⥤ TopCat.{w} where
  obj j := of ↥(U j)
  map f := ofHom (ContinuousMap.inclusion (hU f.le))
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

/-- The cocone of inclusions `U j ⟶ X` over `TauCeti.subsetDiagram`. -/
-- Exposed so `pt` computes definitionally in leg types and `@[simps]` elaborates.
@[expose, simps]
def subsetCocone (hU : Monotone U) : Cocone (subsetDiagram hU) where
  pt := X
  ι :=
    { app j := ofHom (ContinuousMap.subtypeVal (U j))
      naturality _ _ _ := by
        dsimp [subsetDiagram]
        rw [Category.comp_id]
        exact TopCat.ofHom_inclusion_comp_ofHom_subtypeVal _ }

variable [IsDirected J (· ≤ ·)]

/-- **Singular simplices of a family absorbing compact sets.** If `U` is a monotone family of
subsets of `X` indexed by a directed preorder such that every compact subset of `X` lies in some
`U j`, then the singular simplicial set of `X` is the colimit of those of the `U j`. -/
def isColimitMapCoconeToSSetSubset (hU : Monotone U)
    (hK : ∀ K : Set X, IsCompact K → ∃ j, K ⊆ U j) :
    IsColimit (toSSet.mapCocone (subsetCocone hU)) :=
  have : Nonempty J := ⟨(hK ∅ isCompact_empty).choose⟩
  isColimitMapCoconeToSSet (subsetCocone hU)
    (fun _ ↦ IsEmbedding.subtypeVal)
    fun K hKc ↦ (hK K hKc).imp fun _ hj x hx ↦ ⟨⟨x, hj hx⟩, rfl⟩

/-- **Singular homology of a family absorbing compact sets.** If `U` is a monotone family of
subsets of `X` indexed by a directed preorder such that every compact subset of `X` lies in some
`U j`, then the singular homology of `X` is the colimit of the singular homology of the `U j`,
whenever filtered colimits of shape `J` exist in `Type w` and are exact in `C`. -/
def isColimitMapCoconeSingularHomologySubset {C : Type u} [Category.{v} C] [HasCoproducts.{w} C]
    [Abelian C] (R : C) (k : ℕ) [HasColimitsOfShape J (Type w)] [HasColimitsOfShape J C]
    [HasExactColimitsOfShape J C] (hU : Monotone U)
    (hK : ∀ K : Set X, IsCompact K → ∃ j, K ⊆ U j) :
    IsColimit (((singularHomologyFunctor C k).obj R).mapCocone (subsetCocone hU)) :=
  have : Nonempty J := ⟨(hK ∅ isCompact_empty).choose⟩
  isColimitMapCoconeSingularHomology R k (subsetCocone hU)
    (fun _ ↦ IsEmbedding.subtypeVal)
    fun K hKc ↦ (hK K hKc).imp fun _ hj x hx ↦ ⟨⟨x, hj hx⟩, rfl⟩

end SubsetDiagram

end TauCeti

namespace TopCat

/-- The diagram of compact subsets `Compacts X` of `X`, ordered by inclusion. -/
-- Exposed so `obj K` computes to `of K` in the types of `compactsDiagram_map` and cocone legs.
@[expose]
def compactsDiagram (X : TopCat.{w}) : Compacts X ⥤ TopCat.{w} :=
  TauCeti.subsetDiagram (U := SetLike.coe) fun _ _ h ↦ h

@[simp]
theorem compactsDiagram_obj (X : TopCat.{w}) (K : Compacts X) :
    X.compactsDiagram.obj K = of K :=
  (rfl)

@[simp]
theorem compactsDiagram_map (X : TopCat.{w}) {K L : Compacts X} (f : K ⟶ L) :
    X.compactsDiagram.map f = ofHom (ContinuousMap.inclusion (s := (K : Set X)) f.le) :=
  (rfl)

/-- The cocone of inclusions `K ⟶ X` over the diagram `TopCat.compactsDiagram` of compact subsets
of `X`. -/
-- Exposed so `pt` computes to `X` in the type of `compactsCocone_ι_app` and colimit consumers.
@[expose]
def compactsCocone (X : TopCat.{w}) : Cocone X.compactsDiagram :=
  TauCeti.subsetCocone (U := SetLike.coe) fun _ _ h ↦ h

@[simp]
theorem compactsCocone_pt (X : TopCat.{w}) : X.compactsCocone.pt = X :=
  (rfl)

@[simp]
theorem compactsCocone_ι_app (X : TopCat.{w}) (K : Compacts X) :
    X.compactsCocone.ι.app K = ofHom (ContinuousMap.subtypeVal (K : Set X)) :=
  (rfl)

/-- **Singular simplices are the colimit over compact subsets.** The singular simplicial set of `X`
is the filtered colimit of the singular simplicial sets of the compact subsets of `X`. -/
def isColimitMapCoconeToSSetCompacts (X : TopCat.{w}) :
    IsColimit (toSSet.mapCocone X.compactsCocone) :=
  TauCeti.isColimitMapCoconeToSSetSubset (X := X) (U := fun K : Compacts X ↦ (K : Set X))
    (fun _ _ h ↦ h) fun K hK ↦ ⟨⟨K, hK⟩, subset_rfl⟩

end TopCat

namespace TauCeti

section CompactSubsets

/-- **Singular homology is the colimit over compact subsets** (Hatcher, Proposition 3.33). In every
degree, the singular homology of `X` is the filtered colimit of the singular homology of the
compact subsets `Compacts X` of `X`, provided filtered colimits over `Compacts X` are exact in
`C`. -/
def isColimitMapCoconeSingularHomologyCompacts {C : Type u} [Category.{v} C]
    [HasCoproducts.{w} C] [Abelian C] (R : C) (k : ℕ) (X : TopCat.{w})
    [HasColimitsOfShape (Compacts X) C] [HasExactColimitsOfShape (Compacts X) C] :
    IsColimit (((singularHomologyFunctor C k).obj R).mapCocone X.compactsCocone) :=
  isColimitMapCoconeSingularHomologySubset (X := X) (U := fun K : Compacts X ↦ (K : Set X))
    R k (fun _ _ h ↦ h) fun K hK ↦ ⟨⟨K, hK⟩, subset_rfl⟩

variable {Λ : Type*} [Ring Λ] (N : ModuleCat.{w} Λ) (k : ℕ) {Y : Type w} [TopologicalSpace Y]

/-- **Every singular homology class is supported on a compact set** (Hatcher, Proposition 3.33).
With coefficients in a module `N`, every class of `Hₖ(Y; N)` is the image of a class of `Hₖ(K; N)`
for some compact subset `K ⊆ Y`. -/
theorem exists_isCompact_singularHomologyMap_subtypeVal_eq
    (x : ((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj (of Y)) :
    ∃ (K : Set Y) (_ : IsCompact K)
      (y : ((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj (of ↥K)),
      ((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).map
        (ofHom (ContinuousMap.subtypeVal K)) y = x := by
  obtain ⟨K, y, hy⟩ :=
    Concrete.isColimit_exists_rep _ (isColimitMapCoconeSingularHomologyCompacts N k (of Y)) x
  exact ⟨K.carrier, K.isCompact', y, hy⟩

/-- **A class on a compact subset that vanishes in the space vanishes in a compact superset**
(Hatcher, Proposition 3.33). If `K ⊆ Y` is compact and `y ∈ Hₖ(K; N)` maps to zero in `Hₖ(Y; N)`,
then `y` already maps to zero in `Hₖ(L; N)` for some compact `L` with `K ⊆ L`. -/
theorem exists_isCompact_singularHomologyMap_inclusion_eq_zero {K : Set Y} (hK : IsCompact K)
    (y : ((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj (of ↥K))
    (hy : ((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).map
      (ofHom (ContinuousMap.subtypeVal K)) y = 0) :
    ∃ (L : Set Y) (_ : IsCompact L) (hKL : K ⊆ L),
      ((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).map
        (ofHom (ContinuousMap.inclusion hKL)) y = 0 := by
  let K₀ : Compacts (of Y) := ⟨K, hK⟩
  obtain ⟨L, f, g, hfg⟩ := Concrete.isColimit_exists_of_rep_eq (i := K₀) (j := K₀) _
    (isColimitMapCoconeSingularHomologyCompacts N k (of Y)) y 0 (by rw [map_zero]; exact hy)
  dsimp only [Functor.comp_map, compactsDiagram_map] at hfg
  rw [map_zero] at hfg
  exact ⟨L.carrier, L.isCompact', f.le, hfg⟩

/-- **In a weakly locally compact space, every homology class comes from an open set contained in a
compact set.** Every class of `Hₖ(Y; N)` is the image of a class of `Hₖ(U; N)` for an open subset
`U` contained in a compact subset `K` of `Y`. -/
theorem exists_isOpen_isCompact_singularHomologyMap_subtypeVal_eq [WeaklyLocallyCompactSpace Y]
    (x : ((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj (of Y)) :
    ∃ (U K : Set Y), IsOpen U ∧ IsCompact K ∧ U ⊆ K ∧
      ∃ u : ((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj (of ↥U),
        ((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).map
          (ofHom (ContinuousMap.subtypeVal U)) u = x := by
  obtain ⟨A, hA, a, rfl⟩ := exists_isCompact_singularHomologyMap_subtypeVal_eq N k x
  obtain ⟨K, hK, hAK⟩ := exists_compact_superset hA
  refine ⟨interior K, K, isOpen_interior, hK, interior_subset,
    ((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).map (ofHom (ContinuousMap.inclusion hAK))
      a, ?_⟩
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp,
    TopCat.ofHom_inclusion_comp_ofHom_subtypeVal]

end CompactSubsets

end TauCeti
