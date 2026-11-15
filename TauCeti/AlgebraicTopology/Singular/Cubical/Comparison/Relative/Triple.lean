/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Relative.Basic
public import TauCeti.CategoryTheory.Abelian.DiagramLemmas.CokernelComp
public import TauCeti.Topology.Category.TopTriple

/-!
# The short exact sequence of a triple in relative cubical chains

For a triple `B ⊆ A ⊆ X` of topological spaces the relative normalized cubical chain complexes of
the three pairs it determines form a short exact sequence

`0 ⟶ N(A, B) ⟶ N(X, B) ⟶ N(X, A) ⟶ 0`

(`TauCeti.TopTriple.shortExact_cubicalChainComplexShortComplex`), because each of them is the
quotient of the chains of the ambient space by those of the subspace. This is the cubical form of
`TauCeti.TopTriple.shortExact_singularChainComplexShortComplex`; its long homology sequence is the
long exact sequence of the triple in cubical homology.

## Main definitions

* `TauCeti.TopTriple.cubicalChainComplexShortComplex`: the sequence
  `N(A, B) ⟶ N(X, B) ⟶ N(X, A)` of a triple `(X, A, B)`.

## Main results

* `TauCeti.TopTriple.cubicalChainComplexMap_innerToTotal_comp_totalToOuter`: the two maps compose
  to zero.
* `TauCeti.TopTriple.shortExact_cubicalChainComplexShortComplex`: the sequence is short exact.

## References

* S. Eilenberg and N. Steenrod, *Foundations of Algebraic Topology*, Princeton, 1952,
  Chapters I–III.
-/

public section

noncomputable section

open CategoryTheory Limits

universe u

namespace TauCeti

namespace TopTriple

variable (k : Type u) [Ring k] (T : TopTriple.{u})

/-- The maps `N(A, B) ⟶ N(X, B) ⟶ N(X, A)` of relative cubical chains of a triple `(X, A, B)`
compose to zero: their composite is induced by the map of pairs `(A, B) ⟶ (X, A)`, which carries
`A` into the subspace of the target. -/
@[reassoc (attr := simp)]
theorem cubicalChainComplexMap_innerToTotal_comp_totalToOuter :
    TopPair.cubicalChainComplexMap k (innerToTotal.app T) ≫
      TopPair.cubicalChainComplexMap k (totalToOuter.app T) = 0 := by
  refine (cancel_epi (cokernel.π _)).1 ?_
  rw [Limits.comp_zero, ← TopPair.cubicalChainComplexMap_comp, TopPair.π_cubicalChainComplexMap,
    TopPair.Hom.fst_comp, innerToTotal_app_fst, totalToOuter_app_fst, Category.comp_id]
  exact cokernel.condition ((normalizedCubicalChainComplex k).map (outerPair.obj T).map)

/-- The sequence `N(A, B) ⟶ N(X, B) ⟶ N(X, A)` of relative normalized cubical chains of a triple
`(X, A, B)`. -/
abbrev cubicalChainComplexShortComplex : ShortComplex (ChainComplex (ModuleCat.{u} k) ℕ) :=
  ShortComplex.mk _ _ (T.cubicalChainComplexMap_innerToTotal_comp_totalToOuter k)

/-- **The short exact sequence of a triple** `0 ⟶ N(A, B) ⟶ N(X, B) ⟶ N(X, A) ⟶ 0` of relative
normalized cubical chains. -/
theorem shortExact_cubicalChainComplexShortComplex :
    (T.cubicalChainComplexShortComplex k).ShortExact := by
  -- On the chains of the ambient space `X`, the map of pairs `(X, B) ⟶ (X, A)` is the identity.
  have hv : cokernel.π ((normalizedCubicalChainComplex k).map T.totalMap) ≫
      TopPair.cubicalChainComplexMap k (totalToOuter.app T) =
        cokernel.π ((normalizedCubicalChainComplex k).map T.outerMap) := by
    refine (TopPair.π_cubicalChainComplexMap k (totalToOuter.app T)).trans ?_
    rw [totalToOuter_app_fst, CategoryTheory.Functor.map_id, Category.id_comp]
  exact shortExact_of_isColimit_cokernelCofork
    (f := (normalizedCubicalChainComplex k).map T.innerMap)
    (g := (normalizedCubicalChainComplex k).map T.outerMap)
    (k := (normalizedCubicalChainComplex k).map T.totalMap)
    (u := TopPair.cubicalChainComplexMap k (innerToTotal.app T))
    (v := TopPair.cubicalChainComplexMap k (totalToOuter.app T))
    (by rw [← Functor.map_comp, T.innerMap_comp_outerMap])
    (TopPair.mono_normalizedCubicalChainComplex_map k (outerPair.obj T))
    (colimit.isColimit _) (colimit.isColimit _) (colimit.isColimit _)
    (TopPair.π_cubicalChainComplexMap k (innerToTotal.app T)) hv

end TopTriple

end TauCeti
