/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.FiniteRepType.AffineSubgraph
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Signless.Affine.D
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Signless.Affine.E

/-!
# Nonzero cyclic classes of non-Dynkin trees

Let `G` be a finite tree which is not a Dynkin diagram. This file shows that the cyclic quotient
`Π⁺(G) / [Π⁺(G), Π⁺(G)]` of the signless preprojective algebra of `G`, its zeroth Hochschild
homology, is nonzero in some positive path degree, namely `4`, `6`, `8` or `12`, over every
nontrivial commutative ring. Since a tree is bipartite, `Π⁺(G)` is isomorphic to the additive
preprojective algebra of any orientation of `G`
(`SimpleGraph.IsBipartite.signlessPreprojectiveAlgebraEquiv`).

The tree contains a copy of affine `Dₙ` (`n ≥ 4`), `E₆`, `E₇` or `E₈`
(`SimpleGraph.IsTree.isContained_affineDynkinType_of_not_exists_dynkinType_iso`), and each of
these produces a nonzero cyclic class, in degree `4`, `6`, `8` or `12` respectively
(`TauCeti.exists_mem_signlessPreprojectiveGrade_four_notMem_commutatorSubmodule` and its
companions for `E₆`, `E₇` and `E₈`). For a quiver whose underlying graph is a tree, Liu and Wang
identify the degree-`(q + 2)` piece of this cyclic quotient with the second Hochschild cohomology
`HH^{2,q}` of the two-dimensional Ginzburg algebra `Π₂(Q)`, which controls the `A∞` deformations
of the zigzag algebra of the tree. A nonzero class in positive degree is the input to their
theorem that the zigzag algebra of a non-Dynkin tree is not intrinsically formal.

## Main results

* `SimpleGraph.IsTree.exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule`: a
  finite tree which is not a Dynkin diagram has a nonzero cyclic class in path degree `4`, `6`,
  `8` or `12`.

## References

* Y. Liu and Z. Wang, *A-infinity deformations of zigzag algebras via Ginzburg dg algebras*,
  https://arxiv.org/abs/2301.06757, for the role of the cyclic quotient of the preprojective
  algebra.
-/

public section

namespace SimpleGraph.IsTree

open TauCeti

universe u w

variable {k : Type w} [CommRing k] {V : Type u} [Fintype V] {G : SimpleGraph V}
  [DecidableRel G.Adj]

/-- **Non-Dynkin trees have nonzero cyclic classes in positive degree.** If a finite tree `G` is
not isomorphic to the diagram of any valid Dynkin type, then over every nontrivial commutative
ring some element of path degree `4`, `6`, `8` or `12` of the signless preprojective algebra
`Π⁺(G)` does not lie in the commutator submodule `[Π⁺(G), Π⁺(G)]`: its class in the cyclic
quotient is nonzero. -/
theorem exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule
    [Nontrivial k] (hG : G.IsTree)
    (hD : ¬ ∃ t : DynkinType, t.Valid ∧ Nonempty (G ≃g diagramGraph t.cartanMatrix)) :
    ∃ d ∈ ({4, 6, 8, 12} : Finset ℕ), ∃ x ∈ signlessPreprojectiveGrade k (DoubledQuiver G) d,
      x ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  rcases hG.isContained_affineDynkinType_of_not_exists_dynkinType_iso hD with
    ⟨n, hn, h⟩ | h | h | h
  · exact ⟨4, by simp, exists_mem_signlessPreprojectiveGrade_four_notMem_commutatorSubmodule hn h⟩
  · exact ⟨6, by simp, exists_mem_signlessPreprojectiveGrade_six_notMem_commutatorSubmodule h⟩
  · exact ⟨8, by simp, exists_mem_signlessPreprojectiveGrade_eight_notMem_commutatorSubmodule h⟩
  · exact ⟨12, by simp, exists_mem_signlessPreprojectiveGrade_twelve_notMem_commutatorSubmodule h⟩

end SimpleGraph.IsTree
