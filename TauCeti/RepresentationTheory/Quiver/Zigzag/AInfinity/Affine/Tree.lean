/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.Signless.Affine.Tree
public import TauCeti.RepresentationTheory.Quiver.Zigzag.AInfinity.Affine.D.Contained
public import TauCeti.RepresentationTheory.Quiver.Zigzag.AInfinity.Affine.E

/-!
# Higher Hochschild classes of zigzag algebras of non-Dynkin trees

Let `Z` be the zigzag algebra of a finite tree `G`, graded by path length and regarded as an `A∞`
algebra whose only operation is the product (`TauCeti.zigzagStrictAInfinityAlgebra`). A finite tree
which is not a Dynkin diagram contains a copy of one of the affine diagrams `Dₙ`, `E₆`, `E₇` or
`E₈` (`SimpleGraph.IsTree.isContained_affineDynkinType_of_not_exists_dynkinType_iso`). Each of
these gives a nonzero Hochschild class of `Z`, the class of the loop operation of a closed walk
detected by a matrix representation of the signless preprojective algebra of the affine diagram:
in `HH^{4, -2}` for `Dₙ`
(`TauCeti.not_hochschildVanishesAt_four_zigzagStrictAInfinityAlgebra_of_isContained`), and in
`HH^{6, -4}`, `HH^{8, -6}` and `HH^{12, -10}` for `E₆`, `E₇` and `E₈`
(`TauCeti.not_hochschildVanishesAt_six_zigzagStrictAInfinityAlgebra` and its companions).
Consequently Kadeishvili's criterion
`TauCeti.AInfinityAlgebra.isIntrinsicallyFormal_of_forall_hochschildVanishesAt` does not apply to
the zigzag algebra of any finite non-Dynkin tree.

## Main results

* `SimpleGraph.IsTree.exists_not_hochschildVanishesAt_zigzagStrictAInfinityAlgebra`: the zigzag
  algebra of a finite non-Dynkin tree has a nonzero Hochschild class in `HH^{n, 2 - n}` for some
  `n ∈ {4, 6, 8, 12}`.

## References

* Y. Liu and Z. Wang, *A-infinity deformations of zigzag algebras via Ginzburg dg algebras*,
  https://arxiv.org/abs/2301.06757, Sections 3 and 4.
* T. Kadeishvili, *The structure of the `A(∞)`-algebra, and the Hochschild and Harrison
  cohomologies*, Trudy Tbiliss. Mat. Inst. 91 (1988), 19--27, for the obstruction groups.
-/

public section

namespace SimpleGraph.IsTree

open TauCeti

variable {k : Type*} [CommRing k] [Nontrivial k] {V : Type*} [Finite V] {G : SimpleGraph V}
  {hns : ∀ i : V, ∃ j, G.Adj i j}

/-- **The zigzag algebra of a non-Dynkin tree has a nonzero higher Hochschild class.** If a finite
tree `G` is not isomorphic to the diagram of any valid Dynkin type, then over every nontrivial
commutative ring the Hochschild cohomology `HH^{n, 2 - n}` of the strict zigzag algebra of `G` is
nonzero for some `n ∈ {4, 6, 8, 12}`: some loop operation of a closed walk of length `n` is a
Hochschild cocycle which is not a coboundary. In particular Kadeishvili's criterion
`TauCeti.AInfinityAlgebra.isIntrinsicallyFormal_of_forall_hochschildVanishesAt` does not apply. -/
theorem exists_not_hochschildVanishesAt_zigzagStrictAInfinityAlgebra (hG : G.IsTree)
    (hD : ¬ ∃ t : DynkinType, t.Valid ∧ Nonempty (G ≃g diagramGraph t.cartanMatrix)) :
    ∃ n : {n : ℕ // 1 < n}, (n : ℕ) ∈ ({4, 6, 8, 12} : Finset ℕ) ∧
      ¬(zigzagStrictAInfinityAlgebra k hns).HochschildVanishesAt n := by
  classical
  have := Fintype.ofFinite V
  rcases hG.isContained_affineDynkinType_of_not_exists_dynkinType_iso hD with
    ⟨n, hn, h⟩ | h | h | h
  · exact ⟨⟨4, by norm_num⟩, by simp,
      not_hochschildVanishesAt_four_zigzagStrictAInfinityAlgebra_of_isContained hn h⟩
  · exact ⟨⟨6, by norm_num⟩, by simp,
      not_hochschildVanishesAt_six_zigzagStrictAInfinityAlgebra h⟩
  · exact ⟨⟨8, by norm_num⟩, by simp,
      not_hochschildVanishesAt_eight_zigzagStrictAInfinityAlgebra h⟩
  · exact ⟨⟨12, by norm_num⟩, by simp,
      not_hochschildVanishesAt_twelve_zigzagStrictAInfinityAlgebra h⟩

end SimpleGraph.IsTree
