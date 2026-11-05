/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.Signless.Affine.D
public import TauCeti.RepresentationTheory.Quiver.Zigzag.AInfinity.MatrixRepresentation

/-!
# Quartic Hochschild classes of zigzag algebras containing affine `Dₙ`

Let `Z` be the zigzag algebra of a finite simple graph `G` with no isolated vertex, graded by path
length and regarded as an `A∞` algebra whose only operation is the product
(`TauCeti.zigzagStrictAInfinityAlgebra`). This file shows that if `G` contains a copy of the affine
diagram `Dₙ` (`n ≥ 4`), not necessarily induced, then the Hochschild cohomology `HH^{4, -2}(Z, Z)`
is nonzero, over every nontrivial commutative ring.

The class is that of the loop operation of the closed walk `1 → 0 → 1 → (n - 1) → 1` at the branch
node `1`, with the labelling of `TauCeti.AffineDynkinType.graph`. The matrix representation of the
signless preprojective algebra of `Dₙ` constructed in
`TauCeti.RepresentationTheory.Quiver.Preprojective.Signless.Affine.D` sends the product of these two
backtracks to a matrix of trace one (`TauCeti.trace_affineDMatrix_backtracks`). Since `Dₙ` is
bipartite, the trace twisted by the bipartition detects the loop operation of this walk
(`not_exists_hochschildDifferential_eq_obstruction_zigzagLoopAInfinityAlgebra_of_trace_ne_zero`).
The affine `E₆`, `E₇` and `E₈` counterparts, in arities six, eight and twelve, are in
`TauCeti.RepresentationTheory.Quiver.Zigzag.AInfinity.Affine.E`.

## Main results

* `TauCeti.not_hochschildVanishesAt_four_zigzagStrictAInfinityAlgebra_of_isContained`: if `G`
  contains a copy of the affine diagram `Dₙ`, then `HH^{4, -2}(Z, Z) ≠ 0`.

## References

* Y. Liu and Z. Wang, *A-infinity deformations of zigzag algebras via Ginzburg dg algebras*,
  https://arxiv.org/abs/2301.06757, Sections 3 and 4, for the Hochschild cohomology of zigzag
  algebras of trees and its comparison with the cyclic quotient of the preprojective algebra.
-/

public section

namespace TauCeti

universe u w

variable {k : Type w} [CommRing k] {V : Type u} {G : SimpleGraph V} [Finite V]
  {hns : ∀ i : V, ∃ j, G.Adj i j}

local notation "𝒵" => zigzagStrictAInfinityAlgebra k hns

/-- **Graphs containing an affine `Dₙ` have `HH^{4, -2}` nonzero.** If a graph `G` with no isolated
vertex contains a copy of the affine diagram `Dₙ` (`n ≥ 4`), not necessarily induced, then over
every nontrivial commutative ring the Hochschild cohomology `HH^{4, -2}` of the strict zigzag
algebra of `G` is nonzero: the loop operation of the closed walk `1 → 0 → 1 → (n - 1) → 1` at the
image of the branch node `1` is a Hochschild cocycle which is not a coboundary. -/
theorem not_hochschildVanishesAt_four_zigzagStrictAInfinityAlgebra_of_isContained [Nontrivial k]
    {n : ℕ} (hn : 4 ≤ n) (hG : (AffineDynkinType.D n).graph.IsContained G) :
    ¬(𝒵).HochschildVanishesAt ⟨4, by norm_num⟩ := by
  obtain ⟨f⟩ := hG
  have hnodes := AffineDynkinType.nodes_D n
  let c : Fin (AffineDynkinType.D n).nodes := ⟨1, by omega⟩
  let a : Fin (AffineDynkinType.D n).nodes := ⟨0, by omega⟩
  let b : Fin (AffineDynkinType.D n).nodes := ⟨n - 1, by omega⟩
  have h1n : 1 ≤ n - 2 := by omega
  have h₁ : (AffineDynkinType.D n).graph.Adj c a :=
    (AffineDynkinType.graph_D_adj hn).2 (Or.inr (Or.inl ⟨rfl, h1n⟩))
  have h₂ : (AffineDynkinType.D n).graph.Adj c b :=
    (AffineDynkinType.graph_D_adj hn).2 (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  refine not_hochschildVanishesAt_zigzagStrictAInfinityAlgebra_of_not_exists_eq_obstruction (n := 2)
    (by norm_num) _ _
    (not_exists_hochschildDifferential_eq_obstruction_zigzagLoopAInfinityAlgebra_of_trace_ne_zero f
      (AffineDynkinType.isBipartite_graph_D hn)
      (fun i j : Fin (AffineDynkinType.D n).nodes ↦ affineDMatrix k n i j)
      (sum_affineDMatrix_mul_affineDMatrix k hn) (by norm_num)
      (w := ![⟨(b, c), h₂.symm⟩, ⟨(c, b), h₂⟩, ⟨(a, c), h₁.symm⟩, ⟨(c, a), h₁⟩])
      (fun i ↦ by fin_cases i <;> rfl) ?_)
  have htr := trace_affineDMatrix_backtracks k hn
  simp only [mul_assoc] at htr
  simp [List.ofFn_succ, c, a, b, htr]

end TauCeti
