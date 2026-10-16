/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.CycleGraph
public import TauCeti.Data.Fin.Basic
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Signless.KoszulComplex

/-!
# The signless preprojective Koszul complex of a cycle

On a cycle graph, the successor map chooses a neighbour at every vertex and never chooses the
reverse of the successor chosen at that neighbour. Applying the general left-end exactness theorem
for signless preprojective Koszul complexes gives the exactness needed for cycle graphs, including
odd cycles where the signless algebra need not be an ordinary preprojective algebra.
-/

public section

namespace TauCeti

open _root_.Quiver DoubledQuiver PathAlgebra SimpleGraph

universe u

variable (k : Type u) [CommRing k]

private theorem forall_signlessPreprojectiveMk_ofArrow_reverse_mul_eq_zero_iff_cycleGraph_aux
    {m : ℕ} [NeZero m] (hm : 3 ≤ m) (v : Fin m)
    {y : signlessPreprojectiveAlgebra k (DoubledQuiver (cycleGraph m))}
    (hy : signlessPreprojectiveMk k _ (vertexIdempotent k (vertex (cycleGraph m) v)) * y = y) :
    (∀ (i : DoubledQuiver (cycleGraph m)) (b : i ⟶ vertex (cycleGraph m) v),
      signlessPreprojectiveMk k _ (ofArrow (reverse b)) * y = 0) ↔ y = 0 := by
  exact forall_signlessPreprojectiveMk_ofArrow_reverse_mul_eq_zero_iff_of_adj k
    (G := cycleGraph m) (f := fun w => w + 1)
    (fun w => cycleGraph_adj_add_one hm w)
    (fun w => add_one_add_one_ne_self hm w) v hy

/-- **Exactness at the left end of the signless preprojective Koszul complex of a cycle.** For a
cycle graph with at least three vertices, an element of the vertex corner annihilated by every
incoming reverse arrow is zero. -/
theorem forall_signlessPreprojectiveMk_ofArrow_reverse_mul_eq_zero_iff_cycleGraph
    {m : ℕ} (hm : 3 ≤ m) (v : Fin m)
    {y : signlessPreprojectiveAlgebra k (DoubledQuiver (cycleGraph m))}
    (hy : signlessPreprojectiveMk k _ (vertexIdempotent k (vertex (cycleGraph m) v)) * y = y) :
    (∀ (i : DoubledQuiver (cycleGraph m)) (b : i ⟶ vertex (cycleGraph m) v),
      signlessPreprojectiveMk k _ (ofArrow (reverse b)) * y = 0) ↔ y = 0 := by
  have hne : NeZero m := ⟨by omega⟩
  exact @forall_signlessPreprojectiveMk_ofArrow_reverse_mul_eq_zero_iff_cycleGraph_aux
    k inferInstance m hne hm v y hy

end TauCeti
