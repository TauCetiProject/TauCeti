/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.FiniteRepType.AffineSubgraph

/-!
# Recognition of the affine simply-laced diagrams

A connected finite simple graph `G` carries a nonzero weight `a : V → ℕ` with
`∑_{j ∼ i} a j = 2 * a i` at every vertex, that is a nonzero nonnegative integral null vector of
`2I - A`, exactly when `G` is isomorphic to the graph of a valid affine simply-laced diagram other
than `Ã₁`; that diagram is then unique. The possible graphs are therefore the cycles `Ãₙ` with
`n ≥ 2`, affine `Dₙ` with `n ≥ 4`, and affine `E₆`, `E₇` and `E₈`.

The marks of an affine diagram are such a weight on its graph. Conversely, a nonzero null vector
prevents `2I - A` from being positive definite, so `G` is not a Dynkin diagram and contains a copy
of the graph of an affine diagram
(`SimpleGraph.Connected.exists_isContained_affineDynkinType_of_not_exists_dynkinType_iso`). Since
the marks of that diagram are a positive additive function, the proper-extension obstruction
`SimpleGraph.Copy.exists_iso_of_sum_le_two_mul` forces the copy to be all of `G`. The diagram is
unique by `TauCeti.AffineDynkinType.eq_of_graph_iso`: the graphs of distinct valid diagrams are
already told apart by their numbers of nodes, of leaves and of trivalent nodes.

Away from `Ã₁` this is Kac's characterisation of the connected affine diagrams by a positive null
vector, read on simple graphs; the double edge of `Ã₁` is not a simple-graph edge, so `Ã₁` is not
recognised here.

## Main results

* `SimpleGraph.Connected.exists_sum_eq_two_mul_iff_existsUnique_affineDynkinType_iso`: **the
  recognition theorem**.

## References

* V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., Chapter 4, Theorem 4.3 and Table Aff 1.
* P. Etingof et al., *Introduction to representation theory*, Problem 5.3, for the semidefinite
  form of the classification.
-/

public section

namespace SimpleGraph

open Finset Matrix TauCeti

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **Recognition of the affine simply-laced diagrams.** A connected finite simple graph carries a
nonzero weight `a : V → ℕ` with `∑_{j ∼ i} a j = 2 * a i` at every vertex exactly when it is
isomorphic to the graph of a unique valid affine simply-laced diagram other than `Ã₁`: a cycle
`Ãₙ` with `n ≥ 2`, affine `Dₙ` with `n ≥ 4`, or affine `E₆`, `E₇` or `E₈`. -/
theorem Connected.exists_sum_eq_two_mul_iff_existsUnique_affineDynkinType_iso
    (hG : G.Connected) :
    (∃ a : V → ℕ, a ≠ 0 ∧ ∀ i, ∑ j ∈ G.neighborFinset i, a j = 2 * a i) ↔
      ∃! t : AffineDynkinType, t.Valid ∧ t.IsGraphical ∧ Nonempty (G ≃g t.graph) := by
  classical
  constructor
  · rintro ⟨a, ha, hsum⟩
    -- A nonzero null vector of `2I - A` rules out positive definiteness, so `G` is not a Dynkin
    -- diagram and contains the graph of an affine diagram.
    have hD : ¬ ∃ t : DynkinType, t.Valid ∧ Nonempty (G ≃g diagramGraph t.cartanMatrix) := by
      rw [← exists_valid_isSimplyLaced_dynkinType_iso_iff, ← posDef_graphCartanMatrix_iff hG]
      intro hpos
      have hx : (fun i ↦ (a i : ℚ)) ≠ 0 := fun h ↦ ha (funext fun i ↦ by simpa using congrFun h i)
      have hnull : G.graphCartanMatrix ℚ *ᵥ (fun i ↦ (a i : ℚ)) = 0 :=
        graphCartanMatrix_mulVec_eq_zero G fun i ↦ by exact_mod_cast hsum i
      simpa [hnull] using hpos.dotProduct_mulVec_pos hx
    obtain ⟨t, ht, hg, ⟨f⟩⟩ :=
      hG.exists_isContained_affineDynkinType_of_not_exists_dynkinType_iso hD
    -- The marks are a positive additive function on that graph, so the copy is all of `G`.
    obtain ⟨e, -⟩ := f.exists_iso_of_sum_le_two_mul hG.preconnected AffineDynkinType.marks_pos
      (AffineDynkinType.sum_marks_neighborFinset_eq_two_mul ht hg) (a := fun i ↦ (a i : ℤ))
      (fun i ↦ by simp)
      (fun h ↦ ha (funext fun i ↦ by simpa using congrFun h i))
      (fun i ↦ by exact_mod_cast (hsum i).le)
    exact ⟨t, ⟨ht, hg, ⟨e.symm⟩⟩, fun t' ⟨ht', _, ⟨e'⟩⟩ ↦
      AffineDynkinType.eq_of_graph_iso ht' ht (e'.symm.trans e.symm)⟩
  · rintro ⟨t, ⟨ht, hg, ⟨e⟩⟩, -⟩
    -- The marks, transported along the isomorphism.
    refine ⟨fun v ↦ (t.marks (e v)).toNat, fun h ↦ ?_, fun i ↦ ?_⟩
    · simpa using congrFun h (e.symm t.affineNode)
    · have hsum : ∑ j ∈ G.neighborFinset i, t.marks (e j) = 2 * t.marks (e i) := by
        rw [← AffineDynkinType.sum_marks_neighborFinset_eq_two_mul ht hg (e i)]
        exact sum_equiv e.toEquiv (fun j ↦ by simp [e.map_adj_iff]) fun _ _ ↦ rfl
      have hpos (v : V) : ((t.marks (e v)).toNat : ℤ) = t.marks (e v) :=
        Int.toNat_of_nonneg (AffineDynkinType.marks_pos _).le
      exact (Nat.cast_inj (R := ℤ)).1 (by push_cast [hpos]; exact hsum)

end SimpleGraph
