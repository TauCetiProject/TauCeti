/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Colex
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Nat.Bitwise

/-!
# The extension property and the Rado graph

A simple graph has the *extension property* if for any two disjoint finite sets of vertices `U`
and `W` there is a vertex outside `W` adjacent to every vertex of `U` and to no vertex of `W`.
Such a vertex automatically lies outside `U` as well, since graphs are loopless. Applied with
`U = ∅`, the property shows that a graph with it has infinitely many vertices.

The *Rado graph* `SimpleGraph.radoGraph` has the natural numbers as vertices, two distinct numbers
`i` and `j` being adjacent when the `i`-th binary digit of `j` is one, or the `j`-th binary digit
of `i` is one. It has the extension property: for given `U` and `W`, a vertex whose binary digits
are those of `U` together with one digit beyond every element of `U ∪ W` works. By a
back-and-forth argument every countable graph with the extension property is isomorphic to the
Rado graph (`SimpleGraph.HasExtensionProperty.nonempty_iso`). It is also known as the countable
random graph, since Erdős and Rényi showed that a random graph on `ℕ` is almost surely isomorphic
to it.

## Main definitions

* `SimpleGraph.HasExtensionProperty`: the extension property.
* `SimpleGraph.radoGraph`: the Rado graph on `ℕ`.

## Main results

* `SimpleGraph.HasExtensionProperty.infinite`: a graph with the extension property is infinite.
* `SimpleGraph.hasExtensionProperty_radoGraph`: the Rado graph has the extension property.

## References

* Wilhelm Ackermann, *Die Widerspruchsfreiheit der allgemeinen Mengenlehre*, 1937.
* Paul Erdős and Alfréd Rényi, *Asymmetric graphs*, 1963.
* Richard Rado, *Universal graphs and universal functions*, 1964.
-/

public section

universe u

namespace SimpleGraph

variable {V : Type u} {G : SimpleGraph V}

/-- A graph has the *extension property* if for any two disjoint finite sets of vertices `U` and
`W` some vertex outside `W` is adjacent to every vertex of `U` and to no vertex of `W`. -/
def HasExtensionProperty (G : SimpleGraph V) : Prop :=
  ∀ U W : Finset V, Disjoint U W →
    ∃ z ∉ W, (∀ u ∈ U, G.Adj z u) ∧ ∀ w ∈ W, ¬G.Adj z w

/-- Unfold the extension property. -/
theorem hasExtensionProperty_iff : G.HasExtensionProperty ↔
    ∀ U W : Finset V, Disjoint U W →
      ∃ z ∉ W, (∀ u ∈ U, G.Adj z u) ∧ ∀ w ∈ W, ¬G.Adj z w := Iff.rfl

/-- A graph with the extension property has infinitely many vertices: outside every finite set of
vertices there is another vertex. -/
theorem HasExtensionProperty.infinite (hG : G.HasExtensionProperty) : Infinite V := by
  refine Infinite.of_not_fintype fun _ => ?_
  obtain ⟨z, hz, -⟩ := hG ∅ Finset.univ (Finset.disjoint_empty_left _)
  exact hz (Finset.mem_univ z)

/-- The Rado graph on `ℕ`: distinct `i` and `j` are adjacent when the `i`-th binary digit of `j`
or the `j`-th binary digit of `i` is one. -/
def radoGraph : SimpleGraph ℕ :=
  SimpleGraph.fromRel fun i j => j.testBit i

/-- Adjacency in the Rado graph, read off from binary digits. -/
@[simp]
theorem radoGraph_adj {i j : ℕ} : radoGraph.Adj i j ↔ i ≠ j ∧ (j.testBit i ∨ i.testBit j) := by
  simp only [radoGraph, fromRel_adj]

/-- The Rado graph has the extension property. -/
theorem hasExtensionProperty_radoGraph : radoGraph.HasExtensionProperty := by
  intro U W hUW
  -- Take the vertex whose binary digits are `U` together with a digit `N` above `U ∪ W`.
  let N := (U ∪ W).sup id + 1
  have hN {v : ℕ} (hv : v ∈ U ∪ W) : v < N := Nat.lt_succ_of_le (Finset.le_sup (f := id) hv)
  let z := ∑ i ∈ insert N U, 2 ^ i
  have hbit (i : ℕ) : z.testBit i ↔ i ∈ insert N U := by
    rw [← Nat.mem_bitIndices, ← List.mem_toFinset, Finset.toFinset_bitIndices_sum_two_pow]
  have hz {v : ℕ} (hv : v ∈ U ∪ W) : v < z :=
    (hN hv).trans ((Nat.lt_two_pow_self).trans_le
      (Nat.two_pow_le_of_mem_bitIndices ((Nat.mem_bitIndices).mpr ((hbit N).mpr
        (Finset.mem_insert_self N U)))))
  refine ⟨z, fun hzW => (hz (Finset.mem_union_right U hzW)).false, fun u hu => ?_,
    fun w hw => ?_⟩
  · exact radoGraph_adj.mpr ⟨(hz (Finset.mem_union_left W hu)).ne',
      Or.inr ((hbit u).mpr (Finset.mem_insert_of_mem hu))⟩
  · have hwz := hz (Finset.mem_union_right U hw)
    rw [radoGraph_adj, not_and, not_or]
    refine fun _ => ⟨?_, fun h => ?_⟩
    · exact Bool.eq_false_iff.mp
        (Nat.testBit_eq_false_of_lt (hwz.trans Nat.lt_two_pow_self))
    · rcases Finset.mem_insert.mp ((hbit w).mp h) with rfl | hwU
      · exact (hN (Finset.mem_union_right U hw)).false
      · exact Finset.disjoint_left.mp hUW hwU hw

end SimpleGraph
