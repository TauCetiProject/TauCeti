/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Colex
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# The extension property and the Rado graph

A simple graph has the *extension property* when, for any two disjoint finite sets of vertices
`s` and `t`, some vertex outside `t` is adjacent to every vertex of `s` and to no vertex of `t`.
Graphs with this property are the models of the theory of the random graph.

The Rado graph `TauCeti.radoGraph` on `ℕ`, in which `i < j` are adjacent when bit `i` of `j` is
set, has the extension property.

## Main definitions

* `SimpleGraph.HasExtensionProperty`: the extension property.
* `TauCeti.radoGraph`: the Rado graph on `ℕ`.

## Main results

* `SimpleGraph.HasExtensionProperty.exists_adj_iff`: over any tuple of vertices, a graph with the
  extension property realises any adjacency pattern compatible with the repetitions in the tuple.
* `TauCeti.hasExtensionProperty_radoGraph`: the Rado graph has the extension property.

## References

* Richard Rado, *Universal graphs and universal functions*, Acta Arith. 9 (1964), 331–340.
* Peter J. Cameron, *The random graph*, in *The Mathematics of Paul Erdős II*, Springer, 1997.
-/

public section

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

/-- A simple graph has the extension property when for any two disjoint finite sets of vertices
`s` and `t` there is a vertex outside `t` adjacent to every vertex of `s` and to no vertex of
`t`. Such a vertex also lies outside `s`, since the graph has no loops. -/
def HasExtensionProperty (G : SimpleGraph V) : Prop :=
  ∀ s t : Finset V, Disjoint s t →
    ∃ z, z ∉ t ∧ (∀ u ∈ s, G.Adj z u) ∧ ∀ w ∈ t, ¬ G.Adj z w

/-- Unfolding the extension property. -/
theorem hasExtensionProperty_def : G.HasExtensionProperty ↔ ∀ s t : Finset V, Disjoint s t →
    ∃ z, z ∉ t ∧ (∀ u ∈ s, G.Adj z u) ∧ ∀ w ∈ t, ¬ G.Adj z w := Iff.rfl

namespace HasExtensionProperty

/-- Over any tuple of vertices, a graph with the extension property has a vertex outside the
tuple whose adjacencies to the entries follow any prescribed pattern compatible with the
repetitions in the tuple. -/
theorem exists_adj_iff (hG : G.HasExtensionProperty) {n : ℕ} (a : Fin n → V)
    (p : Fin n → Prop) (hp : ∀ i j, a i = a j → (p i ↔ p j)) :
    ∃ x, (∀ i, x ≠ a i) ∧ ∀ i, G.Adj x (a i) ↔ p i := by
  classical
  obtain ⟨x, hxt, hs, ht⟩ := hasExtensionProperty_def.mp hG ((Finset.univ.filter p).image a)
    ((Finset.univ.filter fun i => ¬ p i).image a) (by
      simp only [Finset.disjoint_left, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
        true_and]
      rintro _ ⟨i, hi, rfl⟩ ⟨j, hj, hji⟩
      exact hj ((hp j i hji).mpr hi))
  have hadj (i : Fin n) : G.Adj x (a i) ↔ p i := by
    by_cases hi : p i
    · exact iff_of_true (hs _ (Finset.mem_image_of_mem _ (by simpa using hi))) hi
    · exact iff_of_false (ht _ (Finset.mem_image_of_mem _ (by simpa using hi))) hi
  refine ⟨x, fun i => ?_, hadj⟩
  by_cases hi : p i
  · exact ((hadj i).mpr hi).ne
  · rintro rfl
    exact hxt (Finset.mem_image_of_mem _ (by simpa using hi))

end HasExtensionProperty

end SimpleGraph

namespace TauCeti

open SimpleGraph

/-- The Rado graph on `ℕ`: two numbers `i < j` are adjacent when bit `i` of `j` is set. -/
def radoGraph : SimpleGraph ℕ := fromRel fun i j => j.testBit i

/-- Distinct numbers `i` and `j` are adjacent in the Rado graph when bit `i` of `j` is set or bit
`j` of `i` is set. -/
@[simp]
theorem radoGraph_adj {i j : ℕ} : radoGraph.Adj i j ↔ i ≠ j ∧ (j.testBit i ∨ i.testBit j) :=
  fromRel_adj _ _ _

/-- The Rado graph has the extension property. -/
theorem hasExtensionProperty_radoGraph : radoGraph.HasExtensionProperty := by
  refine hasExtensionProperty_def.mpr fun s t hst => ?_
  -- The witness is the sum of `2 ^ i` over `s` and one index `N` above `s ∪ t`.
  let N := (s ∪ t).sup id + 1
  have hN {v : ℕ} (hv : v ∈ s ∪ t) : v < N := Nat.lt_succ_of_le (Finset.le_sup (f := id) hv)
  let z := ∑ i ∈ insert N s, 2 ^ i
  have hbit (j : ℕ) : z.testBit j ↔ j ∈ insert N s := by
    rw [← Nat.mem_bitIndices, ← List.mem_toFinset, Finset.toFinset_bitIndices_sum_two_pow]
  have hlt {v : ℕ} (hv : v ∈ s ∪ t) : v < z :=
    (hN hv).trans (Finset.lt_geomSum_of_mem le_rfl (Finset.mem_insert_self N s))
  have hadj {v : ℕ} (hv : v ∈ s ∪ t) : radoGraph.Adj z v ↔ v ∈ s := by
    have h₁ : v.testBit z = false := Nat.testBit_lt_two_pow ((hlt hv).trans z.lt_two_pow_self)
    simp [h₁, hbit, (hlt hv).ne', (hN hv).ne]
  refine ⟨z, fun hz => (hlt (Finset.mem_union_right s hz)).false, fun u hu => ?_, fun w hw => ?_⟩
  · exact (hadj (Finset.mem_union_left t hu)).mpr hu
  · exact fun h => Finset.disjoint_right.mp hst hw ((hadj (Finset.mem_union_right s hw)).mp h)

end TauCeti
