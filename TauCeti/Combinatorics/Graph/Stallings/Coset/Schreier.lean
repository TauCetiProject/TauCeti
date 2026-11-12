/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Stallings.Basis
public import TauCeti.Combinatorics.Graph.Stallings.Coset.Basic
public import TauCeti.Combinatorics.Graph.Serre.Cycle.SpanningTree
public import Mathlib.GroupTheory.Schreier
public import Mathlib.Tactic.LinearCombination

/-!
# The Schreier index formula for subgroups of free groups

Let `α` be finite and let `H` be a subgroup of finite index `i` of the free group on `α`. Then
`H` is finitely generated (Mathlib's `Subgroup.fg_of_index_ne_zero`) and its rank satisfies the
exact Schreier formula `rank H - 1 = i * (|α| - 1)` as integers. For an empty alphabet both sides
are `-1`. For arbitrary finitely generated groups Mathlib's `Subgroup.rank_le_index_mul_rank` and
Tau Ceti's `Subgroup.rank_le_one_add_index_mul_rank_sub_one` are only inequalities; for a free
group of positive finite rank the latter is attained.

The formula is read off the coset graph of `H`. Its vertices are the `i` cosets of `H`, and its
darts labelled by a basis letter, rather than by the inverse of one, form an orientation with
exactly `i * |α|` darts. The coset graph is folded and connected and accepts `H`, so a spanning
tree gives a free basis of `H` indexed by the positive darts outside the tree, and a spanning
tree of a graph with `i` vertices has `i - 1` positive darts.

## Main results

* `Subgroup.rank_add_index_eq_index_mul_natCard_add_one`: the formula in natural numbers,
  `rank H + i = i * |α| + 1`.
* `Subgroup.rank_sub_one_eq_index_mul_natCard_sub_one`: the formula as integers,
  `rank H - 1 = i * (|α| - 1)`.

## References

* I. Kapovich and A. Myasnikov, *Stallings foldings and subgroups of free groups*,
  Section 8, Lemma 8.2, Proposition 8.3 and Corollary 8.4.
-/

public section

namespace Subgroup

open TauCeti TauCeti.StallingsGraph

variable {α : Type*} (H : Subgroup (FreeGroup α))

/-- The darts of the coset graph labelled by a basis letter form an orientation: exactly one
dart of each reversal pair carries a basis letter rather than its inverse. -/
private theorem isOrientation_cosetGraph_setOf_snd :
    (cosetGraph H).graph.IsOrientation {e | e.2.2 = true} :=
  ((cosetGraph H).graph.isOrientation_iff _).mpr fun e => by
    obtain ⟨q, a, _ | _⟩ := e <;> simp

/-- The coset graph has one dart labelled by each basis letter leaving each coset. -/
private theorem natCard_cosetGraph_setOf_snd :
    Nat.card {e : (cosetGraph H).graph.E | e.2.2 = true} =
      Nat.card (FreeGroup α ⧸ H) * Nat.card α := by
  rw [← Nat.card_prod]
  exact Nat.card_congr ⟨fun e => (e.1.1, e.1.2.1), fun p => ⟨(p.1, p.2, true), rfl⟩,
    fun ⟨⟨_, _, _⟩, h⟩ => by cases h; rfl, fun _ => rfl⟩

/-- **Schreier's index formula** for a subgroup `H` of finite index `i` of the free group on a
finite alphabet `α`, in natural numbers: `rank H + i = i * |α| + 1`. -/
theorem rank_add_index_eq_index_mul_natCard_add_one [Finite α] [H.FiniteIndex] :
    Group.rank H + H.index = H.index * Nat.card α + 1 := by
  obtain ⟨T⟩ := (SerreGraph.nonempty_spanningTree_iff _).mpr (cosetGraph_connected H)
  have hO := isOrientation_cosetGraph_setOf_snd H
  have : Group.FG ((cosetGraph H).subgroup (cosetGraph H).base) := by
    rw [cosetGraph_subgroup]
    infer_instance
  have hrank := (cosetGraph H).rank_subgroup T (cosetGraph H).base (cosetGraph_isFolded H) hO
  rw [rank_congr (cosetGraph_subgroup H)] at hrank
  have hcard := T.card_diff_add_card hO
  rw [natCard_cosetGraph_setOf_snd, ← index_eq_card] at hcard
  omega

/-- **Schreier's index formula**: a subgroup `H` of finite index `i` of the free group on a
finite alphabet `α` satisfies `rank H - 1 = i * (|α| - 1)` as integers. -/
theorem rank_sub_one_eq_index_mul_natCard_sub_one [Finite α] [H.FiniteIndex] :
    (Group.rank H : ℤ) - 1 = H.index * (Nat.card α - 1) := by
  have h := H.rank_add_index_eq_index_mul_natCard_add_one
  zify at h
  linear_combination h

end Subgroup
