/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Fintype.Lattice
public import TauCeti.NumberTheory.Markoff.Descent

import Mathlib.Data.Set.Card
import TauCeti.Combinatorics.SimpleGraph.Acyclic

/-!
# The positive Markoff graph is a tree

The integer Markoff graph `markoffGraph` has the positive Markoff triples as vertices, two of
them being adjacent when one is obtained from the other by a Vieta move. This file proves that it
is a `3`-regular tree rooted at `(1, 1, 1)`.

The height of a triple is its largest coordinate. By the descent inequality, a Vieta move never
fixes a positive Markoff triple and always changes its height: the move in the position of the
(unique) largest coordinate lowers it, unless the triple is `(1, 1, 1)`, and the other two moves
raise it. So every vertex other than `(1, 1, 1)` has exactly one neighbour of smaller height, and
`(1, 1, 1)` has none. A vertex of greatest height on a cycle would have two distinct neighbours
of smaller height, so the graph is acyclic; it is connected by Markoff's theorem.

The statement is about ordered positive triples: on the signed nonzero integer solutions, the
moves generate four copies of this tree, one for each sign pattern with product `+1`.

## Main results

* `TauCeti.markoffVieta_ne_self`: no Vieta move fixes a positive Markoff triple.
* `TauCeti.markoffGraph_neighborSet`: the neighbours of `x` are the three triples `R_i x`.
* `TauCeti.markoffGraph_isRegularOfDegree`: every vertex has degree exactly `3`.
* `TauCeti.existsUnique_markoffGraph_adj_sup'_lt`: every vertex other than `(1, 1, 1)` has
  exactly one neighbour with smaller largest coordinate.
* `TauCeti.exists_markoffGraph_adj_sup'_lt_iff`: `(1, 1, 1)` is the only vertex with no such
  neighbour.
* `TauCeti.markoffGraph_isTree`: the positive Markoff graph is a tree.

## References

* D. E. Martin, *A new proof of Chen's theorem for Markoff graphs*, §1.
* Y. Zhang, *An elementary proof of Markoff conjecture for prime powers*, §3, after the proof of
  the Markoff Theorem.
-/

public section

namespace TauCeti

open Finset

variable {x : Fin 3 → ℤ} {i j : Fin 3}

/-! ### Heights and the Vieta moves -/

/-- In a positive Markoff triple other than `(1, 1, 1)`, a largest coordinate is strictly larger
than the other two coordinates. -/
theorem lt_of_mem_positiveMarkoffTriples_of_forall_le (hx : x ∈ positiveMarkoffTriples)
    (hmax : ∀ k, x k ≤ x i) (hne : x ≠ 1) (hji : j ≠ i) : x j < x i := by
  refine (hmax j).lt_of_ne fun hj => ?_
  -- If `x j = x i`, then `x_j` is also a largest coordinate, so the move `R_j` both lowers it
  -- (descent at `j`) and raises it above `x_i` (ascent away from `i`).
  have hdown := markoffVieta_apply_self_lt hx (i := j) (fun k => hj ▸ hmax k) hne
  have hup := lt_markoffVieta_apply_self_of_ne (mem_positiveMarkoffTriples.mp hx).2 hmax hji
  omega

/-- If `x_i` is a largest coordinate of a positive Markoff triple `x ≠ (1, 1, 1)`, the move `R_i`
strictly lowers the largest coordinate. -/
theorem sup'_markoffVieta_lt (hx : x ∈ positiveMarkoffTriples) (hmax : ∀ k, x k ≤ x i)
    (hne : x ≠ 1) : univ.sup' univ_nonempty (markoffVieta i x) < univ.sup' univ_nonempty x := by
  refine (sup'_lt_iff _).mpr fun k _ => lt_of_lt_of_le ?_ (le_sup' x (mem_univ i))
  rcases eq_or_ne k i with rfl | hk
  · exact markoffVieta_apply_self_lt hx hmax hne
  · rw [markoffVieta_apply_of_ne hk]
    exact lt_of_mem_positiveMarkoffTriples_of_forall_le hx hmax hne hk

/-- If `x_i` is a largest coordinate of a triple of positive integers, the moves in the other two
positions strictly raise the largest coordinate. -/
theorem sup'_lt_sup'_markoffVieta (hpos : ∀ k, 0 < x k) (hmax : ∀ k, x k ≤ x i) (hji : j ≠ i) :
    univ.sup' univ_nonempty x < univ.sup' univ_nonempty (markoffVieta j x) := by
  exact (sup'_le _ _ fun k _ => hmax k).trans_lt <|
    (lt_markoffVieta_apply_self_of_ne hpos hmax hji).trans_le (le_sup' _ (mem_univ j))

/-- Unless `x_j` is a largest coordinate of `x ≠ (1, 1, 1)`, some largest coordinate of `x` sits
in a position other than `j`. -/
private lemma exists_ne_forall_le (h : ¬(x ≠ 1 ∧ ∀ k, x k ≤ x j)) :
    ∃ i ≠ j, ∀ k, x k ≤ x i := by
  by_cases h1 : x = 1
  · exact ⟨j + 1, by fin_cases j <;> decide, fun k => by simp [h1]⟩
  · obtain ⟨i, hi⟩ := Finite.exists_max x
    exact ⟨i, fun hij => h ⟨h1, hij ▸ hi⟩, hi⟩

/-- A Vieta move lowers the largest coordinate of a positive Markoff triple `x` exactly when
`x ≠ (1, 1, 1)` and the move is in the position of a largest coordinate. -/
theorem sup'_markoffVieta_lt_iff (hx : x ∈ positiveMarkoffTriples) :
    univ.sup' univ_nonempty (markoffVieta j x) < univ.sup' univ_nonempty x ↔
      x ≠ 1 ∧ ∀ k, x k ≤ x j := by
  refine ⟨fun hlt => ?_, fun ⟨hne, hmax⟩ => sup'_markoffVieta_lt hx hmax hne⟩
  by_contra h
  obtain ⟨i, hij, hi⟩ := exists_ne_forall_le h
  exact (sup'_lt_sup'_markoffVieta (mem_positiveMarkoffTriples.mp hx).2 hi hij.symm).not_gt hlt

/-- A Vieta move always changes the largest coordinate of a positive Markoff triple. -/
theorem sup'_markoffVieta_ne (hx : x ∈ positiveMarkoffTriples) (j : Fin 3) :
    univ.sup' univ_nonempty (markoffVieta j x) ≠ univ.sup' univ_nonempty x := by
  by_cases h : x ≠ 1 ∧ ∀ k, x k ≤ x j
  · exact (sup'_markoffVieta_lt hx h.2 h.1).ne
  · obtain ⟨i, hij, hi⟩ := exists_ne_forall_le h
    exact (sup'_lt_sup'_markoffVieta (mem_positiveMarkoffTriples.mp hx).2 hi hij.symm).ne'

/-- No Vieta move fixes a positive Markoff triple. -/
theorem markoffVieta_ne_self (hx : x ∈ positiveMarkoffTriples) (i : Fin 3) :
    markoffVieta i x ≠ x := fun h => sup'_markoffVieta_ne hx i (by rw [h])

/-- On a positive Markoff triple, the three Vieta moves give three distinct triples: `R_i x` and
`R_j x` differ in the `i`-th coordinate when `i ≠ j`. -/
theorem markoffVieta_left_injective (hx : x ∈ positiveMarkoffTriples) :
    Function.Injective fun i => markoffVieta i x := by
  intro i j hij
  by_contra hne
  refine markoffVieta_ne_self hx i (funext fun k => ?_)
  rcases eq_or_ne k i with rfl | hk
  · exact (congrFun hij k).trans (markoffVieta_apply_of_ne hne x)
  · exact markoffVieta_apply_of_ne hk x

/-! ### Neighbours and degrees in the Markoff graph -/

/-- Two positive Markoff triples are adjacent in the Markoff graph exactly when one is obtained
from the other by a Vieta move; distinctness is automatic. -/
theorem markoffGraph_adj_iff_exists {x y : positiveMarkoffTriples} :
    markoffGraph.Adj x y ↔ ∃ i, markoffVieta i x.1 = y.1 := by
  refine markoffGraph_adj.trans ⟨fun h => h.2, fun ⟨i, hi⟩ => ⟨fun hxy => ?_, i, hi⟩⟩
  exact markoffVieta_ne_self x.2 i (by rw [hi, hxy])

/-- Each Vieta move `R_i x` of a positive Markoff triple `x` is a neighbour of `x`. -/
theorem markoffGraph_adj_markoffVieta (x : positiveMarkoffTriples) (i : Fin 3) :
    markoffGraph.Adj x ⟨markoffVieta i x.1, markoffVieta_mem_positiveMarkoffTriples x.2 i⟩ :=
  markoffGraph_adj_iff_exists.mpr ⟨i, rfl⟩

/-- The neighbours of a positive Markoff triple `x` are its three Vieta moves `R₀ x, R₁ x, R₂ x`. -/
theorem markoffGraph_neighborSet (x : positiveMarkoffTriples) :
    markoffGraph.neighborSet x =
      Set.range fun i => ⟨markoffVieta i x.1, markoffVieta_mem_positiveMarkoffTriples x.2 i⟩ := by
  ext y
  simp only [SimpleGraph.mem_neighborSet, markoffGraph_adj_iff_exists, Set.mem_range,
    Subtype.ext_iff]

/-- The Markoff graph is locally finite: each vertex has the three Vieta moves as neighbours. -/
noncomputable instance : markoffGraph.LocallyFinite := fun x =>
  (markoffGraph_neighborSet x ▸ Set.finite_range _ : (markoffGraph.neighborSet x).Finite).fintype

/-- Every vertex of the Markoff graph has degree exactly `3`, including `(1, 1, 1)`. -/
@[simp]
theorem markoffGraph_degree (x : positiveMarkoffTriples) : markoffGraph.degree x = 3 := by
  rw [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card,
    markoffGraph_neighborSet, Nat.card_range_of_injective, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  intro i j hij
  exact markoffVieta_left_injective x.2 (congrArg Subtype.val hij)

/-- The Markoff graph is `3`-regular. -/
theorem markoffGraph_isRegularOfDegree : markoffGraph.IsRegularOfDegree 3 :=
  markoffGraph_degree

/-! ### The descending neighbour and the tree -/

/-- Adjacent positive Markoff triples have different largest coordinates. -/
theorem sup'_ne_of_markoffGraph_adj {x y : positiveMarkoffTriples} (h : markoffGraph.Adj x y) :
    univ.sup' univ_nonempty y.1 ≠ univ.sup' univ_nonempty x.1 := by
  obtain ⟨i, hi⟩ := markoffGraph_adj_iff_exists.mp h
  exact hi ▸ sup'_markoffVieta_ne x.2 i

/-- A positive Markoff triple has at most one neighbour with smaller largest coordinate. -/
theorem eq_of_markoffGraph_adj_of_sup'_lt {x y z : positiveMarkoffTriples}
    (hy : markoffGraph.Adj x y) (hz : markoffGraph.Adj x z)
    (hy' : univ.sup' univ_nonempty y.1 < univ.sup' univ_nonempty x.1)
    (hz' : univ.sup' univ_nonempty z.1 < univ.sup' univ_nonempty x.1) : y = z := by
  obtain ⟨i, hi⟩ := markoffGraph_adj_iff_exists.mp hy
  obtain ⟨j, hj⟩ := markoffGraph_adj_iff_exists.mp hz
  rw [← hi] at hy'
  rw [← hj] at hz'
  obtain ⟨hne, hmi⟩ := (sup'_markoffVieta_lt_iff x.2).mp hy'
  obtain ⟨-, hmj⟩ := (sup'_markoffVieta_lt_iff x.2).mp hz'
  -- Both moves sit in the position of a largest coordinate, which is unique.
  have hij : i = j := by
    by_contra hij
    exact (lt_of_mem_positiveMarkoffTriples_of_forall_le x.2 hmj hne hij).not_ge (hmi j)
  ext1
  rw [← hi, ← hj, hij]

/-- `(1, 1, 1)` is the only positive Markoff triple with no neighbour of smaller largest
coordinate. -/
theorem exists_markoffGraph_adj_sup'_lt_iff (x : positiveMarkoffTriples) :
    (∃ y, markoffGraph.Adj x y ∧ univ.sup' univ_nonempty y.1 < univ.sup' univ_nonempty x.1) ↔
      x.1 ≠ 1 := by
  refine ⟨fun ⟨y, hy, hlt⟩ => ?_, fun hne => ?_⟩
  · obtain ⟨i, hi⟩ := markoffGraph_adj_iff_exists.mp hy
    rw [← hi] at hlt
    exact ((sup'_markoffVieta_lt_iff x.2).mp hlt).1
  · obtain ⟨i, hi⟩ := Finite.exists_max x.1
    exact ⟨_, markoffGraph_adj_markoffVieta x i, sup'_markoffVieta_lt x.2 hi hne⟩

/-- Every positive Markoff triple other than `(1, 1, 1)` has exactly one neighbour in the Markoff
graph with smaller largest coordinate. -/
theorem existsUnique_markoffGraph_adj_sup'_lt {x : positiveMarkoffTriples} (hx : x.1 ≠ 1) :
    ∃! y, markoffGraph.Adj x y ∧ univ.sup' univ_nonempty y.1 < univ.sup' univ_nonempty x.1 := by
  obtain ⟨y, hy⟩ := (exists_markoffGraph_adj_sup'_lt_iff x).mpr hx
  exact ⟨y, hy, fun z hz => eq_of_markoffGraph_adj_of_sup'_lt hz.1 hy.1 hz.2 hy.2⟩

/-- The Markoff graph is acyclic. -/
theorem markoffGraph_isAcyclic : markoffGraph.IsAcyclic :=
  SimpleGraph.isAcyclic_of_forall_adj_le_eq (fun x : positiveMarkoffTriples =>
    univ.sup' univ_nonempty x.1) fun _ _ _ hu hw hu' hw' =>
    eq_of_markoffGraph_adj_of_sup'_lt hu hw (hu'.lt_of_ne (sup'_ne_of_markoffGraph_adj hu))
      (hw'.lt_of_ne (sup'_ne_of_markoffGraph_adj hw))

/-- **The positive Markoff graph is a tree.** Its vertices are the ordered positive Markoff
triples, and two of them are adjacent when they are related by a Vieta move. -/
theorem markoffGraph_isTree : markoffGraph.IsTree :=
  ⟨markoffGraph_connected, markoffGraph_isAcyclic⟩

/-! ### Examples -/

/-- The neighbours of `(1, 1, 2)` are `(1, 1, 1)`, `(5, 1, 2)` and `(1, 5, 2)`. -/
example : (fun i => markoffVieta i (![1, 1, 2] : Fin 3 → ℤ)) = ![![5, 1, 2], ![1, 5, 2], 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [markoffVieta_apply_of_ne]

end TauCeti
