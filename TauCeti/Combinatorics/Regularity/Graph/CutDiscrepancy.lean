/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Density
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import TauCeti.Combinatorics.SimpleGraph.Density
public import TauCeti.Order.Partition.Finpartition

/-!
# Stepped counts and the cut discrepancy of a partition

A finite partition `P` of the vertices of a graph `G` determines the *`P`-stepped graph*: the
weighted graph whose weight on a pair of vertices is the edge density of `G` between their parts.
Its number of edges between two vertex sets `A` and `B`, `G.steppedCount P A B`, is the count of
edges from `A` to `B` that the partition predicts: each pair of parts `(C, D)` contributes its
edge density times the trace masses `#(A ∩ C) * #(B ∩ D)`.

The *cut discrepancy* `G.cutDiscrepancy P` is the largest deviation, over all rectangles `(A, B)`,
between the true number of edges `#(G.interedges A B)` and the stepped prediction. It is
count-scaled: it is at most `(card V) ^ 2`, rather than normalized to lie in `[0, 1]`. A partition
whose cut discrepancy is at most `ε * (card V) ^ 2` is a weak regular partition in the sense of
Frieze and Kannan.

Densities include the diagonal blocks: a part `C` is paired with itself, with the density
`G.edgeDensity C C` over `#C * #C` ordered pairs.

## Main declarations

* `SimpleGraph.steppedCount G P A B`: the number of edges from `A` to `B` predicted by `P`.
* `SimpleGraph.steppedCount_eq_card_interedges`: the prediction is exact on rectangles whose
  sides are unions of parts.
* `SimpleGraph.steppedCount_eq_sum_refinementParent`: the prediction of a coarse partition,
  written over the parts of a refinement.
* `SimpleGraph.cutDiscrepancy G P`: the maximum deviation of the prediction from the true count.
* `SimpleGraph.cutDiscrepancy_le_iff` and `SimpleGraph.lt_cutDiscrepancy_iff`: bounds on the cut
  discrepancy are rectangle bounds, and exceeding a bound is witnessed by a rectangle.
* `SimpleGraph.cutDiscrepancy_bot`: the partition into singletons has cut discrepancy `0`.

## References

* A. Frieze, R. Kannan, *Quick approximation to matrices and applications*, Combinatorica 19
  (1999).
* The names `steppedCount` and `cutDiscrepancy` follow `RegularityLemmata/Graph/CutNorm.lean` in
  `cameronfreer/regularity-lemmata` at commit `315ef979f55f31cc43cd791302519d9a34cc2dc0`, where
  they are stated for directed relations.
-/

public section

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (P : Finpartition (univ : Finset V))

/-! ### The stepped count -/

/-- The number of edges from `A` to `B` predicted by the partition `P`: the number of edges of the
`P`-stepped graph between `A` and `B`. Each pair of parts `(C, D)` contributes its edge density
times the trace masses `#(A ∩ C) * #(B ∩ D)`. -/
noncomputable def steppedCount (A B : Finset V) : ℝ :=
  ∑ C ∈ P.parts, ∑ D ∈ P.parts, (G.edgeDensity C D : ℝ) * #(A ∩ C) * #(B ∩ D)

/-- Unfolding lemma for `SimpleGraph.steppedCount`. -/
theorem steppedCount_def (A B : Finset V) :
    G.steppedCount P A B =
      ∑ C ∈ P.parts, ∑ D ∈ P.parts, (G.edgeDensity C D : ℝ) * #(A ∩ C) * #(B ∩ D) := (rfl)

/-- The prediction on a rectangle with an empty side is `0`. -/
@[simp]
theorem steppedCount_empty_left (B : Finset V) : G.steppedCount P ∅ B = 0 := by
  simp [steppedCount_def]

/-- The prediction on a rectangle with an empty side is `0`. -/
@[simp]
theorem steppedCount_empty_right (A : Finset V) : G.steppedCount P A ∅ = 0 := by
  simp [steppedCount_def]

/-- The stepped prediction is symmetric, like the edge count it predicts. -/
theorem steppedCount_comm (A B : Finset V) : G.steppedCount P A B = G.steppedCount P B A := by
  rw [steppedCount_def, steppedCount_def, sum_comm]
  refine sum_congr rfl fun C _ ↦ sum_congr rfl fun D _ ↦ ?_
  rw [G.edgeDensity_comm]
  ring

/-- The stepped prediction is nonnegative. -/
theorem steppedCount_nonneg (A B : Finset V) : 0 ≤ G.steppedCount P A B := by
  rw [steppedCount_def]
  exact sum_nonneg fun C _ ↦ sum_nonneg fun D _ ↦
    mul_nonneg (mul_nonneg (mod_cast G.edgeDensity_nonneg C D) (Nat.cast_nonneg _))
      (Nat.cast_nonneg _)

/-- The stepped prediction never exceeds the number `#A * #B` of ordered pairs. -/
theorem steppedCount_le_card_mul_card (A B : Finset V) : G.steppedCount P A B ≤ #A * #B := by
  calc G.steppedCount P A B ≤ ∑ C ∈ P.parts, ∑ D ∈ P.parts, (#(A ∩ C) : ℝ) * #(B ∩ D) := by
        rw [steppedCount_def]
        gcongr with C _ D _
        exact mul_le_of_le_one_left (by positivity) (mod_cast G.edgeDensity_le_one C D)
    _ = #A * #B := by
        rw [← sum_mul_sum, ← Nat.cast_sum, ← Nat.cast_sum, P.sum_card_inter_parts (subset_univ A),
          P.sum_card_inter_parts (subset_univ B)]

/-- If `A` and `B` are unions of parts of `P`, the stepped prediction on `(A, B)` is the true
number of edges from `A` to `B`. -/
theorem steppedCount_eq_card_interedges {A B : Finset V}
    (hA : ∀ C ∈ P.parts, C ⊆ A ∨ Disjoint C A) (hB : ∀ D ∈ P.parts, D ⊆ B ∨ Disjoint D B) :
    G.steppedCount P A B = #(G.interedges A B) := by
  rw [G.card_interedges_eq_sum_parts P P (subset_univ A) (subset_univ B), steppedCount_def]
  push_cast
  refine sum_congr rfl fun C hC ↦ sum_congr rfl fun D hD ↦ ?_
  -- Each trace is either empty or the whole part, and a pair of whole parts is exact.
  rcases hA C hC with hCA | hCA
  · rcases hB D hD with hDB | hDB
    · rw [inter_eq_right.2 hCA, inter_eq_right.2 hDB, ← G.card_mul_card_mul_edgeDensity_real]
      ring
    · rw [inter_comm B, disjoint_iff_inter_eq_empty.1 hDB]
      simp [interedges_def]
  · rw [inter_comm A, disjoint_iff_inter_eq_empty.1 hCA]
    simp

/-- The partition into singletons predicts every edge count exactly. -/
@[simp]
theorem steppedCount_bot (A B : Finset V) : G.steppedCount ⊥ A B = #(G.interedges A B) := by
  have h (X : Finset V) : ∀ C ∈ (⊥ : Finpartition (univ : Finset V)).parts,
      C ⊆ X ∨ Disjoint C X := by
    simp [Finpartition.parts_bot, em]
  exact G.steppedCount_eq_card_interedges ⊥ (h A) (h B)

/-- The one-part partition predicts the global edge density on every rectangle. -/
theorem steppedCount_top (A B : Finset V) :
    G.steppedCount ⊤ A B = G.edgeDensity univ univ * #A * #B := by
  cases isEmpty_or_nonempty V
  · simp [eq_empty_of_isEmpty A]
  have htop : (⊤ : Finpartition (univ : Finset V)).parts = {univ} := by
    refine (subset_singleton_iff.1 (Finpartition.parts_top_subset _)).resolve_left ?_
    exact (Finpartition.parts_nonempty_iff.2 (univ_nonempty.ne_empty)).ne_empty
  simp [steppedCount_def, htop]

/-- The stepped prediction of `P`, written over the subtype of parts. -/
theorem steppedCount_eq_sum_subtype (A B : Finset V) :
    G.steppedCount P A B = ∑ C : P.parts, ∑ D : P.parts,
      (G.edgeDensity C.1 D.1 : ℝ) * #(A ∩ C.1) * #(B ∩ D.1) := by
  rw [steppedCount_def, ← sum_coe_sort P.parts]
  exact sum_congr rfl fun C _ ↦ (sum_coe_sort _ _).symm

/-- Under a refinement `Q ≤ P`, the prediction of `P` sums, over the pairs of parts of `Q`, the
edge density between their coarse parents times their trace masses. -/
theorem steppedCount_eq_sum_refinementParent {Q : Finpartition (univ : Finset V)} (h : Q ≤ P)
    (A B : Finset V) :
    G.steppedCount P A B = ∑ C : Q.parts, ∑ D : Q.parts,
      (G.edgeDensity (Finpartition.refinementParent h C).1
        (Finpartition.refinementParent h D).1 : ℝ) * #(A ∩ C.1) * #(B ∩ D.1) := by
  rw [Finpartition.sum_sum_eq_sum_sum_fiber h, steppedCount_eq_sum_subtype]
  refine sum_congr rfl fun C' _ ↦ sum_congr rfl fun D' _ ↦ ?_
  -- The trace of `A` on a coarse part is the sum of its traces on the fine parts below it.
  rw [← Finpartition.sum_card_inter_filter_refinementParent_eq h C' A,
    ← Finpartition.sum_card_inter_filter_refinementParent_eq h D' B]
  push_cast
  rw [mul_assoc, sum_mul_sum, mul_sum]
  refine sum_congr rfl fun C hC ↦ ?_
  rw [mul_sum]
  refine sum_congr rfl fun D hD ↦ ?_
  rw [(mem_filter.1 hC).2, (mem_filter.1 hD).2]
  ring

/-! ### The cut discrepancy -/

/-- The cut discrepancy of `G` with respect to `P`: the largest deviation, over all rectangles
`(A, B)`, between the number of edges from `A` to `B` and its stepped prediction. It is
count-scaled, so it lies between `0` and `(card V) ^ 2`. -/
noncomputable def cutDiscrepancy : ℝ :=
  univ.sup' univ_nonempty fun p : Finset V × Finset V ↦
    |(#(G.interedges p.1 p.2) : ℝ) - G.steppedCount P p.1 p.2|

/-- Every rectangle deviation is bounded by the cut discrepancy. -/
theorem abs_card_interedges_sub_steppedCount_le_cutDiscrepancy (A B : Finset V) :
    |(#(G.interedges A B) : ℝ) - G.steppedCount P A B| ≤ G.cutDiscrepancy P :=
  le_sup' (fun p : Finset V × Finset V ↦
    |(#(G.interedges p.1 p.2) : ℝ) - G.steppedCount P p.1 p.2|) (mem_univ (A, B))

variable {G P} in
/-- A bound on the cut discrepancy is exactly a bound on every rectangle deviation. -/
theorem cutDiscrepancy_le_iff {c : ℝ} :
    G.cutDiscrepancy P ≤ c ↔
      ∀ A B : Finset V, |(#(G.interedges A B) : ℝ) - G.steppedCount P A B| ≤ c := by
  simp [cutDiscrepancy, Prod.forall]

variable {G P} in
/-- The cut discrepancy exceeds `c` exactly when some rectangle deviation does. -/
theorem lt_cutDiscrepancy_iff {c : ℝ} :
    c < G.cutDiscrepancy P ↔
      ∃ A B : Finset V, c < |(#(G.interedges A B) : ℝ) - G.steppedCount P A B| := by
  simp [cutDiscrepancy, lt_sup'_iff, Prod.exists]

/-- The cut discrepancy is nonnegative. -/
theorem cutDiscrepancy_nonneg : 0 ≤ G.cutDiscrepancy P :=
  (abs_nonneg _).trans (G.abs_card_interedges_sub_steppedCount_le_cutDiscrepancy P ∅ ∅)

/-- The cut discrepancy is at most the number `(card V) ^ 2` of ordered pairs of vertices. -/
theorem cutDiscrepancy_le_card_sq : G.cutDiscrepancy P ≤ (Fintype.card V : ℝ) ^ 2 := by
  refine cutDiscrepancy_le_iff.2 fun A B ↦ ?_
  have hcount : (#(G.interedges A B) : ℝ) ≤ #A * #B := mod_cast G.card_interedges_le_mul A B
  have hstep := G.steppedCount_le_card_mul_card P A B
  have hnn := G.steppedCount_nonneg P A B
  have hA : (#A : ℝ) ≤ Fintype.card V := mod_cast card_le_univ A
  have hB : (#B : ℝ) ≤ Fintype.card V := mod_cast card_le_univ B
  have hAB : (#A : ℝ) * #B ≤ (Fintype.card V : ℝ) ^ 2 := by
    rw [sq]
    exact mul_le_mul hA hB (by positivity) (by positivity)
  rw [abs_sub_le_iff]
  constructor <;> linarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ #(G.interedges A B))]

/-- The partition into singletons has cut discrepancy `0`. -/
@[simp]
theorem cutDiscrepancy_bot : G.cutDiscrepancy ⊥ = 0 :=
  le_antisymm (cutDiscrepancy_le_iff.2 fun A B ↦ by simp) (G.cutDiscrepancy_nonneg ⊥)

end SimpleGraph
