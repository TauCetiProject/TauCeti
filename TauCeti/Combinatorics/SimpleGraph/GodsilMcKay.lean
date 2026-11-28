/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# Godsil–McKay switching

A *Godsil–McKay partition* of a finite simple graph `G` splits the vertices into nonempty cells
`X_i` and a remaining set `Y` such that the partition of `⋃ X_i` into the `X_i` is equitable
(every vertex of `X_i` has the same number of neighbours in `X_j`), and every vertex of `Y` is
adjacent to none, exactly half, or all of each `X_i`. Switching complements the adjacency between
each `y ∈ Y` and each cell `X_i` of which `y` sees exactly half.

Over a field of characteristic zero, the block-diagonal matrix `Q` with blocks `(2 / |X_i|) J - I`
on the cells `X_i` and `I` on `Y` is symmetric, squares to `I`, fixes the all-ones matrix `J` and
conjugates the adjacency matrix of `G` to that of the switched graph. Consequently the switched
graph has the same characteristic polynomial as `G` over every commutative ring, and so does its
complement: Godsil–McKay switching produces cospectral graphs with cospectral complements.

## Main definitions

* `SimpleGraph.GodsilMcKayPartition G ι`: a Godsil–McKay partition of `G` with cells indexed
  by `ι`.
* `SimpleGraph.GodsilMcKayPartition.Flips`: the pairs `(y, x)` whose adjacency is complemented.
* `SimpleGraph.GodsilMcKayPartition.switch`: the switched graph.
* `SimpleGraph.GodsilMcKayPartition.toSwitch`: the same cells, as a partition of the switched
  graph.
* `SimpleGraph.GodsilMcKayPartition.conjMatrix`: the conjugating matrix `Q`.

## Main results

* `SimpleGraph.GodsilMcKayPartition.switch_toSwitch`: switching twice returns `G`.
* `SimpleGraph.GodsilMcKayPartition.isSymm_conjMatrix`,
  `SimpleGraph.GodsilMcKayPartition.conjMatrix_mul_self`,
  `SimpleGraph.GodsilMcKayPartition.conjMatrix_mul_of_one`: `Q` is symmetric, `Q² = I`, `QJ = J`.
* `SimpleGraph.GodsilMcKayPartition.conjMatrix_mul_adjMatrix`,
  `SimpleGraph.GodsilMcKayPartition.conjMatrix_conj`: `Q A(G) = A(P.switch) Q` and
  `Q A(G) Q = A(P.switch)`.
* `SimpleGraph.GodsilMcKayPartition.charpoly_adjMatrix_switch`,
  `SimpleGraph.GodsilMcKayPartition.charpoly_adjMatrix_compl_switch`: switching preserves the
  characteristic polynomial of the adjacency matrix and that of the complement.

## References

* C. D. Godsil and B. D. McKay, *Constructing cospectral graphs*, Aequationes Math. 25 (1982),
  257–268.
* A. E. Brouwer and W. H. Haemers, *Spectra of Graphs*, Universitext, Springer, 2012, §1.8.3.
-/

public section

open Finset Matrix

namespace SimpleGraph

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A **Godsil–McKay partition** of `G`: the cells `X_i = cell⁻¹ (some i)` are nonempty, and with
`Y = cell⁻¹ none`, the partition of `⋃ X_i` into the `X_i` is equitable, and every vertex of `Y`
has `0`, `|X_i| / 2` or `|X_i|` neighbours in each `X_i`. -/
@[ext]
structure GodsilMcKayPartition (ι : Type*) [DecidableEq ι] where
  /-- The cell of a vertex: `some i` for `X_i`, `none` for `Y`. -/
  cell : V → Option ι
  /-- Every cell `X_i` is nonempty. -/
  nonempty : ∀ i, ∃ x, cell x = some i
  /-- The partition into the `X_i` is equitable: vertices of one cell have equally many
  neighbours in each cell. -/
  equitable : ∀ x x' i j, cell x = some i → cell x' = some i →
    #{z ∈ G.neighborFinset x | cell z = some j} = #{z ∈ G.neighborFinset x' | cell z = some j}
  /-- Each vertex of `Y` sees none, exactly half, or all of each `X_i`. -/
  outside : ∀ y i, cell y = none →
    #{z ∈ G.neighborFinset y | cell z = some i} = 0 ∨
      2 * #{z ∈ G.neighborFinset y | cell z = some i} = #{z | cell z = some i} ∨
      #{z ∈ G.neighborFinset y | cell z = some i} = #{z | cell z = some i}

namespace GodsilMcKayPartition

variable {G} {ι : Type*} [DecidableEq ι] (P : G.GodsilMcKayPartition ι)

/-- The neighbours of `y` in a set `{z | p z}` are the elements of that set adjacent to `y`. -/
private theorem filter_neighborFinset (H : SimpleGraph V) [DecidableRel H.Adj] (y : V)
    (p : V → Prop) [DecidablePred p] :
    {z ∈ H.neighborFinset y | p z} = {z ∈ ({z | p z} : Finset V) | H.Adj y z} := by
  ext z
  simp [and_comm]

/-- Every cell `X_i` has positive size. -/
theorem card_cell_pos (i : ι) : 0 < #{z | P.cell z = some i} := by
  obtain ⟨x, hx⟩ := P.nonempty i
  exact card_pos.2 ⟨x, by simpa using hx⟩

/-- The pairs whose adjacency the switching complements: `y ∈ Y` and `x ∈ X_i`, where `y` has
exactly half of `X_i` as neighbours. -/
def Flips (y x : V) : Prop :=
  P.cell y = none ∧ ∃ i, P.cell x = some i ∧
    2 * #{z ∈ G.neighborFinset y | P.cell z = some i} = #{z | P.cell z = some i}

/-- Whether a pair is flipped is decidable. -/
instance (y x : V) : Decidable (P.Flips y x) :=
  decidable_of_iff (P.cell y = none ∧ ∃ i ∈ P.cell x,
      2 * #{z ∈ G.neighborFinset y | P.cell z = some i} = #{z | P.cell z = some i})
    (by simp [Flips])

/-- A pair `(y, x)` with `x ∈ X_i` is flipped exactly when `y ∈ Y` has half of `X_i` as
neighbours. -/
theorem flips_iff_of_cell_eq_some {y x : V} {i : ι} (hx : P.cell x = some i) :
    P.Flips y x ↔ P.cell y = none ∧
      2 * #{z ∈ G.neighborFinset y | P.cell z = some i} = #{z | P.cell z = some i} := by
  simp [Flips, hx]

/-- No pair `(y, x)` with `y` in a cell `X_i` is flipped. -/
theorem not_flips_of_cell_eq_some {y x : V} {i : ι} (hy : P.cell y = some i) :
    ¬ P.Flips y x := by
  simp [Flips, hy]

/-- No pair `(y, x)` with `x ∈ Y` is flipped. -/
theorem not_flips_of_cell_eq_none {y x : V} (hx : P.cell x = none) : ¬ P.Flips y x := by
  simp [Flips, hx]

/-- **The Godsil–McKay switched graph**: the adjacency between `y ∈ Y` and `x ∈ X_i` is
complemented when `y` has exactly half of `X_i` as neighbours, and kept otherwise. -/
def switch : SimpleGraph V where
  Adj x y := Xor (G.Adj x y) (P.Flips x y ∨ P.Flips y x)
  symm := ⟨fun x y h ↦ by rwa [G.adj_comm, or_comm] at h⟩
  loopless := ⟨fun x ↦ by
    cases hx : P.cell x <;> simp [not_flips_of_cell_eq_none, not_flips_of_cell_eq_some, hx]⟩

/-- Adjacency in the switched graph: the adjacency of `G`, complemented at flipped pairs. -/
@[simp]
theorem switch_adj {x y : V} : P.switch.Adj x y ↔ Xor (G.Adj x y) (P.Flips x y ∨ P.Flips y x) :=
  Iff.rfl

/-- Adjacency in the switched graph is decidable. -/
instance : DecidableRel P.switch.Adj := fun x y ↦
  inferInstanceAs (Decidable (Xor (G.Adj x y) (P.Flips x y ∨ P.Flips y x)))

/-- Inside `⋃ X_i` the switched graph agrees with `G`. -/
theorem switch_adj_of_cell_eq_some {x z : V} {i j : ι} (hx : P.cell x = some i)
    (hz : P.cell z = some j) : P.switch.Adj x z ↔ G.Adj x z := by
  simp [xor_def, P.not_flips_of_cell_eq_some hx, P.not_flips_of_cell_eq_some hz]

/-- Inside `Y` the switched graph agrees with `G`. -/
theorem switch_adj_of_cell_eq_none {y z : V} (hy : P.cell y = none) (hz : P.cell z = none) :
    P.switch.Adj y z ↔ G.Adj y z := by
  simp [xor_def, P.not_flips_of_cell_eq_none hy, P.not_flips_of_cell_eq_none hz]

/-- Between `y ∈ Y` and `x ∈ X_i` the adjacency is complemented exactly when `y` has half of
`X_i` as neighbours. -/
theorem switch_adj_of_cell_eq_none_of_cell_eq_some {y x : V} {i : ι} (hy : P.cell y = none)
    (hx : P.cell x = some i) :
    P.switch.Adj y x ↔ Xor (G.Adj y x)
      (2 * #{z ∈ G.neighborFinset y | P.cell z = some i} = #{z | P.cell z = some i}) := by
  simp [P.flips_iff_of_cell_eq_some hx, P.not_flips_of_cell_eq_some hx, hy]

/-- A vertex of `⋃ X_i` has as many neighbours in each cell after switching as before. -/
theorem card_switch_neighborFinset_filter_of_cell_eq_some {x : V} {i : ι}
    (hx : P.cell x = some i) (j : ι) :
    #{z ∈ P.switch.neighborFinset x | P.cell z = some j} =
      #{z ∈ G.neighborFinset x | P.cell z = some j} := by
  rw [filter_neighborFinset, filter_neighborFinset]
  congr 1
  refine filter_congr fun z hz ↦ P.switch_adj_of_cell_eq_some hx (by simpa using hz)

/-- A vertex `y ∈ Y` with exactly half of `X_i` as neighbours has the other half as neighbours
after switching; otherwise its neighbours in `X_i` are unchanged. -/
theorem card_switch_neighborFinset_filter_of_cell_eq_none {y : V} (hy : P.cell y = none)
    (i : ι) :
    #{z ∈ P.switch.neighborFinset y | P.cell z = some i} =
      if 2 * #{z ∈ G.neighborFinset y | P.cell z = some i} = #{z | P.cell z = some i} then
        #{z | P.cell z = some i} - #{z ∈ G.neighborFinset y | P.cell z = some i}
      else #{z ∈ G.neighborFinset y | P.cell z = some i} := by
  have key (z : V) (hz : z ∈ ({z | P.cell z = some i} : Finset V)) :=
    P.switch_adj_of_cell_eq_none_of_cell_eq_some (x := z) hy (by simpa using hz)
  rw [filter_neighborFinset P.switch]
  split_ifs with h
  · simp only [h, xor_def, not_true_eq_false, and_false, true_and, false_or] at key
    have := card_filter_add_card_filter_not (s := ({z | P.cell z = some i} : Finset V))
      (fun z ↦ G.Adj y z)
    rw [filter_congr key, filter_neighborFinset]
    omega
  · simp only [h, xor_def, not_false_eq_true, and_true, false_and, or_false] at key
    rw [filter_congr key, ← filter_neighborFinset]

/-- The cells of a Godsil–McKay partition form a Godsil–McKay partition of the switched
graph. -/
def toSwitch : P.switch.GodsilMcKayPartition ι where
  cell := P.cell
  nonempty := P.nonempty
  equitable x x' i j hx hx' := by
    rw [P.card_switch_neighborFinset_filter_of_cell_eq_some hx,
      P.card_switch_neighborFinset_filter_of_cell_eq_some hx', P.equitable x x' i j hx hx']
  outside y i hy := by
    rw [P.card_switch_neighborFinset_filter_of_cell_eq_none hy]
    have hle : #{z ∈ G.neighborFinset y | P.cell z = some i} ≤ #{z | P.cell z = some i} := by
      rw [filter_neighborFinset]
      exact card_filter_le _ _
    rcases P.outside y i hy with h | h | h <;> split_ifs <;> omega

/-- The partition `P.toSwitch` of the switched graph has the cells of `P`. -/
@[simp]
theorem toSwitch_cell : P.toSwitch.cell = P.cell :=
  (rfl)

/-- The switched graph has the same flipped pairs as `G`. -/
@[simp]
theorem toSwitch_flips_iff {y x : V} : P.toSwitch.Flips y x ↔ P.Flips y x := by
  cases hx : P.cell x with
  | none => simp [not_flips_of_cell_eq_none, hx]
  | some i =>
    rw [flips_iff_of_cell_eq_some _ (by simpa using hx), flips_iff_of_cell_eq_some _ hx]
    refine and_congr_right fun hy ↦ ?_
    simp only [toSwitch_cell]
    rw [P.card_switch_neighborFinset_filter_of_cell_eq_none hy]
    have hle : #{z ∈ G.neighborFinset y | P.cell z = some i} ≤ #{z | P.cell z = some i} := by
      rw [filter_neighborFinset]
      exact card_filter_le _ _
    split_ifs <;> omega

/-- **Switching twice returns the original graph.** -/
@[simp]
theorem switch_toSwitch : P.toSwitch.switch = G := by
  ext x y
  simp only [switch_adj, toSwitch_flips_iff]
  by_cases P.Flips x y ∨ P.Flips y x <;> by_cases G.Adj x y <;> simp_all [xor_def]

/-- Switching twice returns the original adjacency matrix. -/
theorem adjMatrix_switch_toSwitch {R : Type*} [Zero R] [One R] :
    P.toSwitch.switch.adjMatrix R = G.adjMatrix R := by
  ext x y
  simp only [adjMatrix_apply]
  exact if_congr (by rw [switch_toSwitch]) rfl rfl

/-- In a Godsil–McKay partition, the edges between `X_i` and `X_j` counted from either side give
`|X_i| b_{ij} = |X_j| b_{ji}`, where `b_{ij}` is the number of neighbours in `X_j` of a vertex
of `X_i`. -/
theorem card_cell_mul_card_neighborFinset_filter {x z : V} {i j : ι} (hx : P.cell x = some i)
    (hz : P.cell z = some j) :
    #{w | P.cell w = some i} * #{w ∈ G.neighborFinset x | P.cell w = some j} =
      #{w | P.cell w = some j} * #{w ∈ G.neighborFinset z | P.cell w = some i} := by
  have hsum := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := ({w | P.cell w = some i} : Finset V)) (t := {w | P.cell w = some j}) G.Adj
  have hi : ∀ x' ∈ ({w | P.cell w = some i} : Finset V),
      #(bipartiteAbove G.Adj {w | P.cell w = some j} x') =
        #{w ∈ G.neighborFinset x | P.cell w = some j} := fun x' hx' ↦ by
    rw [bipartiteAbove, ← filter_neighborFinset]
    exact P.equitable x' x i j (by simpa using hx') hx
  have hj : ∀ z' ∈ ({w | P.cell w = some j} : Finset V),
      #(bipartiteBelow G.Adj {w | P.cell w = some i} z') =
        #{w ∈ G.neighborFinset z | P.cell w = some i} := fun z' hz' ↦ by
    rw [bipartiteBelow, ← P.equitable z' z j i (by simpa using hz') hz, filter_neighborFinset]
    simp_rw [G.adj_comm z']
  rw [sum_congr rfl hi, sum_congr rfl hj, sum_const, sum_const, smul_eq_mul,
    smul_eq_mul] at hsum
  exact hsum

/-- The entries of `A` in a column, summed over a cell, count the neighbours in that cell. -/
private theorem sum_adjMatrix_cell {R : Type*} [NonAssocSemiring R] (H : SimpleGraph V)
    [DecidableRel H.Adj] (i : ι) (z : V) :
    ∑ w with P.cell w = some i, H.adjMatrix R w z =
      #{w ∈ H.neighborFinset z | P.cell w = some i} := by
  rw [filter_neighborFinset]
  simp [adjMatrix_apply, sum_boole, H.adj_comm z]

section conjMatrix

variable [DecidableEq V] (R : Type*) [Field R]

/-- **The Godsil–McKay conjugating matrix**: the block-diagonal matrix with blocks
`(2 / |X_i|) J - I` on the cells `X_i` and `I` on `Y`. -/
def conjMatrix : Matrix V V R :=
  of fun x y ↦
    match P.cell x with
    | none => (1 : Matrix V V R) x y
    | some i => (if P.cell y = some i then 2 / (#{z | P.cell z = some i} : R) else 0) -
        (1 : Matrix V V R) x y

variable {R}

/-- A row of `Q` in `Y` is the corresponding row of the identity. -/
theorem conjMatrix_apply_of_cell_eq_none {x : V} (hx : P.cell x = none) (y : V) :
    P.conjMatrix R x y = (1 : Matrix V V R) x y := by
  simp [conjMatrix, hx]

/-- A row of `Q` in `X_i` is `2 / |X_i|` on `X_i` and `0` elsewhere, minus the row of the
identity. -/
theorem conjMatrix_apply_of_cell_eq_some {x : V} {i : ι} (hx : P.cell x = some i) (y : V) :
    P.conjMatrix R x y =
      (if P.cell y = some i then 2 / (#{z | P.cell z = some i} : R) else 0) -
        (1 : Matrix V V R) x y := by
  simp [conjMatrix, hx]

/-- **`Q` is symmetric.** -/
theorem isSymm_conjMatrix : (P.conjMatrix R).IsSymm := by
  refine IsSymm.ext fun x y ↦ ?_
  obtain rfl | hxy := eq_or_ne x y
  · rfl
  simp only [conjMatrix, of_apply, Matrix.one_apply, hxy, hxy.symm, ite_false, sub_zero]
  cases P.cell x <;> cases P.cell y <;> simp only [reduceCtorEq, ite_false, Option.some.injEq]
  split_ifs <;> subst_vars <;> first | rfl | exact absurd rfl ‹_›

/-- A row of `Q` in `Y` picks out the corresponding row of the right factor. -/
theorem conjMatrix_mul_apply_of_cell_eq_none {x : V} (hx : P.cell x = none) (M : Matrix V V R)
    (z : V) : (P.conjMatrix R * M) x z = M x z := by
  simp [Matrix.mul_apply, P.conjMatrix_apply_of_cell_eq_none hx, Matrix.one_apply]

/-- A row of `Q` in `X_i` takes `2 / |X_i|` times the sum of the rows of the right factor over
`X_i`, minus the corresponding row. -/
theorem conjMatrix_mul_apply_of_cell_eq_some {x : V} {i : ι} (hx : P.cell x = some i)
    (M : Matrix V V R) (z : V) :
    (P.conjMatrix R * M) x z =
      2 / (#{w | P.cell w = some i} : R) * ∑ w with P.cell w = some i, M w z - M x z := by
  simp [Matrix.mul_apply, P.conjMatrix_apply_of_cell_eq_some hx, sub_mul, Matrix.one_apply,
    sum_sub_distrib, ite_mul, sum_ite, mul_sum]

/-- The sum of a column of `Q` over a cell `X_i` whose size is invertible is `1` on `X_i` and `0`
elsewhere. -/
private theorem sum_cell_conjMatrix {i : ι} (hm : (#{z | P.cell z = some i} : R) ≠ 0) (z : V) :
    ∑ w with P.cell w = some i, P.conjMatrix R w z = if P.cell z = some i then 1 else 0 := by
  rw [sum_congr rfl fun w hw ↦ P.conjMatrix_apply_of_cell_eq_some (by simpa using hw) z,
    sum_sub_distrib, sum_const, nsmul_eq_mul]
  simp only [Matrix.one_apply, sum_ite_eq', mem_filter, mem_univ, true_and]
  split_ifs
  · field_simp
    ring
  · simp

/-- **`Q` is an involution.** -/
theorem conjMatrix_mul_self : P.conjMatrix R * P.conjMatrix R = 1 := by
  ext x z
  cases hx : P.cell x with
  | none => rw [P.conjMatrix_mul_apply_of_cell_eq_none hx, P.conjMatrix_apply_of_cell_eq_none hx]
  | some i =>
    rw [P.conjMatrix_mul_apply_of_cell_eq_some hx, P.conjMatrix_apply_of_cell_eq_some hx]
    by_cases hm : (#{z | P.cell z = some i} : R) = 0
    · -- a cell of size zero in `R` makes the block `-I`
      simp [hm]
    · rw [P.sum_cell_conjMatrix hm]
      split_ifs <;> ring

variable [CharZero R]

omit [DecidableEq V] in
/-- The size of a cell is nonzero in a field of characteristic zero. -/
theorem card_cell_ne_zero (i : ι) : (#{z | P.cell z = some i} : R) ≠ 0 :=
  Nat.cast_ne_zero.2 (P.card_cell_pos i).ne'

/-- **`Q` fixes the all-ones matrix.** -/
theorem conjMatrix_mul_of_one :
    P.conjMatrix R * of (fun _ _ ↦ (1 : R)) = of (fun _ _ ↦ (1 : R)) := by
  ext x z
  cases hx : P.cell x with
  | none => rw [P.conjMatrix_mul_apply_of_cell_eq_none hx]
  | some i =>
    have hm := P.card_cell_ne_zero (R := R) i
    rw [P.conjMatrix_mul_apply_of_cell_eq_some hx]
    simp only [of_apply, sum_const, nsmul_eq_mul, mul_one]
    field_simp
    ring

/-- **The all-ones matrix is fixed by `Q` on the right.** -/
theorem of_one_mul_conjMatrix :
    of (fun _ _ ↦ (1 : R)) * P.conjMatrix R = of (fun _ _ ↦ (1 : R)) := by
  simpa [transpose_mul, P.isSymm_conjMatrix.eq] using
    congrArg transpose (P.conjMatrix_mul_of_one (R := R))

omit [DecidableEq V] in
/-- The entry of `Q A(G)` between `y ∈ Y` and `x ∈ X_i` is the adjacency of the switched graph:
`(2 / |X_i|) |N(y) ∩ X_i| - [y ∼ x] = [y ∼' x]`. -/
private theorem two_div_mul_sub_adjMatrix {y x : V} {i : ι} (hy : P.cell y = none)
    (hx : P.cell x = some i) :
    2 / (#{w | P.cell w = some i} : R) * #{w ∈ G.neighborFinset y | P.cell w = some i} -
      G.adjMatrix R y x = P.switch.adjMatrix R y x := by
  have hm := P.card_cell_pos i
  have hmR := P.card_cell_ne_zero (R := R) i
  have hxi : x ∈ ({w | P.cell w = some i} : Finset V) := by simpa using hx
  simp only [adjMatrix_apply, P.switch_adj_of_cell_eq_none_of_cell_eq_some hy hx]
  rcases P.outside y i hy with h | h | h
  · have hadj : ¬ G.Adj y x := by
      rw [filter_neighborFinset, card_eq_zero] at h
      exact filter_eq_empty_iff.1 h hxi
    simp [h, hadj, hm.ne]
  · have hcast : (2 : R) * #{w ∈ G.neighborFinset y | P.cell w = some i} =
        #{w | P.cell w = some i} := by exact_mod_cast h
    rw [div_mul_eq_mul_div, hcast, div_self hmR]
    by_cases hadj : G.Adj y x <;> simp [h, hadj, xor_def]
  · have hadj : G.Adj y x := by
      rw [filter_neighborFinset] at h
      exact (mem_filter.1 (eq_of_subset_of_card_le (filter_subset _ _) h.ge ▸ hxi)).2
    have hflip : ¬ 2 * #{w | P.cell w = some i} = #{w | P.cell w = some i} := by omega
    rw [h, div_mul_cancel₀ _ hmR]
    simp only [hadj, hflip, xor_def]
    norm_num

/-- **`Q` intertwines the adjacency matrices**: `Q A(G) = A(P.switch) Q`. -/
theorem conjMatrix_mul_adjMatrix :
    P.conjMatrix R * G.adjMatrix R = P.switch.adjMatrix R * P.conjMatrix R := by
  ext x z
  have hT : (P.switch.adjMatrix R * P.conjMatrix R) x z =
      (P.conjMatrix R * P.switch.adjMatrix R) z x := by
    rw [← transpose_apply (P.conjMatrix R * _), transpose_mul, P.isSymm_conjMatrix.eq,
      transpose_adjMatrix]
  rw [hT]
  cases hx : P.cell x with
  | none =>
    cases hz : P.cell z with
    | none =>
      rw [P.conjMatrix_mul_apply_of_cell_eq_none hx, P.conjMatrix_mul_apply_of_cell_eq_none hz]
      simp only [adjMatrix_apply, P.switch_adj_of_cell_eq_none hz hx, G.adj_comm]
    | some j =>
      -- the entry between `x ∈ Y` and `z ∈ X_j`, read off the partition of the switched graph
      have h := P.toSwitch.two_div_mul_sub_adjMatrix (R := R) hx hz
      rw [P.adjMatrix_switch_toSwitch] at h
      simp only [toSwitch_cell] at h
      rw [P.conjMatrix_mul_apply_of_cell_eq_none hx, P.conjMatrix_mul_apply_of_cell_eq_some hz,
        P.sum_adjMatrix_cell, (P.switch.isSymm_adjMatrix (α := R)).apply x z, ← h]
  | some i =>
    cases hz : P.cell z with
    | none =>
      rw [P.conjMatrix_mul_apply_of_cell_eq_some hx, P.conjMatrix_mul_apply_of_cell_eq_none hz,
        P.sum_adjMatrix_cell, ← (G.isSymm_adjMatrix (α := R)).apply x z,
        P.two_div_mul_sub_adjMatrix hz hx]
    | some j =>
      -- inside `⋃ X_i` the switched graph is `G`, and `b_{ji} / |X_i| = b_{ij} / |X_j|`
      have hm := P.card_cell_mul_card_neighborFinset_filter hx hz
      have hi := P.card_cell_ne_zero (R := R) i
      have hj := P.card_cell_ne_zero (R := R) j
      rw [P.conjMatrix_mul_apply_of_cell_eq_some hx, P.conjMatrix_mul_apply_of_cell_eq_some hz,
        P.sum_adjMatrix_cell, P.sum_adjMatrix_cell,
        P.card_switch_neighborFinset_filter_of_cell_eq_some hx]
      simp only [adjMatrix_apply, P.switch_adj_of_cell_eq_some hz hx, G.adj_comm z x]
      congr 1
      field_simp
      exact_mod_cast (mul_comm _ _).trans hm.symm

/-- **The conjugating matrix.** `Q A(G) Q = A(P.switch)`. -/
theorem conjMatrix_conj :
    P.conjMatrix R * G.adjMatrix R * P.conjMatrix R = P.switch.adjMatrix R := by
  rw [conjMatrix_mul_adjMatrix, mul_assoc, conjMatrix_mul_self, mul_one]

end conjMatrix

/-- **Godsil–McKay switching preserves the characteristic polynomial** of the adjacency
matrix. -/
theorem charpoly_adjMatrix_switch [DecidableEq V] (R : Type*) [CommRing R] :
    (P.switch.adjMatrix R).charpoly = (G.adjMatrix R).charpoly := by
  refine charpoly_adjMatrix_eq_of_charpoly_rat_eq ?_
  rw [← P.conjMatrix_conj, mul_assoc, charpoly_mul_comm, mul_assoc, conjMatrix_mul_self, mul_one]

/-- **Godsil–McKay switching preserves the characteristic polynomial of the complement.** -/
theorem charpoly_adjMatrix_compl_switch [DecidableEq V] (R : Type*) [CommRing R] :
    (P.switchᶜ.adjMatrix R).charpoly = (Gᶜ.adjMatrix R).charpoly := by
  refine charpoly_adjMatrix_eq_of_charpoly_rat_eq ?_
  have h : P.switchᶜ.adjMatrix ℚ = P.conjMatrix ℚ * Gᶜ.adjMatrix ℚ * P.conjMatrix ℚ := by
    rw [adjMatrix_compl, adjMatrix_compl, mul_sub, sub_mul, mul_sub, sub_mul, mul_one,
      conjMatrix_mul_self, conjMatrix_mul_of_one, of_one_mul_conjMatrix, conjMatrix_conj]
  rw [h, mul_assoc, charpoly_mul_comm, mul_assoc, conjMatrix_mul_self, mul_one]

end GodsilMcKayPartition

end SimpleGraph
