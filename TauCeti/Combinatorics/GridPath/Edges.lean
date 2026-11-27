/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Sum
public import TauCeti.Combinatorics.GridPath.TwoGrid

/-!
# Edges of monotone grid paths

A path has an ordered list of directed edges. The list has no repetitions, so an assignment of
local data can be indexed by geometric edges rather than by their positions in the list. For a
path through two grids, the two halves are tagged separately, even when their coordinates agree.
The append law lets one keep the same edge data on either side of a corner when making a turn.

The indexing is motivated by the edge tuples of `New.Data.IsPathDatum` in
`grh/src/New/Determinant/AuxiliaryForms/PathData.lean` of lsernau/grh-lean (commit `72fead1`).
-/

public section

namespace TauCeti.GridPath

/-- A directed unit edge in the grid, named by its endpoint with the smaller coordinates. -/
inductive Edge where
  /-- The step from `(a, b + 1)` to `(a, b)`. -/
  | down (a b : ℕ)
  /-- The step from `(a, b)` to `(a + 1, b)`. -/
  | right (a b : ℕ)
  deriving DecidableEq

/-- The node from which the edge departs. -/
@[simp] def Edge.source : Edge → ℕ × ℕ
  | .down a b => (a, b + 1)
  | .right a b => (a, b)

/-- The node at which the edge arrives. -/
@[simp] def Edge.target : Edge → ℕ × ℕ
  | .down a b => (a, b)
  | .right a b => (a + 1, b)

variable {a₀ b₀ a b c d : ℕ}

/-- The directed edges of a path in traversal order. -/
def edges : ∀ {a b}, GridPath a₀ b₀ a b → List Edge
  | _, _, .nil => []
  | a, b, .down p => p.edges ++ [.down a b]
  | a + 1, b, .right p => p.edges ++ [.right a b]

/-- The empty path has no edges. -/
@[simp] theorem edges_nil : (nil : GridPath a₀ b₀ a₀ b₀).edges = [] := (rfl)

/-- Extending a path down appends the corresponding downward edge. -/
@[simp] theorem edges_down (p : GridPath a₀ b₀ a (b + 1)) :
    p.down.edges = p.edges ++ [.down a b] := (rfl)

/-- Extending a path right appends the corresponding rightward edge. -/
@[simp] theorem edges_right (p : GridPath a₀ b₀ a b) :
    p.right.edges = p.edges ++ [.right a b] := (rfl)

/-- Concatenation of paths concatenates their edge lists. -/
@[simp] theorem edges_append (p : GridPath a₀ b₀ a b) (q : GridPath a b c d) :
    (p.append q).edges = p.edges ++ q.edges := by
  induction q <;> simp [*, List.append_assoc]

/-- There is one step for every column gained and every row lost. -/
@[simp] theorem length_edges (p : GridPath a₀ b₀ a b) : p.edges.length = (a - a₀) + (b₀ - b) := by
  induction p with
  | nil => simp
  | down p ih =>
    have := p.le_and_le
    simp only [edges_down, List.length_append, List.length_singleton, ih]
    omega
  | right p ih =>
    have := p.le_and_le
    simp only [edges_right, List.length_append, List.length_singleton, ih]
    omega

/-- Both endpoints of an edge lie in the rectangle between the path's endpoints. The source is
northwest of the target in the order given by rightward and downward steps. -/
theorem bounds_of_mem_edges (p : GridPath a₀ b₀ a b) {e : Edge} (he : e ∈ p.edges) :
    a₀ ≤ e.source.1 ∧ e.source.1 ≤ e.target.1 ∧ e.target.1 ≤ a ∧
    b ≤ e.target.2 ∧ e.target.2 ≤ e.source.2 ∧ e.source.2 ≤ b₀ := by
  induction p with
  | nil => simp at he
  | down p ih =>
    rcases List.mem_append.mp (by simpa only [edges_down] using he) with h | h
    · have := ih h
      omega
    · obtain rfl := List.mem_singleton.mp h
      have := p.le_and_le
      simp at *
      omega
  | right p ih =>
    rcases List.mem_append.mp (by simpa only [edges_right] using he) with h | h
    · have := ih h
      omega
    · obtain rfl := List.mem_singleton.mp h
      have := p.le_and_le
      simp at *
      omega

/-- No directed edge is traversed twice. -/
theorem edges_nodup (p : GridPath a₀ b₀ a b) : p.edges.Nodup := by
  induction p with
  | nil => simp
  | @down a b p ih =>
    rw [edges_down, List.nodup_append_comm, List.singleton_append, List.nodup_cons]
    refine ⟨fun h ↦ ?_, ih⟩
    have := (p.bounds_of_mem_edges h).2.2.2.1
    simp only [Edge.target] at this
    omega
  | @right a b p ih =>
    rw [edges_right, List.nodup_append_comm, List.singleton_append, List.nodup_cons]
    refine ⟨fun h ↦ ?_, ih⟩
    have := (p.bounds_of_mem_edges h).2.2.1
    simp only [Edge.target] at this
    omega

/-- The edges of the top row are the successive steps to the right, in order of increasing
column. -/
theorem edges_row (m a : ℕ) : (row m a).edges = (List.range a).map (fun i ↦ .right i m) := by
  induction a with
  | zero => simp
  | succ a ih => simp [List.range_succ, ih]

/-- The edges down the first column are the steps at rows `b` through `m - 1`, taken in
reverse order. -/
theorem edges_column {m b : ℕ} (hb : b ≤ m) :
    (column hb).edges = (List.range' b (m - b)).reverse.map (.down 0) := by
  induction hb using Nat.decreasingInduction with
  | self => simp
  | of_succ b h ih =>
    rw [column_of_lt h, edges_down, ih]
    have hlen : m - b = m - (b + 1) + 1 := by omega
    rw [hlen, List.range'_succ]
    simp

/-- The two routes around a square have exactly their two corner edges as differences, even
with a common prefix and suffix. -/
theorem edges_sdiff_corner {i j : ℕ} (q : GridPath a₀ b₀ i (j + 1))
    (r : GridPath (i + 1) j c d) :
    let old := (q.down.right.append r).edges.toFinset
    let new := (q.right.down.append r).edges.toFinset
    (old \ new, new \ old) =
      ({Edge.down i j, Edge.right i j}, {Edge.right i (j + 1), Edge.down (i + 1) j}) := by
  have hold := (q.down.right.append r).edges_nodup
  have hnew := (q.right.down.append r).edges_nodup
  -- Non-repetition excludes each changed edge from the common prefix and suffix.
  simp only [edges_append, edges_down, edges_right, List.nodup_append', List.nodup_singleton,
    List.disjoint_left, List.mem_append, List.mem_singleton, true_and] at hold hnew
  dsimp only
  apply Prod.ext <;> ext e <;>
    simp only [edges_append, edges_down, edges_right, Finset.mem_sdiff, List.mem_toFinset,
      List.mem_append, List.mem_singleton, Finset.mem_insert, Finset.mem_singleton] <;>
    grind

end TauCeti.GridPath

namespace TauCeti.TwoGridPath

open GridPath (Edge)

/-- The finite edge index for a two-grid path. The left summand belongs to the first grid
(`half false`), the right summand to the second (`half true`). Each edge uses the local
coordinates of its own half. -/
def edges {m : ℕ} (p : TwoGridPath m) : Finset (Edge ⊕ Edge) :=
  (p.half false).edges.toFinset.disjSum (p.half true).edges.toFinset

/-- A left-tagged edge occurs exactly when it is traversed by the first half. -/
@[simp] theorem inl_mem_edges {m : ℕ} {p : TwoGridPath m} {e : Edge} :
    Sum.inl e ∈ p.edges ↔ e ∈ (p.half false).edges := by
  simp [edges]

/-- A right-tagged edge occurs exactly when it is traversed by the second half. -/
@[simp] theorem inr_mem_edges {m : ℕ} {p : TwoGridPath m} {e : Edge} :
    Sum.inr e ∈ p.edges ↔ e ∈ (p.half true).edges := by
  simp [edges]

/-- Every path through two grids of size `m` has exactly `2 * m` tagged edges, independently
of where its halves reach the diagonal. -/
@[simp] theorem card_edges {m : ℕ} (p : TwoGridPath m) : p.edges.card = 2 * m := by
  simp only [edges, Finset.card_disjSum, List.toFinset_card_of_nodup (GridPath.edges_nodup _),
    GridPath.length_edges, Nat.sub_zero]
  have := p.diagonalIndex_le
  omega

/-- The changed edge sets of a turn: each set records only the edges absent on the other path.
An off-diagonal turn changes two edges in one grid, while a diagonal turn changes one in each. -/
theorem Turn.edges_sdiff {m : ℕ} {p p' : TwoGridPath m} {i j : ℕ}
    (h : p.Turn (i, j) p') :
    (p.edges \ p'.edges, p'.edges \ p.edges) =
      if i < j then
        ({Sum.inl (.down i j), Sum.inl (.right i j)},
          {Sum.inl (.right i (j + 1)), Sum.inl (.down (i + 1) j)})
      else if j < i then
        ({Sum.inr (.down j i), Sum.inr (.right j i)},
          {Sum.inr (.right j (i + 1)), Sum.inr (.down (j + 1) i)})
      else
        ({Sum.inl (.down i j), Sum.inr (.down i j)},
          {Sum.inl (.right i (j + 1)), Sum.inr (.right i (j + 1))}) := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · obtain ⟨q, r, hp, rfl⟩ := h.exists_half_false_eq_of_lt hij
    have hcut := GridPath.edges_sdiff_corner q r
    rw [ite_eq_left hij]
    apply Prod.ext
    · ext (e | e)
      · have hs := Finset.ext_iff.mp (congrArg Prod.fst hcut) e
        simp [hp] at hs ⊢
        tauto
      · simp
    · ext (e | e)
      · have hs := Finset.ext_iff.mp (congrArg Prod.snd hcut) e
        simp [hp] at hs ⊢
        tauto
      · simp
  · obtain ⟨q, rfl, rfl⟩ := h.exists_eq_down_and_eq_right
    have hdown (z : Bool) : Edge.down i i ∉ (q z).edges := fun he ↦ by
      have := ((q z).bounds_of_mem_edges he).2.2.2.1
      simp only [Edge.target] at this
      omega
    have hright (z : Bool) : Edge.right i (i + 1) ∉ (q z).edges := fun he ↦ by
      have := ((q z).bounds_of_mem_edges he).2.2.1
      simp only [Edge.target] at this
      omega
    simp only [lt_irrefl, ite_false]
    apply Prod.ext <;> ext e <;> cases e <;>
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, inl_mem_edges,
        inr_mem_edges, GridPath.edges_down, GridPath.edges_right, List.mem_append,
        List.mem_singleton] <;> grind
  · obtain ⟨q, r, hp, rfl⟩ := h.exists_half_true_eq_of_gt hji
    have hcut := GridPath.edges_sdiff_corner q r
    rw [ite_eq_right hji.not_gt, ite_eq_left hji]
    apply Prod.ext
    · ext (e | e)
      · simp
      · have hs := Finset.ext_iff.mp (congrArg Prod.fst hcut) e
        simp [hp] at hs ⊢
        tauto
    · ext (e | e)
      · simp
      · have hs := Finset.ext_iff.mp (congrArg Prod.snd hcut) e
        simp [hp] at hs ⊢
        tauto

end TauCeti.TwoGridPath
