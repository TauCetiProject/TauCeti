/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.GridPath.Basic

/-!
# Paths through two grids and their turns

A path from the node `(m, 0)` to the node `(0, m)` by steps up or left meets the diagonal once, at
some `(l, l)`. Splitting it there gives two halves that are both recorded as grid paths from
`(0, m)` to `(l, l)` by steps down or right (`TauCeti.TwoGridPath`): in the application one half
lies in each of two grids of unitary groups, the grid of the spaces `Y^a_b` and the grid of the
spaces `Y'^b_a`. The *first* path
(`TauCeti.TwoGridPath.first`) runs through `(0, 0)`, the *last* (`TauCeti.TwoGridPath.last`)
through `(m, m)`.

A *turn* at `(i, j)` (`TauCeti.TwoGridPath.Turn`) replaces the node `(i, j)` by `(i + 1, j + 1)`:
off the diagonal it exchanges a step down and a step right at a corner of one half, and on the
diagonal it replaces the last step down of both halves by a step right, moving the diagonal node
from `(j, j)` to `(j + 1, j + 1)`. The squares between the first path and a path
(`TauCeti.TwoGridPath.squares`) gain exactly the square `(i, j)` under a turn at `(i, j)`
(`TauCeti.TwoGridPath.Turn.notMem_squares`, `TauCeti.TwoGridPath.Turn.squares_eq`). Every path but
the last has a turn (`TauCeti.TwoGridPath.exists_turn`), so a property that holds at the last path
and passes backwards along turns holds at the first path, collecting all `m²` squares
(`TauCeti.TwoGridPath.turn_induction`).

In the application, periods of automorphic forms are moved, one square at a time, from the first
path (the chain of theta lifts) to the last, where all spaces are definite.

## Main declarations

* `TauCeti.TwoGridPath`, `TauCeti.TwoGridPath.first`, `TauCeti.TwoGridPath.last`.
* `TauCeti.TwoGridPath.Turn`: turns.
* `TauCeti.TwoGridPath.squares`, `TauCeti.TwoGridPath.Turn.notMem_squares`,
  `TauCeti.TwoGridPath.Turn.squares_eq`: the squares between the first path and a path, and their
  change under a turn.
* `TauCeti.TwoGridPath.exists_turn`: every path but the last can be turned.
* `TauCeti.TwoGridPath.turn_induction`: induction backwards along turns.

## References

* Adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026
  Anthropic, PBC), `src/New/Determinant/AuxiliaryForms/GridPaths.lean`: `New.TwoGridPath`,
  `New.TwoGridPath.Turn`, `New.TwoGridPath.exists_turn` and `New.TwoGridPath.turn_induction`.
-/

public section

namespace TauCeti

open Finset

/-- A path from `(m, 0)` to `(0, m)` by steps up or left, through the two grids. It meets the
diagonal at `(l, l)` with `l = diagonalIndex`. Both halves are recorded as paths from `(0, m)` to
`(l, l)`: `half false` is the part after the diagonal read backwards, in the grid of the `Y`, where
`(a, b)` is `Y^a_b`, and `half true` is the part before the diagonal with the two indices
exchanged, in the grid of the `Y'`, where `(a, b)` is `Y'^b_a`. -/
structure TwoGridPath (m : ℕ) where
  /-- The index `l` of the node `(l, l)` at which the path meets the diagonal. -/
  diagonalIndex : ℕ
  /-- The halves in the two grids, each recorded as a path from `(0, m)` to the diagonal node. -/
  half : Bool → GridPath 0 m diagonalIndex diagonalIndex

namespace TwoGridPath

variable {m : ℕ} {Γ Γ' : TwoGridPath m} {s : ℕ × ℕ}

/-- The first path, through `(0, 0)`: it goes left from `Y'^m_0` to `Y'^0_0` and up from `Y^0_0` to
`Y^0_m`, so both halves are recorded as going down the first column. -/
@[expose] def first (m : ℕ) : TwoGridPath m := ⟨0, fun _ : Bool ↦ .column m.zero_le⟩

/-- The last path, through `(m, m)`: it goes up from `Y'^m_0` to `Y'^m_m` and left from `Y^m_m` to
`Y^0_m`, so both halves are recorded as going along the row `m`. -/
@[expose] def last (m : ℕ) : TwoGridPath m := ⟨m, fun _ : Bool ↦ .row m m⟩

/-- The first path meets the diagonal at `(0, 0)`. -/
@[simp]
theorem first_diagonalIndex : (first m).diagonalIndex = 0 := rfl

/-- Both halves of the first path go down the first column. -/
@[simp]
theorem first_half (z : Bool) : (first m).half z = .column m.zero_le := rfl

/-- The last path meets the diagonal at `(m, m)`. -/
@[simp]
theorem last_diagonalIndex : (last m).diagonalIndex = m := rfl

/-- Both halves of the last path go along the row `m`. -/
@[simp]
theorem last_half (z : Bool) : (last m).half z = .row m m := rfl

/-- `Turn Γ (i, j) Γ'`: the path `Γ` reaches `(i, j)` from the right and leaves it upwards, and `Γ'`
arises from `Γ` by replacing the node `(i, j)` by `(i + 1, j + 1)`. -/
inductive Turn : TwoGridPath m → ℕ × ℕ → TwoGridPath m → Prop
  /-- A turn off the diagonal, at a corner `(a, b)` where one half comes down and leaves to the
  right. For `half true` the node has the indices `(b, a)`. -/
  | inner (Γ : TwoGridPath m) (z : Bool) {a b : ℕ} (q : GridPath 0 m a (b + 1))
      (r : GridPath (a + 1) b Γ.diagonalIndex Γ.diagonalIndex)
      (hΓ : Γ.half z = q.down.right.append r) :
      Turn Γ (bif z then (b, a) else (a, b))
        ⟨Γ.diagonalIndex, Function.update Γ.half z (q.right.down.append r)⟩
  /-- A turn on the diagonal: both halves end with a step down. -/
  | diagonal {j : ℕ} (q : Bool → GridPath 0 m j (j + 1)) :
      Turn ⟨j, fun z : Bool ↦ (q z).down⟩ (j, j) ⟨j + 1, fun z : Bool ↦ (q z).right⟩

/-- The unit squares between the first path and `Γ`, each named by its corner with the least
indices: the `(i, j)` with `i, j < Γ.diagonalIndex`, the squares of `Γ.half false`, and the mirror
images in the diagonal of the squares of `Γ.half true`. -/
def squares (Γ : TwoGridPath m) : Finset (ℕ × ℕ) :=
  range Γ.diagonalIndex ×ˢ range Γ.diagonalIndex ∪ (Γ.half false).squares ∪
    (Γ.half true).squares.image Prod.swap

/-- The unit square with least corner `s` lies between the first path, through `(0, 0)`, and the
path `Γ` if and only if both indices of `s` are less than `Γ.diagonalIndex`, or `s` lies to the left
of a step down of `Γ.half false`, or its mirror image `s.swap` lies to the left of a step down of
`Γ.half true`. -/
theorem mem_squares : s ∈ Γ.squares ↔
    (s.1 < Γ.diagonalIndex ∧ s.2 < Γ.diagonalIndex) ∨
    s ∈ (Γ.half false).squares ∨
    s.swap ∈ (Γ.half true).squares := by
  grind [squares]

/-- A path from `(m, 0)` to `(0, m)` meets the diagonal at a node with indices at most `m`. -/
theorem diagonalIndex_le (Γ : TwoGridPath m) : Γ.diagonalIndex ≤ m := (Γ.half false).le_and_le.2

/-- Let `Γ` be a path from `(m, 0)` to `(0, m)` by steps up or left. The set `Γ.squares` of unit
squares between `Γ` and the path `first m` through `(0, 0)`, each named by its corner `(i, j)` with
the least indices, has only members with `i, j < m`. -/
theorem squares_subset (Γ : TwoGridPath m) : Γ.squares ⊆ range m ×ˢ range m := by
  rintro ⟨i, j⟩ hs
  suffices i < m ∧ j < m by simpa
  have hl : Γ.diagonalIndex ≤ m := Γ.diagonalIndex_le
  obtain ⟨hi : i < Γ.diagonalIndex, hj : j < Γ.diagonalIndex⟩ | h_false | h_true :=
    mem_squares.mp hs
  · omega
  · obtain ⟨hi : i < Γ.diagonalIndex, -, hj : j < m⟩ := GridPath.bounds_of_mem_squares h_false
    omega
  · obtain ⟨hj : j < Γ.diagonalIndex, -, hi : i < m⟩ := GridPath.bounds_of_mem_squares h_true
    omega

/-- No unit square lies between the first path, through `(0, 0)`, and itself. -/
@[simp]
theorem squares_first : (first m).squares = ∅ := by
  simp [squares]

/-- For the last path `last m`, the one through `(m, m)`, the set `(last m).squares` is exactly the
`(i, j)` with `i, j < m`, that is `range m ×ˢ range m`. -/
@[simp]
theorem squares_last : (last m).squares = range m ×ˢ range m := by
  simp [squares]

/-- Both halves of `Turn.notMem_squares` and `Turn.squares_eq`, proved together by cases on the
turn. -/
private theorem Turn.notMem_squares_and_squares_eq (h_turn : Γ.Turn s Γ') :
    s ∉ Γ.squares ∧ Γ'.squares = insert s Γ.squares := by
  cases h_turn with
  | @inner _ z a b q r hΓ =>
    obtain ⟨-, hb : Γ.diagonalIndex ≤ b⟩ := r.le_and_le
    have h_notMem : (a, b) ∉ (Γ.half z).squares := by
      simpa [hΓ] using GridPath.notMem_squares_down_right_append q r
    have h_notMem_swap (z' : Bool) : (b, a) ∉ (Γ.half z').squares := by
      grind
    have h_insert : (q.right.down.append r).squares = insert (a, b) (Γ.half z).squares := by
      rw [hΓ, GridPath.squares_right_down_append]
    constructor
    · cases z <;> simp [mem_squares, hb.not_gt, h_notMem, h_notMem_swap]
    · cases z <;> simp [squares, h_insert]
  | @diagonal j q =>
    have h_notMem (z : Bool) : (j, j) ∉ (q z).squares :=
      fun h_mem ↦ lt_irrefl j (GridPath.bounds_of_mem_squares h_mem).1
    have h_block : range (j + 1) ×ˢ range (j + 1) = insert (j, j)
        (range j ×ˢ range j ∪ range j ×ˢ {j} ∪ (range j ×ˢ {j}).image Prod.swap) := by
      rw [image_swap_product]
      grind
    refine ⟨by simp [mem_squares, h_notMem], ?_⟩
    simp only [squares, GridPath.squares_down, GridPath.squares_right, h_block, image_union,
      insert_union]
    ac_rfl

/-- Let `Γ` and `Γ'` be paths in `TwoGridPath m` with `Γ.Turn s Γ'`. Then the square `s` is not
among `Γ.squares`. -/
theorem Turn.notMem_squares (h_turn : Γ.Turn s Γ') : s ∉ Γ.squares :=
  h_turn.notMem_squares_and_squares_eq.1

/-- Let `Γ` and `Γ'` be paths in `TwoGridPath m` with `Γ.Turn s Γ'`. Then `Γ'.squares` is
`Γ.squares` with `s` inserted. -/
theorem Turn.squares_eq (h_turn : Γ.Turn s Γ') : Γ'.squares = insert s Γ.squares :=
  h_turn.notMem_squares_and_squares_eq.2

/-- If a path from `(m, 0)` to `(0, m)` has a turn at the node `s = (i, j)`, then `i, j < m`. -/
theorem Turn.mem_product (h_turn : Γ.Turn s Γ') : s ∈ range m ×ˢ range m :=
  Γ'.squares_subset (by simp [h_turn.squares_eq])

/-- A turn at a node `(i, j)` off the diagonal is an inner turn: in some half `z`, where the node
appears as `(i, j)` for `z = false` and as `(j, i)` for `z = true`, the half splits as a path `q`
to the node above the corner, a step down, a step right and a path `r` to the diagonal, and `Γ'`
has these two steps exchanged, with the same diagonal node and the same other half. -/
theorem Turn.exists_inner_of_ne {i j : ℕ} (h_turn : Γ.Turn (i, j) Γ') (hij : i ≠ j) :
    ∃ (z : Bool) (a b : ℕ) (q : GridPath 0 m a (b + 1))
      (r : GridPath (a + 1) b Γ.diagonalIndex Γ.diagonalIndex),
      (bif z then (b, a) else (a, b)) = (i, j) ∧
      Γ.half z = q.down.right.append r ∧
      Γ' = ⟨Γ.diagonalIndex, Function.update Γ.half z (q.right.down.append r)⟩ := by
  generalize hs : (i, j) = s at h_turn
  cases h_turn with
  | @inner _ z a b q r hΓ => exact ⟨z, a, b, q, r, rfl, hΓ, rfl⟩
  | diagonal q => grind

/-- Let `Γ'` arise from `Γ`, a path from `(m, 0)` to `(0, m)` by steps up or left, by replacing the
node `(i, j)` by `(i + 1, j + 1)`, where `i < j`. The turn takes place in `Γ.half false`, the part
of `Γ` after the diagonal node `(Γ.diagonalIndex, Γ.diagonalIndex)`, read backwards from `(0, m)`.
This half splits as a path `q` to `(i, j + 1)`, a step down, a step right and a path `r` to the
diagonal. The path `Γ'` has these two steps exchanged, and has the same diagonal node and the same
other half. -/
theorem Turn.exists_half_false_eq_of_lt {i j : ℕ} (h_turn : Γ.Turn (i, j) Γ') (hij : i < j) :
    ∃ (q : GridPath 0 m i (j + 1)) (r : GridPath (i + 1) j Γ.diagonalIndex Γ.diagonalIndex),
      Γ.half false = q.down.right.append r ∧
      Γ' = ⟨Γ.diagonalIndex, Function.update Γ.half false (q.right.down.append r)⟩ := by
  obtain ⟨z, a, b, q, r, hs, hΓ, rfl⟩ := h_turn.exists_inner_of_ne hij.ne
  have hab : a + 1 ≤ Γ.diagonalIndex ∧ Γ.diagonalIndex ≤ b := r.le_and_le
  cases z <;> cases hs
  · exact ⟨q, r, hΓ, rfl⟩
  · omega

/-- Let `Γ'` arise from `Γ`, a path from `(m, 0)` to `(0, m)` by steps up or left, by replacing the
node `(i, j)` by `(i + 1, j + 1)`, where `j < i`. The turn takes place in `Γ.half true`, the part
of `Γ` from `(m, 0)` to the diagonal node `(Γ.diagonalIndex, Γ.diagonalIndex)`, recorded with the
two indices exchanged, so that the node `(i, j)` appears as `(j, i)`. This half splits as a path
`q` to `(j, i + 1)`, a step down, a step right and a path `r` to the diagonal. The path `Γ'` has
these two steps exchanged, and has the same diagonal node and the same other half. -/
theorem Turn.exists_half_true_eq_of_gt {i j : ℕ} (h_turn : Γ.Turn (i, j) Γ') (hji : j < i) :
    ∃ (q : GridPath 0 m j (i + 1)) (r : GridPath (j + 1) i Γ.diagonalIndex Γ.diagonalIndex),
      Γ.half true = q.down.right.append r ∧
      Γ' = ⟨Γ.diagonalIndex, Function.update Γ.half true (q.right.down.append r)⟩ := by
  obtain ⟨z, a, b, q, r, hs, hΓ, rfl⟩ := h_turn.exists_inner_of_ne hji.ne'
  have hab : a + 1 ≤ Γ.diagonalIndex ∧ Γ.diagonalIndex ≤ b := r.le_and_le
  cases z <;> cases hs
  · omega
  · exact ⟨q, r, hΓ, rfl⟩

/-- A turn at `(j, j)` takes place on the diagonal: both halves reach `(j, j + 1)`, and their last
step, down to `(j, j)`, is replaced by the step right to `(j + 1, j + 1)`. -/
theorem Turn.exists_eq_down_and_eq_right {j : ℕ} (h_turn : Γ.Turn (j, j) Γ') :
    ∃ q : Bool → GridPath 0 m j (j + 1),
      Γ = ⟨j, fun z : Bool ↦ (q z).down⟩ ∧
      Γ' = ⟨j + 1, fun z : Bool ↦ (q z).right⟩ := by
  generalize hs : (j, j) = s at h_turn
  cases h_turn with
  | @inner _ z a b q r hΓ =>
    have hab : a + 1 ≤ Γ.diagonalIndex ∧ Γ.diagonalIndex ≤ b := r.le_and_le
    grind
  | diagonal q =>
    cases hs
    exact ⟨q, rfl, rfl⟩

/-- Every path `Γ` from `(m, 0)` to `(0, m)` by steps up or left, other than `last m`, has a
turn. -/
theorem exists_turn (hΓ : Γ ≠ last m) : ∃ (s : ℕ × ℕ) (Γ' : TwoGridPath m), Γ.Turn s Γ' := by
  by_cases h_corner : ∃ (z : Bool) (a b : ℕ) (q : GridPath 0 m a (b + 1))
      (r : GridPath (a + 1) b Γ.diagonalIndex Γ.diagonalIndex), Γ.half z = q.down.right.append r
  · obtain ⟨z, a, b, q, r, h_eq⟩ := h_corner
    exact ⟨_, _, .inner Γ z q r h_eq⟩
  obtain ⟨l, half⟩ := Γ
  obtain rfl | hl := eq_or_ne l m
  · obtain rfl : half = fun _ : Bool ↦ .row l l := funext fun z ↦ (half z).eq_row
    exact absurd rfl hΓ
  -- Without corners, and below the last row, both halves end with a step down.
  have h_down (z : Bool) : ∃ q : GridPath 0 m l (l + 1), half z = q.down := by
    obtain h_has_corner | h_ends_down | h_last_row := (half z).exists_corner_or_eq_down_or_eq
    · exact absurd ⟨z, h_has_corner⟩ h_corner
    · exact h_ends_down
    · exact absurd h_last_row hl
  choose q hq using h_down
  obtain rfl : half = fun z ↦ (q z).down := funext hq
  exact ⟨(l, l), ⟨l + 1, fun z ↦ (q z).right⟩, .diagonal q⟩

/-- Let a property of a path and a finite set of index pairs hold for the last path, through
`(m, m)`, and the empty set. Suppose that for each turn at `s` from `Γ` to `Γ'` and each set `T`
without `s`, it passes from `Γ'` and `T` to `Γ` and `insert s T`. Then it holds for the first path,
through `(0, 0)`, and the set of all `(i, j)` with `i, j < m`. -/
theorem turn_induction {motive : TwoGridPath m → Finset (ℕ × ℕ) → Prop} (h_last : motive (last m) ∅)
    (h_turn : ∀ (Γ : TwoGridPath m) (s : ℕ × ℕ) (Γ' : TwoGridPath m) (T : Finset (ℕ × ℕ)),
      Γ.Turn s Γ' → s ∉ T → motive Γ' T → motive Γ (insert s T)) :
    motive (first m) (range m ×ˢ range m) := by
  -- Induction on the number of squares between `Γ` and the last path.
  suffices h_above_path : ∀ (k : ℕ) (Γ : TwoGridPath m),
      #(range m ×ˢ range m \ Γ.squares) = k → motive Γ (range m ×ˢ range m \ Γ.squares) by
    simpa using h_above_path _ (first m) rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro Γ hk
    obtain rfl | h_ne := eq_or_ne Γ (last m)
    · simpa using h_last
    obtain ⟨s, Γ', hΓΓ' : Γ.Turn s Γ'⟩ := exists_turn h_ne
    have hs : s ∉ Γ.squares := hΓΓ'.notMem_squares
    have h_eq : Γ'.squares = insert s Γ.squares := hΓΓ'.squares_eq
    have h_new : s ∉ range m ×ˢ range m \ Γ'.squares := by simp [h_eq]
    have h_above : range m ×ˢ range m \ Γ.squares =
        insert s (range m ×ˢ range m \ Γ'.squares) := by
      rw [h_eq, sdiff_insert, insert_erase (mem_sdiff.mpr ⟨hΓΓ'.mem_product, hs⟩)]
    rw [h_above] at hk ⊢
    exact h_turn Γ s Γ' _ hΓΓ' h_new (ih _ (by simp [← hk, h_new]) Γ' rfl)

end TwoGridPath

end TauCeti
