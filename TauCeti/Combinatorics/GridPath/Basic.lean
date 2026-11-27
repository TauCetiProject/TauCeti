/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Nat.Init
import Mathlib.Order.Interval.Finset.Nat

/-!
# Monotone paths in a grid

A *grid path* from the node `(a₀, b₀)` to the node `(a, b)` of `ℕ × ℕ` is a sequence of steps,
each of which either lowers the second index by one (a step *down*) or raises the first index by
one (a step *right*) (`TauCeti.GridPath`). It is an inductive family indexed by its end node, built
by appending steps. To a path is attached the finite set of unit squares between it and the first
column (`TauCeti.GridPath.squares`): the step down from `(a, b + 1)` to `(a, b)` contributes the
squares `(i, b)` with `i < a`, each square named by its corner with the least indices.

The main facts concern corners. A path either has a corner, where it comes down and leaves to the
right, or ends with a step down, or has no step down at all
(`TauCeti.GridPath.exists_corner_or_eq_down_or_eq`). Replacing a corner at `(i, j)`, that is the
steps `(i, j + 1) → (i, j) → (i + 1, j)`, by the steps `(i, j + 1) → (i + 1, j + 1) → (i + 1, j)`
adds exactly the square `(i, j)` (`TauCeti.GridPath.squares_right_down_append`,
`TauCeti.GridPath.notMem_squares_down_right_append`).

These paths index the theta lifts moved through a grid of unitary groups; the paths through two
grids and their turns are in `TauCeti.Combinatorics.GridPath.TwoGrid`.

## Main declarations

* `TauCeti.GridPath`: monotone grid paths; `TauCeti.GridPath.append`, `TauCeti.GridPath.column`,
  `TauCeti.GridPath.row`.
* `TauCeti.GridPath.squares`: the squares to the left of the steps down.
* `TauCeti.GridPath.exists_corner_or_eq_down_or_eq`: the trichotomy of corners.

## References

* Adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026
  Anthropic, PBC), `src/New/Determinant/AuxiliaryForms/GridPaths.lean`, `New.GridPath`.
-/

public section

namespace TauCeti

open Finset

/-- A monotone path in a grid from the node `(a₀, b₀)` to the node `(a, b)`: each step lowers the
second index or raises the first. -/
inductive GridPath (a₀ b₀ : ℕ) : ℕ → ℕ → Type
  /-- The path without steps. -/
  | nil : GridPath a₀ b₀ a₀ b₀
  /-- A path followed by the step from `(a, b + 1)` to `(a, b)`. -/
  | down {a b : ℕ} (p : GridPath a₀ b₀ a (b + 1)) : GridPath a₀ b₀ a b
  /-- A path followed by the step from `(a, b)` to `(a + 1, b)`. -/
  | right {a b : ℕ} (p : GridPath a₀ b₀ a b) : GridPath a₀ b₀ (a + 1) b

namespace GridPath

variable {a₀ b₀ a b a' b' a'' b'' m : ℕ}

/-- One path followed by another. -/
def append (p : GridPath a₀ b₀ a b) : ∀ {a' b' : ℕ}, GridPath a b a' b' → GridPath a₀ b₀ a' b'
  | _, _, nil => p
  | _, _, down q => (p.append q).down
  | _, _, right q => (p.append q).right

/-- A path followed by the path without steps is itself. -/
@[simp]
theorem append_nil (p : GridPath a₀ b₀ a b) : p.append nil = p := (rfl)

/-- Appending a path that ends with a step down appends the path, then the step down. -/
@[simp]
theorem append_down (p : GridPath a₀ b₀ a b) (q : GridPath a b a' (b' + 1)) :
    p.append q.down = (p.append q).down := (rfl)

/-- Appending a path that ends with a step right appends the path, then the step right. -/
@[simp]
theorem append_right (p : GridPath a₀ b₀ a b) (q : GridPath a b a' b') :
    p.append q.right = (p.append q).right := (rfl)

/-- The path without steps followed by a path is that path. -/
@[simp]
theorem nil_append (p : GridPath a₀ b₀ a b) : nil.append p = p := by
  induction p <;> simp [*]

/-- Appending paths is associative. -/
@[simp]
theorem append_assoc (p : GridPath a₀ b₀ a b) (q : GridPath a b a' b')
    (r : GridPath a' b' a'' b'') : (p.append q).append r = p.append (q.append r) := by
  induction r <;> simp [*]

/-- The path down the first column, from `(0, m)` to `(0, b)`. -/
def column (hb : b ≤ m) : GridPath 0 m 0 b :=
  Nat.decreasingInduction (motive := fun b _ ↦ GridPath 0 m 0 b) (fun _ _ p ↦ p.down) nil hb

/-- The path along the row `m`, from `(0, m)` to `(a, m)`. -/
def row (m : ℕ) : ∀ a : ℕ, GridPath 0 m a m
  | 0 => nil
  | a + 1 => (row m a).right

/-- The path along the row `m` to `(0, m)` has no steps. -/
@[simp]
theorem row_zero (m : ℕ) : row m 0 = nil := (rfl)

/-- The path along the row `m` to `(a + 1, m)` is the one to `(a, m)` followed by a step right. -/
@[simp]
theorem row_succ (m a : ℕ) : row m (a + 1) = (row m a).right := (rfl)

/-- The unit squares between the first column and the steps down of a path, each named by its
corner with the least indices: the step from `(a, b + 1)` to `(a, b)` contributes the `(i, b)` with
`i < a`. -/
def squares : ∀ {a b : ℕ}, GridPath a₀ b₀ a b → Finset (ℕ × ℕ)
  | _, _, nil => ∅
  | a, b, down p => p.squares ∪ range a ×ˢ {b}
  | _, _, right p => p.squares

/-- The path without steps has no squares. -/
@[simp]
theorem squares_nil : (nil : GridPath a₀ b₀ a₀ b₀).squares = ∅ := by
  simp [squares]

/-- A step down from `(a, b + 1)` to `(a, b)` adds the squares `(i, b)` with `i < a`. -/
@[simp]
theorem squares_down (p : GridPath a₀ b₀ a (b + 1)) :
    p.down.squares = p.squares ∪ range a ×ˢ {b} := by
  simp [squares]

/-- A step right adds no squares. -/
@[simp]
theorem squares_right (p : GridPath a₀ b₀ a b) : p.right.squares = p.squares := by
  simp [squares]

/-- The path down the first column from `(0, m)` to itself has no steps. -/
@[simp]
theorem column_self : column (le_refl m) = nil := by
  rw [column, Nat.decreasingInduction_self]

/-- The path down the first column from `(0, m)` to `(0, b)`, for `b < m`, is the one to
`(0, b + 1)` followed by a step down. -/
theorem column_of_lt (hb : b < m) : column hb.le = (column hb).down := by
  rw [column, column, Nat.decreasingInduction_succ_left (smn := hb)]

/-- Along a path from `(a₀, b₀)` to `(a, b)` the first index does not fall and the second does
not grow. -/
theorem le_and_le (p : GridPath a₀ b₀ a b) : a₀ ≤ a ∧ b ≤ b₀ := by
  induction p <;> omega

/-- The only path from `(0, m)` to `(a, m)` is `row m a`, the one that stays in the row `m`. -/
theorem eq_row (p : GridPath 0 m a m) : p = row m a := by
  have h_no_down {k : ℕ} (q : GridPath 0 m k (m + 1)) : False := by grind [q.le_and_le]
  induction a with
  | zero =>
    cases p with
    | nil => rfl
    | down q => exact (h_no_down q).elim
  | succ a ih =>
    cases p with
    | down q => exact (h_no_down q).elim
    | right q => rw [row, ih q]

/-- The squares to the left of the steps down of `p` followed by `q` are those of `p` and those
of `q`. -/
@[simp]
theorem squares_append (p : GridPath a₀ b₀ a b) (q : GridPath a b a' b') :
    (p.append q).squares = p.squares ∪ q.squares := by
  induction q <;> simp [append, squares, *]

/-- A square `s` to the left of a step down of a path from `(a₀, b₀)` to `(a, b)` lies to the left
of the column `a` and between the rows `b` and `b₀`. -/
@[grind →]
theorem bounds_of_mem_squares {p : GridPath a₀ b₀ a b} {s : ℕ × ℕ} (hs : s ∈ p.squares) :
    s.1 < a ∧ b ≤ s.2 ∧ s.2 < b₀ := by
  induction p with
  | nil => simp [squares] at hs
  | down p ih => grind [squares, p.le_and_le]
  | right p ih => grind [squares]

/-- The path along a row has no step down, hence no squares. -/
@[simp]
theorem squares_row (m a : ℕ) : (row m a).squares = ∅ := by
  induction a <;> simp [*]

/-- The path down the first column has no square to the left of its steps down. -/
@[simp]
theorem squares_column (hb : b ≤ m) : (column hb).squares = ∅ := by
  induction hb using Nat.decreasingInduction with
  | self => simp
  | of_succ b hb ih => simp [column_of_lt hb, ih]

/-- Let a path follow `q` to `(i, j + 1)`, step down to `(i, j)`, step right to `(i + 1, j)` and
follow `r`. Then the unit square with lower left corner `(i, j)` is not among the `squares` of the
path, the unit squares to the left of its steps down. -/
theorem notMem_squares_down_right_append {i j : ℕ} (q : GridPath a₀ b₀ i (j + 1))
    (r : GridPath (i + 1) j a b) : (i, j) ∉ (q.down.right.append r).squares := by
  have hq : (i, j) ∉ q.squares := by grind
  have hr : (i, j) ∉ r.squares := by grind
  simp [squares_append, squares, hq, hr]

/-- Let a path follow `q` to `(i, j + 1)`, go to `(i + 1, j)` in two steps and follow `r`. If it
passes through `(i + 1, j + 1)` instead of `(i, j)`, then its set of `squares`, the unit squares to
the left of its steps down, gains the square with lower left corner `(i, j)`. -/
theorem squares_right_down_append {i j : ℕ} (q : GridPath a₀ b₀ i (j + 1))
    (r : GridPath (i + 1) j a b) :
    (q.right.down.append r).squares = insert (i, j) (q.down.right.append r).squares := by
  have h_strip : range (i + 1) ×ˢ {j} = insert (i, j) (range i ×ˢ {j}) := by grind
  simp [squares_append, squares, h_strip]

/-- A path from `(a₀, b₀)` to `(a, b)` has a corner `(i, j)`, where it comes down and leaves to the
right, or ends with a step down, or has no step down (`b = b₀`). -/
theorem exists_corner_or_eq_down_or_eq (p : GridPath a₀ b₀ a b) :
    (∃ (i j : ℕ) (q : GridPath a₀ b₀ i (j + 1)) (r : GridPath (i + 1) j a b),
      p = q.down.right.append r) ∨
    (∃ q : GridPath a₀ b₀ a (b + 1), p = q.down) ∨
    b = b₀ := by
  induction p with
  | nil => exact .inr (.inr rfl)
  | down p _ => exact .inr (.inl ⟨p, rfl⟩)
  | @right a b p ih =>
    obtain ⟨i, j, q, r, rfl⟩ | ⟨q, rfl⟩ | hb := ih
    · exact .inl ⟨i, j, q, r.right, rfl⟩
    · exact .inl ⟨a, b, q, nil, rfl⟩
    · exact .inr (.inr hb)

end GridPath

end TauCeti
