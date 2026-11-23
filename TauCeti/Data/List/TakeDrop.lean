/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.Basic
public import Mathlib.Logic.Function.Iterate

/-!
# Prefix-mapping length and two-stack list-iteration steps

This file provides reusable helpers for transforming prefixes of lists:

* `List.length_map_take_append_drop`: mapping over `l.take d` while preserving `l.drop d` keeps
  the length `l.length`.
* `List.splitStep` and `List.splitStep_iterate`: iterating the one-step prefix-splitting
  transition `d` times moves `l.take d` (mapped by `f` and reversed) onto the accumulator list,
  leaving `l.drop d`.
* `List.reverseStep`, `List.reverseStep_iterate`, and `List.reverseStep_iterate_of_length_le`:
  iterating the one-step transfer transition `d` times moves `rl.take d` (reversed) onto the
  target list, leaving `rl.drop d` (and emptying `rl` when `rl.length ≤ d`).
-/

public section

namespace List

variable {α β : Type*}

/-- Mapping over the prefix `l.take d` while keeping the remaining suffix `l.drop d` preserves
the length of `l`. -/
theorem length_map_take_append_drop (f : α → α) (d : ℕ) (l : List α) :
    ((l.take d).map f ++ l.drop d).length = l.length := by
  simp
  omega

/-- One-step prefix-splitting transition on `(rl, l)`: moves the head of `l` onto `rl` after
applying `f`, leaving `(rl, [])` unchanged. -/
def splitStep (f : α → β) : List β × List α → List β × List α
  | (rl, []) => (rl, [])
  | (rl, a :: l) => (f a :: rl, l)

/-- `splitStep f` leaves `(rl, [])` unchanged. -/
@[simp]
theorem splitStep_nil (f : α → β) (rl : List β) : splitStep f (rl, []) = (rl, []) := (rfl)

/-- `splitStep f` moves the head `a` of `a :: l` onto `rl` as `f a`. -/
@[simp]
theorem splitStep_cons (f : α → β) (rl : List β) (a : α) (l : List α) :
    splitStep f (rl, a :: l) = (f a :: rl, l) := (rfl)

/-- Iterating `splitStep f` `d` times from `(rl, l)` moves `(l.take d).map f` reversed onto
`rl` and leaves `l.drop d`. -/
theorem splitStep_iterate (f : α → β) (d : ℕ) (rl : List β) (l : List α) :
    (splitStep f)^[d] (rl, l) = (((l.take d).map f).reverseAux rl, l.drop d) := by
  induction d generalizing rl l with
  | zero => simp
  | succ d ih =>
    cases l with
    | nil =>
      rw [Function.iterate_succ_apply, splitStep_nil]
      simpa using ih rl []
    | cons a l' =>
      rw [Function.iterate_succ_apply, splitStep_cons, ih]
      simp [take_succ_cons]

/-- One-step list-transfer transition on `(rl, l)`: moves the head of `rl` onto `l`, leaving
`([], l)` unchanged. -/
def reverseStep : List α × List α → List α × List α
  | ([], l) => ([], l)
  | (b :: rl, l) => (rl, b :: l)

/-- `reverseStep` leaves `([], l)` unchanged. -/
@[simp]
theorem reverseStep_nil (l : List α) : reverseStep ([], l) = ([], l) := (rfl)

/-- `reverseStep` moves the head `b` of `b :: rl` onto `l`. -/
@[simp]
theorem reverseStep_cons (b : α) (rl l : List α) :
    reverseStep (b :: rl, l) = (rl, b :: l) := (rfl)

/-- Iterating `reverseStep` `d` times from `(rl, l)` moves `rl.take d` reversed onto `l` and
leaves `rl.drop d`. -/
theorem reverseStep_iterate (d : ℕ) (rl l : List α) :
    reverseStep^[d] (rl, l) = (rl.drop d, (rl.take d).reverseAux l) := by
  induction d generalizing rl l with
  | zero => simp
  | succ d ih =>
    cases rl with
    | nil =>
      rw [Function.iterate_succ_apply, reverseStep_nil]
      simpa using ih [] l
    | cons b rl' =>
      rw [Function.iterate_succ_apply, reverseStep_cons, ih]
      simp [take_succ_cons]

/-- Iterating `reverseStep` at least `rl.length` times from `(rl, l)` empties `rl` into
`rl.reverseAux l`. -/
theorem reverseStep_iterate_of_length_le {d : ℕ} {rl : List α} (hd : rl.length ≤ d) (l : List α) :
    reverseStep^[d] (rl, l) = ([], rl.reverseAux l) := by
  rw [reverseStep_iterate, drop_eq_nil_of_le hd, take_of_length_le hd]

end List
