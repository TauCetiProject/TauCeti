/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.Zip

/-!
# Differences of consecutive entries of a list

The entries of the differences of consecutive entries of a list, closed up by an extra entry `b`,
are described by `List.getElem_zipWith_sub_tail_append_singleton`.
-/

public section

namespace List

/-- The entry at `i` of the differences of consecutive entries of `l`, closed up by `b`, is the
difference from `l[i]` to the next entry of `l`, or to `b` at the last index. -/
theorem getElem_zipWith_sub_tail_append_singleton {G : Type*} [Sub G] {b : G} {l : List G}
    {i : ℕ} (hi : i < (zipWith (· - ·) (l.tail ++ [b]) l).length) :
    (zipWith (· - ·) (l.tail ++ [b]) l)[i] =
      (if h : i + 1 < l.length then l[i + 1] else b) - l[i]'(by simp at hi; omega) := by
  rw [getElem_zipWith]
  split_ifs with h
  · rw [getElem_append_left (by simp; omega), getElem_tail]
  · rw [getElem_append_right (by simp; omega)]
    simp

end List
