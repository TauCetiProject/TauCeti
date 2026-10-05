/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.Range

/-!
# Mapping along a reversed range

Lists of the form `[f (b - 1), …, f 0]`, that is `(List.range b).reverse.map f`, record
coefficient sequences from the top index down. This file peels off the top entry and collapses a
run of vanishing entries at the top into a block of zeros.

## Main results

* `List.map_reverse_range_succ`: the list `[f k, …, f 0]` begins with `f k`.
* `List.map_reverse_range_eq_replicate_append`: if `f` vanishes on `[a, b)`, then
  `[f (b - 1), …, f 0]` is `b - a` zeros followed by `[f (a - 1), …, f 0]`.
-/

public section

namespace TauCeti

/-- The list `[f k, …, f 0]` begins with `f k`. -/
theorem _root_.List.map_reverse_range_succ {α : Type*} (f : ℕ → α) (k : ℕ) :
    (List.range (k + 1)).reverse.map f = f k :: (List.range k).reverse.map f := by
  simp [List.range_succ]

/-- Mapping a function along the reversed range `[b - 1, …, 0]`, where it vanishes on
`[a, b)`, gives `b - a` zeros followed by the map along `[a - 1, …, 0]`. -/
theorem _root_.List.map_reverse_range_eq_replicate_append {α : Type*} [Zero α] (f : ℕ → α)
    {a b : ℕ} (hab : a ≤ b) (h : ∀ j, a ≤ j → j < b → f j = 0) :
    (List.range b).reverse.map f = List.replicate (b - a) 0 ++ (List.range a).reverse.map f := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    have hlen : b + 1 - a = (b - a) + 1 := by omega
    rw [List.map_reverse_range_succ, h b hab (by omega), ih fun j h1 h2 => h j h1 (by omega),
      hlen, List.replicate_succ, List.cons_append]

end TauCeti
