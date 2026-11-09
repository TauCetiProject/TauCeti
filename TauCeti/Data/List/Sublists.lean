/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.Sublists

/-!
# Complementary pairs of sublists

`l.sublists'.revzip` lists the `2 ^ l.length` pairs of complementary sublists of `l`, the ways of
distributing the entries of `l` between two lists while keeping their relative order (Mathlib's
`List.revzip_sublists'`). These pairs index the terms of the general Leibniz rule: the iterated
derivative of a product along a word of directions is the sum, over these pairs, of the product of
the derivatives of the two factors along the two parts.

This file records how the pairs of `a :: l` arise from those of `l`, the recursion behind inductive
proofs over them.
-/

public section

namespace List

variable {α : Type*}

/-- The complementary pairs of sublists of `a :: l`: those with `a` in the second part, followed
by those with `a` in the first part. -/
theorem revzip_sublists'_cons (a : α) (l : List α) :
    (a :: l).sublists'.revzip =
      l.sublists'.revzip.map (Prod.map id (cons a)) ++
        l.sublists'.revzip.map (Prod.map (cons a) id) := by
  rw [revzip, sublists'_cons, reverse_append, ← map_reverse,
    zip_append (by simp), zip_map_right, zip_map_left, revzip]

end List
