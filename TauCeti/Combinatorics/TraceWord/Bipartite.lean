/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.TraceWord.Counting
public import Mathlib.Data.Finset.Sum
public import TauCeti.Data.Fin.Sum

/-!
# Bipartite trace words

For rectangular matrices `A : Matrix α β R` and `B : Matrix β α R`, the trace of `(A * B) ^ k`
expands over pairs of sequences `i : Fin k → α` and `j : Fin k → β`
(`Matrix.trace_mul_pow_eq_sum_prod`). Such a pair is the closed walk

`i 0 → j 0 → i 1 → j 1 → ⋯ → i (k - 1) → j (k - 1) → i 0`

of length `2 * k` on the disjoint union `α ⊕ β`, alternating between the two sides. This file
builds that cyclic word, `TauCeti.bipartiteWord i j : Fin (2 * k) → α ⊕ β`, so that the vertex and
edge counts of cyclic trace words in `TauCeti.Combinatorics.TraceWord.Counting` apply to the moments
of sample covariance matrices `X Xᴴ / n`.

The step `i t → j t` of the word has the unordered edge `s(inl (i t), inr (j t))` and the step
`j t → i (t + 1)` has the edge `s(inl (i (t + 1)), inr (j t))`. Edges between the two sides are in
bijection with matrix positions `(a, b) : α × β`, so the step `i t → j t` reads the entry at
`(i t, j t)` and the step `j t → i (t + 1)` reads the entry at `(i (t + 1), j t)`. A bipartite word
in which no edge is traversed exactly once visits at most `k + 1` vertices: the rows and columns it
uses number at most `k + 1` in total.

The word is indexed through the interleaving `TauCeti.finSumFinInterleaveEquiv` of
`TauCeti.Data.Fin.Sum`, which places `i` at the even positions and `j` at the odd positions.

## Main declarations

* `TauCeti.bipartiteWord`: the alternating cyclic word of a pair of sequences.
* `TauCeti.card_image_bipartiteWord`: it visits `#(image i) + #(image j)` vertices.
* `TauCeti.card_image_add_card_image_le_of_no_singleton_edge`: with no singleton edge, at most
  `k + 1` vertices.

## References

* Z. Bai and J. Silverstein, *Spectral Analysis of Large Dimensional Random Matrices*, second
  edition, Springer (2010), §3.1.2: the graphs of the moment method for sample covariance
  matrices.
-/

public section

open Finset

namespace TauCeti

variable {α β : Type*} {k : ℕ}

/-- The closed walk `i 0 → j 0 → i 1 → j 1 → ⋯ → i (k - 1) → j (k - 1) → i 0` on `α ⊕ β`, as a
cyclic word of length `2 * k`: its even positions visit `i` and its odd positions visit `j`. -/
def bipartiteWord (i : Fin k → α) (j : Fin k → β) (s : Fin (2 * k)) : α ⊕ β :=
  Sum.map i j ((finSumFinInterleaveEquiv k).symm s)

@[simp]
theorem bipartiteWord_inl (i : Fin k → α) (j : Fin k → β) (t : Fin k) :
    bipartiteWord i j (finSumFinInterleaveEquiv k (.inl t)) = .inl (i t) := by
  simp [bipartiteWord]

@[simp]
theorem bipartiteWord_inr (i : Fin k → α) (j : Fin k → β) (t : Fin k) :
    bipartiteWord i j (finSumFinInterleaveEquiv k (.inr t)) = .inr (j t) := by
  simp [bipartiteWord]

variable [DecidableEq α] [DecidableEq β]

/-- A bipartite word visits `#(image i) + #(image j)` vertices: the rows of `i` and the columns
of `j`, which lie on different sides of `α ⊕ β`. -/
theorem card_image_bipartiteWord (i : Fin k → α) (j : Fin k → β) :
    #(univ.image (bipartiteWord i j)) = #(univ.image i) + #(univ.image j) := by
  rw [← card_disjSum]
  congr 1
  ext (a | b) <;>
    simp [(finSumFinInterleaveEquiv k).surjective.exists, bipartiteWord]

/-- A bipartite word of length `2 * k` in which no unordered edge is traversed exactly once uses
at most `k + 1` rows and columns in total. -/
theorem card_image_add_card_image_le_of_no_singleton_edge {i : Fin k → α} {j : Fin k → β}
    (h : ∀ s, ∃ s' ≠ s, s(bipartiteWord i j s', bipartiteWord i j (finRotate (2 * k) s')) =
      s(bipartiteWord i j s, bipartiteWord i j (finRotate (2 * k) s))) :
    #(univ.image i) + #(univ.image j) ≤ k + 1 := by
  rw [← card_image_bipartiteWord]
  simpa using card_image_le_div_two_add_one_of_no_singleton_edge _ h

end TauCeti
