/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.Fin
public import Mathlib.Data.Finsupp.Lex
public import Mathlib.Order.Fin.Tuple

/-!
# Addition and lexicographic comparison of `Finsupp.cons`

`Finsupp.cons x s : Fin (n + 1) →₀ M` puts `x` in front of `s`. Adding two of them adds heads and
tails separately. The lexicographic order compares the entries at `0` first, so two of them are
compared by their heads, and then by their tails.
-/

public section

namespace Finsupp

variable {n : ℕ} {M : Type*}

theorem cons_add_cons [AddZeroClass M] (x y : M) (s t : Fin n →₀ M) :
    cons x s + cons y t = cons (x + y) (s + t) := by
  ext i
  cases i using Fin.cases <;> simp

/-- Strict lexicographic comparison of `Finsupp.cons` compares the heads first and compares
the tails when the heads are equal. -/
theorem toLex_cons_lt_toLex_cons_iff [Zero M] [LT M] {x y : M} {s t : Fin n →₀ M} :
    toLex (cons x s) < toLex (cons y t) ↔ x < y ∨ x = y ∧ toLex s < toLex t := by
  simp only [Lex.lt_iff, ofLex_toLex]
  exact Fin.pi_lex_lt_cons_cons (α := fun _ ↦ M) (s := fun {_} ↦ (· < ·))

end Finsupp
