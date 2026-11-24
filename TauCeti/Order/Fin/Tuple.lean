/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Order.PiLex

/-!
# Order properties on tuples

This file complements `Mathlib.Order.Fin.Tuple` with the `Fin.snoc` analogue of
`Fin.pi_lex_lt_cons_cons`: comparing two appended dependent tuples lexicographically compares
their prefixes first, and compares their last entries when the prefixes are equal.
-/

public section

namespace Fin

/-- Lexicographic comparison of `Fin.snoc` compares the initial tuples first and compares
the last entries when the initial tuples are equal. -/
theorem pi_lex_lt_snoc_snoc {n : ℕ} {α : Fin (n + 1) → Type*}
    {x y : ∀ i : Fin n, α i.castSucc} {xₙ yₙ : α (Fin.last n)}
    (s : ∀ {i : Fin (n + 1)}, α i → α i → Prop) :
    Pi.Lex (· < ·) (@s) (Fin.snoc x xₙ) (Fin.snoc y yₙ) ↔
      Pi.Lex (· < ·) (@fun i : Fin n ↦ @s i.castSucc) x y ∨ x = y ∧ s xₙ yₙ := by
  -- Modelled on Mathlib's `Fin.pi_lex_lt_cons_cons`, splitting the quantifiers of the
  -- lexicographic order at the last index instead of the first.
  simp only [Pi.Lex, Fin.exists_fin_succ', Fin.forall_fin_succ', Fin.snoc_castSucc, Fin.snoc_last,
    Fin.castSucc_lt_castSucc_iff, Fin.castSucc_lt_last, (Fin.castSucc_lt_last _).not_gt,
    lt_self_iff_false, funext_iff, false_imp_iff, true_imp_iff, and_true]

end Fin
