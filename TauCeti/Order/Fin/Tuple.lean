/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Order.Fin.Tuple
public import Mathlib.Order.PiLex

/-!
# Order properties on tuples

This file complements `Mathlib.Order.Fin.Tuple` with results on `Fin.snoc`.

## Main results

* `Fin.pi_lex_lt_snoc_snoc`: the `Fin.snoc` analogue of `Fin.pi_lex_lt_cons_cons`: comparing two
  appended dependent tuples lexicographically compares their prefixes first, and compares their
  last entries when the prefixes are equal.
* `OrderEmbedding.snoc`: an increasing tuple `s : Fin n ↪o α` extended by a point above all of its
  entries, the increasing-tuple form of `Fin.snoc`.
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

namespace OrderEmbedding

variable {α : Type*} [Preorder α] {n : ℕ}

/-- The increasing tuple `s` extended by a point `a` lying above all of its entries: the
increasing-tuple form of `Fin.snoc`. -/
def snoc (s : Fin n ↪o α) (a : α) (h : ∀ k, s k < a) : Fin (n + 1) ↪o α :=
  .ofStrictMono (Fin.snoc s a) <| by
    simpa [Fin.insertNth_last'] using
      (Fin.strictMono_insertNth_iff (Fin.last n) a s).2 ⟨s.strictMono, fun k _ ↦ h k,
        fun k hk ↦ absurd hk (Fin.castSucc_lt_last k).not_ge⟩

@[simp]
theorem coe_snoc (s : Fin n ↪o α) (a : α) (h : ∀ k, s k < a) :
    ⇑(s.snoc a h) = Fin.snoc s a :=
  (rfl)

@[simp]
theorem snoc_castSucc (s : Fin n ↪o α) (a : α) (h : ∀ k, s k < a) (k : Fin n) :
    s.snoc a h k.castSucc = s k := by
  simp

@[simp]
theorem snoc_last (s : Fin n ↪o α) (a : α) (h : ∀ k, s k < a) : s.snoc a h (Fin.last n) = a := by
  simp

end OrderEmbedding
