/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Fin.Rev

/-!
# Reversal on `Fin`

On `Fin 2` the reversal `Fin.rev` exchanges the two elements, so every index is either a given
index or its reverse: `Fin.fin_two_eq_or_eq_rev`. This is how the two branches of an edge of a
graph, indexed by `Fin 2`, are told apart.

On `Fin (n + 1)` the reversal is `j ↦ n - j`, so a condition on the indices `j` and `n - j` can be
restated over the natural numbers `m ≤ n` with `m = n - j`: `Fin.forall_imp_sub_iff_forall_le`.

`Fin.neg_one_pow_rev_add_rev_add_one` shows that reversing both indices preserves the sign
`(-1) ^ (i + j + 1)`. This is the parity identity used by signed graph automorphisms.
-/

public section

namespace Fin

/-- An index of `Fin 2` is either a given index or its reverse. -/
theorem fin_two_eq_or_eq_rev (i j : Fin 2) : j = i ∨ j = i.rev := by
  revert i j
  decide

/-- Reindex a condition on the indices `j : Fin (n + 1)` and their reversals `n - j` by the
natural numbers `m = n - j ≤ n`. -/
theorem forall_imp_sub_iff_forall_le {n : ℕ} {p q : ℕ → Prop} :
    (∀ j : Fin (n + 1), p j → q (n - j)) ↔ ∀ m ≤ n, p (n - m) → q m := by
  refine ⟨fun h m hm hp ↦ ?_, fun h j hp ↦ h _ (Nat.sub_le n j) ?_⟩
  · simpa [Nat.sub_sub_self hm] using h ⟨n - m, by omega⟩ hp
  · rwa [Nat.sub_sub_self (Nat.lt_succ_iff.1 j.2)]

/-- Reversing both indices of a pair in `Fin n` preserves the parity of their sum, so the sign
`(-1) ^ (i + j + 1)` attached to a root `ε_i - ε_j` is unchanged by the reversal. -/
theorem neg_one_pow_rev_add_rev_add_one {M : Type*} [Monoid M] [HasDistribNeg M] {n : ℕ}
    (i j : Fin n) :
    (-1 : M) ^ ((j.rev : ℕ) + (i.rev : ℕ) + 1) = (-1) ^ ((i : ℕ) + (j : ℕ) + 1) :=
  neg_one_pow_congr (by simp only [Nat.even_iff, Fin.val_rev]; omega)

end Fin
