/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Fin.Rev
public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Abel

/-!
# Reversal on `Fin`

On `Fin 2` the reversal `Fin.rev` exchanges the two elements, so every index is either a given
index or its reverse: `Fin.fin_two_eq_or_eq_rev`. This is how the two branches of an edge of a
graph, indexed by `Fin 2`, are told apart.

On `Fin (n + 1)` the reversal is `j ↦ n - j`, so a condition on the indices `j` and `n - j` can be
restated over the natural numbers `m ≤ n` with `m = n - j`: `Fin.forall_imp_sub_iff_forall_le`.

Cast into an additive commutative group with one, the reversal of `i : Fin n` is `n - 1 - i`:
`Fin.natCast_val_rev`.

`Fin.neg_one_pow_rev_add_rev_add_one` shows that reversing both indices preserves the sign
`(-1) ^ (i + j + 1)`. This is the parity identity used by signed graph automorphisms.
`Fin.neg_one_pow_val_rev_mul` compares the signs `(-1) ^ j` and `(-1) ^ (n - j)` with the
reversal signs `(-1) ^ n.choose 2` and `(-1) ^ (n + 1).choose 2`, as needed to commute a
reversal of vertices with a simplicial differential.
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
  · rwa [Nat.sub_sub_self (Nat.lt_succ_iff.1 j.isLt)]

/-- Cast to an additive commutative group with one, the reversal of `i : Fin n` is `n - 1 - i`,
without the truncated subtraction of `Fin.val_rev`. -/
theorem natCast_val_rev {R : Type*} [AddCommGroupWithOne R] {n : ℕ} (i : Fin n) :
    ((i.rev : ℕ) : R) = n - 1 - i := by
  rw [Fin.val_rev, Nat.cast_sub i.isLt]
  push_cast
  abel

/-- Reversing both indices of a pair in `Fin n` preserves the parity of their sum, so the sign
`(-1) ^ (i + j + 1)` attached to a root `ε_i - ε_j` is unchanged by the reversal. -/
theorem neg_one_pow_rev_add_rev_add_one {M : Type*} [Monoid M] [HasDistribNeg M] {n : ℕ}
    (i j : Fin n) :
    (-1 : M) ^ ((j.rev : ℕ) + (i.rev : ℕ) + 1) = (-1) ^ ((i : ℕ) + (j : ℕ) + 1) :=
  neg_one_pow_congr (by simp only [Nat.even_iff, Fin.val_rev]; omega)

/-- The sign `(-1) ^ j` of the coface `j` of `n + 1` vertices, times the sign of the reversal of
`n + 1` vertices, is the sign of the coface `rev j` times the sign of the reversal of `n`
vertices. -/
theorem neg_one_pow_val_rev_mul {M : Type*} [Monoid M] [HasDistribNeg M] {n : ℕ}
    (j : Fin (n + 1)) :
    (-1 : M) ^ (j.rev : ℕ) * (-1) ^ n.choose 2 = (-1) ^ (n + 1).choose 2 * (-1) ^ (j : ℕ) := by
  rw [← pow_add, ← pow_add, Nat.choose_succ_succ', Nat.choose_one_right]
  exact neg_one_pow_congr (by
    have := j.isLt
    simp only [Nat.reduceAdd, Nat.even_iff, Fin.val_rev]
    omega)

end Fin
