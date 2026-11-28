/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The exceptional pairs of Lawrence and Sawin

The sequence starts at `(1, 5)` and replaces `(a, b)` by `(b, 4 * b + 1 - a)`.
Its terms are precisely the ordered positive solutions to
`a ^ 2 - 4 * a * b + b ^ 2 = a + b`. Replacing the larger entry by the other root
of the same quadratic gives a descent on the smaller entry.

## References

* B. Lawrence and W. Sawin, *The Shafarevich conjecture for hypersurfaces in abelian varieties*,
  Lemma B.7 and the sequence preceding Theorem 3.5.
-/

public section

namespace TauCeti

/-- Consecutive terms of the exceptional Pell sequence, indexed from the pair `(1, 5)`. -/
@[expose] def exceptionalPair : ℕ → ℕ × ℕ
  | 0 => (1, 5)
  | j + 1 =>
    let p := exceptionalPair j
    (p.2, 4 * p.2 + 1 - p.1)

@[simp] theorem exceptionalPair_zero : exceptionalPair 0 = (1, 5) := rfl

theorem exceptionalPair_succ (j : ℕ) : exceptionalPair (j + 1) =
    ((exceptionalPair j).2, 4 * (exceptionalPair j).2 + 1 - (exceptionalPair j).1) := rfl

private theorem exceptionalPair_order (j : ℕ) :
    0 < (exceptionalPair j).1 ∧ (exceptionalPair j).1 < (exceptionalPair j).2 := by
  induction j with
  | zero => decide
  | succ j ih =>
    rw [exceptionalPair_succ]
    dsimp only
    omega

/-- The first entry of every exceptional pair is positive. -/
theorem exceptionalPair_fst_pos (j : ℕ) : 0 < (exceptionalPair j).1 :=
  (exceptionalPair_order j).1

/-- The entries of every exceptional pair are strictly ordered. -/
theorem exceptionalPair_fst_lt_snd (j : ℕ) : (exceptionalPair j).1 < (exceptionalPair j).2 :=
  (exceptionalPair_order j).2

/-- The second entry of every exceptional pair is positive. -/
theorem exceptionalPair_snd_pos (j : ℕ) : 0 < (exceptionalPair j).2 :=
  (exceptionalPair_fst_pos j).trans (exceptionalPair_fst_lt_snd j)

/-- Adding the subtracted entry back recovers the minuend in the recurrence. -/
theorem exceptionalPair_sub_exact (j : ℕ) :
    (exceptionalPair (j + 1)).2 + (exceptionalPair j).1 = 4 * (exceptionalPair j).2 + 1 := by
  rw [exceptionalPair_succ]
  exact Nat.sub_add_cancel (by have := exceptionalPair_fst_lt_snd j; omega)

/-- The smaller entry increases strictly with the sequence index. -/
theorem exceptionalPair_fst_strictMono : StrictMono fun j => (exceptionalPair j).1 :=
  strictMono_nat_of_lt_succ exceptionalPair_fst_lt_snd

/-- The larger entry increases strictly with the sequence index. -/
theorem exceptionalPair_snd_strictMono : StrictMono fun j => (exceptionalPair j).2 :=
  strictMono_nat_of_lt_succ fun j => exceptionalPair_fst_lt_snd (j + 1)

/-- The quadratic equation preserved by the exceptional-pair recurrence. -/
theorem exceptionalPair_invariant (j : ℕ) :
    ((exceptionalPair j).1 : ℤ) ^ 2 - 4 * (exceptionalPair j).1 * (exceptionalPair j).2 +
      ((exceptionalPair j).2 : ℤ) ^ 2 = (exceptionalPair j).1 + (exceptionalPair j).2 := by
  induction j with
  | zero => decide
  | succ j ih =>
    have hle : (exceptionalPair j).1 ≤ 4 * (exceptionalPair j).2 + 1 := by
      have := exceptionalPair_fst_lt_snd j
      omega
    rw [exceptionalPair_succ]
    dsimp only
    push_cast [Nat.cast_sub hle]
    nlinarith only [ih]

private theorem exceptionalPair_descent {a b : ℕ} (ha : 1 < a) (hab : a ≤ b)
    (heq : (a : ℤ) ^ 2 - 4 * a * b + (b : ℤ) ^ 2 = a + b) :
    ∃ c : ℕ, 0 < c ∧ c < a ∧ c + b = 4 * a + 1 ∧
      (c : ℤ) ^ 2 - 4 * c * a + (a : ℤ) ^ 2 = c + a := by
  have hnat : a ^ 2 + b ^ 2 = 4 * a * b + a + b := by
    exact_mod_cast (show (a : ℤ) ^ 2 + (b : ℤ) ^ 2 = 4 * a * b + a + b by linarith)
  have hasq : a * 1 < a * a := Nat.mul_lt_mul_of_pos_left ha (by omega)
  have hb : b < 4 * a + 1 := by
    by_contra! hlarge
    nlinarith [Nat.mul_le_mul_right b hlarge]
  let c := 4 * a + 1 - b
  have hsum : c + b = 4 * a + 1 := Nat.sub_add_cancel hb.le
  have hprod : b * c + a = a ^ 2 := by nlinarith [congrArg (fun x => x * b) hsum]
  have hca : c < a := by
    by_contra! hlarge
    nlinarith [Nat.mul_le_mul hab hlarge]
  refine ⟨c, Nat.sub_pos_of_lt hb, hca, hsum, ?_⟩
  have hsumZ : (c : ℤ) + b = 4 * a + 1 := by exact_mod_cast hsum
  rw [show (c : ℤ) = 4 * a + 1 - b by linarith only [hsumZ]]
  nlinarith only [heq]

private theorem exists_exceptionalPair {a b : ℕ} (ha : 0 < a) (hab : a ≤ b)
    (heq : (a : ℤ) ^ 2 - 4 * a * b + (b : ℤ) ^ 2 = a + b) :
    ∃ j : ℕ, (a, b) = exceptionalPair j := by
  induction a using Nat.strong_induction_on generalizing b with
  | ind a ih =>
    by_cases hbase : a = 1
    · subst a
      have hz : (b : ℤ) * (b - 5) = 0 := by norm_num at heq; nlinarith only [heq]
      have hb : b = 5 := by rcases mul_eq_zero.mp hz with h | h <;> omega
      exact ⟨0, by simp [hb]⟩
    obtain ⟨c, hc, hca, hsum, heq'⟩ := exceptionalPair_descent (by omega : 1 < a) hab heq
    obtain ⟨j, hj⟩ := ih c hca hc hca.le heq'
    refine ⟨j + 1, ?_⟩
    rw [exceptionalPair_succ, ← hj]
    congr 1
    omega

/-- A positive ordered pair satisfies the Pell equation exactly when it occurs at a unique
index of the exceptional sequence. -/
theorem exceptionalPair_classification (a b : ℕ) (ha : 0 < a) (hab : a ≤ b) :
    (a : ℤ) ^ 2 - 4 * a * b + (b : ℤ) ^ 2 = a + b ↔
      ∃! j : ℕ, exceptionalPair j = (a, b) := by
  constructor
  · intro heq
    obtain ⟨j, hj⟩ := exists_exceptionalPair ha hab heq
    refine ⟨j, hj.symm, fun k hk => exceptionalPair_fst_strictMono.injective ?_⟩
    exact congrArg Prod.fst (hk.trans hj)
  · rintro ⟨j, hj, _⟩
    have h := exceptionalPair_invariant j
    rwa [hj] at h

end TauCeti
