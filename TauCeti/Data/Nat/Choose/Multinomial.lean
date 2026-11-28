/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Data.Nat.Factorization.Defs
public import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Choose.Factorization

/-!
# Multiplicities of primes in multinomial coefficients

Successively choosing the parts of a multinomial coefficient lets us apply the binomial
multiplicity bound from Kummer's theorem to each choice. The resulting size bound is useful
for clearing multinomial denominators in a local ring.
-/

public section

open Finset

namespace Nat

/-- The multiplicity of `p` in a multinomial coefficient for `s.card` parts is bounded by
`s.card - 1` times the base-`p` logarithm of the sum of the parts. -/
theorem factorization_multinomial_le {ι : Type*} (s : Finset ι) (a : ι → ℕ) (p : ℕ) :
    (multinomial s a).factorization p ≤ (s.card - 1) * log p (∑ i ∈ s, a i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ih =>
    rcases s.eq_empty_or_nonempty with rfl | hs
    · simp
    have hcard : 1 ≤ s.card := hs.card_pos
    rw [multinomial_cons hi, factorization_mul
      (choose_pos (le_add_right _ _)).ne' (multinomial_pos s a).ne', Finsupp.add_apply,
      sum_cons, card_cons, Nat.add_sub_cancel]
    calc
      _ ≤ log p (a i + ∑ j ∈ s, a j) + (s.card - 1) * log p (a i + ∑ j ∈ s, a j) :=
        add_le_add factorization_choose_le_log
          (ih.trans (Nat.mul_le_mul_left _ (log_mono_right (le_add_left _ _))))
      _ = _ := by rw [← one_add_mul, Nat.add_comm 1, Nat.sub_add_cancel hcard]

end Nat
