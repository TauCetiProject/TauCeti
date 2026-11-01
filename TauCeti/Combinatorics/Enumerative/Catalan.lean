/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# Recurrences of the Catalan numbers

Mathlib defines `catalan` by the convolution recurrence and proves
`(n + 1) * catalan n = Nat.centralBinom n`. Combined with the ratio recurrence of the central
binomial coefficients, this gives the first-order recurrence
`(n + 2) * catalan (n + 1) = 2 * (2 * n + 1) * catalan n`. This is the form in which Catalan
numbers arise as solutions of linear moment recurrences, such as the even moments of the
semicircle law.

The signed Catalan numbers `(-1)^k C_k` satisfy the Catalan recurrence up to a sign:
`∑_{i ≤ k} (-1)^i C_i (-1)^(k-i) C_(k-i) = (-1)^k C_(k+1)`. This is the recurrence satisfied by
the Möbius function `μ(0̂, 1̂)` of the lattice of noncrossing partitions.

## Main results

* `Nat.add_two_mul_catalan_succ` — the first-order recurrence `(n + 2) Cₙ₊₁ = 2 (2n + 1) Cₙ`.
* `TauCeti.sum_range_neg_one_pow_mul_catalan` — the convolution of the signed Catalan numbers.
-/

public section

namespace Nat

/-- The first-order recurrence `(n + 2) Cₙ₊₁ = 2 (2n + 1) Cₙ` of the Catalan numbers. -/
theorem add_two_mul_catalan_succ (n : ℕ) :
    (n + 2) * catalan (n + 1) = 2 * (2 * n + 1) * catalan n := by
  apply Nat.eq_of_mul_eq_mul_left n.succ_pos
  calc
    (n + 1) * ((n + 2) * catalan (n + 1)) = (n + 1) * (n + 1).centralBinom := by
      rw [← succ_mul_catalan_eq_centralBinom]
    _ = 2 * (2 * n + 1) * n.centralBinom := Nat.succ_mul_centralBinom_succ n
    _ = (n + 1) * (2 * (2 * n + 1) * catalan n) := by
      rw [← succ_mul_catalan_eq_centralBinom]
      ring

end Nat

open Finset

namespace TauCeti

/-- The convolution of the signed Catalan numbers:
`∑_{i ≤ k} (-1)^i C_i (-1)^(k-i) C_(k-i) = (-1)^k C_(k+1)`. -/
theorem sum_range_neg_one_pow_mul_catalan {R : Type*} [CommRing R] (k : ℕ) :
    ∑ i ∈ range (k + 1), (-1 : R) ^ i * catalan i * ((-1) ^ (k - i) * catalan (k - i)) =
      (-1) ^ k * catalan (k + 1) := by
  rw [catalan_succ, ← sum_range fun i => catalan i * catalan (k - i), Nat.cast_sum, mul_sum]
  refine sum_congr rfl fun i hi => ?_
  rw [← Nat.add_sub_cancel' (Nat.lt_succ_iff.1 (mem_range.1 hi)), pow_add, Nat.add_sub_cancel_left]
  push_cast
  ring

end TauCeti
