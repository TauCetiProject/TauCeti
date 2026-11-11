/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Group.Nat.Even
public import TauCeti.Algebra.Algebra.CyclicQuotient

/-!
# Two square-zero elements with a nilpotent sum

Let `x` and `y` be elements of an `R`-algebra with `x * x = 0` and `y * y = 0`, and write
`s = x + y`. A product of factors from `{x, y}` vanishes as soon as two neighbouring factors are
equal, so the only surviving products are the alternating words `x y x ⋯` and `y x y ⋯`. These are
`x * s ^ t` and `y * s ^ t`, since every other word in the expansion of `s ^ t` has a repeated
neighbour. Hence the `t + 1`-st power of the span of `{x, y}` is spanned by `x * s ^ t` and
`y * s ^ t`, and **if `s ^ m = 0` then every product of `m + 1` factors from `{x, y}` vanishes**.

For the preprojective algebra of a graph, `x` and `y` are the two backtracks from a vertex into
two leaves attached to it, each of which squares to zero by the relation at its leaf. This is
the step which bounds the length of the nonzero paths through the branch vertex of `Dₙ`.

## Main results

* `TauCeti.mul_add_eq_add_mul_of_mul_self_eq_zero` and
  `TauCeti.mul_add_pow_eq_add_pow_mul_of_mul_self_eq_zero`: moving an element of a square-zero
  pair past a power of their sum preserves or exchanges the element according to parity.
* `TauCeti.span_pair_pow_succ`: the `t + 1`-st power of the span of `{x, y}` is the span of
  `x * (x + y) ^ t` and `y * (x + y) ^ t`.
* `TauCeti.span_pair_pow_succ_eq_bot`: if moreover `(x + y) ^ m = 0`, then the `m + 1`-st power of
  the span of `{x, y}` is zero.
* `TauCeti.mul_add_pow_mem_commutatorSubmodule`: if `2` is invertible, and `x` and the positive
  powers of `s` are sums of commutators, then so is every alternating word `x * s ^ t`.
-/

public section

namespace TauCeti

open Submodule

variable {A : Type*}

section NonUnitalNonAssocSemiring

variable [NonUnitalNonAssocSemiring A] {x y : A}

/-- Moving an element of a square-zero pair past their sum exchanges the element. -/
theorem mul_add_eq_add_mul_of_mul_self_eq_zero (hx : x * x = 0) (hy : y * y = 0) :
    x * (x + y) = (x + y) * y := by
  simp only [mul_add, add_mul, hx, hy, zero_add, add_zero]

end NonUnitalNonAssocSemiring

variable [Semiring A] {x y : A}

/-- Moving an element of a square-zero pair past a power of their sum preserves it at even
exponents and exchanges it at odd exponents. -/
theorem mul_add_pow_eq_add_pow_mul_of_mul_self_eq_zero (hx : x * x = 0) (hy : y * y = 0)
    (t : ℕ) : x * (x + y) ^ t = (x + y) ^ t * (if Even t then x else y) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ, ← mul_assoc, ih, mul_assoc, mul_assoc]
    congr 1
    by_cases ht : Even t
    · simpa [ht, Nat.even_add_one] using mul_add_eq_add_mul_of_mul_self_eq_zero hx hy
    · simpa [ht, Nat.even_add_one, add_comm] using mul_add_eq_add_mul_of_mul_self_eq_zero hy hx

variable {R : Type*} [CommSemiring R] [Algebra R A]

/-- If `x` and `y` square to zero, the products of `t + 1` factors from `{x, y}` span exactly
the two alternating words `x * (x + y) ^ t` and `y * (x + y) ^ t`. -/
theorem span_pair_pow_succ (hx : x * x = 0) (hy : y * y = 0) (t : ℕ) :
    span R {x, y} ^ (t + 1) = span R {x * (x + y) ^ t, y * (x + y) ^ t} := by
  refine le_antisymm ?_ <| span_le.2 <| Set.pair_subset_iff.2 <| by
    -- Each alternating word is a factor times a power of `x + y`, which lies in the span.
    have hx' : x ∈ span R {x, y} := subset_span (by simp)
    have hy' : y ∈ span R {x, y} := subset_span (by simp)
    have hs := pow_mem_pow _ (add_mem hx' hy') t
    rw [pow_succ']
    exact ⟨mul_mem_mul hx' hs, mul_mem_mul hy' hs⟩
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ' (span R {x, y})]
    refine (mul_le_mul_right ih _).trans ?_
    rw [span_mul_span, span_le]
    rintro _ ⟨a, ha, b, hb, rfl⟩
    -- A repeated factor vanishes, and the alternating products extend the alternating words.
    have hxs : x * (y * (x + y) ^ t) = x * (x + y) ^ (t + 1) := by
      rw [pow_succ', ← mul_assoc, ← mul_assoc, mul_add, hx, zero_add]
    have hys : y * (x * (x + y) ^ t) = y * (x + y) ^ (t + 1) := by
      rw [pow_succ', ← mul_assoc, ← mul_assoc, mul_add, hy, add_zero]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · simp [← mul_assoc, hx]
    · exact subset_span (by simp [hxs])
    · exact subset_span (by simp [hys])
    · simp [← mul_assoc, hy]

/-- **Two square-zero elements with a nilpotent sum.** If `x * x = 0`, `y * y = 0` and
`(x + y) ^ m = 0`, then every product of `m + 1` factors from `{x, y}` vanishes. -/
theorem span_pair_pow_succ_eq_bot (hx : x * x = 0) (hy : y * y = 0) {m : ℕ}
    (hm : (x + y) ^ m = 0) : span R {x, y} ^ (m + 1) = ⊥ := by
  simp [span_pair_pow_succ hx hy, hm]

/-- **Alternating words in a square-zero pair are sums of commutators.** Let `x` and `y` square to
zero, and suppose that `x` and every positive power of `s = x + y` lie in the commutator submodule
`[B, B]`. If `2` is a unit in `k`, then so does every alternating word `x * s ^ t`.

For odd `t` the word `x * s ^ t = s ^ t * y` and its rotation `s ^ t * x` sum to `s ^ (t + 1)`,
so twice the word is a sum of commutators; this is where `2` must be invertible. For even
`t ≥ 2` the word ends with `x`, and its rotation begins with `x * x = 0`. -/
theorem mul_add_pow_mem_commutatorSubmodule {B : Type*} [Ring B] {k : Type*} [Semiring k]
    [Module k B] {x y : B} (h2 : IsUnit (2 : k)) (hx : x * x = 0) (hy : y * y = 0)
    (hx₀ : x ∈ commutatorSubmodule k B) (hs : ∀ t, (x + y) ^ (t + 1) ∈ commutatorSubmodule k B)
    (t : ℕ) : x * (x + y) ^ t ∈ commutatorSubmodule k B := by
  -- At odd exponents, moving `x` past the power of `s` turns it into `y`.
  have hodd (i : ℕ) : x * (x + y) ^ (2 * i + 1) = (x + y) ^ (2 * i + 1) * y := by
    simpa [Nat.even_add_one] using mul_add_pow_eq_add_pow_mul_of_mul_self_eq_zero hx hy (2 * i + 1)
  obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' t
  · cases i with
    | zero => simpa using hx₀
    | succ i =>
      -- The word ends with `x`, since the alternating word before it ends with `y`.
      have heq : x * (x + y) ^ (2 * (i + 1)) = x * (x + y) ^ (2 * i + 1) * x := by
        rw [show 2 * (i + 1) = 2 * i + 1 + 1 by omega, pow_succ, ← mul_assoc, mul_add, hodd]
        simp [mul_assoc, hy]
      have hrot := mul_sub_mul_mem_commutatorSubmodule k B (x * (x + y) ^ (2 * i + 1)) x
      rwa [← heq, ← mul_assoc x x, hx, zero_mul, sub_zero] at hrot
  · -- The word and its rotation sum to the next power of `s`.
    have hsum : x * (x + y) ^ (2 * i + 1) + (x + y) ^ (2 * i + 1) * x =
        (x + y) ^ (2 * i + 1 + 1) := by
      rw [hodd, ← mul_add, add_comm y x, ← pow_succ]
    have hrot := mul_sub_mul_mem_commutatorSubmodule k B x ((x + y) ^ (2 * i + 1))
    have htwo := add_mem hrot (hsum ▸ hs (2 * i + 1))
    rw [sub_add_add_cancel, ← two_smul k] at htwo
    exact (Submodule.smul_mem_iff_of_isUnit _ h2).1 htwo

end TauCeti
