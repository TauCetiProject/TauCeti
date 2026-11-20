/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Algebraic identities for `PowerSeries.mk`

Compatibility identities for `PowerSeries.mk : (ℕ → R) → R⟦X⟧` with `0`, `+`, `-`, `•`, `Pi.single`,
`PowerSeries.map`, and multiplication (Cauchy convolution), complementing Mathlib's
`PowerSeries.coeff_mk`, `PowerSeries.constantCoeff_mk`, and `PowerSeries.rescale_mk`.

## Main results

* `PowerSeries.mk_zero`, `PowerSeries.mk_add`, `PowerSeries.mk_neg`, `PowerSeries.mk_sub`,
  `PowerSeries.mk_smul`, `PowerSeries.mk_single`: compatibility with module operations and
  `Pi.single`.
* `PowerSeries.map_mk`: `PowerSeries.map f (PowerSeries.mk a) = PowerSeries.mk (f ∘ a)`.
* `PowerSeries.mk_mul_mk`: Cauchy product of `PowerSeries.mk a` and `PowerSeries.mk b`.
-/

public section

namespace PowerSeries

/-- The zero sequence constructs the zero power series. -/
@[simp]
theorem mk_zero {R : Type*} [Zero R] : mk (0 : ℕ → R) = 0 := (rfl)

/-- `PowerSeries.mk` preserves addition. -/
theorem mk_add {R : Type*} [AddMonoid R] (a b : ℕ → R) : mk (a + b) = mk a + mk b := (rfl)

/-- `PowerSeries.mk` preserves negation. -/
theorem mk_neg {R : Type*} [AddGroup R] (a : ℕ → R) : mk (-a) = -mk a := (rfl)

/-- `PowerSeries.mk` preserves subtraction. -/
theorem mk_sub {R : Type*} [AddGroup R] (a b : ℕ → R) : mk (a - b) = mk a - mk b := (rfl)

/-- `PowerSeries.mk` preserves scalar multiplication. -/
theorem mk_smul {M R : Type*} [Semiring M] [AddCommMonoid R] [Module M R] (c : M) (a : ℕ → R) :
    mk (c • a) = c • mk a := (rfl)

section Semiring

variable {R : Type*} [Semiring R]

/-- A sequence supported at a single index `k` constructs `monomial k c`. -/
@[simp]
theorem mk_single (k : ℕ) (c : R) : mk (Pi.single k c) = monomial k c := by
  ext n; simp [Pi.single_apply, coeff_monomial]

/-- Coefficientwise mapping of `PowerSeries.mk a` along a ring homomorphism `f`. -/
@[simp]
theorem map_mk {S : Type*} [Semiring S] (f : R →+* S) (a : ℕ → R) :
    map f (mk a) = mk (f ∘ a) := by ext n; simp

/-- Multiplying two power series constructed by `PowerSeries.mk` yields the Cauchy convolution
sum over `Finset.range (n + 1)`. -/
theorem mk_mul_mk (a b : ℕ → R) :
    mk a * mk b = mk fun n ↦ ∑ k ∈ Finset.range (n + 1), a k * b (n - k) := by
  ext n; simp only [coeff_mul, coeff_mk]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j ↦ a i * b j) n

end Semiring

end PowerSeries
