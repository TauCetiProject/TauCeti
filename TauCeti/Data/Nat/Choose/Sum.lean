/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.RingTheory.PowerSeries.WellKnown
import TauCeti.Data.Nat.Choose.Basic

/-!
# Upper-index Vandermonde convolution

This file proves the convolution identity for binomial coefficients whose *lower* index is
fixed and whose upper index runs along an antidiagonal:

```text
  ∑_{i + j = n} C(a + i, a) * C(b + j, b) = C(a + b + 1 + n, a + b + 1).
```

It is the coefficient identity behind `(1 - X)⁻⁽ᵃ⁺¹⁾ * (1 - X)⁻⁽ᵇ⁺¹⁾ = (1 - X)⁻⁽ᵃ⁺ᵇ⁺²⁾`, and
generalizes Mathlib's hockey-stick identity `Finset.sum_antidiagonal_choose_add` (the case
`b = 0`). In probability it normalizes the negative hypergeometric law: placing the `(a + 1)`st
of `a + b + 1` marked objects at position `a + 1 + i` among `a + b + 1 + n` objects leaves
`C(a + i, a)` choices before it and `C(b + j, b)` after it.

Weighting the summands by a rising factorial `(k + r)⁽ᵐ⁾` of the position of the marked object
gives again a single binomial coefficient, `r⁽ᵐ⁾ * C(N + m, K + m)`; these are the rising
factorial moments of the negative hypergeometric law.

## Main results

* `Nat.sum_antidiagonal_choose_add_mul_choose_add`: the upper-index Vandermonde convolution.
* `Nat.sum_range_ascFactorial_mul_choose_mul_choose`: its version weighted by a rising factorial,
  `∑_{k ≤ N - K} (k + r)⁽ᵐ⁾ * C(k + r - 1, k) * C(N - r - k, K - r) = r⁽ᵐ⁾ * C(N + m, K + m)`.

## References

* R. L. Graham, D. E. Knuth, O. Patashnik, *Concrete Mathematics*, 2nd ed., Addison-Wesley, 1994,
  Section 5.1, equation (5.26).
-/

public section

open Finset

namespace Nat

/-- **Upper-index Vandermonde convolution:**
`∑_{i + j = n} C(a + i, a) * C(b + j, b) = C(a + b + 1 + n, a + b + 1)`.

For `b = 0` this is the hockey-stick identity `Finset.sum_antidiagonal_choose_add`. -/
theorem sum_antidiagonal_choose_add_mul_choose_add (a b n : ℕ) :
    ∑ ij ∈ antidiagonal n, (a + ij.1).choose a * (b + ij.2).choose b =
      (a + b + 1 + n).choose (a + b + 1) := by
  -- Compare the `n`th coefficients of `(∑ Xᵏ) ^ (a + b + 2) = (∑ Xᵏ) ^ (a + 1) * (∑ Xᵏ) ^ (b + 1)`.
  have h := congrArg (PowerSeries.coeff (R := ℤ) n)
    (pow_add (PowerSeries.mk 1 : PowerSeries ℤ) (a + 1) (b + 1))
  rw [show a + 1 + (b + 1) = a + b + 1 + 1 by omega, PowerSeries.mk_one_pow_eq_mk_choose_add,
    PowerSeries.mk_one_pow_eq_mk_choose_add, PowerSeries.mk_one_pow_eq_mk_choose_add,
    PowerSeries.coeff_mul] at h
  simp only [PowerSeries.coeff_mk] at h
  exact_mod_cast h.symm

/-- **Upper-index Vandermonde convolution weighted by a rising factorial:** for `r ≤ K ≤ N`,
`∑_{k ≤ N - K} (k + r)⁽ᵐ⁾ * C(k + r - 1, k) * C(N - r - k, K - r) = r⁽ᵐ⁾ * C(N + m, K + m)`,
where `n⁽ᵐ⁾` is the rising factorial `n.ascFactorial m`.

For `m = 0` it is the normalization `∑ₖ C(k + r - 1, k) * C(N - r - k, K - r) = C(N, K)` of the
negative hypergeometric law. The hypotheses are needed because natural subtraction is
totalized: for instance, without `r ≤ K`, the case `N = 1`, `K = 0`, `r = 1`, `m = 0` has
left-hand side `2` and right-hand side `1`. -/
theorem sum_range_ascFactorial_mul_choose_mul_choose {N K r : ℕ} (hr : r ≤ K) (hK : K ≤ N)
    (m : ℕ) :
    ∑ k ∈ Finset.range (N - K + 1),
        (k + r).ascFactorial m * ((k + r - 1).choose k * (N - r - k).choose (K - r)) =
      r.ascFactorial m * (N + m).choose (K + m) := by
  have hterm : ∀ k ∈ Finset.range (N - K + 1),
      (k + r).ascFactorial m * ((k + r - 1).choose k * (N - r - k).choose (K - r)) =
        r.ascFactorial m * ((k + r + m - 1).choose k * (N - r - k).choose (K - r)) := by
    intro k _
    have h := add_ascFactorial_mul_multichoose r m k
    rw [multichoose_eq, multichoose_eq] at h
    rw [← mul_assoc, ← mul_assoc, Nat.add_comm k r, h,
      show r + k + m - 1 = r + m + k - 1 by omega]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  congr 1
  rcases Nat.eq_zero_or_pos (r + m) with hrm | hrm
  · -- With `r = m = 0`, only the term `k = 0` survives.
    obtain ⟨rfl, rfl⟩ : r = 0 ∧ m = 0 := by omega
    rw [Finset.sum_range_succ']
    simp [Nat.choose_succ_self]
  · -- Otherwise this is the upper-index Vandermonde convolution with lower indices
    -- `r + m - 1` and `K - r`.
    have h := Nat.sum_antidiagonal_choose_add_mul_choose_add (r + m - 1) (K - r) (N - K)
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j ↦ (r + m - 1 + i).choose (r + m - 1) * (K - r + j).choose (K - r))] at h
    rw [show N + m = r + m - 1 + (K - r) + 1 + (N - K) by omega,
      show K + m = r + m - 1 + (K - r) + 1 by omega, ← h]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    have hk : k ≤ N - K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [show k + r + m - 1 = r + m - 1 + k by omega, Nat.choose_symm_add,
      show N - r - k = K - r + (N - K - k) by omega]

end Nat
