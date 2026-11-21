/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
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

The partial-sum complement identity partitions subsets according to the position of their `r`th
element. Its recurrence follows from Pascal's identity, and the initial value is Mathlib's
`Nat.add_choose_eq`.

Weighting a binomial antidiagonal sum by its first index lowers its order by one. This identity
applies to sums in any additive commutative monoid, including coefficient sums for formal fields.

## Main results

* `Finset.sum_filter_antidiagonal_choose`: filtering `antidiagonal m ×ˢ antidiagonal n` by
  componentwise sum `(a, b)` with `a + b = m + n` and summing `a.choose p.1 * b.choose p.2`
  yields `(m + n).choose m`.
* `Nat.sum_antidiagonal_choose_add_mul_choose_add`: the upper-index Vandermonde convolution.
* `Nat.sum_antidiagonal_snd_add_choose`: summing `(r + m).choose (k + m)` over the second
  coordinate of the antidiagonal of `N` gives `(N + (m + 1)).choose (k + (m + 1))`.
* `Nat.sum_range_ascFactorial_mul_choose_mul_choose`: its version weighted by a rising factorial,
  `∑_{k ≤ N - K} (k + r)⁽ᵐ⁾ * C(k + r - 1, k) * C(N - r - k, K - r) = r⁽ᵐ⁾ * C(N + m, K + m)`.
* `Nat.sum_range_choose_mul_choose_add_sum_range_choose_mul_choose`: the complementary partial
  sums, distinguished by whether the `r`th element lies among the first `k + r` positions.
* `Nat.one_add_mul_sum_range_add_choose_le`: the hockey-stick majorant bound
  `1 + m * ∑ k ∈ range (n + 1), (k + m).choose m ≤ (n + 1) * (n + 1 + m).choose m`.

## References

* R. L. Graham, D. E. Knuth, O. Patashnik, *Concrete Mathematics*, 2nd ed., Addison-Wesley, 1994,
  Section 5.1, equation (5.26).
-/

public section

open Finset

namespace Finset

/-- Weighting a binomial antidiagonal sum by its first index lowers its order by one. -/
theorem sum_antidiagonal_choose_succ_nsmul_nsmul {M : Type*} [AddCommMonoid M]
    (f : ℕ → ℕ → M) (N : ℕ) :
    ∑ ij ∈ antidiagonal (N + 1), (N + 1).choose ij.1 • ij.1 • f ij.1 ij.2 =
      (N + 1) • ∑ ij ∈ antidiagonal N, N.choose ij.1 • f (ij.1 + 1) ij.2 := by
  rw [Nat.sum_antidiagonal_succ]
  simp only [zero_smul, smul_zero, zero_add]
  simp_rw [← mul_smul, ← Nat.add_one_mul_choose_eq, mul_smul]
  rw [smul_sum]

/-- Filtering pairs `(p, q) ∈ antidiagonal m ×ˢ antidiagonal n` by fixed componentwise sums
`(p.1 + q.1, p.2 + q.2) = (a, b)` (with `a + b = m + n`) and summing `a.choose p.1 * b.choose p.2`
yields `(m + n).choose m`, via Vandermonde's identity `Nat.add_choose_eq`. -/
theorem sum_filter_antidiagonal_choose {m n a b : ℕ} (hab : a + b = m + n) :
    ∑ pq ∈ (antidiagonal m ×ˢ antidiagonal n).filter
        (fun pq ↦ (pq.1.1 + pq.2.1, pq.1.2 + pq.2.2) = (a, b)),
      a.choose pq.1.1 * b.choose pq.1.2 = (m + n).choose m := by
  rw [← hab, Nat.add_choose_eq a b m]
  have hfilt : ∑ p ∈ antidiagonal m, a.choose p.1 * b.choose p.2 =
      ∑ p ∈ (antidiagonal m).filter (fun p ↦ p.1 ≤ a ∧ p.2 ≤ b),
        a.choose p.1 * b.choose p.2 := by
    symm
    refine sum_filter_of_ne fun p _ hne ↦ ?_
    by_contra h
    rw [not_and_or, not_le, not_le] at h
    rcases h with h | h
    · exact hne (by simp [Nat.choose_eq_zero_of_lt h])
    · exact hne (by simp [Nat.choose_eq_zero_of_lt h])
  rw [hfilt]
  refine sum_nbij' (fun pq ↦ pq.1) (fun p ↦ (p, (a - p.1, b - p.2))) ?_ ?_ ?_ ?_ ?_
  · intro ⟨⟨i, j⟩, ⟨k, l⟩⟩ hpq
    simp only [mem_filter, mem_product, mem_antidiagonal, Prod.mk.injEq] at hpq ⊢
    omega
  · intro ⟨i, j⟩ hp
    simp only [mem_filter, mem_product, mem_antidiagonal, Prod.mk.injEq] at hp ⊢
    omega
  · intro ⟨⟨i, j⟩, ⟨k, l⟩⟩ hpq
    simp only [mem_filter, mem_product, mem_antidiagonal, Prod.mk.injEq] at hpq ⊢
    exact ⟨trivial, by omega, by omega⟩
  · intro ⟨i, j⟩ _
    rfl
  · intro ⟨⟨i, j⟩, ⟨k, l⟩⟩ _
    rfl

end Finset

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
    rw [← mul_assoc, ← mul_assoc, add_comm k r, h,
      show r + k + m - 1 = r + m + k - 1 by omega]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  congr 1
  rcases eq_zero_or_pos (r + m) with hrm | hrm
  · -- With `r = m = 0`, only the term `k = 0` survives.
    obtain ⟨rfl, rfl⟩ : r = 0 ∧ m = 0 := by omega
    rw [Finset.sum_range_succ']
    simp [choose_succ_self]
  · -- Otherwise this is the upper-index Vandermonde convolution with lower indices
    -- `r + m - 1` and `K - r`.
    have h := sum_antidiagonal_choose_add_mul_choose_add (r + m - 1) (K - r) (N - K)
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j ↦ (r + m - 1 + i).choose (r + m - 1) * (K - r + j).choose (K - r))] at h
    rw [show N + m = r + m - 1 + (K - r) + 1 + (N - K) by omega,
      show K + m = r + m - 1 + (K - r) + 1 by omega, ← h]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    have hk : k ≤ N - K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [show k + r + m - 1 = r + m - 1 + k by omega, choose_symm_add,
      show N - r - k = K - r + (N - K - k) by omega]

/-- Moving one element from the second population to the first in a partial Vandermonde sum
changes it by the boundary term at the cutoff. -/
theorem sum_range_choose_mul_choose_succ (m n K r : ℕ) (hr : r < K) :
    (∑ j ∈ range (r + 1), (m + 1).choose j * n.choose (K - j)) +
        m.choose r * n.choose (K - (r + 1)) =
      ∑ j ∈ range (r + 1), m.choose j * (n + 1).choose (K - j) := by
  induction r with
  | zero =>
    simp only [zero_add, sum_range_one, choose_zero_right, one_mul, Nat.sub_zero]
    rw [choose_succ_left _ _ (by omega)]
    omega
  | succ r ih =>
    have ih := ih (by omega)
    rw [sum_range_succ _ (r + 1),
      sum_range_succ (fun j ↦ m.choose j * (n + 1).choose (K - j)) (r + 1),
      choose_succ_succ']
    rw [choose_succ_left n (K - (r + 1)) (by omega)]
    have heq : K - (r + 1) - 1 = K - (r + 1 + 1) := by omega
    rw [heq]
    nlinarith

/-- A partial upper-index Vandermonde sum and its complementary lower tail add to the full
binomial coefficient. It partitions `K`-element subsets by whether their `r`th element occurs
among the first `k + r` positions. For `r = 0` the second sum is empty and only the term `i = 0`
of the first sum is nonzero. -/
theorem sum_range_choose_mul_choose_add_sum_range_choose_mul_choose
    {N K r k : ℕ} (hrK : r ≤ K) (hk : k + r ≤ N) :
    (∑ i ∈ range (k + 1), (i + r - 1).choose i * (N - r - i).choose (K - r)) +
        (∑ j ∈ range r, (k + r).choose j * (N - k - r).choose (K - j)) =
      N.choose K := by
  rcases eq_zero_or_pos r with rfl | hr
  · -- Only the term `i = 0` of the first sum is nonzero, and the second sum is empty.
    simp [sum_range_succ', choose_succ_self]
  induction k with
  | zero =>
    have hsum := add_choose_eq r (N - r) K
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j ↦ r.choose i * (N - r).choose j)] at hsum
    have htruncate :
        (∑ j ∈ range (K + 1), r.choose j * (N - r).choose (K - j)) =
          ∑ j ∈ range (r + 1), r.choose j * (N - r).choose (K - j) := by
      symm
      apply sum_subset (range_mono (by omega))
      intro j _ hj
      simp only [mem_range, not_lt] at hj
      simp [choose_eq_zero_of_lt (by omega : r < j)]
    rw [htruncate, sum_range_succ] at hsum
    simp only [sum_range_one, zero_add, choose_zero_right, one_mul, Nat.sub_zero,
      choose_self] at *
    rw [add_sub_of_le (by omega : r ≤ N)] at hsum
    omega
  | succ k ih =>
    have ih := ih (by omega)
    have hstep := sum_range_choose_mul_choose_succ (k + r) (N - (k + 1) - r) K
      (r - 1) (by omega)
    have heq : r - 1 + 1 = r := by omega
    have hn : N - (k + 1) - r + 1 = N - k - r := by omega
    rw [heq, hn, (choose_symm (by omega : r - 1 ≤ k + r)).symm] at hstep
    have hi : k + r - (r - 1) = k + 1 := by omega
    rw [hi] at hstep
    rw [sum_range_succ]
    have hm : k + 1 + r - 1 = k + r := by omega
    have hsub : N - r - (k + 1) = N - (k + 1) - r := by omega
    rw [hm, hsub]
    have hadd : k + 1 + r = k + r + 1 := by omega
    rw [hadd]
    omega

/-- Summing `(r + m).choose (k + m)` over the second coordinate of the antidiagonal of `N` raises
both binomial indices by one. -/
theorem sum_antidiagonal_snd_add_choose (N k m : ℕ) :
    ∑ r ∈ antidiagonal N, (r.2 + m).choose (k + m) = (N + (m + 1)).choose (k + (m + 1)) := by
  rw [← Nat.sum_antidiagonal_swap]
  simp only [Prod.snd_swap]
  rw [Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  calc
    ∑ r ∈ range (N + 1), (r + m).choose (k + m) =
        ∑ r ∈ Icc m (N + m), r.choose (k + m) := by
      convert! (sum_map (range (N + 1)) (addRightEmbedding m)
        (fun r ↦ r.choose (k + m))).symm using 2
      rw [range_eq_Ico, map_add_right_Ico, zero_add, add_right_comm,
        Ico_add_one_right_eq_Icc]
    _ = ∑ r ∈ Icc (k + m) (N + m), r.choose (k + m) := by
      symm
      apply sum_subset (by intro r hr; simp only [mem_Icc] at *; omega)
      intro r hr hnot
      apply choose_eq_zero_of_lt
      simp only [mem_Icc] at *
      omega
    _ = (N + (m + 1)).choose (k + (m + 1)) := by
      simpa only [add_assoc] using sum_Icc_choose (N + m) (k + m)

/-- Majorant bound from the hockey-stick identity `Nat.sum_range_add_choose` and absorption
`Nat.choose_succ_right_eq`:
`1 + m * ∑ k ∈ range (n + 1), (k + m).choose m ≤ (n + 1) * (n + 1 + m).choose m`. -/
theorem one_add_mul_sum_range_add_choose_le (n m : ℕ) :
    1 + m * ∑ k ∈ range (n + 1), (k + m).choose m ≤
      (n + 1) * (n + 1 + m).choose m := by
  rw [sum_range_add_choose n m]
  have h1 : 1 ≤ (n + m + 1).choose (m + 1) := choose_pos (by omega)
  have h2 : (n + m + 1).choose (m + 1) * (m + 1) = (n + 1) * (n + 1 + m).choose m := by
    rw [choose_succ_right_eq (n + m + 1) m, Nat.add_right_comm n m 1,
      Nat.add_sub_cancel, Nat.mul_comm]
  calc
    1 + m * (n + m + 1).choose (m + 1)
        ≤ (n + m + 1).choose (m + 1) + m * (n + m + 1).choose (m + 1) :=
          Nat.add_le_add_right h1 _
    _ = (n + m + 1).choose (m + 1) * (m + 1) := by ring
    _ = (n + 1) * (n + 1 + m).choose m := h2

end Nat
