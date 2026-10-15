/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Divisors

/-!
# Divisor sums picking out a shifted index

For `N ≠ 0`, the divisors `d` of `N` with `a = N + d` (respectively `a = N - d`) are at most one,
and such a divisor exists exactly when `a - N` divides `N` (respectively `N - a` divides `a`).
These lemmas evaluate the corresponding indicator sums over `N.divisors`.
-/

public section

namespace Nat

variable {M : Type*} [AddCommMonoid M]

/-- The sum over the divisors `d` of `N` of `f d` restricted to `a = N + d`. -/
theorem sum_divisors_ite_eq_add {N : ℕ} (hN : N ≠ 0) (a : ℕ) (f : ℕ → M) :
    ∑ d ∈ N.divisors, (if a = N + d then f d else 0) =
      if N < a ∧ a - N ∣ N then f (a - N) else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single (a - N)]
    · rw [ite_eq_left (by omega)]
    · intro d _ hd
      rw [ite_eq_right (by omega)]
    · intro h'
      exact absurd (Nat.mem_divisors.mpr ⟨h.2, hN⟩) h'
  · refine Finset.sum_eq_zero fun d hd ↦ ite_eq_right fun ha ↦ h ⟨?_, ?_⟩
    · have := Nat.pos_of_mem_divisors hd
      omega
    · have had : a - N = d := by omega
      rw [had]
      exact Nat.dvd_of_mem_divisors hd

/-- The sum over the divisors `d` of `N` of `f d` restricted to `a = N - d`. -/
theorem sum_divisors_ite_eq_sub {N : ℕ} (hN : N ≠ 0) (a : ℕ) (f : ℕ → M) :
    ∑ d ∈ N.divisors, (if a = N - d then f d else 0) =
      if a < N ∧ N - a ∣ a then f (N - a) else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single (N - a)]
    · rw [ite_eq_left (by omega)]
    · intro d hd hne
      have := Nat.divisor_le hd
      rw [ite_eq_right (by omega)]
    · refine fun h' ↦ absurd (Nat.mem_divisors.mpr ⟨?_, hN⟩) h'
      have h'' := Nat.dvd_add_self_right.mpr h.2
      rwa [Nat.add_sub_cancel' h.1.le] at h''
  · refine Finset.sum_eq_zero fun d hd ↦ ite_eq_right fun ha ↦ h ⟨?_, ?_⟩
    · have := Nat.pos_of_mem_divisors hd
      have := Nat.divisor_le hd
      omega
    · have := Nat.divisor_le hd
      have had : N - a = d := by omega
      have hN' : N = a + d := by omega
      rw [had]
      have h' := Nat.dvd_of_mem_divisors hd
      rwa [hN', Nat.dvd_add_self_right] at h'

end Nat
