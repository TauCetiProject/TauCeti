/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.Ring

/-!
# Uniform meshes and cell indexing

For a uniform mesh of step `h > 0` on a period `n h`, the intervals `[j h, j h + h]` and
`[k h, k h + h]` of two distinct steps `j ≠ k` in `{0, …, n - 1}` overlap at most at an endpoint,
even after shifting one of them by an integer multiple of the period. On each half-open cell
`[n * h, (n + 1) * h)`, the floor quotient `⌊t / h⌋₊` identifies the cell index `n`.

## Main results

* `TauCeti.add_mul_add_h_le_or_le_of_ne`: the shifted interval `[j h + m n h, j h + m n h + h]` lies
  on one side of `[k h, k h + h]`.
* `TauCeti.floor_div_eq_of_mem_Ico`: `⌊t / h⌋₊ = n` on `[n * h, (n + 1) * h)`.
-/

public section

namespace TauCeti

/-- Distinct steps `j ≠ k` of a uniform mesh `h = T / n` stay distinct modulo the period `n h`: the
interval `[j h + m n h, j h + m n h + h]` and `[k h, k h + h]` overlap at most at an endpoint. -/
theorem add_mul_add_h_le_or_le_of_ne {n j k : ℕ} (hj : j < n) (hk : k < n) (hjk : j ≠ k)
    {h : ℝ} (hh : 0 < h) (m : ℤ) :
    j * h + m * (n * h) + h ≤ k * h ∨ k * h + h ≤ j * h + m * (n * h) := by
  have hne : (j : ℤ) + m * n ≠ k := fun he ↦ hjk <| by
    have h0 := Int.eq_zero_of_abs_lt_dvd (m := n) (x := k - j) ⟨m, by rw [← he]; ring⟩
      (abs_sub_lt_iff.2 ⟨by omega, by omega⟩)
    omega
  rcases hne.lt_or_gt with hlt | hlt
  · left
    have : ((j : ℝ) + m * n + 1) * h ≤ k * h :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hlt) hh.le
    linarith
  · right
    have : ((k : ℝ) + 1) * h ≤ (j + m * n) * h :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hlt) hh.le
    linarith

/-- On the half-open cell `[n * h, (n + 1) * h)` of a uniform mesh of step `h > 0`, the floor of
`t / h` equals `n`. -/
theorem floor_div_eq_of_mem_Ico {K : Type*} [DivisionSemiring K] [LinearOrder K]
    [IsStrictOrderedRing K] [FloorSemiring K] {h : K} (hh : 0 < h) {n : ℕ} {t : K}
    (ht : t ∈ Set.Ico ((n : K) * h) (((n + 1 : ℕ) : K) * h)) : ⌊t / h⌋₊ = n := by
  have h1 : (n : K) ≤ t / h := (le_div_iff₀ hh).mpr ht.1
  have h2 : t / h < (n : K) + 1 :=
    (div_lt_iff₀ hh).mpr (by simpa only [Nat.cast_add, Nat.cast_one] using ht.2)
  exact Nat.floor_eq_on_Ico n (t / h) ⟨h1, h2⟩

end TauCeti
