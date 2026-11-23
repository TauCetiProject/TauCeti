/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import TauCeti.Analysis.Convex.Sequence.Basic

/-!
# Logarithmically convex sequences

A real sequence `a` with `a j ^ 2 ≤ c a (j - 1) a (j + 1)` for `0 < j < k` and a constant `c ≥ 0`
is logarithmically convex up to the factor `c`. If `a 0` and `a k` are nonnegative, it is bounded on
`[0, k]` by the geometric interpolation of its end values,

`a j ^ k ≤ c ^ (j (k - j) k / 2) a 0 ^ (k - j) a k ^ j`,

where the division by `2` is exact.

The absolute values `|a j|` satisfy the same inequalities, which reduces the bound to nonnegative
sequences. For positive sequences it is the discrete chord inequality
`TauCeti.natCast_mul_le_of_two_mul_le_add` applied to `log (a j) + (log c / 2) j²`, which the
hypothesis makes convex. A vanishing term forces every interior term to vanish, since the
hypothesis spreads zeros to both neighbours.

This is the form in which interpolation inequalities
`‖D^j u‖ ≤ C ‖u‖ ^ (1 - j / k) ‖D^k u‖ ^ (j / k)` for intermediate derivatives follow from a
one-step inequality `‖D^j u‖ ^ 2 ≤ C ‖D^(j-1) u‖ ‖D^(j+1) u‖`.

## Main results

* `TauCeti.pow_le_mul_pow_mul_pow_of_sq_le_mul`: the geometric interpolation bound.
-/

public section

namespace TauCeti

/-- If `a i ^ 2 ≤ c a (i - 1) a (i + 1)` for `0 < i < k`, a vanishing term `a m = 0`, `m ≤ k`,
forces every interior term `a j`, `0 < j < k`, to vanish. -/
private theorem eq_zero_of_sq_le_mul {a : ℕ → ℝ} {c : ℝ} {k m : ℕ} (ham : 0 ≤ a m)
    (h : ∀ j, 0 < j → j < k → a j ^ 2 ≤ c * a (j - 1) * a (j + 1)) (hmk : m ≤ k) (hm : a m ≤ 0)
    {j : ℕ} (hj0 : 0 < j) (hjk : j < k) : a j = 0 := by
  have hm0 : a m = 0 := le_antisymm hm ham
  have hspread : ∀ i, 0 < i → i < k → (a (i - 1) = 0 ∨ a (i + 1) = 0) → a i = 0 := by
    intro i hi hik hn
    have := h i hi hik
    rcases hn with hn | hn <;> simpa [hn] using this
  rcases le_or_gt m j with hmj | hjm
  · have hup : ∀ i, m ≤ i → i < k → a i = 0 := by
      intro i hmi
      induction i, hmi using Nat.le_induction with
      | base => exact fun _ ↦ hm0
      | succ i _ ih =>
        exact fun hik ↦ hspread _ (by omega) hik (Or.inl (by simpa using ih (by omega)))
    exact hup j hmj hjk
  · exact Nat.decreasingInduction (motive := fun i _ ↦ 0 < i → a i = 0)
      (fun i him ih hi ↦ hspread i hi (by omega) (Or.inr (ih (by omega))))
      (fun _ ↦ hm0) hjm.le hj0

/-- `j (k - j) k` is even, so that `c ^ (j (k - j) k / 2)` is an exact square root. -/
private theorem two_dvd_mul_sub_mul (j k : ℕ) : 2 ∣ j * (k - j) * k := by
  rcases Nat.even_or_odd j with hj | hj
  · exact ((hj.mul_right _).mul_right _).two_dvd
  rcases Nat.even_or_odd k with hk | hk
  · exact (hk.mul_left _).two_dvd
  · exact (((Nat.Odd.sub_odd hk hj).mul_left _).mul_right _).two_dvd

/-- The nonnegative case of `TauCeti.pow_le_mul_pow_mul_pow_of_sq_le_mul`. -/
private theorem pow_le_mul_pow_mul_pow_of_sq_le_mul_of_nonneg {a : ℕ → ℝ} {c : ℝ} {k : ℕ}
    (hc : 0 ≤ c) (ha : ∀ j ≤ k, 0 ≤ a j)
    (h : ∀ j, 0 < j → j < k → a j ^ 2 ≤ c * a (j - 1) * a (j + 1)) {j : ℕ} (hj : j ≤ k) :
    a j ^ k ≤ c ^ (j * (k - j) * k / 2) * a 0 ^ (k - j) * a k ^ j := by
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp
  rcases hj.eq_or_lt with rfl | hjk
  · simp
  by_cases hpos : ∀ i ≤ k, 0 < a i
  · -- logarithmic convexity; the hypothesis at `j` forces `0 < c`
    have hc0 : 0 < c := hc.lt_of_ne fun hc0 ↦ by
      have := h j hj0 hjk
      rw [← hc0, zero_mul, zero_mul] at this
      exact absurd this (not_le.2 (pow_pos (hpos j hj) 2))
    set γ := Real.log c / 2
    have hconv := natCast_mul_le_of_two_mul_le_add (d := fun i ↦ Real.log (a i) + γ * i ^ 2)
      (k := k) (fun i hi hik ↦ by
        have h' := Real.log_le_log (by have := hpos i hik.le; positivity) (h i hi hik)
        rw [Real.log_pow, Real.log_mul (by have := hpos (i - 1) (by omega); positivity)
          (hpos (i + 1) (by omega)).ne', Real.log_mul hc0.ne' (hpos (i - 1) (by omega)).ne'] at h'
        push_cast [Nat.cast_sub hi] at h' ⊢
        simp only [γ]
        nlinarith) hj
    simp only [Nat.cast_zero, zero_pow two_ne_zero, mul_zero, add_zero] at hconv
    have hexp : ((j * (k - j) * k / 2 : ℕ) : ℝ) = j * (k - j) * k / 2 := by
      rw [Nat.cast_div (two_dvd_mul_sub_mul j k) two_ne_zero]
      push_cast [Nat.cast_sub hj]
      ring
    have hlog : Real.log (a j ^ k) ≤
        Real.log (c ^ (j * (k - j) * k / 2) * a 0 ^ (k - j) * a k ^ j) := by
      rw [Real.log_pow, Real.log_mul (by have := hpos 0 (by omega); positivity)
        (pow_ne_zero _ (hpos k le_rfl).ne'), Real.log_mul (pow_ne_zero _ hc0.ne')
        (pow_ne_zero _ (hpos 0 (by omega)).ne'), Real.log_pow, Real.log_pow, Real.log_pow, hexp]
      push_cast [Nat.cast_sub hj]
      simp only [γ] at hconv
      nlinarith
    exact (Real.log_le_log_iff (pow_pos (hpos j hj) k) (by
      have := hpos 0 (by omega); have := hpos k le_rfl; positivity)).1 hlog
  · -- a vanishing term forces all interior terms to vanish
    push Not at hpos
    obtain ⟨m, hmk, hm⟩ := hpos
    rw [eq_zero_of_sq_le_mul (ha m hmk) h hmk hm hj0 hjk, zero_pow (by omega)]
    have := ha 0 (by omega); have := ha k le_rfl
    positivity

/-- A sequence that is logarithmically convex up to the factor `c ≥ 0`, in the sense
`a j ^ 2 ≤ c a (j - 1) a (j + 1)` for `0 < j < k`, and nonnegative at the end points `0` and `k`,
is bounded by the geometric interpolation of its end values:
`a j ^ k ≤ c ^ (j (k - j) k / 2) a 0 ^ (k - j) a k ^ j` for `j ≤ k`. The division by `2` is exact,
since `j (k - j) k` is even. -/
theorem pow_le_mul_pow_mul_pow_of_sq_le_mul {a : ℕ → ℝ} {c : ℝ} {k : ℕ} (hc : 0 ≤ c)
    (ha₀ : 0 ≤ a 0) (haₖ : 0 ≤ a k)
    (h : ∀ j, 0 < j → j < k → a j ^ 2 ≤ c * a (j - 1) * a (j + 1)) {j : ℕ} (hj : j ≤ k) :
    a j ^ k ≤ c ^ (j * (k - j) * k / 2) * a 0 ^ (k - j) * a k ^ j := by
  -- the absolute values satisfy the same inequalities and are nonnegative
  have habs := pow_le_mul_pow_mul_pow_of_sq_le_mul_of_nonneg (a := fun i ↦ |a i|) hc
    (fun _ _ ↦ abs_nonneg _) (fun i hi hik ↦ by
      simp only [sq_abs, mul_assoc]
      exact (h i hi hik).trans (by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans (abs_mul _ _).le) hc)) hj
  simp only [abs_of_nonneg ha₀, abs_of_nonneg haₖ] at habs
  exact (le_abs_self _).trans ((abs_pow _ _).trans_le habs)

end TauCeti
