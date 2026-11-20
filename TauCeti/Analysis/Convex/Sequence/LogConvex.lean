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

A real sequence `a` with `a j ^ 2 ≤ c a (j - 1) a (j + 1)` for `0 < j < k` and a constant `c ≥ 1`
is logarithmically convex up to the factor `c`. If `a 0` and `a k` are nonnegative, it is bounded on
`[0, k]` by the geometric interpolation of its end values,

`a j ^ k ≤ c ^ (j (k - j) k) a 0 ^ (k - j) a k ^ j`.

The absolute values `|a j|` satisfy the same inequalities, which reduces the bound to nonnegative
sequences. For positive sequences it is the discrete chord inequality
`TauCeti.IsConvexSeq.chord_inequality` applied to `log (a j) + (log c / 2) j²`, which the
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

/-- The midpoint convexity of a real sequence on `[0, k]` gives the chord inequality from `0` to
`k`. -/
private theorem natCast_mul_le_of_two_mul_le_add {d : ℕ → ℝ} {k : ℕ}
    (h : ∀ j, 0 < j → j < k → 2 * d j ≤ d (j - 1) + d (j + 1)) {j : ℕ} (hj : j ≤ k) :
    (k : ℝ) * d j ≤ (k - j) * d 0 + j * d k := by
  classical
  have hconv : IsConvexSeq (fun n ↦ if n ∈ Set.Iic k then (d n : WithTop ℝ) else ⊤) := by
    refine isConvexSeq_iff_two_mul_le.2 ⟨by simpa [← Set.Iic_def] using Set.ordConnected_Iic,
      fun n _ hn₂ ↦ ?_⟩
    have hn₂' : n + 2 ≤ k := by by_contra h'; simp_all
    simpa [show n ≤ k by omega, show n + 1 ≤ k by omega, hn₂'] using
      h (n + 1) (by omega) (by omega)
  simpa [hj] using hconv.chord_inequality (i := 0) (j := j) (k := k) (by simp) (by simp)
    (Nat.zero_le j) hj

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

/-- The nonnegative case of `TauCeti.pow_le_mul_pow_mul_pow_of_sq_le_mul`. -/
private theorem pow_le_mul_pow_mul_pow_of_sq_le_mul_of_nonneg {a : ℕ → ℝ} {c : ℝ} {k : ℕ}
    (hc : 1 ≤ c) (ha : ∀ j ≤ k, 0 ≤ a j)
    (h : ∀ j, 0 < j → j < k → a j ^ 2 ≤ c * a (j - 1) * a (j + 1)) {j : ℕ} (hj : j ≤ k) :
    a j ^ k ≤ c ^ (j * (k - j) * k) * a 0 ^ (k - j) * a k ^ j := by
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp
  rcases hj.eq_or_lt with rfl | hjk
  · simp
  have hc0 : 0 < c := by linarith
  by_cases hpos : ∀ i ≤ k, 0 < a i
  · -- logarithmic convexity
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
    have hlog : Real.log (a j ^ k) ≤
        Real.log (c ^ (j * (k - j) * k) * a 0 ^ (k - j) * a k ^ j) := by
      rw [Real.log_pow, Real.log_mul (by have := hpos 0 (by omega); positivity)
        (pow_ne_zero _ (hpos k le_rfl).ne'), Real.log_mul (pow_ne_zero _ hc0.ne')
        (pow_ne_zero _ (hpos 0 (by omega)).ne'), Real.log_pow, Real.log_pow, Real.log_pow]
      push_cast [Nat.cast_sub hj]
      have hlc := Real.log_nonneg hc
      have hjk' : (0 : ℝ) ≤ (j : ℝ) * (k - j) * k := by
        have : (j : ℝ) ≤ k := by exact_mod_cast hj
        positivity
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

/-- A sequence that is logarithmically convex up to the factor `c ≥ 1`, in the sense
`a j ^ 2 ≤ c a (j - 1) a (j + 1)` for `0 < j < k`, and nonnegative at the end points `0` and `k`,
is bounded by the geometric interpolation of its end values:
`a j ^ k ≤ c ^ (j (k - j) k) a 0 ^ (k - j) a k ^ j` for `j ≤ k`. -/
theorem pow_le_mul_pow_mul_pow_of_sq_le_mul {a : ℕ → ℝ} {c : ℝ} {k : ℕ} (hc : 1 ≤ c)
    (ha₀ : 0 ≤ a 0) (haₖ : 0 ≤ a k)
    (h : ∀ j, 0 < j → j < k → a j ^ 2 ≤ c * a (j - 1) * a (j + 1)) {j : ℕ} (hj : j ≤ k) :
    a j ^ k ≤ c ^ (j * (k - j) * k) * a 0 ^ (k - j) * a k ^ j := by
  -- the absolute values satisfy the same inequalities and are nonnegative
  have habs := pow_le_mul_pow_mul_pow_of_sq_le_mul_of_nonneg (a := fun i ↦ |a i|) hc
    (fun _ _ ↦ abs_nonneg _) (fun i hi hik ↦ by
      simp only [sq_abs, mul_assoc]
      exact (h i hi hik).trans (by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans (abs_mul _ _).le)
          (by linarith))) hj
  simp only [abs_of_nonneg ha₀, abs_of_nonneg haₖ] at habs
  exact (le_abs_self _).trans ((abs_pow _ _).trans_le habs)

end TauCeti
