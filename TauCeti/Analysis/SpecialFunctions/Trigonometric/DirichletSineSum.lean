/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import TauCeti.Algebra.Order.BigOperators.Sum.ByParts

/-!
# Uniform bounds on Dirichlet sine sums

This file proves the classical uniform bound on the partial sums of the sawtooth sine series
`∑ j ∈ Finset.Icc 1 m, sin (j * θ) / j` (the Gibbs–Fejér–Jackson bound).

The argument proceeds in three elementary steps:

* By the telescoping identity `Real.sin_mul_sum_sin`, the unweighted sine sums satisfy
  `|∑ j ∈ Finset.Icc 1 n, sin (j * θ)| ≤ (sin (θ / 2))⁻¹` for `0 < θ < 2 * π`, and hence
  `|∑ j ∈ Finset.Icc 1 n, sin (j * θ)| ≤ π / θ` on `(0, π]` via Jordan's inequality
  (`Real.mul_le_sin`).
* Abel's tail estimate (`TauCeti.abs_sum_Ioc_mul_le`) bounds every tail over `Finset.Ioc K m` by
  `2 * (π / θ) / (K + 1)`.
* For `θ ∈ (0, π]`, splitting `Finset.Icc 1 m` at `K = min m ⌊1 / θ⌋₊` bounds the initial block
  using `|sin (j * θ)| ≤ j * θ` by `1` and the tail by `2 * π`. Reducing an arbitrary real `θ`
  modulo `2 * π` to `[-π, π]` and using oddness gives the global uniform bound `1 + 2 * π`.

## Main results

* `TauCeti.abs_sum_Icc_sin_le_inv_sin_half`: `|∑ j ∈ Icc 1 n, sin (j * θ)| ≤ (sin (θ / 2))⁻¹` for
  `0 < θ < 2 * π`.
* `TauCeti.abs_sum_Icc_sin_le_pi_div`: `|∑ j ∈ Icc 1 n, sin (j * θ)| ≤ π / θ` for `0 < θ ≤ π`.
* `TauCeti.abs_sum_Ioc_sin_div_le`: `|∑ j ∈ Ioc K m, sin (j * θ) / j| ≤ 2 * (π / θ) / (K + 1)`
  for `0 < θ ≤ π`.
* `TauCeti.abs_sum_Icc_sin_div_le`: `|∑ j ∈ Icc 1 m, sin (j * θ) / j| ≤ 1 + 2 * π` for all
  `m : ℕ` and `θ : ℝ`.

## References

* A. Zygmund, *Trigonometric Series*, 3rd ed., Vol. I, Ch. II, §9.
* Y. Katznelson, *An Introduction to Harmonic Analysis*, 3rd ed., Ch. II, §2.
-/

public section

open Real Finset

namespace TauCeti

private theorem sum_range_succ_sin_eq_sum_Icc (θ : ℝ) (n : ℕ) :
    ∑ i ∈ range (n + 1), sin (i * θ) = ∑ j ∈ Icc 1 n, sin (j * θ) := by
  rw [sum_range_eq_add_Ico _ n.succ_pos]
  simp [Ico_add_one_right_eq_Icc]

/-- For `0 < θ < 2 * π`, the unweighted sine sum `∑ j ∈ Icc 1 n, sin (j * θ)` is bounded in
absolute value by `(sin (θ / 2))⁻¹`. -/
theorem abs_sum_Icc_sin_le_inv_sin_half {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ < 2 * π) (n : ℕ) :
    |∑ j ∈ Icc 1 n, sin (j * θ)| ≤ (sin (θ / 2))⁻¹ := by
  have hsin_pos : 0 < sin (θ / 2) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hsum : ∑ i ∈ range (n + 1), sin (θ * i + 0) = ∑ j ∈ Icc 1 n, sin (j * θ) := by
    simp only [add_zero, mul_comm θ]
    exact sum_range_succ_sin_eq_sum_Icc θ n
  have hmul : sin (θ / 2) * ∑ j ∈ Icc 1 n, sin (j * θ) =
      sin ((n + 1 : ℕ) * θ / 2) * sin (((n + 1 : ℕ) - 1) * θ / 2 + 0) := by
    rw [← hsum, sin_mul_sum_sin]
  have habs : sin (θ / 2) * |∑ j ∈ Icc 1 n, sin (j * θ)| ≤ 1 := by
    rw [← abs_of_pos hsin_pos, ← abs_mul, hmul, abs_mul]
    exact (mul_le_mul (abs_sin_le_one _) (abs_sin_le_one _) (abs_nonneg _) zero_le_one).trans_eq
      (one_mul 1)
  calc |∑ j ∈ Icc 1 n, sin (j * θ)|
      = (sin (θ / 2))⁻¹ * (sin (θ / 2) * |∑ j ∈ Icc 1 n, sin (j * θ)|) := by
        rw [inv_mul_cancel_left₀ hsin_pos.ne']
    _ ≤ (sin (θ / 2))⁻¹ * 1 := by gcongr
    _ = (sin (θ / 2))⁻¹ := mul_one _

/-- For `0 < θ ≤ π`, the unweighted sine sum `∑ j ∈ Icc 1 n, sin (j * θ)` is bounded in absolute
value by `π / θ`, combining `abs_sum_Icc_sin_le_inv_sin_half` with Jordan's inequality. -/
theorem abs_sum_Icc_sin_le_pi_div {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ ≤ π) (n : ℕ) :
    |∑ j ∈ Icc 1 n, sin (j * θ)| ≤ π / θ := by
  have hsin_ge : θ / π ≤ sin (θ / 2) :=
    calc θ / π = 2 / π * (θ / 2) := by ring
      _ ≤ sin (θ / 2) := mul_le_sin (by positivity) (by linarith)
  calc |∑ j ∈ Icc 1 n, sin (j * θ)|
      ≤ (sin (θ / 2))⁻¹ := abs_sum_Icc_sin_le_inv_sin_half hθ0 (by linarith [pi_pos]) n
    _ ≤ (θ / π)⁻¹ := inv_anti₀ (by positivity) hsin_ge
    _ = π / θ := inv_div θ π

/-- **Summation-by-parts tail bound.** For `0 < θ ≤ π` and any `K, m : ℕ`, the tail of the
sawtooth sine series over `Ioc K m` has absolute value at most `2 * (π / θ) / (K + 1)`. -/
theorem abs_sum_Ioc_sin_div_le {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ ≤ π) (K m : ℕ) :
    |∑ j ∈ Ioc K m, sin (j * θ) / j| ≤ 2 * (π / θ) / (K + 1 : ℝ) := by
  have hG (n : ℕ) : |∑ i ∈ range n, sin (i * θ)| ≤ π / θ := by
    cases n with
    | zero =>
      simp only [range_zero, sum_empty, abs_zero]
      positivity
    | succ n =>
      rw [sum_range_succ_sin_eq_sum_Icc]
      exact abs_sum_Icc_sin_le_pi_div hθ0 hθ n
  have habel := abs_sum_Ioc_mul_le (f := fun j : ℕ ↦ (j : ℝ)⁻¹)
    (g := fun j : ℕ ↦ sin (j * θ)) (B := π / θ) (K := K) (m := m)
    (by positivity) (fun _ ↦ by positivity)
    (fun j hj ↦ inv_anti₀ (Nat.cast_pos.mpr (by grind)) (by exact_mod_cast Nat.le_succ j))
    (by positivity) (fun n _ ↦ hG n)
  calc |∑ j ∈ Ioc K m, sin (j * θ) / j|
      = |∑ j ∈ Ioc K m, (j : ℝ)⁻¹ * sin (j * θ)| := by
        congr 1
        exact sum_congr rfl fun j _ ↦ by rw [div_eq_inv_mul]
    _ ≤ 2 * ((K + 1 : ℕ) : ℝ)⁻¹ * (π / θ) := habel
    _ = 2 * (π / θ) / (K + 1 : ℝ) := by push_cast; ring

/-- **Uniform Gibbs–Fejér bound on `(0, π]`.** -/
private theorem abs_sum_Icc_sin_div_le_of_pos_of_le_pi (m : ℕ) {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ ≤ π) :
    |∑ j ∈ Icc 1 m, sin (j * θ) / j| ≤ 1 + 2 * π := by
  set K := min m ⌊1 / θ⌋₊
  have hsplit : ∑ j ∈ Icc 1 m, sin (j * θ) / j =
      (∑ j ∈ Icc 1 K, sin (j * θ) / j) + ∑ j ∈ Ioc K m, sin (j * θ) / j := by
    rw [← zero_add 1, Icc_add_one_left_eq_Ioc, Icc_add_one_left_eq_Ioc,
      sum_Ioc_consecutive _ (Nat.zero_le K) (min_le_left m _)]
  rw [hsplit]
  have hhead : |∑ j ∈ Icc 1 K, sin (j * θ) / j| ≤ 1 := by
    calc |∑ j ∈ Icc 1 K, sin (j * θ) / j|
        ≤ ∑ j ∈ Icc 1 K, |sin (j * θ) / j| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ Icc 1 K, θ := by
          refine sum_le_sum fun j hj ↦ ?_
          have hj_pos : (0 : ℝ) < j := Nat.cast_pos.mpr (mem_Icc.mp hj).1
          rw [abs_div, abs_of_pos hj_pos]
          calc |sin (j * θ)| / j
              ≤ |↑j * θ| / j := div_le_div_of_nonneg_right abs_sin_le_abs hj_pos.le
            _ = (j * θ) / j := by rw [abs_of_pos (mul_pos hj_pos hθ0)]
            _ = θ := mul_div_cancel_left₀ θ hj_pos.ne'
      _ = K * θ := by simp
      _ ≤ (⌊1 / θ⌋₊ : ℝ) * θ := by
          gcongr
          exact_mod_cast min_le_right m _
      _ ≤ (1 / θ) * θ := by
          gcongr
          exact Nat.floor_le (by positivity)
      _ = 1 := one_div_mul_cancel hθ0.ne'
  have htail : |∑ j ∈ Ioc K m, sin (j * θ) / j| ≤ 2 * π := by
    by_cases hKm : K < m
    · have hKeq : K = ⌊1 / θ⌋₊ := by
        have : ¬ m ≤ ⌊1 / θ⌋₊ := fun h ↦ by simp [K, min_eq_left h] at hKm
        exact min_eq_right (le_of_not_ge this)
      have hK_gt : 1 / θ < (K : ℝ) + 1 := by
        rw [hKeq]
        exact Nat.lt_floor_add_one (1 / θ)
      refine (abs_sum_Ioc_sin_div_le hθ0 hθ K m).trans ?_
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < K + 1)]
      have hmul : 1 / θ * θ ≤ ((K : ℝ) + 1) * θ := by gcongr
      rw [one_div_mul_cancel hθ0.ne'] at hmul
      calc 2 * (π / θ) = 2 * π * (1 / θ) := by ring
        _ ≤ 2 * π * (K + 1) := by gcongr
    · rw [Ioc_eq_empty hKm, sum_empty, abs_zero]
      positivity
  exact (abs_add_le _ _).trans (add_le_add hhead htail)

/-- **Uniform bound on the Dirichlet sine sums.** For every `m : ℕ` and every real `θ`,
`|∑ j ∈ Finset.Icc 1 m, sin (j * θ) / j| ≤ 1 + 2 * π`. -/
theorem abs_sum_Icc_sin_div_le (m : ℕ) (θ : ℝ) :
    |∑ j ∈ Icc 1 m, sin (j * θ) / j| ≤ 1 + 2 * π := by
  -- Shift `θ` by periodicity into `[-π, π)`.
  have hper : Function.Periodic (fun x : ℝ ↦ ∑ j ∈ Icc 1 m, sin (j * x) / j) (2 * π) := by
    intro x
    refine sum_congr rfl fun j _ ↦ ?_
    rw [mul_add, (sin_periodic.nat_mul j) (j * x)]
  obtain ⟨θ', hmem, hshift⟩ := hper.exists_mem_Ico two_pi_pos θ (-π)
  have habs : |θ'| ≤ π := abs_le.mpr ⟨hmem.1, by linarith [hmem.2]⟩
  rw [hshift]
  rcases lt_trichotomy θ' 0 with hneg | hzero | hpos
  · have hneg_sum : ∑ j ∈ Icc 1 m, sin (j * θ') / j =
        -(∑ j ∈ Icc 1 m, sin (j * (-θ')) / j) := by
      rw [← sum_neg_distrib]
      refine sum_congr rfl fun j _ ↦ ?_
      rw [mul_neg, sin_neg, neg_div, neg_neg]
    rw [hneg_sum, abs_neg]
    exact abs_sum_Icc_sin_div_le_of_pos_of_le_pi m (neg_pos.mpr hneg)
      ((abs_of_neg hneg) ▸ habs)
  · rw [hzero]
    simp only [mul_zero, sin_zero, zero_div, sum_const_zero, abs_zero]
    positivity
  · exact abs_sum_Icc_sin_div_le_of_pos_of_le_pi m hpos ((abs_of_pos hpos) ▸ habs)

end TauCeti
