/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import TauCeti.Analysis.Contour.Argument.Lift
import TauCeti.Analysis.Contour.LogDerivFTC
import TauCeti.Analysis.Contour.Winding.Number.AbsolutelyContinuous

/-!
# The index integral as a sum of segment logarithm increments

Given an absolutely continuous curve `γ` on `[a, b]` and a monotone partition
`a = s 0 ≤ ⋯ ≤ s N = b` fine enough that on each segment the normalized ratio
`(γ t - w) / (γ (s j) - w)` stays in `Complex.slitPlane`, the winding integral splits into a sum of
per-segment logarithm increments:

`∫ t in a..b, (γ t - w)⁻¹ * deriv γ t = ∑ j < N, Complex.log ((γ (s (j+1)) - w) / (γ (s j) - w))`.

The per-segment slit-plane hypothesis is exactly the data the continuous argument-lift partition
supplies, so this evaluation bridges that partition to the winding-number computation: for a
closed curve the real parts of these increments telescope away and the imaginary parts sum to the
total argument change.

## Main results

* `AbsolutelyContinuousOnInterval.integral_inv_sub_mul_deriv_eq_sum_log` — the partition sum.
* `AbsolutelyContinuousOnInterval.integral_inv_sub_mul_deriv_eq_log_norm_add_I_mul_sum_log_im` —
  its real/imaginary refinement: a real logarithm-of-modulus increment plus `I` times the
  imaginary part of the segment logarithm sum.
* `AbsolutelyContinuousOnInterval.re_integral_inv_sub_mul_deriv_eq_log_norm` — the real part of the
  index integral of an arc avoiding the point is the log-norm difference of its endpoints, with no
  slit-plane hypothesis.

## Provenance

Adapted from `contourIntegral_inv_eq_sum_log_segRatio` in `WindingArgDiff.lean` of the AINTLIB
`LeanModularForms` development, restated for a raw `γ : ℝ → ℂ` on `[a, b]`.
-/

public section

open Complex MeasureTheory Set intervalIntegral TauCeti.Contour

open scoped Interval

namespace AbsolutelyContinuousOnInterval

/-- **Index integral as a sum of segment logarithm increments.** For an absolutely continuous
curve `γ` on `[a, b]` and a monotone partition `a = s 0 ≤ ⋯ ≤ s N = b` with the normalized segment
ratio `(γ t - w) / (γ (s j) - w)` in `Complex.slitPlane` on each `[s j, s (j+1)]`, the winding
integrand integrates to the sum of the per-segment `Complex.log` increments. -/
theorem integral_inv_sub_mul_deriv_eq_sum_log {γ : ℝ → ℂ} {w : ℂ} {a b : ℝ} {N : ℕ}
    {s : ℕ → ℝ} (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hs_zero : s 0 = a) (hs_N : s N = b) (hs_mono : Monotone s)
    (h_slit : ∀ j, j < N → ∀ t ∈ Icc (s j) (s (j + 1)), (γ t - w) / (γ (s j) - w) ∈ slitPlane) :
    ∫ t in a..b, (γ t - w)⁻¹ * deriv γ t
      = ∑ j ∈ Finset.range N, Complex.log ((γ (s (j + 1)) - w) / (γ (s j) - w)) := by
  have hab : a ≤ b := by have := hs_mono (Nat.zero_le N); rwa [hs_zero, hs_N] at this
  have hs_in : ∀ j ≤ N, s j ∈ uIcc a b := fun j hj ↦ by
    rw [uIcc_of_le hab]
    exact ⟨by rw [← hs_zero]; exact hs_mono (Nat.zero_le j), by rw [← hs_N]; exact hs_mono hj⟩
  have hmono_seg : ∀ j, s j ≤ s (j + 1) := fun j ↦ hs_mono (Nat.le_succ j)
  have hseg : ∀ k < N, AbsolutelyContinuousOnInterval γ (s k) (s (k + 1)) := fun k hk ↦
    hγ.mono (uIcc_subset_uIcc (hs_in k hk.le) (hs_in (k + 1) hk))
  have hslit_seg : ∀ k < N, ∀ t ∈ uIcc (s k) (s (k + 1)),
      (γ t - w) / (γ (s k) - w) ∈ slitPlane := fun k hk ↦ by
    rw [uIcc_of_le (hmono_seg k)]
    exact h_slit k hk
  have h_int_seg : ∀ k < N,
      IntervalIntegrable (fun t ↦ (γ t - w)⁻¹ * deriv γ t) volume (s k) (s (k + 1)) :=
    fun k hk ↦ (hseg k hk).intervalIntegrable_inv_sub_mul_deriv fun ⟨t, ht, h⟩ ↦
      zero_notMem_slitPlane (by simpa [h] using hslit_seg k hk t ht)
  rw [← hs_zero, ← hs_N, ← sum_integral_adjacent_intervals h_int_seg]
  exact Finset.sum_congr rfl fun j hj ↦
    (hseg j (Finset.mem_range.mp hj)).integral_inv_sub_mul_deriv_eq_log
      (hslit_seg j (Finset.mem_range.mp hj))

/-- **Real/imaginary decomposition of the index integral.** Refining
`AbsolutelyContinuousOnInterval.integral_inv_sub_mul_deriv_eq_sum_log`, over the same
slit-compatible monotone partition the winding integral splits into a real
logarithm-of-modulus increment `Real.log ‖γ b - w‖ - Real.log ‖γ a - w‖` plus `I` times the
imaginary part of the segment logarithm sum. For a closed curve the real increment vanishes,
isolating the total argument change. -/
theorem integral_inv_sub_mul_deriv_eq_log_norm_add_I_mul_sum_log_im {γ : ℝ → ℂ} {w : ℂ}
    {a b : ℝ} {N : ℕ} {s : ℕ → ℝ} (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hs_zero : s 0 = a) (hs_N : s N = b) (hs_mono : Monotone s)
    (h_slit : ∀ j, j < N → ∀ t ∈ Icc (s j) (s (j + 1)), (γ t - w) / (γ (s j) - w) ∈ slitPlane) :
    ∫ t in a..b, (γ t - w)⁻¹ * deriv γ t
      = ((Real.log ‖γ b - w‖ - Real.log ‖γ a - w‖ : ℝ) : ℂ)
        + Complex.I * ((∑ j ∈ Finset.range N,
            (Complex.log ((γ (s (j + 1)) - w) / (γ (s j) - w))).im : ℝ) : ℂ) := by
  rw [hγ.integral_inv_sub_mul_deriv_eq_sum_log hs_zero hs_N hs_mono h_slit]
  have hmono_seg : ∀ j, s j ≤ s (j + 1) := fun j ↦ hs_mono (Nat.le_succ j)
  have hne : ∀ j, j < N → γ (s j) - w ≠ 0 ∧ γ (s (j + 1)) - w ≠ 0 := fun j hj ↦
    ⟨(div_ne_zero_iff.mp (slitPlane_ne_zero
        (h_slit j hj (s j) (left_mem_Icc.mpr (hmono_seg j))))).1,
      (div_ne_zero_iff.mp (slitPlane_ne_zero
        (h_slit j hj (s (j + 1)) (right_mem_Icc.mpr (hmono_seg j))))).1⟩
  apply Complex.ext
  · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
    rw [Complex.re_sum]
    calc ∑ j ∈ Finset.range N, (Complex.log ((γ (s (j + 1)) - w) / (γ (s j) - w))).re
        = ∑ j ∈ Finset.range N, (Real.log ‖γ (s (j + 1)) - w‖ - Real.log ‖γ (s j) - w‖) := by
          refine Finset.sum_congr rfl fun j hj ↦ ?_
          rw [Finset.mem_range] at hj
          rw [Complex.log_re, norm_div,
            Real.log_div (norm_ne_zero_iff.mpr (hne j hj).2) (norm_ne_zero_iff.mpr (hne j hj).1)]
      _ = Real.log ‖γ (s N) - w‖ - Real.log ‖γ (s 0) - w‖ :=
          Finset.sum_range_sub (fun j ↦ Real.log ‖γ (s j) - w‖) N
      _ = Real.log ‖γ b - w‖ - Real.log ‖γ a - w‖ := by rw [hs_N, hs_zero]
  · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, zero_mul, zero_add, one_mul]
    exact Complex.im_sum _ _

/-- **The real part of the index integral of an arc is the log-norm difference of its
endpoints.** For an absolutely continuous curve `γ` on `[[l, u]]` avoiding `s`, the real part of
`∫ t in l..u, (γ t - s)⁻¹ * deriv γ t` is `Real.log ‖γ u - s‖ - Real.log ‖γ l - s‖`, with no
slit-plane hypothesis and for either order of `l` and `u`. -/
theorem re_integral_inv_sub_mul_deriv_eq_log_norm {γ : ℝ → ℂ} {s : ℂ} {l u : ℝ}
    (hγ : AbsolutelyContinuousOnInterval γ l u) (h_ne : ∀ t ∈ uIcc l u, γ t ≠ s) :
    (∫ t in l..u, (γ t - s)⁻¹ * deriv γ t).re = Real.log ‖γ u - s‖ - Real.log ‖γ l - s‖ := by
  wlog hlu : l ≤ u generalizing l u
  · rw [intervalIntegral.integral_symm, Complex.neg_re,
      this hγ.symm (uIcc_comm l u ▸ h_ne) (le_of_not_ge hlu), neg_sub]
  -- Taking real parts of the decomposition over the partition that
  -- `exists_continuousOn_arg_lift_with_partition` supplies discards its imaginary term.
  obtain ⟨N, part, -, hpart_zero, hpart_N, hpart_mono, -, -, h_slit, -, -⟩ :=
    exists_continuousOn_arg_lift_with_partition hlu (uIcc_of_le hlu ▸ hγ.continuousOn)
      (uIcc_of_le hlu ▸ h_ne)
  have heq := hγ.integral_inv_sub_mul_deriv_eq_log_norm_add_I_mul_sum_log_im hpart_zero hpart_N
    hpart_mono h_slit
  simp [heq]

end AbsolutelyContinuousOnInterval
