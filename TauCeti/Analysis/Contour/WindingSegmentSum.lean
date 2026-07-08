module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import TauCeti.Analysis.Contour.LogDerivFTC

/-!
# The index integral as a sum of segment logarithm increments

Given a monotone partition `a = s 0 ≤ ⋯ ≤ s N = b` fine enough that on each segment the normalized
ratio `(γ t - w) / (γ (s j) - w)` stays in `Complex.slitPlane`, the index integral splits into a sum
of per-segment logarithm increments:

`∫ t in a..b, (γ t - w)⁻¹ * deriv γ t = ∑ j < N, Complex.log ((γ (s (j+1)) - w) / (γ (s j) - w))`.

The proof splits the integral over the partition with `sum_integral_adjacent_intervals` and
evaluates each segment with the per-segment logarithmic-derivative FTC
`integral_inv_sub_mul_deriv_eq_log`; the slit-plane hypothesis on each segment is exactly what the
argument-lift partition supplies. This is the first half of showing the winding number of a closed
curve is an integer: for a closed curve the real parts of these increments telescope away and the
imaginary parts sum to the total argument change.

## Provenance

Adapted from `contourIntegral_inv_eq_sum_log_segRatio` in `WindingArgDiff.lean` of the AINTLIB
`LeanModularForms` development.
-/

public section

open Complex MeasureTheory Set intervalIntegral

open scoped Interval

namespace TauCeti.Contour

/-- **Index integral as a sum of segment logarithm increments.** For a monotone partition
`a = s 0 ≤ ⋯ ≤ s N = b` of `[a, b]` with `γ` continuous there, differentiable off a countable set
`P`, avoiding `w` at each node, and with the normalized segment ratio `(γ t - w) / (γ (s j) - w)` in
`Complex.slitPlane` on each `[s j, s (j+1)]`, the index integral of `(γ t - w)⁻¹ * deriv γ t` equals
the sum of the per-segment `Complex.log` increments. -/
theorem integral_inv_sub_mul_deriv_eq_sum_log {γ : ℝ → ℂ} {w : ℂ} {a b : ℝ} {P : Set ℝ}
    {N : ℕ} {s : ℕ → ℝ} (hP : P.Countable)
    (hs_zero : s 0 = a) (hs_N : s N = b) (hs_mono : Monotone s)
    (hs_in : ∀ j ≤ N, s j ∈ Icc a b) (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_diff : ∀ t ∈ Ioo a b \ P, DifferentiableAt ℝ γ t)
    (h_slit : ∀ j, j < N → ∀ t ∈ Icc (s j) (s (j + 1)),
      (γ t - w) / (γ (s j) - w) ∈ slitPlane)
    (h_int : IntervalIntegrable (fun t ↦ (γ t - w)⁻¹ * deriv γ t) volume a b) :
    ∫ t in a..b, (γ t - w)⁻¹ * deriv γ t
      = ∑ j ∈ Finset.range N, Complex.log ((γ (s (j + 1)) - w) / (γ (s j) - w)) := by
  have hab : a ≤ b := by have := hs_mono (Nat.zero_le N); rwa [hs_zero, hs_N] at this
  have hmono_seg : ∀ j, s j ≤ s (j + 1) := fun j ↦ hs_mono (Nat.le_succ j)
  have h_int_seg : ∀ k < N,
      IntervalIntegrable (fun t ↦ (γ t - w)⁻¹ * deriv γ t) volume (s k) (s (k + 1)) := by
    intro k hk
    refine h_int.mono_set ?_
    rw [uIcc_of_le (hmono_seg k), uIcc_of_le hab]
    exact Icc_subset_Icc (hs_in k hk.le).1 (hs_in (k + 1) hk).2
  rw [← hs_zero, ← hs_N, ← sum_integral_adjacent_intervals h_int_seg]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [Finset.mem_range] at hj
  refine integral_inv_sub_mul_deriv_eq_log hP ?_ ?_ ?_ (h_int_seg j hj)
  · rw [uIcc_of_le (hmono_seg j)]
    exact hγ_cont.mono (Icc_subset_Icc (hs_in j hj.le).1 (hs_in (j + 1) hj).2)
  · intro t ht
    rw [min_eq_left (hmono_seg j), max_eq_right (hmono_seg j)] at ht
    refine hγ_diff t ⟨⟨(hs_in j hj.le).1.trans_lt ht.1.1, ?_⟩, ht.2⟩
    exact ht.1.2.trans_le (hs_in (j + 1) hj).2
  · rw [uIcc_of_le (hmono_seg j)]
    exact h_slit j hj

end TauCeti.Contour
