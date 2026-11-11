/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.RCLike.Basic

/-!
# Equality in the triangle inequality for a real-valued sum

If a finite sum of real or complex numbers equals the sum of their norms, every summand is
nonnegative real. This detects the common phase of summands after rotating their sum to the
positive real axis, and shows that positively weighted unit complex numbers whose weighted sum has
the maximal absolute value all equal the common phase.

## Main declarations

* `RCLike.eq_norm_of_sum_eq_sum_norm`: a sum equal to the sum of the norms has every summand equal
  to its norm.
* `Complex.eq_of_sum_mul_eq_of_norm_eq_one`: positively weighted unit complex numbers whose
  weighted sum has the maximal absolute value all equal the common phase.
-/

public section

namespace RCLike

/-- If a finite sum equals the sum of the norms of its summands, each summand is its norm. -/
theorem eq_norm_of_sum_eq_sum_norm {𝕜 : Type*} [RCLike 𝕜] {ι : Type*}
    {s : Finset ι} {z : ι → 𝕜} (h : ∑ i ∈ s, z i = ((∑ i ∈ s, ‖z i‖ : ℝ) : 𝕜))
    {i : ι} (hi : i ∈ s) : z i = (‖z i‖ : 𝕜) := by
  have hre : ∑ i ∈ s, re (z i) = ∑ i ∈ s, ‖z i‖ := by
    simpa using congrArg re h
  exact norm_le_re_iff_eq_norm.1 <|
    ((Finset.sum_eq_sum_iff_of_le fun j _ ↦ re_le_norm (z j)).1 hre i hi).ge

end RCLike

namespace Complex

/-- **Weighted unit complex numbers of the maximal sum point the same way.** If the unit complex
numbers `z i`, `i ∈ s`, with positive real weights `d i` have weighted sum `μ₀ * ∑ d i` for a
unit `μ₀`, then every `z i` equals `μ₀`. -/
theorem eq_of_sum_mul_eq_of_norm_eq_one {ι : Type*} {s : Finset ι} {z : ι → ℂ} {d : ι → ℝ}
    {μ₀ : ℂ} (hμ₀ : ‖μ₀‖ = 1) (hd : ∀ i ∈ s, 0 < d i) (hz : ∀ i ∈ s, ‖z i‖ = 1)
    (hsum : ∑ i ∈ s, (d i : ℂ) * z i = μ₀ * ∑ i ∈ s, (d i : ℂ)) :
    ∀ i ∈ s, z i = μ₀ := by
  have hconj : μ₀ * (starRingEnd ℂ) μ₀ = 1 := by
    rw [Complex.mul_conj', hμ₀]
    norm_num
  -- After rotating by `conj μ₀`, the weighted sum is the sum of the norms, so every rotated term
  -- is its own norm.
  have hkey : ∑ i ∈ s, (d i : ℂ) * ((starRingEnd ℂ) μ₀ * z i) = ∑ i ∈ s, (d i : ℂ) := by
    calc ∑ i ∈ s, (d i : ℂ) * ((starRingEnd ℂ) μ₀ * z i)
        = (starRingEnd ℂ) μ₀ * ∑ i ∈ s, (d i : ℂ) * z i := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun _ _ ↦ by ring
      _ = ∑ i ∈ s, (d i : ℂ) := by
          rw [hsum, ← mul_assoc, mul_comm _ μ₀, hconj, one_mul]
  have hnorm : ∀ i ∈ s, ‖(d i : ℂ) * ((starRingEnd ℂ) μ₀ * z i)‖ = d i := fun i hi ↦ by
    rw [norm_mul, norm_mul, Complex.norm_conj, hμ₀, hz i hi, Complex.norm_real,
      Real.norm_of_nonneg (hd i hi).le]
    ring
  intro i hi
  have h := RCLike.eq_norm_of_sum_eq_sum_norm
    (z := fun i ↦ (d i : ℂ) * ((starRingEnd ℂ) μ₀ * z i)) (s := s)
    (by
      rw [hkey, Finset.sum_congr rfl hnorm]
      push_cast
      rfl) hi
  rw [hnorm i hi] at h
  have h1 : (starRingEnd ℂ) μ₀ * z i = 1 :=
    mul_left_cancel₀ (Complex.ofReal_ne_zero.2 (hd i hi).ne') (by simpa using h)
  calc z i = μ₀ * ((starRingEnd ℂ) μ₀ * z i) := by
        rw [← mul_assoc, hconj, one_mul]
    _ = μ₀ := by rw [h1, mul_one]

end Complex
