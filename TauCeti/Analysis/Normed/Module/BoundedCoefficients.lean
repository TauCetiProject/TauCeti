/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic

/-!
# Finite sums with bounded coefficients

Let `v` be a family of vectors in a real or complex normed space such that every subsum
`∑ i ∈ u, v i` over a subset `u` of a finite set `s` has norm at most `S`. Then bounded
coefficients change the norm of `∑ i ∈ s, a i • v i` by a bounded factor:

* `TauCeti.norm_sum_ofReal_smul_le_of_nonneg`: real coefficients in `[0, t]` give `t * S`;
* `TauCeti.norm_sum_ofReal_smul_le_two_mul`: real coefficients of absolute value at most `t`
  give `2 * t * S`;
* `TauCeti.norm_sum_smul_le_four_mul`: scalar coefficients of norm at most `t` give `4 * t * S`.

The first estimate peels off the smallest coefficient, which multiplies the full sum; the others
split coefficients into positive and negative parts and into real and imaginary parts. These are
the estimates by which the coordinate projections of an unconditional basis control its bounded
coordinate multipliers.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, Section 3.1.
-/

public section

namespace TauCeti

variable {ι 𝕜 E : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  {v : ι → E} {s : Finset ι} {S t : ℝ}

/-- If every subsum of `v` over a subset of `s` has norm at most `S`, then a combination of the
`v i` with real coefficients in `[0, t]` has norm at most `t * S`. -/
theorem norm_sum_ofReal_smul_le_of_nonneg (hS : ∀ u ⊆ s, ‖∑ i ∈ u, v i‖ ≤ S) (ht : 0 ≤ t)
    {a : ι → ℝ} (ha₀ : ∀ i ∈ s, 0 ≤ a i) (ha : ∀ i ∈ s, a i ≤ t) :
    ‖∑ i ∈ s, (a i : 𝕜) • v i‖ ≤ t * S := by
  classical
  induction s using Finset.strongInduction generalizing a t with
  | H s ih =>
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simpa using mul_nonneg ht (by simpa using hS ∅ (Finset.empty_subset _))
  -- Peel off the smallest coefficient `a j`, which multiplies the full sum; the remaining
  -- coefficients lie in `[0, t - a j]` and are supported on `s.erase j`.
  obtain ⟨j, hj, hmin⟩ := s.exists_min_image a hs
  have hsplit : ∑ i ∈ s, (a i : 𝕜) • v i =
      (a j : 𝕜) • ∑ i ∈ s, v i + ∑ i ∈ s.erase j, ((a i - a j : ℝ) : 𝕜) • v i := by
    rw [Finset.sum_erase _ (by simp), Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [RCLike.ofReal_sub, sub_smul, add_sub_cancel]
  have hrest := ih (s.erase j) (Finset.erase_ssubset hj)
    (fun u hu ↦ hS u (hu.trans (Finset.erase_subset _ _))) (sub_nonneg.2 (ha j hj))
    (fun i hi ↦ sub_nonneg.2 (hmin i (Finset.mem_of_mem_erase hi)))
    (fun i hi ↦ sub_le_sub_right (ha i (Finset.mem_of_mem_erase hi)) _)
  calc
    ‖∑ i ∈ s, (a i : 𝕜) • v i‖ ≤ a j * S + (t - a j) * S := by
      rw [hsplit]
      refine (norm_add_le _ _).trans (add_le_add ?_ hrest)
      rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg (ha₀ j hj)]
      exact mul_le_mul_of_nonneg_left (hS s subset_rfl) (ha₀ j hj)
    _ = t * S := by ring

/-- If every subsum of `v` over a subset of `s` has norm at most `S`, then a combination of the
`v i` with real coefficients of absolute value at most `t` has norm at most `2 * t * S`. -/
theorem norm_sum_ofReal_smul_le_two_mul (hS : ∀ u ⊆ s, ‖∑ i ∈ u, v i‖ ≤ S) (ht : 0 ≤ t)
    {a : ι → ℝ} (ha : ∀ i ∈ s, |a i| ≤ t) :
    ‖∑ i ∈ s, (a i : 𝕜) • v i‖ ≤ 2 * t * S := by
  -- Split each coefficient into its positive and negative parts, both in `[0, t]`.
  have hpos (i : ι) (hi : i ∈ s) : (a i)⁺ ≤ t :=
    (le_add_of_nonneg_right (negPart_nonneg (a i))).trans ((posPart_add_negPart _).trans_le
      (ha i hi))
  have hneg (i : ι) (hi : i ∈ s) : (a i)⁻ ≤ t :=
    (le_add_of_nonneg_left (posPart_nonneg (a i))).trans ((posPart_add_negPart _).trans_le
      (ha i hi))
  have hsplit : ∑ i ∈ s, (a i : 𝕜) • v i =
      ∑ i ∈ s, (((a i)⁺ : ℝ) : 𝕜) • v i - ∑ i ∈ s, (((a i)⁻ : ℝ) : 𝕜) • v i := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← sub_smul, ← RCLike.ofReal_sub, posPart_sub_negPart]
  calc
    ‖∑ i ∈ s, (a i : 𝕜) • v i‖ ≤ t * S + t * S := by
      rw [hsplit]
      exact (norm_sub_le _ _).trans (add_le_add
        (norm_sum_ofReal_smul_le_of_nonneg hS ht (fun i _ ↦ posPart_nonneg _) hpos)
        (norm_sum_ofReal_smul_le_of_nonneg hS ht (fun i _ ↦ negPart_nonneg _) hneg))
    _ = 2 * t * S := by ring

/-- If every subsum of `v` over a subset of `s` has norm at most `S`, then a combination of the
`v i` with scalar coefficients of norm at most `t` has norm at most `4 * t * S`. -/
theorem norm_sum_smul_le_four_mul (hS : ∀ u ⊆ s, ‖∑ i ∈ u, v i‖ ≤ S) (ht : 0 ≤ t)
    {a : ι → 𝕜} (ha : ∀ i ∈ s, ‖a i‖ ≤ t) :
    ‖∑ i ∈ s, a i • v i‖ ≤ 4 * t * S := by
  -- Split each coefficient into its real and imaginary parts; multiplying the family by `I`
  -- keeps the subsum bound.
  have hI : ∀ u ⊆ s, ‖∑ i ∈ u, (RCLike.I : 𝕜) • v i‖ ≤ S := fun u hu ↦ by
    rw [← Finset.smul_sum, norm_smul]
    refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (hS u hu)
    rw [RCLike.norm_I]
    split_ifs <;> norm_num
  have hsplit : ∑ i ∈ s, a i • v i =
      ∑ i ∈ s, (RCLike.re (a i) : 𝕜) • v i +
        ∑ i ∈ s, (RCLike.im (a i) : 𝕜) • (RCLike.I : 𝕜) • v i := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [smul_smul, ← add_smul, RCLike.re_add_im]
  calc
    ‖∑ i ∈ s, a i • v i‖ ≤ 2 * t * S + 2 * t * S := by
      rw [hsplit]
      exact (norm_add_le _ _).trans (add_le_add
        (norm_sum_ofReal_smul_le_two_mul hS ht fun i hi ↦
          (RCLike.abs_re_le_norm _).trans (ha i hi))
        (norm_sum_ofReal_smul_le_two_mul hI ht fun i hi ↦
          (RCLike.abs_im_le_norm _).trans (ha i hi)))
    _ = 4 * t * S := by ring

end TauCeti
