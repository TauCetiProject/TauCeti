/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.OrthogonalFamily

/-!
# Sums of operators with orthogonal ranges

Pythagoras bounds the norm of a finite sum of operators with pairwise orthogonal ranges
by the square root of the sum of their squared operator norms. In particular, a sum of
`N` such operators of norm at most `C` has norm at most `√N * C`.

These estimates apply to the orthogonal-range pieces in projection averaging arguments.
Neither the source nor the target needs to be complete.
-/

public section

open scoped InnerProductSpace

namespace ContinuousLinearMap

variable {𝕜 E F ι : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The norm of a sum of operators with orthogonal ranges is bounded by the square root
of the sum of their squared norms. Only indices in `s` need have orthogonal ranges. -/
theorem norm_sum_le_sqrt_sum_norm_sq_of_orthogonal (T : ι → E →L[𝕜] F) (s : Finset ι)
    (hT : (s : Set ι).Pairwise fun i j ↦ ∀ x y, ⟪T i x, T j y⟫_𝕜 = 0) :
    ‖∑ i ∈ s, T i‖ ≤ Real.sqrt (∑ i ∈ s, ‖T i‖ ^ 2) := by
  refine opNorm_le_bound _ (Real.sqrt_nonneg _) fun x ↦ ?_
  have hsq : ‖∑ i ∈ s, T i x‖ ^ 2 ≤ (∑ i ∈ s, ‖T i‖ ^ 2) * ‖x‖ ^ 2 := by
    rw [TauCeti.norm_sum_sq_eq_sum_norm_sq_of_pairwise_inner_eq_zero
      (fun i hi j hj hij ↦ hT hi hj hij x x), Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ ↦ by
      simpa [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) ((T i).le_opNorm x) 2
  have hs : 0 ≤ ∑ i ∈ s, ‖T i‖ ^ 2 := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  simp only [sum_apply]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  simpa [mul_pow, Real.sq_sqrt hs] using hsq

/-- A sum of `N` operators with pairwise orthogonal ranges and norms at most `C` has
norm at most `√N * C`, including the empty sum. -/
theorem norm_sum_le_sqrt_card_mul_of_orthogonal (T : ι → E →L[𝕜] F) (s : Finset ι)
    (hT : (s : Set ι).Pairwise fun i j ↦ ∀ x y, ⟪T i x, T j y⟫_𝕜 = 0)
    {C : ℝ} (hbound : ∀ i ∈ s, ‖T i‖ ≤ C) :
    ‖∑ i ∈ s, T i‖ ≤ Real.sqrt s.card * C := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨i, hi⟩
  · simp
  have hC : 0 ≤ C := (norm_nonneg (T i)).trans (hbound i hi)
  refine (norm_sum_le_sqrt_sum_norm_sq_of_orthogonal T s hT).trans ?_
  have hsum : ∑ i ∈ s, ‖T i‖ ^ 2 ≤ (s.card : ℝ) * C ^ 2 := by
    simpa using Finset.sum_le_sum (s := s) fun i hi ↦
      pow_le_pow_left₀ (norm_nonneg _) (hbound i hi) 2
  calc Real.sqrt (∑ i ∈ s, ‖T i‖ ^ 2)
      ≤ Real.sqrt ((s.card : ℝ) * C ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt s.card * C := by rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hC]

end ContinuousLinearMap
