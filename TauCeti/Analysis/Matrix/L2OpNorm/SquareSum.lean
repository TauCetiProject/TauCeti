/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# The `ℓ²` operator norm through square sums, and large-sieve duality

For a rectangular matrix `A` over `ℝ` or `ℂ`, the `ℓ²` operator norm (`Matrix.Norms.L2Operator`)
is the least constant `c` with `∑ᵢ |(A a)ᵢ|² ≤ c² ∑ⱼ |aⱼ|²` for every vector `a`. This file states
that characterization with explicit sums, and deduces the *duality principle* of the large sieve:
an inequality `∑ᵢ |∑ⱼ Aᵢⱼ aⱼ|² ≤ C ∑ⱼ |aⱼ|²` for all `a` holds with the same constant for the
conjugate transpose, `∑ⱼ |∑ᵢ conj(Aᵢⱼ) bᵢ|² ≤ C ∑ᵢ |bᵢ|²` for all `b`, and for the transpose. In
the large sieve `A` is a matrix of values of exponentials or characters, and duality exchanges
the roles of the frequencies and the sample points.

The duality is `Matrix.l2_opNorm_conjTranspose`, `‖Aᴴ‖ = ‖A‖`, read through the square-sum
characterization of the norm.

## Main results

* `Matrix.sum_norm_sq_mulVec_le`: `∑ᵢ |(A a)ᵢ|² ≤ ‖A‖² ∑ⱼ |aⱼ|²`.
* `Matrix.l2_opNorm_sq_le_iff`: `‖A‖² ≤ C` exactly when `∑ᵢ |(A a)ᵢ|² ≤ C ∑ⱼ |aⱼ|²` for all `a`.
* `Matrix.forall_sum_norm_sq_mulVec_le_iff_conjTranspose`: large-sieve duality, for `Aᴴ`.
* `Matrix.forall_sum_norm_sq_mulVec_le_iff_vecMul`: large-sieve duality without conjugation, for
  the row action `b ᵥ* A`.

## References

* K. S. Kedlaya, *Notes on analytic number theory*, Chapter 15 (An additive large sieve
  inequality), Lemma 15.4 (duality, in the form without conjugation).
-/

public section

open scoped Matrix.Norms.L2Operator

namespace Matrix

variable {𝕜 m n : Type*} [RCLike 𝕜] [Fintype m] [Fintype n] [DecidableEq n]

/-- The square-sum form of the operator norm inequality:
`∑ᵢ |(A a)ᵢ|² ≤ ‖A‖² ∑ⱼ |aⱼ|²`. -/
theorem sum_norm_sq_mulVec_le (A : Matrix m n 𝕜) (a : n → 𝕜) :
    ∑ i, ‖(A *ᵥ a) i‖ ^ 2 ≤ ‖A‖ ^ 2 * ∑ j, ‖a j‖ ^ 2 := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (A.l2_opNorm_mulVec (WithLp.toLp 2 a)) 2
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at h
  simpa using h

/-- A constant `C ≥ 0` bounds the square of the `ℓ²` operator norm of `A` exactly when
`∑ᵢ |(A a)ᵢ|² ≤ C ∑ⱼ |aⱼ|²` for every vector `a`. -/
theorem l2_opNorm_sq_le_iff {A : Matrix m n 𝕜} {C : ℝ} (hC : 0 ≤ C) :
    ‖A‖ ^ 2 ≤ C ↔ ∀ a : n → 𝕜, ∑ i, ‖(A *ᵥ a) i‖ ^ 2 ≤ C * ∑ j, ‖a j‖ ^ 2 := by
  refine ⟨fun h a ↦ (A.sum_norm_sq_mulVec_le a).trans
    (mul_le_mul_of_nonneg_right h (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)), fun h ↦ ?_⟩
  have hA : ‖A‖ ≤ √C := by
    rw [l2_opNorm_def]
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg C) fun x ↦ ?_
    refine (pow_le_pow_iff_left₀ (norm_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg C) (norm_nonneg _)) two_ne_zero).1 ?_
    rw [mul_pow, Real.sq_sqrt hC, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    simpa using h (WithLp.ofLp x)
  calc ‖A‖ ^ 2 ≤ √C ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hA 2
    _ = C := Real.sq_sqrt hC

omit [DecidableEq n] in
/-- **Large-sieve duality.** For a rectangular matrix `A` and `C ≥ 0`, the inequality
`∑ᵢ |∑ⱼ Aᵢⱼ aⱼ|² ≤ C ∑ⱼ |aⱼ|²` holds for every `a` exactly when
`∑ⱼ |∑ᵢ conj(Aᵢⱼ) bᵢ|² ≤ C ∑ᵢ |bᵢ|²` holds for every `b`. Both say `‖A‖² ≤ C`. -/
theorem forall_sum_norm_sq_mulVec_le_iff_conjTranspose (A : Matrix m n 𝕜) {C : ℝ}
    (hC : 0 ≤ C) :
    (∀ a : n → 𝕜, ∑ i, ‖(A *ᵥ a) i‖ ^ 2 ≤ C * ∑ j, ‖a j‖ ^ 2) ↔
      ∀ b : m → 𝕜, ∑ j, ‖(Aᴴ *ᵥ b) j‖ ^ 2 ≤ C * ∑ i, ‖b i‖ ^ 2 := by
  classical
  rw [← l2_opNorm_sq_le_iff hC, ← l2_opNorm_sq_le_iff hC, l2_opNorm_conjTranspose]

omit [DecidableEq n] in
/-- **Large-sieve duality**, without conjugation: for a rectangular matrix `A` and `C ≥ 0`, the
inequality `∑ᵢ |∑ⱼ Aᵢⱼ aⱼ|² ≤ C ∑ⱼ |aⱼ|²` holds for every `a` exactly when
`∑ⱼ |∑ᵢ bᵢ Aᵢⱼ|² ≤ C ∑ᵢ |bᵢ|²` holds for every `b`. -/
theorem forall_sum_norm_sq_mulVec_le_iff_vecMul (A : Matrix m n 𝕜) {C : ℝ} (hC : 0 ≤ C) :
    (∀ a : n → 𝕜, ∑ i, ‖(A *ᵥ a) i‖ ^ 2 ≤ C * ∑ j, ‖a j‖ ^ 2) ↔
      ∀ b : m → 𝕜, ∑ j, ‖(b ᵥ* A) j‖ ^ 2 ≤ C * ∑ i, ‖b i‖ ^ 2 := by
  have hstar (b : m → 𝕜) : ∑ j, ‖(Aᴴ *ᵥ star b) j‖ ^ 2 = ∑ j, ‖(b ᵥ* A) j‖ ^ 2 := by
    simp [← star_vecMul]
  have hnorm (b : m → 𝕜) : ∑ i, ‖(star b) i‖ ^ 2 = ∑ i, ‖b i‖ ^ 2 := by simp
  rw [forall_sum_norm_sq_mulVec_le_iff_conjTranspose A hC]
  refine ⟨fun h b ↦ ?_, fun h b ↦ ?_⟩
  · rw [← hstar b, ← hnorm b]
    exact h (star b)
  · have h' := h (star b)
    rwa [← hstar (star b), star_star, hnorm b] at h'

end Matrix
