/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.SNumbers.Entropy.Basic
public import TauCeti.Analysis.Normed.Operator.SNumbers.Hilbert
import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Factorization

/-!
# Approximation and Hilbert numbers against entropy numbers

Over `ℝ` or `ℂ`, the entropy numbers dominate the approximation numbers between inner product
spaces, and the Hilbert numbers between arbitrary normed spaces, up to the factor `2`:

* `ContinuousLinearMap.singularValue_le_two_mul_entropyNumber`: `aₙ(T) ≤ 2 eₙ(T)` for a bounded
  operator `T` between inner product spaces;
* `ContinuousLinearMap.hilbertNumber_le_two_mul_entropyNumber`: `hₙ(T) ≤ 2 eₙ(T)` for a bounded
  operator `T` between normed spaces.

For `0 < c < aₙ(T)`, the scalar factorization theorem
(`ContinuousLinearMap.exists_comp_comp_eq_smul_id`) writes `c • id` on `ℓ₂^{n+1}` as a compression
`B ∘ T ∘ A` of `T` by contractions. Entropy numbers are homogeneous and do not increase under such
compressions, and the identity of a space of dimension `n + 1` has `eₙ ≥ 1 / 2`
(`ContinuousLinearMap.one_half_le_entropyNumber_id`), so `c / 2 ≤ eₙ(T)`. Neither space needs to be
complete. Since the Hilbert numbers are the supremum of the approximation numbers of compressions
of `T` to `ℓ₂` by contractions, the first bound passes to them.

Unlike the s-numbers, the entropy numbers do not vanish on nonzero operators of finite rank
(`ContinuousLinearMap.entropyNumber_pos`), so neither inequality can be reversed by a constant:
`e₁(id_ℝ) > 0` while `a₁(id_ℝ) = h₁(id_ℝ) = 0`.

## References

* A. Pietsch, *Operator Ideals*, North-Holland Mathematical Library 20, North-Holland (1980),
  12.3.1.
* B. Carl and I. Stephani, *Entropy, Compactness and the Approximation of Operators*, Cambridge
  Tracts in Mathematics 98, Cambridge University Press (1990), Chapters 1–2.
-/

public section

open scoped NNReal

namespace ContinuousLinearMap

variable {𝕜 : Type*} [RCLike 𝕜]

/-- **Approximation numbers against entropy numbers.** Between inner product spaces over `ℝ` or
`ℂ`, `aₙ(T) ≤ 2 eₙ(T)`. Neither space needs to be complete. -/
theorem singularValue_le_two_mul_entropyNumber {H₁ H₂ : Type*}
    [SeminormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁]
    [SeminormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂]
    (T : H₁ →L[𝕜] H₂) (n : ℕ) :
    T.singularValue n ≤ 2 * T.entropyNumber n := by
  rw [← NNReal.coe_le_coe]
  refine le_of_forall_lt_imp_le_of_dense fun c hc ↦ ?_
  rcases le_or_gt c 0 with hc0 | hc_pos
  · exact hc0.trans (NNReal.coe_nonneg _)
  -- Factor `c • id` on `ℓ₂^{n+1}` through `T` by contractions.
  obtain ⟨A, B, hA, hB, hfac⟩ := T.exists_comp_comp_eq_smul_id n hc_pos.le hc
  have hcomp := entropyNumber_comp_comp_le_of_norm_le_one hB hA T n
  rw [hfac, entropyNumber_smul, ← NNReal.coe_le_coe, NNReal.coe_mul, coe_nnNorm,
    RCLike.norm_ofReal, abs_of_pos hc_pos] at hcomp
  -- The identity of the `(n + 1)`-dimensional space `ℓ₂^{n+1}` has `eₙ ≥ 1 / 2`.
  have hid : (1 / 2 : ℝ) ≤
      (ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1)))).entropyNumber n := by
    have hrank : (n : Cardinal) < Module.rank 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1))) := by
      rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin, Nat.cast_lt]
      exact n.lt_succ_self
    exact_mod_cast one_half_le_entropyNumber_id hrank
  push_cast
  nlinarith

/-- **Hilbert numbers against entropy numbers.** Between normed spaces over `ℝ` or `ℂ`,
`hₙ(T) ≤ 2 eₙ(T)`. -/
theorem hilbertNumber_le_two_mul_entropyNumber {E F : Type*}
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
    (T : E →L[𝕜] F) (n : ℕ) :
    T.hilbertNumber n ≤ 2 * T.entropyNumber n :=
  hilbertNumber_le_iff.mpr fun A B hA hB ↦
    (singularValue_le_two_mul_entropyNumber (B ∘L T ∘L A) n).trans
      (mul_le_mul_right (entropyNumber_comp_comp_le_of_norm_le_one hB hA T n) 2)

end ContinuousLinearMap
