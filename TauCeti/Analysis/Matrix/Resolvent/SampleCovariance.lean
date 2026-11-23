/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Resolvent.RankOne
public import TauCeti.Analysis.Matrix.SampleSecondMoment
public import TauCeti.Analysis.Matrix.SpectralMeasure.Basic

/-!
# The resolvent identity of a sample covariance matrix

Let `X` be a `p × n` matrix with columns `xₖ = X.col k`, let `S = X Xᴴ / n` be its sample
covariance, and let `Sₖ = sampleCovariance (X.updateCol k 0) = S - n⁻¹ xₖ xₖᴴ` be the
leave-one-out matrix, which depends only on the columns other than `xₖ`. For non-real `z`,
write `R = (S - z • 1)⁻¹`, `Rₖ = (Sₖ - z • 1)⁻¹` and `qₖ = xₖᴴ Rₖ xₖ`. This file proves the exact
finite-dimensional identity

`p + z tr R = n - ∑ₖ (1 + n⁻¹ qₖ)⁻¹`.

It follows by taking the trace of `S R = 1 + z R`, expanding `S` as the average of the rank-one
matrices `xₖ xₖᴴ`, and evaluating each quadratic form `xₖᴴ R xₖ` by the rank-one resolvent update
from `Sₖ`. Each summand is bounded by `|z| / |Im z|`, since `Sₖ` is positive semidefinite.

In terms of the resolvent transform `m(z) = ∫ (x - z)⁻¹ dL_S(x)` of the empirical spectral measure,
the identity reads `p (1 + z m(z)) = n - ∑ₖ (1 + n⁻¹ qₖ)⁻¹`. This is the deterministic input of the
resolvent proof of the Marchenko–Pastur law. When `p / n → y` and each `n⁻¹ qₖ` is close to
`n⁻¹ tr Rₖ`, hence to `y m(z)`, it becomes the self-consistent equation
`y z m² + (z + y - 1) m + 1 = 0`.

## Main results

* `Matrix.card_add_mul_trace_inv_sampleCovariance_sub_smul_one`: the identity
  `p + z tr R = n - ∑ₖ (1 + n⁻¹ qₖ)⁻¹`.
* `Matrix.card_mul_one_add_mul_resolventTransform_spectralMeasure_sampleCovariance`: the same
  identity for the resolvent transform of the empirical spectral measure.
* `Matrix.norm_inv_one_add_mul_dotProduct_inv_sampleCovariance_updateCol_sub_smul_one_mulVec_le`:
  each summand has norm at most `|z| / |Im z|`.

## References

* Z. D. Bai, *Methodologies in spectral analysis of large dimensional random matrices, a review*,
  Statistica Sinica 9 (1999), 611–677, §2.2 (proof of Theorem 2.5 by Stieltjes transforms).
* Z. D. Bai, J. W. Silverstein, *Spectral Analysis of Large Dimensional Random Matrices*, 2nd ed.,
  Springer, 2010, §3.3.
-/

public section

noncomputable section

open MeasureTheory

namespace Matrix

variable {𝕜 p n : Type*} [RCLike 𝕜] [Fintype p] [DecidableEq p] [Fintype n] [DecidableEq n]

/-- **Resolvent identity of a sample covariance matrix.** For `S = X Xᴴ / n`, the leave-one-out
matrices `Sₖ = sampleCovariance (X.updateCol k 0)` and non-real `z`,
`p + z tr (S - z • 1)⁻¹ = n - ∑ₖ (1 + n⁻¹ xₖᴴ (Sₖ - z • 1)⁻¹ xₖ)⁻¹`. -/
theorem card_add_mul_trace_inv_sampleCovariance_sub_smul_one (X : Matrix p n 𝕜) {z : 𝕜}
    (hz : RCLike.im z ≠ 0) :
    (Fintype.card p : 𝕜) + z * (sampleCovariance X - z • 1)⁻¹.trace =
      Fintype.card n - ∑ k, (1 + (Fintype.card n : 𝕜)⁻¹ *
        (star (X.col k) ⬝ᵥ ((sampleCovariance (X.updateCol k 0) - z • 1)⁻¹ *ᵥ X.col k)))⁻¹ := by
  set R := (sampleCovariance X - z • 1)⁻¹
  have hR : sampleCovariance X * R = 1 + z • R := by
    have h := mul_nonsing_inv _
      (((isHermitian_sampleCovariance X).isUnit_sub_smul_one_of_im_ne_zero hz).map
        Matrix.detMonoidHom)
    rw [sub_mul, smul_mul_assoc, one_mul] at h
    rw [← h]
    abel
  -- Each column contributes `n⁻¹ xₖᴴ R xₖ`, evaluated by the rank-one update from `Sₖ`.
  have hterm (k : n) : (Fintype.card n : 𝕜)⁻¹ * (star (X.col k) ⬝ᵥ (R *ᵥ X.col k)) =
      1 - (1 + (Fintype.card n : 𝕜)⁻¹ *
        (star (X.col k) ⬝ᵥ ((sampleCovariance (X.updateCol k 0) - z • 1)⁻¹ *ᵥ X.col k)))⁻¹ := by
    have hk := isHermitian_sampleCovariance (X.updateCol k 0)
    have hS : sampleCovariance (X.updateCol k 0) +
        (((Fintype.card n : ℝ)⁻¹ : ℝ) : 𝕜) • vecMulVec (X.col k) (star (X.col k)) =
          sampleCovariance X := by
      rw [← RCLike.real_smul_eq_coe_smul, inv_eq_one_div, sampleCovariance_updateCol_zero_add]
    have h := hk.dotProduct_inv_add_smul_vecMulVec_sub_smul_one_mulVec
      (Fintype.card n : ℝ)⁻¹ (X.col k) hz
    have hden := hk.one_add_mul_dotProduct_inv_sub_smul_one_ne_zero
      (Fintype.card n : ℝ)⁻¹ (X.col k) hz
    rw [hS] at h
    simp only [RCLike.ofReal_inv, RCLike.ofReal_natCast] at h hden
    rw [h]
    generalize star (X.col k) ⬝ᵥ ((sampleCovariance (X.updateCol k 0) - z • 1)⁻¹ *ᵥ X.col k) = q
      at hden ⊢
    generalize (Fintype.card n : 𝕜)⁻¹ = c at hden ⊢
    field_simp
    ring
  -- `tr (S R)` is the average over the columns of the quadratic forms `xₖᴴ R xₖ`.
  have htrace : (sampleCovariance X * R).trace =
      ∑ k, (Fintype.card n : 𝕜)⁻¹ * (star (X.col k) ⬝ᵥ (R *ᵥ X.col k)) := by
    rw [sampleCovariance_eq_sampleSecondMoment, TauCeti.sampleSecondMoment_def,
      TauCeti.finiteMean_eq_inv_smul_sum, smul_mul_assoc, trace_smul, Finset.sum_mul, trace_sum,
      smul_eq_mul, Finset.mul_sum]
    simp only [col_apply', vecMulVec_mul, trace_vecMulVec, dotProduct_comm (fun i ↦ X i _),
      ← dotProduct_mulVec]
  have h := congrArg trace hR
  rw [htrace, trace_add, trace_one, trace_smul, smul_eq_mul,
    Finset.sum_congr rfl fun k _ ↦ hterm k, Finset.sum_sub_distrib] at h
  simpa [eq_sub_iff_add_eq] using h.symm

/-- Each summand in the resolvent identity of a sample covariance matrix has norm at most
`|z| / |Im z|`, because the leave-one-out matrix is positive semidefinite. -/
theorem norm_inv_one_add_mul_dotProduct_inv_sampleCovariance_updateCol_sub_smul_one_mulVec_le
    (X : Matrix p n 𝕜) (k : n) {z : 𝕜} (hz : RCLike.im z ≠ 0) :
    ‖(1 + (Fintype.card n : 𝕜)⁻¹ *
        (star (X.col k) ⬝ᵥ ((sampleCovariance (X.updateCol k 0) - z • 1)⁻¹ *ᵥ X.col k)))⁻¹‖ ≤
      ‖z‖ / |RCLike.im z| := by
  simpa using PosSemidef.norm_inv_one_add_mul_dotProduct_inv_sub_smul_one_mulVec_le
    (posSemidef_sampleCovariance (X.updateCol k 0))
    (inv_nonneg.mpr (Nat.cast_nonneg (Fintype.card n))) (X.col k) hz

/-- **Resolvent identity of a sample covariance matrix, transform form.** The resolvent transform
`m` of the empirical spectral measure of `S = X Xᴴ / n` satisfies
`p (1 + z m(z)) = n - ∑ₖ (1 + n⁻¹ xₖᴴ (Sₖ - z • 1)⁻¹ xₖ)⁻¹` at every non-real `z`, where
`Sₖ = sampleCovariance (X.updateCol k 0)`. -/
theorem card_mul_one_add_mul_resolventTransform_spectralMeasure_sampleCovariance [Nonempty p]
    (X : Matrix p n ℂ) {z : ℂ} (hz : z.im ≠ 0) :
    (Fintype.card p : ℂ) * (1 + z * resolventTransform
        ((sampleCovariance X).spectralMeasure (isHermitian_sampleCovariance X) : Measure ℝ) z) =
      Fintype.card n - ∑ k, (1 + (Fintype.card n : ℂ)⁻¹ *
        (star (X.col k) ⬝ᵥ ((sampleCovariance (X.updateCol k 0) - z • 1)⁻¹ *ᵥ X.col k)))⁻¹ := by
  have hp : (Fintype.card p : ℂ) ≠ 0 := by simp
  rw [resolventTransform_spectralMeasure _ _
      ((isHermitian_sampleCovariance X).notMem_spectrum_of_im_ne_zero hz),
    ← card_add_mul_trace_inv_sampleCovariance_sub_smul_one X hz]
  field_simp

end Matrix
