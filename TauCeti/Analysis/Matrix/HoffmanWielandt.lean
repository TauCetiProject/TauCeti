/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HoffmanWielandt
public import TauCeti.Analysis.Matrix.SpectralMeasure

/-!
# The Hoffman–Wielandt inequality for Hermitian matrices

For Hermitian `n × n` matrices `A` and `B` over `ℝ` or `ℂ`, with eigenvalues
`λ₁(A) ≥ ⋯ ≥ λₙ(A)` and `λ₁(B) ≥ ⋯ ≥ λₙ(B)` listed in decreasing order with multiplicity, the
**Hoffman–Wielandt inequality** bounds the Euclidean distance between the sorted spectra by the
Frobenius distance between the matrices:

`∑ᵢ (λᵢ(A) - λᵢ(B))² ≤ ‖A - B‖_F²`.

This is the matrix form of the operator inequality
`LinearMap.IsSymmetric.sum_sq_eigenvalues_sub_le_sum_sq_norm_apply`, applied to
`Matrix.toEuclideanLin A` and `Matrix.toEuclideanLin B` in the standard orthonormal basis. The
Frobenius norm is Mathlib's `Matrix.frobeniusNormedAddCommGroup`, available through
`open scoped Matrix.Norms.Frobenius`.

Combined with the Cauchy–Schwarz inequality it shows that integrals of Lipschitz functions
against empirical spectral measures are Lipschitz in the matrix: if `f` is `K`-Lipschitz, then

`‖∫ f dL_A - ∫ f dL_B‖ ≤ K ‖A - B‖_F / √n`.

This is the deterministic estimate behind truncation and concentration arguments for random
matrices: a perturbation of small Frobenius norm hardly moves linear spectral statistics, and the
map `A ↦ ∫ f dL_A` is a Lipschitz function of the matrix entries.

## Main results

* `Matrix.IsHermitian.sum_sq_eigenvalues₀_sub_le_frobenius_norm_sub_sq`: the Hoffman–Wielandt
  inequality `∑ᵢ (λᵢ(A) - λᵢ(B))² ≤ ‖A - B‖_F²`.
* `Matrix.norm_integral_spectralMeasure_sub_integral_spectralMeasure_le`: for a `K`-Lipschitz
  `f`, `‖∫ f dL_A - ∫ f dL_B‖ ≤ K ‖A - B‖_F / √n`.

## References

* A. J. Hoffman, H. W. Wielandt, *The variation of the spectrum of a normal matrix*, Duke Math. J.
  **20** (1953), 37–39.
* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), Lemma 2.1.19 and §2.3.1.
-/

public section

open MeasureTheory
open scoped Matrix.Norms.Frobenius NNReal

namespace Matrix

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜] {A B : Matrix n n 𝕜}

/-- **The Hoffman–Wielandt inequality** for Hermitian matrices: the squared Euclidean distance
between the decreasingly sorted spectra is at most the squared Frobenius norm `‖A - B‖_F²`. -/
theorem IsHermitian.sum_sq_eigenvalues₀_sub_le_frobenius_norm_sub_sq (hA : A.IsHermitian)
    (hB : B.IsHermitian) :
    ∑ i, (hA.eigenvalues₀ i - hB.eigenvalues₀ i) ^ 2 ≤ ‖A - B‖ ^ 2 := by
  let e := EuclideanSpace.basisFun n 𝕜
  -- The Frobenius norm of `A - B` is the Frobenius seminorm of its Euclidean operator.
  have hF : ‖A - B‖ = TauCeti.UnitarilyInvariantSeminorm.frobenius 𝕜 _ _
      (toEuclideanLin (A - B)) := by
    rw [← LinearMap.frobenius_norm_toMatrix _ e e, toEuclideanLin_eq_toLin_orthonormal,
      LinearMap.toMatrix_toLin]
  rw [hF, TauCeti.UnitarilyInvariantSeminorm.sq_frobenius_apply e]
  -- Unfold only the sorted enumeration to use its defining operator-level API.
  simp only [IsHermitian.eigenvalues₀]
  simpa only [map_sub, LinearMap.sub_apply] using
    LinearMap.IsSymmetric.sum_sq_eigenvalues_sub_le_sum_sq_norm_apply
      (isSymmetric_toEuclideanLin_iff.mpr hA) (isSymmetric_toEuclideanLin_iff.mpr hB)
      finrank_euclideanSpace e

/-- Integrals of a `K`-Lipschitz function against empirical spectral measures are Lipschitz in
the matrix: `‖∫ f dL_A - ∫ f dL_B‖ ≤ K ‖A - B‖_F / √n`, for Hermitian `A` and `B` of size `n`. -/
theorem norm_integral_spectralMeasure_sub_integral_spectralMeasure_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Nonempty n] (hA : A.IsHermitian)
    (hB : B.IsHermitian) {K : ℝ≥0} {f : ℝ → E} (hf : LipschitzWith K f) :
    ‖∫ x, f x ∂(A.spectralMeasure hA : Measure ℝ) - ∫ x, f x ∂(B.spectralMeasure hB : Measure ℝ)‖
      ≤ K * ‖A - B‖ / √(Fintype.card n) := by
  set N : ℝ := (Fintype.card n : ℝ)
  have hN : 0 < N := by simp [N, Fintype.card_pos]
  -- Cauchy–Schwarz turns the Hoffman–Wielandt bound into an `ℓ¹` bound on the sorted spectra.
  have hl1 : ∑ i, |hA.eigenvalues₀ i - hB.eigenvalues₀ i| ≤ √N * ‖A - B‖ := by
    rw [← Real.sqrt_sq (norm_nonneg (A - B)), ← Real.sqrt_mul hN.le]
    refine Real.le_sqrt_of_sq_le ?_
    calc (∑ i, |hA.eigenvalues₀ i - hB.eigenvalues₀ i|) ^ 2
        ≤ (Finset.univ : Finset (Fin (Fintype.card n))).card *
            ∑ i, |hA.eigenvalues₀ i - hB.eigenvalues₀ i| ^ 2 := sq_sum_le_card_mul_sum_sq
      _ ≤ N * ‖A - B‖ ^ 2 := by
        simpa [N, sq_abs] using mul_le_mul_of_nonneg_left
          (hA.sum_sq_eigenvalues₀_sub_le_frobenius_norm_sub_sq hB) hN.le
  rw [integral_spectralMeasure_eq_sum_eigenvalues₀, integral_spectralMeasure_eq_sum_eigenvalues₀,
    ← smul_sub, ← Finset.sum_sub_distrib, norm_smul]
  calc ‖N⁻¹‖ * ‖∑ i, (f (hA.eigenvalues₀ i) - f (hB.eigenvalues₀ i))‖
      ≤ N⁻¹ * ∑ i, K * |hA.eigenvalues₀ i - hB.eigenvalues₀ i| := by
        rw [Real.norm_of_nonneg (inv_nonneg.mpr hN.le)]
        gcongr
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
        simpa [← dist_eq_norm, Real.dist_eq] using hf.dist_le_mul _ _
    _ ≤ N⁻¹ * (K * (√N * ‖A - B‖)) := by
        rw [← Finset.mul_sum]
        gcongr
    _ = K * ‖A - B‖ / √N := by
        have hs : √N ^ 2 = N := Real.sq_sqrt hN.le
        field_simp
        rw [hs]
        ring

end Matrix
