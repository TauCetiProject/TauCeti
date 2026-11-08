/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Signature
public import TauCeti.Analysis.InnerProductSpace.PointSpectrum
import TauCeti.Analysis.InnerProductSpace.Dual

/-!
# The index of inertia of a symmetric form and the spectrum of its Riesz operator

On a finite-dimensional real inner product space, a symmetric bilinear form `B` is represented by
the self-adjoint Riesz operator `continuousLinearMapOfBilin B`, with `⟪B♯ v, w⟫ = B v w`. In an
orthonormal eigenbasis of that operator the form is diagonal, with the eigenvalues as weights, so
by Sylvester's law of inertia its negative index of inertia `sigNeg` is the number of negative
eigenvalues counted with multiplicity: the dimension of the negative point-spectral subspace of
the Riesz operator
(`InnerProductSpace.finrank_pointSpectralSubspace_Iio_continuousLinearMapOfBilin`). Likewise its
positive index of inertia `sigPos` is the dimension of the positive point-spectral subspace
(`InnerProductSpace.finrank_pointSpectralSubspace_Ioi_continuousLinearMapOfBilin`), deduced from
the negative case for `-B` since negating the form exchanges the two spectral subspaces
(`InnerProductSpace.pointSpectralSubspace_Iio_continuousLinearMapOfBilin_neg`).

The spectral subspaces depend on the inner product, their dimensions do not. This identifies, for
instance, the ranks of the negative and positive spectral subbundles of a field of symmetric forms
with the index and coindex of the form.

## References

* J. J. Sylvester, *A demonstration of the theorem that every homogeneous quadratic polynomial is
  reducible by real orthogonal substitutions to the form of a sum of positive and negative
  squares*, Philosophical Magazine (4) 4 (1852), 138–142.
-/

public section

open Set

namespace InnerProductSpace

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- Negating a real bilinear form exchanges the negative and positive spectral subspaces of its
Riesz operator. -/
theorem pointSpectralSubspace_Iio_continuousLinearMapOfBilin_neg [CompleteSpace W]
    (B : W →L[ℝ] W →L[ℝ] ℝ) :
    Module.End.pointSpectralSubspace (continuousLinearMapOfBilin (-B)).toLinearMap (Iio 0) =
      Module.End.pointSpectralSubspace (continuousLinearMapOfBilin B).toLinearMap (Ioi 0) := by
  rw [continuousLinearMapOfBilin_neg, ContinuousLinearMap.toLinearMap_neg,
    Module.End.pointSpectralSubspace_neg, neg_Iio, neg_zero]

variable [FiniteDimensional ℝ W]

/-- **Sylvester's law of inertia, spectrally.** The negative index of inertia of a symmetric real
bilinear form on a finite-dimensional inner product space is the dimension of the negative
spectral subspace of its Riesz operator. -/
theorem finrank_pointSpectralSubspace_Iio_continuousLinearMapOfBilin
    {B : W →L[ℝ] W →L[ℝ] ℝ} (hB : ∀ v w, B v w = B w v) :
    Module.finrank ℝ (Module.End.pointSpectralSubspace
        (continuousLinearMapOfBilin B).toLinearMap (Iio 0)) =
      sigNeg B.toBilinForm.toQuadraticMap := by
  have hT := (isSelfAdjoint_continuousLinearMapOfBilin hB).isSymmetric
  let b := hT.eigenvectorBasis rfl
  -- In an eigenbasis of the Riesz operator the form is diagonal, with the eigenvalues as weights.
  have hdiag (i j : Fin (Module.finrank ℝ W)) :
      B (b i) (b j) = if i = j then hT.eigenvalues rfl i else 0 := by
    have heigen := hT.apply_eigenvectorBasis rfl i
    rw [ContinuousLinearMap.coe_coe, RCLike.ofReal_real_eq_id, id] at heigen
    rw [← continuousLinearMapOfBilin_apply, heigen, real_inner_smul_left,
      orthonormal_iff_ite.mp b.orthonormal i j]
    split_ifs <;> simp
  have hassoc : QuadraticMap.associated (R := ℝ) B.toBilinForm.toQuadraticMap = B.toBilinForm :=
    QuadraticMap.associated_left_inverse ℝ fun v w ↦ hB v w
  have horth : (QuadraticMap.associated (R := ℝ) B.toBilinForm.toQuadraticMap).IsOrthoᵢ b := by
    rw [hassoc, LinearMap.isOrthoᵢ_def]
    intro i j hij
    simp [hdiag, hij]
  have hequiv := QuadraticForm.isometryEquivWeightedSumSquares _ b.toBasis horth
  have hweights : (fun i ↦ B.toBilinForm.toQuadraticMap (b.toBasis i)) = hT.eigenvalues rfl := by
    funext i
    simp [hdiag]
  rw [hweights] at hequiv
  rw [QuadraticForm.sigNeg_of_equiv_weightedSumSquares ⟨hequiv⟩,
    hT.finrank_pointSpectralSubspace rfl]
  simp only [mem_Iio]

/-- **Sylvester's law of inertia, spectrally, positive part.** The positive index of inertia of a
symmetric real bilinear form on a finite-dimensional inner product space is the dimension of the
positive spectral subspace of its Riesz operator. -/
theorem finrank_pointSpectralSubspace_Ioi_continuousLinearMapOfBilin
    {B : W →L[ℝ] W →L[ℝ] ℝ} (hB : ∀ v w, B v w = B w v) :
    Module.finrank ℝ (Module.End.pointSpectralSubspace
        (continuousLinearMapOfBilin B).toLinearMap (Ioi 0)) =
      sigPos B.toBilinForm.toQuadraticMap := by
  rw [← pointSpectralSubspace_Iio_continuousLinearMapOfBilin_neg,
    finrank_pointSpectralSubspace_Iio_continuousLinearMapOfBilin fun v w ↦ by simp [hB v w],
    ← sigNeg_neg]
  congr 1

end InnerProductSpace

