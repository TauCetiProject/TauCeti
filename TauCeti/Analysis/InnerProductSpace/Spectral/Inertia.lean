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
(`InnerProductSpace.finrank_pointSpectralSubspace_Iio_continuousLinearMapOfBilin`).

The spectral subspace depends on the inner product, its dimension does not. This identifies, for
instance, the rank of a negative spectral subbundle of a field of symmetric forms with the index
of the form.

## References

* J. J. Sylvester, *A demonstration of the theorem that every homogeneous quadratic polynomial is
  reducible by real orthogonal substitutions to the form of a sum of positive and negative
  squares*, Philosophical Magazine (4) 4 (1852), 138–142.
-/

public section

open Set

namespace InnerProductSpace

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

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
    rw [← continuousLinearMapOfBilin_apply,
      show (continuousLinearMapOfBilin B) (b i) = hT.eigenvalues rfl i • b i from
        hT.apply_eigenvectorBasis rfl i, real_inner_smul_left,
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

end InnerProductSpace

