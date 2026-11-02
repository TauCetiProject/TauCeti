/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Resolvent.Basic
public import TauCeti.LinearAlgebra.Matrix.SchurComplement

/-!
# Rank-one updates of Hermitian resolvents

For a Hermitian matrix `A`, a real scalar `c` and a vector `u`, this file gives the resolvent
of `A + c • u uᴴ` in terms of the resolvent of `A`. The sign convention is
`R = (A - z • 1)⁻¹`, so the denominator is `1 + c * uᴴ R u` and the correction is subtracted.
The denominator is nonzero at every non-real `z`: both shifted Hermitian matrices are
invertible, and the rank-one invertibility criterion applies. In particular, no extra
nonvanishing hypothesis is needed for the update.

The matrix, entrywise and trace identities apply also to negative `c`, zero vectors and empty
index types. Trace updates are used when adding or removing one sample in a Gram matrix in the
resolvent method for sample-covariance spectral laws.

## References

* Z. D. Bai, *Methodologies in spectral analysis of large dimensional random matrices, a review*,
  Statistica Sinica 9 (1999), 611–677, §2.2.
* R. A. Horn, C. R. Johnson, *Matrix Analysis*, 2nd ed., Cambridge University Press, 2013,
  §0.7.4 (the Sherman–Morrison–Woodbury formula).
-/

public section

noncomputable section

namespace Matrix.IsHermitian

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]
  {A : Matrix n n 𝕜} (hA : A.IsHermitian)

include hA

/-- The denominator in a real rank-one update of a Hermitian resolvent is nonzero off the real
axis, without any restriction on the sign of the perturbation. -/
theorem one_add_mul_dotProduct_inv_sub_smul_one_ne_zero (c : ℝ) (u : n → 𝕜) {z : 𝕜}
    (hz : RCLike.im z ≠ 0) :
    1 + (c : 𝕜) * (star u ⬝ᵥ ((A - z • 1)⁻¹ *ᵥ u)) ≠ 0 := by
  have hu : (vecMulVec u (star u)).IsHermitian := by
    simp [IsHermitian, conjTranspose_vecMulVec]
  have hB : (A + (c : 𝕜) • vecMulVec u (star u)).IsHermitian :=
    hA.add (hu.smul (by simp [IsSelfAdjoint]))
  have hden := (isUnit_add_vecMulVec_iff (A - z • 1)
    (hA.isUnit_sub_smul_one_of_im_ne_zero hz) ((c : 𝕜) • u) (star u)).1
    (by simpa [smul_vecMulVec, add_sub_right_comm] using
      hB.isUnit_sub_smul_one_of_im_ne_zero hz)
  simpa only [mulVec_smul, dotProduct_smul, smul_eq_mul] using hden.ne_zero

/-- **Rank-one resolvent identity.** A real rank-one perturbation changes the resolvent by an
explicit outer product. Both shifted matrices are automatically invertible at non-real `z`. -/
theorem inv_add_smul_vecMulVec_sub_smul_one (c : ℝ) (u : n → 𝕜) {z : 𝕜}
    (hz : RCLike.im z ≠ 0) :
    (A + (c : 𝕜) • vecMulVec u (star u) - z • 1)⁻¹ = (A - z • 1)⁻¹ -
      ((c : 𝕜) / (1 + (c : 𝕜) * (star u ⬝ᵥ ((A - z • 1)⁻¹ *ᵥ u)))) •
        vecMulVec ((A - z • 1)⁻¹ *ᵥ u) (star u ᵥ* (A - z • 1)⁻¹) := by
  have hden : 1 + star u ⬝ᵥ ((A - z • 1)⁻¹ *ᵥ ((c : 𝕜) • u)) =
      1 + (c : 𝕜) * (star u ⬝ᵥ ((A - z • 1)⁻¹ *ᵥ u)) := by
    simp only [mulVec_smul, dotProduct_smul, smul_eq_mul]
  have hd : IsUnit (1 + star u ⬝ᵥ ((A - z • 1)⁻¹ *ᵥ ((c : 𝕜) • u))) := by
    rw [hden]
    exact isUnit_iff_ne_zero.mpr
      (hA.one_add_mul_dotProduct_inv_sub_smul_one_ne_zero c u hz)
  have h := inv_add_vecMulVec (A - z • 1)
    (hA.isUnit_sub_smul_one_of_im_ne_zero hz) ((c : 𝕜) • u) (star u) hd
  rw [hden, smul_vecMulVec, mulVec_smul, smul_vecMulVec,
    Ring.inverse_eq_inv', smul_smul] at h
  rw [add_sub_right_comm, h, div_eq_mul_inv]
  congr 2
  exact mul_comm _ _

/-- Entrywise form of the real rank-one resolvent update. -/
theorem inv_add_smul_vecMulVec_sub_smul_one_apply (c : ℝ) (u : n → 𝕜) {z : 𝕜}
    (hz : RCLike.im z ≠ 0) (i j : n) :
    (A + (c : 𝕜) • vecMulVec u (star u) - z • 1)⁻¹ i j = (A - z • 1)⁻¹ i j -
      ((c : 𝕜) / (1 + (c : 𝕜) * (star u ⬝ᵥ ((A - z • 1)⁻¹ *ᵥ u)))) *
        (((A - z • 1)⁻¹ *ᵥ u) i * (star u ᵥ* (A - z • 1)⁻¹) j) := by
  rw [hA.inv_add_smul_vecMulVec_sub_smul_one c u hz]
  simp only [sub_apply, smul_apply, smul_eq_mul, vecMulVec_apply]

/-- Trace form of the real rank-one resolvent update. The numerator of the correction is the
quadratic form of the square of the original resolvent, not its squared modulus. -/
theorem trace_inv_add_smul_vecMulVec_sub_smul_one (c : ℝ) (u : n → 𝕜) {z : 𝕜}
    (hz : RCLike.im z ≠ 0) :
    (A + (c : 𝕜) • vecMulVec u (star u) - z • 1)⁻¹.trace = (A - z • 1)⁻¹.trace -
      ((c : 𝕜) / (1 + (c : 𝕜) * (star u ⬝ᵥ ((A - z • 1)⁻¹ *ᵥ u)))) *
        (star u ⬝ᵥ (((A - z • 1)⁻¹ * (A - z • 1)⁻¹) *ᵥ u)) := by
  rw [hA.inv_add_smul_vecMulVec_sub_smul_one c u hz, trace_sub, trace_smul, trace_vecMulVec,
    dotProduct_comm ((A - z • 1)⁻¹ *ᵥ u) (star u ᵥ* (A - z • 1)⁻¹),
    ← dotProduct_mulVec, mulVec_mulVec, smul_eq_mul]

end Matrix.IsHermitian
