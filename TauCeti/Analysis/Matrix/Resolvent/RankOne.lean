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

The matrix, entrywise, trace and quadratic-form identities apply also to negative `c`, zero
vectors and empty index types. The quadratic form of the updated resolvent along `u` is
`q / (1 + c q)`, where `q = uᴴ R u`. For positive semidefinite `A` and `c ≥ 0` the denominator
satisfies `|(1 + c q)⁻¹| ≤ |z| / |Im z|`, because `Im (z q) = Im z · wᴴ A w` with `w = R u`.
Trace updates and these quadratic forms are used when adding or removing one sample in a Gram
matrix in the resolvent method for sample-covariance spectral laws.

## References

* Z. D. Bai, *Methodologies in spectral analysis of large dimensional random matrices, a review*,
  Statistica Sinica 9 (1999), 611–677, §2.2.
* R. A. Horn, C. R. Johnson, *Matrix Analysis*, 2nd ed., Cambridge University Press, 2013,
  §0.7.4 (the Sherman–Morrison–Woodbury formula).
-/

public section

noncomputable section

open scoped ComplexOrder

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
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, vecMulVec_apply]

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

/-- **Quadratic form of a rank-one updated resolvent.** Along the update direction `u`, the
updated resolvent has quadratic form `q / (1 + c q)`, where `q = uᴴ (A - z • 1)⁻¹ u`. -/
theorem dotProduct_inv_add_smul_vecMulVec_sub_smul_one_mulVec (c : ℝ) (u : n → 𝕜) {z : 𝕜}
    (hz : RCLike.im z ≠ 0) :
    star u ⬝ᵥ ((A + (c : 𝕜) • vecMulVec u (star u) - z • 1)⁻¹ *ᵥ u) =
      star u ⬝ᵥ ((A - z • 1)⁻¹ *ᵥ u) /
        (1 + (c : 𝕜) * (star u ⬝ᵥ ((A - z • 1)⁻¹ *ᵥ u))) := by
  have hden := hA.one_add_mul_dotProduct_inv_sub_smul_one_ne_zero c u hz
  rw [hA.inv_add_smul_vecMulVec_sub_smul_one c u hz, sub_mulVec, smul_mulVec, vecMulVec_mulVec,
    dotProduct_sub, dotProduct_smul, dotProduct_smul, ← dotProduct_mulVec]
  generalize star u ⬝ᵥ ((A - z • 1)⁻¹ *ᵥ u) = q at hden ⊢
  simp only [MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, smul_eq_mul]
  rw [eq_div_iff hden, sub_mul, div_mul_eq_mul_div, div_mul_eq_mul_div,
    mul_div_cancel_right₀ _ hden]
  ring

/-- The imaginary part of `z uᴴ R u`, for the resolvent `R = (A - z • 1)⁻¹`, is `Im z` times the
real quadratic form `wᴴ A w` of the vector `w = R u`. If `A - z • 1` is singular, then `R = 0` by
the convention for `⁻¹` and both sides vanish. -/
theorem im_mul_dotProduct_inv_sub_smul_one_mulVec (u : n → 𝕜) (z : 𝕜) :
    RCLike.im (z * (star u ⬝ᵥ ((A - z • 1)⁻¹ *ᵥ u))) =
      RCLike.im z *
        RCLike.re (star ((A - z • 1)⁻¹ *ᵥ u) ⬝ᵥ (A *ᵥ ((A - z • 1)⁻¹ *ᵥ u))) := by
  by_cases hdet : IsUnit (A - z • 1).det
  swap
  · simp [nonsing_inv_apply_not_isUnit _ hdet]
  set w := (A - z • 1)⁻¹ *ᵥ u
  have hu : u = (A - z • 1) *ᵥ w := by
    rw [mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
  -- Writing `u = (A - z • 1) w` turns `uᴴ w` into `wᴴ A w - conj z * wᴴ w`.
  have hq : star u ⬝ᵥ w = star w ⬝ᵥ (A *ᵥ w) - star z * (star w ⬝ᵥ w) := by
    conv_lhs => rw [hu]
    rw [star_mulVec, ← dotProduct_mulVec, conjTranspose_sub, hA.eq, conjTranspose_smul,
      conjTranspose_one, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul,
      smul_eq_mul]
  have ha := hA.im_star_dotProduct_mulVec_self w
  have hw := (RCLike.nonneg_iff.mp (dotProduct_star_self_nonneg w)).2
  rw [hq, mul_sub, ← mul_assoc, RCLike.star_def, RCLike.mul_conj]
  simp [RCLike.mul_im, ha, hw]

end Matrix.IsHermitian

namespace Matrix.PosSemidef

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n] {A : Matrix n n 𝕜}

/-- For positive semidefinite `A` and `c ≥ 0`, the inverse of the denominator `1 + c uᴴ R u` of a
rank-one resolvent update is bounded by `|z| / |Im z|`, uniformly in `A`, `c` and `u`. -/
theorem norm_inv_one_add_mul_dotProduct_inv_sub_smul_one_mulVec_le (hA : A.PosSemidef)
    {c : ℝ} (hc : 0 ≤ c) (u : n → 𝕜) {z : 𝕜} (hz : RCLike.im z ≠ 0) :
    ‖(1 + (c : 𝕜) * (star u ⬝ᵥ ((A - z • 1)⁻¹ *ᵥ u)))⁻¹‖ ≤ ‖z‖ / |RCLike.im z| := by
  have hden := hA.isHermitian.one_add_mul_dotProduct_inv_sub_smul_one_ne_zero c u hz
  have him := hA.isHermitian.im_mul_dotProduct_inv_sub_smul_one_mulVec u z
  have hr := (RCLike.nonneg_iff.mp (hA.dotProduct_mulVec_nonneg ((A - z • 1)⁻¹ *ᵥ u))).1
  generalize star u ⬝ᵥ ((A - z • 1)⁻¹ *ᵥ u) = q at hden him
  generalize RCLike.re (star ((A - z • 1)⁻¹ *ᵥ u) ⬝ᵥ (A *ᵥ ((A - z • 1)⁻¹ *ᵥ u))) = r at hr him
  -- `Im (z (1 + c q)) = Im z (1 + c r)` with `1 + c r ≥ 1`, so `|Im z| ≤ |z| |1 + c q|`.
  have hzD : RCLike.im (z * (1 + c * q)) = RCLike.im z * (1 + c * r) := by
    rw [mul_add, mul_one, mul_left_comm, map_add, RCLike.im_ofReal_mul, him]
    ring
  have hle : |RCLike.im z| ≤ ‖z‖ * ‖1 + (c : 𝕜) * q‖ :=
    calc |RCLike.im z| ≤ |RCLike.im z| * (1 + c * r) :=
          le_mul_of_one_le_right (abs_nonneg _) (by nlinarith)
      _ = |RCLike.im (z * (1 + c * q))| := by
          rw [hzD, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 + c * r)]
      _ ≤ ‖z * (1 + c * q)‖ := RCLike.abs_im_le_norm _
      _ = ‖z‖ * ‖1 + (c : 𝕜) * q‖ := norm_mul _ _
  rw [norm_inv, le_div_iff₀ (abs_pos.mpr hz), inv_mul_le_iff₀ (norm_pos_iff.mpr hden)]
  linarith [mul_comm ‖z‖ ‖1 + (c : 𝕜) * q‖]

end Matrix.PosSemidef
