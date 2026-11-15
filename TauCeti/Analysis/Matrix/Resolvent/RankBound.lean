/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.SpectralMeasure.Basic
public import TauCeti.Analysis.Matrix.Trace.Rank

import TauCeti.LinearAlgebra.Matrix.Rank

/-!
# Low-rank bounds for Hermitian resolvent traces

For Hermitian matrices `A, B` and nonreal `z`, the difference of their resolvents has rank
`rank (A - B)` and Euclidean operator norm at most `1 / |Im z|`. Consequently
`|tr R_A(z) - tr R_B(z)| ≤ rank (A - B) / |Im z|`, and their empirical spectral transforms
differ by at most `rank (A - B) / (n |Im z|)`. No bound on the size of `A - B` is needed.
These estimates control the error from deleting or replacing a low-rank part of a matrix
in the resolvent method for global spectral laws.

The norm estimate uses the unit-disc bound for the Cayley expression
`1 + (z - conj z) • R_A(z)`, rather than the less precise triangle bound on the two resolvents.
All unnormalized estimates allow empty index types; spectral probability measures require
positive dimension. The resolvent convention is `R_A(z) = (A - z • 1)⁻¹`.

## References

* Z. D. Bai, *Methodologies in spectral analysis of large dimensional random matrices, a review*,
  Statistica Sinica 9 (1999), §2.2.
* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.4.
-/

public section

open MeasureTheory
open scoped ComplexConjugate Matrix.Norms.L2Operator

namespace Matrix.IsHermitian

variable {n : Type*} [Fintype n] [DecidableEq n] {A B : Matrix n n ℂ}

/-- Taking resolvents at a fixed nonreal parameter preserves the rank of the difference. -/
theorem rank_inv_sub_smul_one_sub {𝕜 : Type*} [RCLike 𝕜] {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) {z : 𝕜} (hz : RCLike.im z ≠ 0) :
    ((A - z • 1)⁻¹ - (B - z • 1)⁻¹).rank = (A - B).rank := by
  simpa only [sub_sub_sub_cancel_right] using rank_inv_sub_inv
    (hA.isUnit_sub_smul_one_of_im_ne_zero hz) (hB.isUnit_sub_smul_one_of_im_ne_zero hz)

/-- The trace error of a low-rank Hermitian perturbation is at most its rank divided by the
absolute imaginary part of the parameter. -/
theorem norm_trace_inv_sub_smul_one_sub_le_rank (hA : A.IsHermitian) (hB : B.IsHermitian)
    {z : ℂ} (hz : z.im ≠ 0) :
    ‖(A - z • 1)⁻¹.trace - (B - z • 1)⁻¹.trace‖ ≤ (A - B).rank / |z.im| := by
  rw [← trace_sub, div_eq_mul_inv]
  have h := norm_trace_le_rank_mul_l2_opNorm ((A - z • 1)⁻¹ - (B - z • 1)⁻¹)
  rw [hA.rank_inv_sub_smul_one_sub hB hz] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (hA.l2_opNorm_inv_sub_smul_one_sub_le hB hz) (Nat.cast_nonneg _))

/-- Low-rank perturbations change the empirical spectral transform by at most
`rank (A - B) / (n |Im z|)`. -/
theorem norm_resolventTransform_spectralMeasure_sub_le_rank [Nonempty n]
    (hA : A.IsHermitian) (hB : B.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
    ‖resolventTransform (A.spectralMeasure hA : Measure ℝ) z -
        resolventTransform (B.spectralMeasure hB : Measure ℝ) z‖ ≤
      (A - B).rank / ((Fintype.card n : ℝ) * |z.im|) := by
  rw [resolventTransform_spectralMeasure A hA (hA.notMem_spectrum_of_im_ne_zero hz),
    resolventTransform_spectralMeasure B hB (hB.notMem_spectrum_of_im_ne_zero hz),
    ← mul_sub, norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (Fintype.card n : ℝ)⁻¹ * ((A - B).rank / |z.im|) :=
      mul_le_mul_of_nonneg_left (hA.norm_trace_inv_sub_smul_one_sub_le_rank hB hz)
        (by positivity)
    _ = _ := by ring

end Matrix.IsHermitian
