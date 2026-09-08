/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.PosDef

/-!
# Eigen-coordinates of a Hermitian matrix

Let `B` be a Hermitian matrix over an `RCLike` field with orthonormal eigenvector basis
`hB.eigenvectorBasis` and real eigenvalues `hB.eigenvalues`. This file reads three quantities
off the eigen-coordinates: the quadratic form `x ↦ ⟪x, B x⟫`, which becomes a weighted sum of
squared moduli, and the diagonalization and the determinant of the pencil `1 - c • B`, which are
read off the scalars `1 - c * hB.eigenvalues j`. The pencil is diagonal in the eigenbasis for
any scalar `c`; only its positive definiteness asks for a real one.

These are the spectral facts behind the moment-generating function of a Gaussian quadratic form,
whose exponential-integrability domain is a positive-definiteness condition on such a pencil and
whose value is a power of its determinant.

## Main results

* `Matrix.IsHermitian.inner_toEuclideanLin_sum_smul_eigenvectorBasis` — the quadratic form of
  `B` at `∑ j, c j • b j` is `∑ j, hB.eigenvalues j * ‖c j‖ ^ 2`;
* `Matrix.IsHermitian.posDef_one_sub_smul_iff` — `1 - c • B` is positive definite exactly when
  `c * hB.eigenvalues j < 1` for every `j`;
* `Matrix.IsHermitian.one_sub_smul_eq_conjStarAlgAut_diagonal` and
  `Matrix.IsHermitian.det_one_sub_smul` — `1 - c • B` is conjugate to a diagonal matrix, and its
  determinant is `∏ j, (1 - c * hB.eigenvalues j)`.
-/

public section

noncomputable section

open Unitary
open scoped InnerProductSpace

namespace Matrix.IsHermitian

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι] {B : Matrix ι ι 𝕜}
  (hB : B.IsHermitian)
include hB

/-- In the eigen-coordinates of a Hermitian matrix, its quadratic form is the sum of the squared
moduli of the coordinates weighted by the eigenvalues. -/
theorem inner_toEuclideanLin_sum_smul_eigenvectorBasis (c : ι → 𝕜) :
    ⟪∑ j, c j • hB.eigenvectorBasis j,
      B.toEuclideanLin (∑ j, c j • hB.eigenvectorBasis j)⟫_𝕜 =
      ∑ j, (hB.eigenvalues j : 𝕜) * (‖c j‖ : 𝕜) ^ 2 := by
  have hb (j : ι) : B.toEuclideanLin (hB.eigenvectorBasis j) =
      (hB.eigenvalues j : 𝕜) • hB.eigenvectorBasis j := by
    rw [← RCLike.real_smul_eq_coe_smul (K := 𝕜)]
    simp [toLpLin_apply, hB.mulVec_eigenvectorBasis]
  rw [map_sum]
  simp_rw [map_smul, hb, smul_smul]
  rw [hB.eigenvectorBasis.orthonormal.inner_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← mul_assoc, RCLike.conj_mul]
  ring

/-- The pencil `1 - c • B` is conjugate, by the eigenvector unitary of `B`, to the diagonal matrix
with entries `1 - c * hB.eigenvalues j`. -/
theorem one_sub_smul_eq_conjStarAlgAut_diagonal (c : 𝕜) :
    1 - c • B =
      conjStarAlgAut 𝕜 _ hB.eigenvectorUnitary
        (diagonal fun j => 1 - c * (hB.eigenvalues j : 𝕜)) := by
  have h : (diagonal fun j => 1 - c * (hB.eigenvalues j : 𝕜)) =
      1 - c • diagonal (RCLike.ofReal ∘ hB.eigenvalues) := by
    simp [← diagonal_one, ← diagonal_sub, ← diagonal_smul, Pi.smul_def]
  rw [h, map_sub, map_one, map_smul, ← hB.spectral_theorem]

open scoped ComplexOrder in
/-- The pencil `1 - c • B` is positive definite exactly when `c * hB.eigenvalues j < 1` for every
eigenvalue. -/
theorem posDef_one_sub_smul_iff (c : ℝ) :
    (1 - c • B).PosDef ↔ ∀ j, c * hB.eigenvalues j < 1 := by
  have hentry (j : ι) : 1 - (c : 𝕜) * (hB.eigenvalues j : 𝕜) =
      ((1 - c * hB.eigenvalues j : ℝ) : 𝕜) := by push_cast; ring
  rw [RCLike.real_smul_eq_coe_smul (K := 𝕜),
    hB.one_sub_smul_eq_conjStarAlgAut_diagonal (c : 𝕜), conjStarAlgAut_apply,
    IsUnit.posDef_star_right_conjugate_iff isUnit_coe, posDef_diagonal_iff]
  simp only [hentry, RCLike.ofReal_pos, sub_pos]

/-- The determinant of the pencil `1 - c • B` is the product of `1 - c * hB.eigenvalues j` over
the eigenvalues. -/
theorem det_one_sub_smul (c : 𝕜) :
    (1 - c • B).det = ∏ j, (1 - c * (hB.eigenvalues j : 𝕜)) := by
  rw [hB.one_sub_smul_eq_conjStarAlgAut_diagonal c, conjStarAlgAut_apply, det_mul, det_mul,
    mul_right_comm, ← det_mul, mul_star_self_of_mem hB.eigenvectorUnitary.2, det_one,
    one_mul, det_diagonal]

end Matrix.IsHermitian
