/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.LinearAlgebra.Matrix.Block
import TauCeti.LinearAlgebra.Matrix.Triangular

/-!
# Unitary triangular matrices over `ℝ` and `ℂ`

The algebraic API for triangular matrices lives in `TauCeti.LinearAlgebra.Matrix.Triangular`. This
file adds the fact about them that needs the order on an `RCLike` field: a unitary upper
triangular matrix with positive diagonal is the identity. In Lie-theoretic language the unitary
group meets the upper triangular matrices with positive diagonal only in `1`, the identity
`K ∩ A N = 1` behind the uniqueness of the Iwasawa decomposition, the `QR` factorization and the
Cholesky factorization.

## Main results

* `Matrix.IsUpperTriangular.eq_one_of_mem_unitaryGroup`: a unitary upper triangular matrix with
  positive diagonal is the identity.
-/

public section

open scoped ComplexOrder

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- **A unitary upper triangular matrix with positive diagonal is the identity.** Over `ℝ` or `ℂ`,
the unitary group meets the group of upper triangular matrices with positive diagonal only in the
identity: this is `K ∩ A N = 1` in the Iwasawa decomposition. -/
theorem IsUpperTriangular.eq_one_of_mem_unitaryGroup {M : Matrix ι ι 𝕜}
    (hM : M.IsUpperTriangular) (hMU : M ∈ unitaryGroup ι 𝕜) (hpos : ∀ i, 0 < M i i) : M = 1 := by
  have hright : M * star M = 1 := mem_unitaryGroup_iff.1 hMU
  let _ : Invertible M := invertibleOfRightInverse M (star M) hright
  -- `star M` is the inverse of `M`, so it is upper triangular as `M` is
  have hstar : (star M).IsUpperTriangular := by
    rw [← inv_eq_right_inv hright]
    exact blockTriangular_inv_of_blockTriangular hM
  ext i j
  rcases lt_trichotomy i j with hij | rfl | hij
  · rw [one_apply_ne hij.ne]
    simpa [star_apply] using hstar hij
  · obtain ⟨r, hr, hri⟩ := RCLike.pos_iff_exists_ofReal.1 (hpos i)
    have h : M i i * star (M i i) = 1 := by
      rw [← star_apply, ← mul_apply_diag_of_isUpperTriangular hM hstar, hright, one_apply_eq]
    rw [← hri, RCLike.star_def, RCLike.conj_ofReal, ← RCLike.ofReal_mul, ← RCLike.ofReal_one,
      RCLike.ofReal_inj] at h
    rw [one_apply_eq, ← hri, ← RCLike.ofReal_one, RCLike.ofReal_inj]
    rcases mul_self_eq_one_iff.1 h with h | h
    · exact h
    · linarith
  · rw [one_apply_ne hij.ne', hM hij]

end Matrix
