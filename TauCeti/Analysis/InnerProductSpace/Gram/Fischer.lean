/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import TauCeti.Analysis.Matrix.PosSemidef.Determinant

/-!
# The overlapping-family Gram determinant inequality

For three finite families `u`, `v`, `w`, the product of the Gram determinants
of `u` and `(u,v,w)` is at most the product for `(u,v)` and `(u,w)`.
Taking `u` to be a basis of an intersection and completing it to bases of two
subspaces gives the archimedean determinant estimate for subspace-height
submodularity. No independence or finite-dimensional ambient-space hypothesis
is needed; empty and dependent families are included.

## References

* J.-H. Evertse and R. G. Ferretti, *A further improvement of the quantitative
  Subspace Theorem*, §6.1, (6.12).
* R. A. Horn and C. R. Johnson, *Matrix Analysis*, second edition, §7.8.
-/

public section

open scoped InnerProductSpace ComplexOrder

namespace Matrix

variable {𝕜 E ι κ η : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The Gram matrix of a concatenated family, in block form. -/
theorem gram_sumElim (u : ι → E) (v : κ → E) :
    gram 𝕜 (Sum.elim u v) = fromBlocks (gram 𝕜 u)
      (of fun i j ↦ ⟪u i, v j⟫_𝕜) (of fun i j ↦ ⟪u i, v j⟫_𝕜)ᴴ (gram 𝕜 v) := by
  ext i j
  cases i <;> cases j <;> simp [gram_apply, conjTranspose_apply, inner_conj_symm]

variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype η] [DecidableEq η]

/-- The real parts of Gram determinants satisfy the overlapping-family
Hadamard--Fischer inequality, also called Koteljanskii's inequality. -/
theorem re_det_gram_mul_re_det_gram_sumElim_le (u : ι → E) (v : κ → E) (w : η → E) :
    RCLike.re (gram 𝕜 u).det * RCLike.re (gram 𝕜 (Sum.elim u (Sum.elim v w))).det ≤
      RCLike.re (gram 𝕜 (Sum.elim u v)).det *
        RCLike.re (gram 𝕜 (Sum.elim u w)).det := by
  have h := posSemidef_gram 𝕜 (Sum.elim u (Sum.elim v w))
  rw [gram_sumElim, gram_sumElim] at h
  have hcols : (of fun i j ↦ ⟪u i, Sum.elim v w j⟫_𝕜) =
      fromCols (of fun i j ↦ ⟪u i, v j⟫_𝕜) (of fun i j ↦ ⟪u i, w j⟫_𝕜) := by
    ext i j
    cases j <;> rfl
  rw [hcols] at h
  have hbound := h.det_mul_det_fromBlocks_le
  rw [← hcols, ← gram_sumElim, ← gram_sumElim, ← gram_sumElim,
    ← gram_sumElim] at hbound
  rw [← (isHermitian_gram 𝕜 u).ofReal_re_det,
    ← (isHermitian_gram 𝕜 (Sum.elim u (Sum.elim v w))).ofReal_re_det,
    ← (isHermitian_gram 𝕜 (Sum.elim u v)).ofReal_re_det,
    ← (isHermitian_gram 𝕜 (Sum.elim u w)).ofReal_re_det,
    ← RCLike.ofReal_mul, ← RCLike.ofReal_mul, RCLike.ofReal_le_ofReal] at hbound
  exact hbound

end Matrix
