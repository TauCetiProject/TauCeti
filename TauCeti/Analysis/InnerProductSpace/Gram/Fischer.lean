/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import TauCeti.Analysis.Matrix.PosSemidef.Basic
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

/-- The Gram matrix of three concatenated families, with the two complementary families
split into separate blocks. -/
theorem gram_sumElim_sumElim (u : ι → E) (v : κ → E) (w : η → E) :
    gram 𝕜 (Sum.elim u (Sum.elim v w)) =
      fromBlocks (gram 𝕜 u)
        (fromCols (of fun i j ↦ ⟪u i, v j⟫_𝕜) (of fun i j ↦ ⟪u i, w j⟫_𝕜))
        (fromCols (of fun i j ↦ ⟪u i, v j⟫_𝕜) (of fun i j ↦ ⟪u i, w j⟫_𝕜))ᴴ
        (fromBlocks (gram 𝕜 v) (of fun i j ↦ ⟪v i, w j⟫_𝕜)
          (of fun i j ↦ ⟪v i, w j⟫_𝕜)ᴴ (gram 𝕜 w)) := by
  have hcols : (of fun i j ↦ ⟪u i, Sum.elim v w j⟫_𝕜) =
      fromCols (of fun i j ↦ ⟪u i, v j⟫_𝕜) (of fun i j ↦ ⟪u i, w j⟫_𝕜) := by
    ext i j
    cases j <;> simp
  simp only [gram_sumElim, hcols]

variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype η] [DecidableEq η]

/-- Gram determinants satisfy Koteljanskii's overlapping-family inequality over
real or complex scalars, including empty and dependent families. -/
theorem det_gram_mul_det_gram_sumElim_le (u : ι → E) (v : κ → E) (w : η → E) :
    (gram 𝕜 u).det * (gram 𝕜 (Sum.elim u (Sum.elim v w))).det ≤
      (gram 𝕜 (Sum.elim u v)).det * (gram 𝕜 (Sum.elim u w)).det := by
  have h := posSemidef_gram 𝕜 (Sum.elim u (Sum.elim v w))
  rw [gram_sumElim_sumElim] at h
  rw [gram_sumElim_sumElim u v w, gram_sumElim u v, gram_sumElim u w]
  exact h.det_mul_det_fromBlocks_le

/-- The real parts of Gram determinants satisfy the overlapping-family
Hadamard--Fischer inequality, also called Koteljanskii's inequality. -/
theorem re_det_gram_mul_re_det_gram_sumElim_le (u : ι → E) (v : κ → E) (w : η → E) :
    RCLike.re (gram 𝕜 u).det * RCLike.re (gram 𝕜 (Sum.elim u (Sum.elim v w))).det ≤
      RCLike.re (gram 𝕜 (Sum.elim u v)).det *
        RCLike.re (gram 𝕜 (Sum.elim u w)).det := by
  have hbound := det_gram_mul_det_gram_sumElim_le (𝕜 := 𝕜) u v w
  rw [← (isHermitian_gram 𝕜 u).ofReal_re_det,
    ← (isHermitian_gram 𝕜 (Sum.elim u (Sum.elim v w))).ofReal_re_det,
    ← (isHermitian_gram 𝕜 (Sum.elim u v)).ofReal_re_det,
    ← (isHermitian_gram 𝕜 (Sum.elim u w)).ofReal_re_det] at hbound
  exact_mod_cast hbound

end Matrix
