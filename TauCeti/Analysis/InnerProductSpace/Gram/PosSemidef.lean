/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import TauCeti.LinearAlgebra.Matrix.PosSemidef
import TauCeti.Analysis.Matrix.GramFactorization
import TauCeti.Analysis.PositiveDefinite.Kernel.Kolmogorov

/-!
# Gram matrices and positive-semidefinite matrices

For any index type `n` and `RCLike` scalar field `𝕜`, the Gram matrix `(i, j) ↦ ⟪v i, v j⟫_𝕜` of a
family `v : n → E` in an inner product space is positive semidefinite (`TauCeti.posSemidef_gram`
and `Matrix.posSemidef_gram`).

Conversely, every positive-semidefinite matrix `C : Matrix n n 𝕜` indexed by an arbitrary type `n`
is the Gram matrix of a family of vectors in a complete Hilbert space over `𝕜`
(`Matrix.PosSemidef.exists_gram_eq`), obtained from the Kolmogorov reproducing-kernel decomposition
`Matrix.PosSemidef.KolmogorovSpace` (built on Mathlib's `RKHS.OfKernel`). When `n` is finite, `C` is
already the Gram matrix of a family in `EuclideanSpace 𝕜 n`
(`Matrix.PosSemidef.exists_gram_euclideanSpace_eq`), obtained from the matrix factorization
`C = Xᴴ * X` (`Matrix.posSemidef_iff_eq_conjTranspose_mul_self`).

## Main results

* `TauCeti.posSemidef_gram`: the Gram matrix of an arbitrary family is positive semidefinite.
* `Matrix.PosSemidef.exists_gram_eq`, `Matrix.posSemidef_iff_exists_gram_eq`: a matrix of arbitrary
  index type is positive semidefinite if and only if it is the Gram matrix of a family in a
  complete Hilbert space.
* `Matrix.PosSemidef.exists_gram_euclideanSpace_eq`,
  `Matrix.posSemidef_iff_exists_gram_euclideanSpace_eq`: a finite-index matrix is positive
  semidefinite if and only if it is the Gram matrix of a family in `EuclideanSpace 𝕜 n`.

## References

* V. I. Paulsen, M. Raghupathi, *An Introduction to the Theory of Reproducing Kernel Hilbert
  Spaces*, Cambridge University Press (2016), Theorem 2.14 (Moore's theorem).
-/

public section

open Matrix
open scoped ComplexOrder InnerProductSpace

namespace TauCeti

variable {𝕜 E n : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

variable (𝕜) in
/-- The Gram matrix of a family of vectors indexed by an arbitrary type is positive semidefinite. -/
theorem posSemidef_gram (v : n → E) : (gram 𝕜 v).PosSemidef :=
  Matrix.posSemidef_gram 𝕜 v

end TauCeti

namespace Matrix

universe u v

/-- **Gram realization of positive-semidefinite kernels.** Every positive-semidefinite matrix
`C : Matrix n n 𝕜` indexed by an arbitrary type `n` is the Gram matrix of a family of vectors in a
complete Hilbert space over `𝕜`. -/
theorem PosSemidef.exists_gram_eq {𝕜 : Type u} {n : Type v} [RCLike 𝕜] {C : Matrix n n 𝕜}
    (hC : C.PosSemidef) :
    ∃ (H : Type (max u v)) (_ : NormedAddCommGroup H) (_ : InnerProductSpace 𝕜 H)
      (_ : CompleteSpace H) (v : n → H), gram 𝕜 v = C :=
  ⟨hC.KolmogorovSpace, inferInstance, inferInstance, inferInstance,
    hC.kolmogorovFeature, Matrix.ext hC.inner_kolmogorovFeature⟩

/-- A matrix of arbitrary index type over `𝕜` (`ℝ` or `ℂ`) is positive semidefinite if and only if
it is the Gram matrix of a family of vectors in a complete Hilbert space over `𝕜`. -/
theorem posSemidef_iff_exists_gram_eq {𝕜 : Type u} {n : Type v} [RCLike 𝕜] {C : Matrix n n 𝕜} :
    C.PosSemidef ↔
      ∃ (H : Type (max u v)) (_ : NormedAddCommGroup H) (_ : InnerProductSpace 𝕜 H)
        (_ : CompleteSpace H) (v : n → H), gram 𝕜 v = C :=
  ⟨PosSemidef.exists_gram_eq, fun ⟨_, _, _, _, v, hv⟩ ↦ hv ▸ Matrix.posSemidef_gram 𝕜 v⟩

/-- Every finite-index positive-semidefinite matrix `C : Matrix n n 𝕜` is the Gram matrix of a
family of vectors in `EuclideanSpace 𝕜 n`. -/
theorem PosSemidef.exists_gram_euclideanSpace_eq {𝕜 : Type u} {n : Type v} [RCLike 𝕜] [Fintype n]
    {C : Matrix n n 𝕜} (hC : C.PosSemidef) :
    ∃ v : n → EuclideanSpace 𝕜 n, gram 𝕜 v = C := by
  classical
  obtain ⟨X, rfl⟩ := posSemidef_iff_eq_conjTranspose_mul_self.mp hC
  refine ⟨fun j ↦ WithLp.toLp 2 (X · j), ?_⟩
  rw [gram_eq_conjTranspose_mul (EuclideanSpace.basisFun n 𝕜)]
  congr 2

/-- A finite-index matrix over `𝕜` (`ℝ` or `ℂ`) is positive semidefinite if and only if it is the
Gram matrix of a family of vectors in `EuclideanSpace 𝕜 n`. -/
theorem posSemidef_iff_exists_gram_euclideanSpace_eq {𝕜 : Type u} {n : Type v} [RCLike 𝕜]
    [Fintype n] {C : Matrix n n 𝕜} :
    C.PosSemidef ↔ ∃ v : n → EuclideanSpace 𝕜 n, gram 𝕜 v = C :=
  ⟨PosSemidef.exists_gram_euclideanSpace_eq, fun ⟨v, hv⟩ ↦ hv ▸ Matrix.posSemidef_gram 𝕜 v⟩

end Matrix
