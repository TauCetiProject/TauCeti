/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import TauCeti.LinearAlgebra.Matrix.PosSemidef
import Mathlib.Analysis.InnerProductSpace.Reproducing

/-!
# Gram matrices and positive-semidefinite matrices

For any index type `n` and `RCLike` scalar field `𝕜`, the Gram matrix `(i, j) ↦ ⟪v i, v j⟫_𝕜` of a
family `v : n → E` in an inner product space is positive semidefinite (`TauCeti.posSemidef_gram`
and `Matrix.posSemidef_gram`).

Conversely, every positive-semidefinite matrix `C : Matrix n n 𝕜` indexed by an arbitrary type `n`
is the Gram matrix of a family of vectors in a complete Hilbert space over `𝕜`
(`Matrix.PosSemidef.exists_gram_eq`), obtained from Moore's reproducing-kernel construction
`RKHS.OfKernel` with scalar-multiplication kernel `C i j • id`. When `n` is finite, `C` is already
the Gram matrix of a family in `EuclideanSpace 𝕜 n`
(`Matrix.PosSemidef.exists_gram_euclideanSpace_eq`), given by the columns of its Hermitian positive
square root.

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
open scoped ComplexOrder InnerProductSpace MatrixOrder

namespace TauCeti

variable {𝕜 E n : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

variable (𝕜) in
/-- The Gram matrix of a family of vectors indexed by an arbitrary type is positive semidefinite.
This drops the finiteness hypothesis of Mathlib's `Matrix.posSemidef_gram`. -/
theorem posSemidef_gram (v : n → E) : (gram 𝕜 v).PosSemidef := by
  -- Test finite subfamilies in `Type`: each is a finite Gram matrix, covered by Mathlib's theorem.
  refine posSemidef_iff_finite_sum.{_, _, 0}.mpr
    ⟨fun a b ↦ (isHermitian_gram 𝕜 v).apply b a, fun {ι} _ w x ↦ ?_⟩
  simpa only [dotProduct, mulVec, gram_apply, Function.comp_apply, Pi.star_apply,
    Finset.mul_sum, mul_assoc] using
      (Matrix.posSemidef_gram 𝕜 (v ∘ w)).dotProduct_mulVec_nonneg x

end TauCeti

namespace Matrix

universe u v

/-- **Gram realization of positive-semidefinite kernels.** Every positive-semidefinite matrix
`C : Matrix n n 𝕜` indexed by an arbitrary type `n` is the Gram matrix of a family of vectors in a
complete Hilbert space over `𝕜`. -/
theorem PosSemidef.exists_gram_eq {𝕜 : Type u} {n : Type v} [RCLike 𝕜] {C : Matrix n n 𝕜}
    (hC : C.PosSemidef) :
    ∃ (H : Type (max u v)) (_ : NormedAddCommGroup H) (_ : InnerProductSpace 𝕜 H)
      (_ : CompleteSpace H) (v : n → H), gram 𝕜 v = C := by
  -- Interpret `C` as an operator-valued reproducing kernel on the one-dimensional space `𝕜`.
  let K : Matrix n n (𝕜 →L[𝕜] 𝕜) := of fun i j ↦ C i j • ContinuousLinearMap.id 𝕜 𝕜
  have hK : K.PosSemidef := by
    refine RKHS.posSemidef_iff_re_sum_kernel'.mpr ⟨?_, fun vv ↦ ?_⟩
    · ext i j
      simp [K, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_id,
        hC.isHermitian.apply]
    · have hsum : (vv.sum fun x w ↦ vv.sum fun x' w' ↦ ⟪K x' x w, w'⟫_𝕜) =
          vv.sum fun x w ↦ vv.sum fun x' w' ↦ star w * C x x' * w' := by
        refine Finsupp.sum_congr fun x _ ↦ Finsupp.sum_congr fun x' _ ↦ ?_
        simp [K, ← hC.isHermitian.apply x x', mul_comm, mul_left_comm]
      rw [hsum]
      exact (RCLike.nonneg_iff.mp (hC.2 vv)).1
  have : Fact K.PosSemidef := ⟨hK⟩
  refine ⟨RKHS.OfKernel K, inferInstance, inferInstance, inferInstance,
    fun i ↦ RKHS.kerFun (RKHS.OfKernel K) i 1, ?_⟩
  ext i j
  rw [gram_apply, ← RKHS.kernel_inner, RKHS.OfKernel.kernel_ofKernel]
  simpa [K] using hC.isHermitian.apply i j

/-- A matrix of arbitrary index type over `𝕜` (`ℝ` or `ℂ`) is positive semidefinite if and only if
it is the Gram matrix of a family of vectors in a complete Hilbert space over `𝕜`. -/
theorem posSemidef_iff_exists_gram_eq {𝕜 : Type u} {n : Type v} [RCLike 𝕜] {C : Matrix n n 𝕜} :
    C.PosSemidef ↔
      ∃ (H : Type (max u v)) (_ : NormedAddCommGroup H) (_ : InnerProductSpace 𝕜 H)
        (_ : CompleteSpace H) (v : n → H), gram 𝕜 v = C :=
  ⟨PosSemidef.exists_gram_eq, fun ⟨_, _, _, _, v, hv⟩ ↦ hv ▸ Matrix.posSemidef_gram 𝕜 v⟩

/-- Every finite-index positive-semidefinite matrix `C : Matrix n n 𝕜` is the Gram matrix of a
family of vectors in `EuclideanSpace 𝕜 n`, namely the columns of a Hermitian square root of `C`. -/
theorem PosSemidef.exists_gram_euclideanSpace_eq {𝕜 : Type u} {n : Type v} [RCLike 𝕜] [Fintype n]
    {C : Matrix n n 𝕜} (hC : C.PosSemidef) :
    ∃ v : n → EuclideanSpace 𝕜 n, gram 𝕜 v = C := by
  classical
  obtain ⟨X, hX, -, rfl⟩ :=
    CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts hC.isHermitian
      (QuasispectrumRestricts.nnreal_of_nonneg hC.nonneg)
  refine ⟨fun j ↦ WithLp.toLp 2 fun i ↦ X i j, ?_⟩
  rw [gram_eq_conjTranspose_mul (EuclideanSpace.basisFun n 𝕜)]
  have hrepr : (of fun i j ↦ (EuclideanSpace.basisFun n 𝕜).repr
      (WithLp.toLp 2 fun k ↦ X k j) i) = X := by
    ext i j
    simp
  rw [hrepr, ← star_eq_conjTranspose, hX.star_eq]

/-- A finite-index matrix over `𝕜` (`ℝ` or `ℂ`) is positive semidefinite if and only if it is the
Gram matrix of a family of vectors in `EuclideanSpace 𝕜 n`. -/
theorem posSemidef_iff_exists_gram_euclideanSpace_eq {𝕜 : Type u} {n : Type v} [RCLike 𝕜]
    [Fintype n] {C : Matrix n n 𝕜} :
    C.PosSemidef ↔ ∃ v : n → EuclideanSpace 𝕜 n, gram 𝕜 v = C :=
  ⟨PosSemidef.exists_gram_euclideanSpace_eq, fun ⟨v, hv⟩ ↦ hv ▸ Matrix.posSemidef_gram 𝕜 v⟩

end Matrix
