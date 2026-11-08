/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.LinearAlgebra.Matrix.Rank
public import TauCeti.Analysis.Normed.Lp.PiLp

/-!
# The map of a matrix on Euclidean space

Two ingredients of a linear change of variables on `EuclideanSpace 𝕜 ι`.

Pulling the quadratic form `x ↦ ⟪x, B x⟫` of a square matrix `B` back along the linear map of a
rectangular matrix `A` gives the quadratic form of the congruent matrix `Aᴴ * B * A`. This is
the change-of-variables identity behind every computation of a quadratic statistic after a linear
transformation of the underlying vector.

The rank of a matrix is the rank of the linear map it induces, in both the `ℕ`-valued and the
`Cardinal`-valued sense; this is what lets a matrix-rank statement be read off an operator-rank
one.

Normal square matrices induce normal operators on Euclidean space.
The instance `Matrix.isStarNormal_toEuclideanLin` supplies this normality automatically
from `IsStarNormal A`.

An invertible square matrix induces not just a map but a continuous linear equivalence, whose
inverse is the map of the inverse matrix. That is the form a substitution needs: it supplies the
inverse substitution and, through `LinearMap.det_toLpLin`, the Jacobian.

Conversely, every continuous linear automorphism of Euclidean space is the map of an invertible
matrix. This correspondence is a group isomorphism, and the matrix depends continuously on the
automorphism.

A square matrix is unitary exactly when its continuous linear map preserves the inner product.
The rows of a unitary matrix form an orthonormal basis, so the values of the quadratic form of a
matrix `A` on an orthonormal basis are the diagonal entries of a unitary conjugate of `A`; for a
diagonal matrix `diag(w)` the quadratic form is `x ↦ ∑ᵢ |xᵢ|² wᵢ`.

## Main results

* `Matrix.inner_toEuclideanLin_toEuclideanLin` — the quadratic form of `B` at `A x` is the
  quadratic form of `Aᴴ * B * A` at `x`;
* `Matrix.inner_toEuclideanLin_piLpExtendByZero` — the quadratic form of `A` at a vector extended
  by zero is the quadratic form of the principal submatrix at the original vector;

* `Matrix.re_inner_toEuclideanLin_diagonal_apply_self` — the quadratic form of `diag(w)` is
  `x ↦ ∑ᵢ |xᵢ|² wᵢ`;
* `Matrix.exists_mem_unitaryGroup_mul_mul_star_apply_self_eq_inner` — the values of the quadratic
  form of `A` on an orthonormal basis are the diagonal entries of a unitary conjugate `U A Uᴴ`;
* `Matrix.rank_eq_finrank_range_toEuclideanLin`, `Matrix.rank_coe_toEuclideanCLM` — the matrix
  rank is the dimension of the range of the induced map, and the `LinearMap.rank` of the induced
  continuous linear map;
* `Matrix.mem_unitaryGroup_iff_inner_toEuclideanCLM` — a matrix is unitary exactly when its
  Euclidean operator preserves the inner product;
* `Matrix.toEuclideanCLM_apply_apply` — the coordinate formula for the continuous linear map of
  a matrix, which depends continuously on the matrix (`Matrix.continuous_toEuclideanCLM`) and
  conversely (`Matrix.continuous_toEuclideanCLM_symm`);
* `Matrix.toEuclideanCLE` — the continuous linear equivalence of an invertible matrix, with its
  `apply`, `symm_apply`, coercion and determinant lemmas;
* `Matrix.GeneralLinearGroup.ofEuclideanCLE` — the group isomorphism taking a continuous linear
  automorphism to its invertible matrix, inverse to `Matrix.toEuclideanCLE`; both directions are
  continuous in families
  (`Matrix.GeneralLinearGroup.continuous_ofEuclideanCLE`,
  `Matrix.GeneralLinearGroup.continuous_toEuclideanCLE`).
-/

public section

open scoped InnerProductSpace

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
  [DecidableEq κ]

/-- Pulling the quadratic form of `B` back along the linear map of `A` gives the quadratic form
of the congruent matrix `Aᴴ * B * A`. -/
theorem inner_toEuclideanLin_toEuclideanLin (A : Matrix κ ι 𝕜) (B : Matrix κ κ 𝕜)
    (x : EuclideanSpace 𝕜 ι) :
    ⟪A.toEuclideanLin x, B.toEuclideanLin (A.toEuclideanLin x)⟫_𝕜 =
      ⟪x, (Aᴴ * B * A).toEuclideanLin x⟫_𝕜 := by
  rw [← LinearMap.adjoint_inner_right, ← toEuclideanLin_conjTranspose_eq_adjoint]
  simp only [toEuclideanLin, toLpLin_mul_same, LinearMap.comp_apply]

/-- The quadratic form of `A` at a vector extended by zero along `f` is the quadratic form of the
principal submatrix `A.submatrix f f` at the original vector. -/
theorem inner_toEuclideanLin_piLpExtendByZero (A : Matrix κ κ 𝕜) (f : ι ↪ κ)
    (x : EuclideanSpace 𝕜 ι) :
    ⟪A.toEuclideanLin (LinearIsometry.piLpExtendByZero 2 𝕜 𝕜 f x),
        LinearIsometry.piLpExtendByZero 2 𝕜 𝕜 f x⟫_𝕜 =
      ⟪(A.submatrix f f).toEuclideanLin x, x⟫_𝕜 := by
  have hmul : ∀ b, (A.mulVec (LinearIsometry.piLpExtendByZero 2 𝕜 𝕜 f x).ofLp) b =
      ∑ c, A b (f c) * x c := fun b => by
    simpa [mulVec, dotProduct] using LinearIsometry.sum_mul_piLpExtendByZero f x (A b)
  simp only [PiLp.inner_apply, toLpLin_apply, RCLike.inner_apply]
  conv_lhs => enter [2, b]; rw [mul_comm]
  rw [LinearIsometry.sum_mul_piLpExtendByZero f x (fun b => (starRingEnd 𝕜)
    (A.mulVec (LinearIsometry.piLpExtendByZero 2 𝕜 𝕜 f x).ofLp b))]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [mul_comm, hmul (f a)]
  simp [mulVec, dotProduct]

/-- The quadratic form of the diagonal operator `diag(w)` on Euclidean space is
`x ↦ ∑ᵢ |xᵢ|² wᵢ`. -/
theorem re_inner_toEuclideanLin_diagonal_apply_self (w : ι → ℝ) (x : EuclideanSpace 𝕜 ι) :
    RCLike.re ⟪toEuclideanLin (diagonal fun i ↦ (w i : 𝕜)) x, x⟫_𝕜 = ∑ i, ‖x i‖ ^ 2 * w i := by
  simp only [toLpLin_apply, PiLp.inner_apply, mulVec_diagonal, map_sum, RCLike.inner_apply',
    map_mul, RCLike.conj_ofReal]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [mul_assoc, RCLike.conj_mul]
  norm_cast
  simp [mul_comm]

/-- An orthonormal basis `e` of `EuclideanSpace 𝕜 ι` gives a unitary matrix `U`, whose rows are
the conjugates of the vectors `e k`, such that the diagonal entries of `U A Uᴴ` are the values
`⟪e k, A (e k)⟫` of the quadratic form of `A` on the basis vectors. -/
theorem exists_mem_unitaryGroup_mul_mul_star_apply_self_eq_inner (A : Matrix ι ι 𝕜)
    (e : OrthonormalBasis ι 𝕜 (EuclideanSpace 𝕜 ι)) :
    ∃ U ∈ unitaryGroup ι 𝕜, ∀ k, (U * A * star U) k k = ⟪e k, toEuclideanLin A (e k)⟫_𝕜 := by
  refine ⟨star ((EuclideanSpace.basisFun ι 𝕜).toBasis.toMatrix e.toBasis),
    Unitary.star_mem ((EuclideanSpace.basisFun ι 𝕜).toMatrix_orthonormalBasis_mem_unitary e),
    fun k ↦ ?_⟩
  simp only [star_star, Matrix.mul_apply, Matrix.star_apply, Module.Basis.toMatrix_apply,
    OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_toBasis, PiLp.basisFun_repr,
    toLpLin_apply, PiLp.inner_apply, RCLike.inner_apply', mulVec, dotProduct, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [RCLike.star_def]
  ring

omit [Fintype κ] [DecidableEq κ] in
/-- The rank of a matrix is the dimension of the range of the linear map it induces on Euclidean
space. -/
theorem rank_eq_finrank_range_toEuclideanLin (A : Matrix κ ι 𝕜) :
    A.rank = Module.finrank 𝕜 (LinearMap.range (toEuclideanLin A)) := by
  have h : LinearMap.range (toEuclideanLin A) =
      (LinearMap.range A.mulVecLin).map (WithLp.linearEquiv 2 𝕜 (κ → 𝕜)).symm.toLinearMap := by
    ext y
    simp only [LinearMap.mem_range, Submodule.mem_map]
    refine ⟨fun ⟨x, hx⟩ ↦ ⟨WithLp.ofLp y, ⟨WithLp.ofLp x, ?_⟩, rfl⟩,
      fun ⟨_, ⟨x, hx⟩, hy⟩ ↦ ⟨WithLp.toLp 2 x, ?_⟩⟩
    · simpa using congrArg WithLp.ofLp hx
    · ext
      simp [toEuclideanLin, ← hy, ← hx]
  rw [h, LinearEquiv.finrank_map_eq]
  rfl

/-- The `Cardinal`-valued rank of the continuous linear map of a square matrix is its matrix rank.
This is the bridge that turns an operator-rank statement into a matrix-rank one. -/
theorem rank_coe_toEuclideanCLM (A : Matrix ι ι 𝕜) :
    LinearMap.rank
        (toEuclideanCLM (n := ι) (𝕜 := 𝕜) A : EuclideanSpace 𝕜 ι →ₗ[𝕜] EuclideanSpace 𝕜 ι) =
      A.rank := by
  rw [LinearMap.rank, coe_toEuclideanCLM_eq_toEuclideanLin, ← Module.finrank_eq_rank,
    rank_eq_finrank_range_toEuclideanLin]

/-- The continuous linear map of a matrix acts as its Euclidean linear map. -/
@[simp]
theorem toEuclideanCLM_apply (A : Matrix ι ι 𝕜) (x : EuclideanSpace 𝕜 ι) :
    toEuclideanCLM (𝕜 := 𝕜) A x = toEuclideanLin A x := by
  rw [← coe_toEuclideanCLM_eq_toEuclideanLin, ContinuousLinearMap.coe_coe]

/-- The coordinates of the image of a vector under the continuous linear map of a matrix. -/
theorem toEuclideanCLM_apply_apply (A : Matrix ι ι 𝕜) (x : EuclideanSpace 𝕜 ι) (i : ι) :
    toEuclideanCLM (𝕜 := 𝕜) A x i = ∑ j, A i j * x j := by
  simp [mulVec, dotProduct]

/-- The continuous linear map of a matrix depends continuously on the matrix. -/
theorem continuous_toEuclideanCLM :
    Continuous (toEuclideanCLM (n := ι) (𝕜 := 𝕜) :
      Matrix ι ι 𝕜 → EuclideanSpace 𝕜 ι →L[𝕜] EuclideanSpace 𝕜 ι) :=
  LinearMap.continuous_of_finiteDimensional
    (toEuclideanCLM (n := ι) (𝕜 := 𝕜)).toAlgEquiv.toLinearEquiv.toLinearMap

/-- The matrix of a continuous linear map on Euclidean space depends continuously on the map. -/
theorem continuous_toEuclideanCLM_symm :
    Continuous ((toEuclideanCLM (n := ι) (𝕜 := 𝕜)).symm :
      (EuclideanSpace 𝕜 ι →L[𝕜] EuclideanSpace 𝕜 ι) → Matrix ι ι 𝕜) :=
  LinearMap.continuous_of_finiteDimensional
    (toEuclideanCLM (n := ι) (𝕜 := 𝕜)).symm.toAlgEquiv.toLinearEquiv.toLinearMap

/-- A square matrix is unitary exactly when its Euclidean operator preserves the inner product. -/
theorem mem_unitaryGroup_iff_inner_toEuclideanCLM {M : Matrix ι ι 𝕜} :
    M ∈ unitaryGroup ι 𝕜 ↔ ∀ x y : EuclideanSpace 𝕜 ι,
      ⟪toEuclideanCLM (n := ι) (𝕜 := 𝕜) M x, toEuclideanCLM (n := ι) (𝕜 := 𝕜) M y⟫_𝕜 =
        ⟪x, y⟫_𝕜 := by
  refine ⟨fun hM ↦ ContinuousLinearMap.inner_map_map_of_mem_unitary
    (Unitary.map_mem (toEuclideanCLM (n := ι) (𝕜 := 𝕜)) hM), fun h ↦ ?_⟩
  rw [mem_unitaryGroup_iff']
  refine EquivLike.injective (toEuclideanCLM (n := ι) (𝕜 := 𝕜)) ?_
  rw [map_mul, map_star, map_one, ContinuousLinearMap.star_eq_adjoint]
  exact (ContinuousLinearMap.inner_map_map_iff_adjoint_comp_self _).mp h

/-- The determinant of a diagonal continuous linear map is the product of its diagonal entries. -/
@[simp]
theorem det_toEuclideanCLM_diagonal (d : ι → 𝕜) :
    (toEuclideanCLM (𝕜 := 𝕜) (diagonal d)).det = ∏ i, d i := by
  rw [ContinuousLinearMap.det, coe_toEuclideanCLM_eq_toEuclideanLin,
    LinearMap.det_toLpLin, det_diagonal]

section Invertible

/-- **The continuous linear equivalence of an invertible matrix** on Euclidean space, defined
when `A.det` is a unit. It acts as `A` does, and its inverse is the map of `A⁻¹`, so a change of
variables along it substitutes `A⁻¹`. -/
noncomputable def toEuclideanCLE (A : Matrix ι ι 𝕜) (hA : A.det ≠ 0) :
    EuclideanSpace 𝕜 ι ≃L[𝕜] EuclideanSpace 𝕜 ι :=
  (toEuclideanCLM (𝕜 := 𝕜) A).toContinuousLinearEquivOfDetNeZero <| by
    rw [ContinuousLinearMap.det, coe_toEuclideanCLM_eq_toEuclideanLin, LinearMap.det_toLpLin]
    exact hA

/-- The equivalence acts as the matrix does. -/
@[simp]
theorem toEuclideanCLE_apply (A : Matrix ι ι 𝕜) (hA : A.det ≠ 0) (x : EuclideanSpace 𝕜 ι) :
    A.toEuclideanCLE hA x = A.toEuclideanLin x := by
  rw [toEuclideanCLE, ContinuousLinearMap.toContinuousLinearEquivOfDetNeZero_apply,
    toEuclideanCLM_apply]

/-- The inverse of the equivalence is the map of the inverse matrix. -/
@[simp]
theorem toEuclideanCLE_symm_apply (A : Matrix ι ι 𝕜) (hA : A.det ≠ 0)
    (y : EuclideanSpace 𝕜 ι) : (A.toEuclideanCLE hA).symm y = A⁻¹.toEuclideanLin y := by
  rw [ContinuousLinearEquiv.symm_apply_eq, toEuclideanCLE_apply]
  simp only [← toEuclideanCLM_apply]
  rw [← mul_apply_eq_comp, ← map_mul, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hA), map_one,
    one_apply_eq_self]

/-- The equivalence, as a continuous linear map, is the continuous linear map of the matrix. -/
@[simp]
theorem coe_toEuclideanCLE (A : Matrix ι ι 𝕜) (hA : A.det ≠ 0) :
    (A.toEuclideanCLE hA : EuclideanSpace 𝕜 ι →L[𝕜] EuclideanSpace 𝕜 ι) =
      toEuclideanCLM (𝕜 := 𝕜) A :=
  ContinuousLinearMap.ext fun x ↦ by
    rw [ContinuousLinearEquiv.coe_coe, toEuclideanCLE_apply, toEuclideanCLM_apply]

/-- The determinant of the equivalence is the determinant of the matrix. -/
@[simp]
theorem det_toEuclideanCLE (A : Matrix ι ι 𝕜) (hA : A.det ≠ 0) :
    LinearMap.det (A.toEuclideanCLE hA : EuclideanSpace 𝕜 ι →ₗ[𝕜] EuclideanSpace 𝕜 ι) = A.det := by
  have hcoe : (A.toEuclideanCLE hA : EuclideanSpace 𝕜 ι →ₗ[𝕜] EuclideanSpace 𝕜 ι)
      = A.toEuclideanLin := LinearMap.ext fun x => A.toEuclideanCLE_apply hA x
  rw [hcoe, LinearMap.det_toLpLin]

/-- **The invertible matrix of a continuous linear automorphism** of `EuclideanSpace 𝕜 ι`, as a
group isomorphism. Its inverse is `Matrix.toEuclideanCLE`
(`Matrix.GeneralLinearGroup.ofEuclideanCLE_symm_apply`). -/
noncomputable def GeneralLinearGroup.ofEuclideanCLE :
    (EuclideanSpace 𝕜 ι ≃L[𝕜] EuclideanSpace 𝕜 ι) ≃* GL ι 𝕜 :=
  (ContinuousLinearEquiv.unitsEquiv 𝕜 (EuclideanSpace 𝕜 ι)).symm.trans
    (Units.mapEquiv (toEuclideanCLM (n := ι) (𝕜 := 𝕜)).symm.toMulEquiv)

/-- The matrix of a continuous linear automorphism is the matrix of its continuous linear map. -/
theorem GeneralLinearGroup.coe_ofEuclideanCLE (D : EuclideanSpace 𝕜 ι ≃L[𝕜] EuclideanSpace 𝕜 ι) :
    (GeneralLinearGroup.ofEuclideanCLE D : Matrix ι ι 𝕜) =
      (toEuclideanCLM (n := ι) (𝕜 := 𝕜)).symm (D : EuclideanSpace 𝕜 ι →L[𝕜] _) := by
  rfl

/-- The continuous linear map of the matrix of an automorphism is the automorphism. -/
@[simp]
theorem GeneralLinearGroup.toEuclideanCLM_ofEuclideanCLE
    (D : EuclideanSpace 𝕜 ι ≃L[𝕜] EuclideanSpace 𝕜 ι) :
    toEuclideanCLM (𝕜 := 𝕜) (GeneralLinearGroup.ofEuclideanCLE D : Matrix ι ι 𝕜) = D := by
  rw [coe_ofEuclideanCLE, StarAlgEquiv.apply_symm_apply]

/-- The continuous linear equivalence of the matrix of an automorphism is the automorphism. -/
@[simp]
theorem GeneralLinearGroup.toEuclideanCLE_ofEuclideanCLE
    (D : EuclideanSpace 𝕜 ι ≃L[𝕜] EuclideanSpace 𝕜 ι) :
    (GeneralLinearGroup.ofEuclideanCLE D : Matrix ι ι 𝕜).toEuclideanCLE
      (GeneralLinearGroup.ofEuclideanCLE D).det_ne_zero = D :=
  ContinuousLinearEquiv.coe_injective <| by
    rw [coe_toEuclideanCLE, toEuclideanCLM_ofEuclideanCLE]

/-- The matrix of the continuous linear equivalence of an invertible matrix is the matrix. -/
@[simp]
theorem GeneralLinearGroup.ofEuclideanCLE_toEuclideanCLE (A : GL ι 𝕜) :
    GeneralLinearGroup.ofEuclideanCLE ((A : Matrix ι ι 𝕜).toEuclideanCLE A.det_ne_zero) = A :=
  Units.ext <| by rw [coe_ofEuclideanCLE, coe_toEuclideanCLE, StarAlgEquiv.symm_apply_apply]

/-- The inverse of `Matrix.GeneralLinearGroup.ofEuclideanCLE` is the continuous linear equivalence
of an invertible matrix. -/
@[simp]
theorem GeneralLinearGroup.ofEuclideanCLE_symm_apply (A : GL ι 𝕜) :
    GeneralLinearGroup.ofEuclideanCLE.symm A =
      (A : Matrix ι ι 𝕜).toEuclideanCLE A.det_ne_zero :=
  (MulEquiv.symm_apply_eq _).2 (ofEuclideanCLE_toEuclideanCLE A).symm

open scoped Matrix.Norms.L2Operator in
/-- The matrix of a continuous family of automorphisms depends continuously on the parameter. -/
theorem GeneralLinearGroup.continuous_ofEuclideanCLE {X : Type*} [TopologicalSpace X]
    {D : X → EuclideanSpace 𝕜 ι ≃L[𝕜] EuclideanSpace 𝕜 ι}
    (hD : Continuous fun x ↦ (D x : EuclideanSpace 𝕜 ι →L[𝕜] EuclideanSpace 𝕜 ι)) :
    Continuous fun x ↦ GeneralLinearGroup.ofEuclideanCLE (D x) :=
  Units.isOpenEmbedding_val.continuous_iff.2 (continuous_toEuclideanCLM_symm.comp hD)

/-- The continuous linear equivalence of a continuous family of invertible matrices depends
continuously on the parameter. -/
theorem GeneralLinearGroup.continuous_toEuclideanCLE {X : Type*} [TopologicalSpace X]
    {A : X → GL ι 𝕜} (hA : Continuous A) :
    Continuous fun x ↦ ((A x : Matrix ι ι 𝕜).toEuclideanCLE (A x).det_ne_zero :
      EuclideanSpace 𝕜 ι →L[𝕜] EuclideanSpace 𝕜 ι) := by
  simp only [coe_toEuclideanCLE]
  exact continuous_toEuclideanCLM.comp (Units.continuous_val.comp hA)

end Invertible

end Matrix

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The operator of a normal matrix on `EuclideanSpace 𝕜 n` is normal. -/
instance isStarNormal_toEuclideanLin {𝕜 : Type*} [RCLike 𝕜] (A : Matrix n n 𝕜) [IsStarNormal A] :
    IsStarNormal (toEuclideanLin A) where
  star_comm_self := by
    have h : Aᴴ * A = A * Aᴴ := star_comm_self' A
    rw [commute_iff_eq, LinearMap.star_eq_adjoint, ← toEuclideanLin_conjTranspose_eq_adjoint,
      Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← toLpLin_mul_same, ← toLpLin_mul_same, h]

end Matrix
