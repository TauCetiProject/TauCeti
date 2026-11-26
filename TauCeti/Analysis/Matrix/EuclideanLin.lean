/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import TauCeti.Analysis.Normed.Lp.PiLp
public import TauCeti.Geometry.Sphere.LinearIsometry

/-!
# The map of a matrix on Euclidean space

Two ingredients of a linear change of variables on `EuclideanSpace 𝕜 ι`.

Pulling the quadratic form `x ↦ ⟪x, B x⟫` of a square matrix `B` back along the linear map of a
rectangular matrix `A` gives the quadratic form of the congruent matrix `Aᴴ * B * A`. This is
the change-of-variables identity behind every computation of a quadratic statistic after a linear
transformation of the underlying vector.

The rank of a matrix is the rank of the linear map it induces, in both the `ℕ`-valued and the
`Cardinal`-valued sense; this is what lets a matrix-rank statement be read off an operator-rank
one. The kernel of the map of the conjugate transpose is the orthogonal complement of the span of
the columns.

Normal square matrices induce normal operators on Euclidean space.
The instance `Matrix.isStarNormal_toEuclideanLin` supplies this normality automatically
from `IsStarNormal A`.

An invertible square matrix induces not just a map but a continuous linear equivalence, whose
inverse is the map of the inverse matrix. That is the form a substitution needs: it supplies the
inverse substitution and, through `LinearMap.det_toLpLin`, the Jacobian.

Conversely, every continuous linear automorphism of Euclidean space is the map of an invertible
matrix. This correspondence is a group isomorphism, and the matrix depends continuously on the
automorphism.

A square matrix is unitary exactly when its continuous linear map preserves the inner product,
and a unitary matrix acts as a linear isometry equivalence of Euclidean space; every linear
isometry equivalence arises in this way.
The rows of a unitary matrix form an orthonormal basis, so the values of the quadratic form of a
matrix `A` on an orthonormal basis are the diagonal entries of a unitary conjugate of `A`; for a
diagonal matrix `diag(w)` the quadratic form `x ↦ ⟪x, diag(w) x⟫` is `x ↦ ∑ᵢ |xᵢ|² wᵢ`.

## Main results

* `Matrix.inner_toEuclideanLin_toEuclideanLin` — the quadratic form of `B` at `A x` is the
  quadratic form of `Aᴴ * B * A` at `x`;
* `Matrix.inner_toEuclideanLin_piLpExtendByZero` — the form `y ↦ ⟪A y, y⟫` (the conjugate of the
  quadratic form `⟪y, A y⟫`) at a vector extended by zero is the same form of the principal
  submatrix at the original vector;
* `TauCeti.inner_self_toEuclideanLin_diagonal_apply` — the quadratic form `⟪x, diag(w) x⟫` of
  `diag(w)` is `∑ᵢ |xᵢ|² wᵢ`; for real weights the real part of `⟪diag(w) x, x⟫` is the same sum
  (`Matrix.re_inner_toEuclideanLin_diagonal_apply_self`);
* `Matrix.exists_mem_unitaryGroup_mul_mul_star_apply_self_eq_inner` — the values of the quadratic
  form of `A` on an orthonormal basis are the diagonal entries of a unitary conjugate `U A Uᴴ`;
* `Matrix.rank_eq_finrank_range_toEuclideanLin`, `Matrix.rank_coe_toEuclideanCLM` — the matrix
  rank is the dimension of the range of the induced map, and the `LinearMap.rank` of the induced
  continuous linear map;
* `Matrix.ker_toEuclideanLin_conjTranspose` — the kernel of the map of `Aᴴ` is the orthogonal
  complement of the span of the columns of `A`;
* `Matrix.mem_unitaryGroup_iff_inner_toEuclideanCLM` — a matrix is unitary exactly when its
  Euclidean operator preserves the inner product;
* `Matrix.adjoint_toEuclideanCLM`, `Matrix.det_toEuclideanCLM`, `Matrix.trace_toEuclideanCLM`:
  the adjoint, the determinant and the trace of the induced continuous linear map are those of
  the conjugate transpose and of the matrix;
* `Matrix.inner_toEuclideanCLM_mul_mul_conjTranspose` — the sesquilinear form of `A * B * Aᴴ`
  at `x, y` is that of `B` at `Aᴴ x, Aᴴ y`;
* `Matrix.UnitaryGroup.toLinearIsometryEquiv` — the group isomorphism from the unitary group to
  the linear isometry group of Euclidean space, acting as the matrix does
  (`Matrix.UnitaryGroup.toLinearIsometryEquiv_apply`); it preserves determinants
  (`Matrix.UnitaryGroup.det_toLinearIsometryEquiv`) and is continuous for the operator-norm
  topology (`Matrix.UnitaryGroup.continuous_toLinearIsometryEquiv`), and its action on the unit
  sphere is jointly continuous
  (`Matrix.UnitaryGroup.continuous_toLinearIsometryEquiv_smul_unitSphere`);
* `Matrix.UnitaryGroup.ofLinearIsometryEquiv` — the inverse group isomorphism, taking a linear
  isometry of Euclidean space to its unitary matrix
  (`Matrix.UnitaryGroup.symm_toLinearIsometryEquiv`), with entries
  `Matrix.UnitaryGroup.ofLinearIsometryEquiv_apply`, continuous in families
  (`Matrix.UnitaryGroup.continuous_ofLinearIsometryEquiv`);
* the actions of the unitary and special unitary groups on the unit sphere of Euclidean space by
  matrix-vector multiplication (`Matrix.UnitaryGroup.coe_smul_unitSphere`,
  `Matrix.coe_specialUnitaryGroup_smul_unitSphere`), which are jointly continuous;
* `Matrix.toEuclideanCLM_apply_apply` — the coordinate formula for the continuous linear map of
  a matrix, which depends continuously on the matrix (`Matrix.continuous_toEuclideanCLM`) and
  conversely (`Matrix.continuous_toEuclideanCLM_symm`);
* `Matrix.toEuclideanCLM_apply_toEuclideanCLM_nonsing_inv_apply` — the map of an invertible
  matrix undoes the map of its inverse;
* `Matrix.toEuclideanCLE` — the continuous linear equivalence of an invertible matrix, with its
  `apply`, `symm_apply`, coercion and determinant lemmas;
* `Matrix.GeneralLinearGroup.ofEuclideanCLE` — the group isomorphism taking a continuous linear
  automorphism to its invertible matrix, inverse to `Matrix.toEuclideanCLE`; both directions are
  continuous in families
  (`Matrix.GeneralLinearGroup.continuous_ofEuclideanCLE`,
  `Matrix.GeneralLinearGroup.continuous_toEuclideanCLE`);
* `TauCeti.matrixUnitaryContinuousMulEquivEuclidean` — topological group isomorphism induced by
  `Matrix.toEuclideanCLM` identifying unitary matrices with unitary operators on
  `EuclideanSpace 𝕜 ι`.
-/

public section

open scoped InnerProductSpace

namespace ContinuousLinearMap

/-- The inverse Euclidean matrix equivalence gives the coordinate matrix in the standard
orthonormal basis. -/
theorem toEuclideanCLM_symm_eq_toMatrix {ι 𝕜 : Type*} [RCLike 𝕜] [Fintype ι]
    [DecidableEq ι] (f : EuclideanSpace 𝕜 ι →L[𝕜] EuclideanSpace 𝕜 ι) :
    (Matrix.toEuclideanCLM (n := ι) (𝕜 := 𝕜)).symm f =
      LinearMap.toMatrix (EuclideanSpace.basisFun ι 𝕜).toBasis
        (EuclideanSpace.basisFun ι 𝕜).toBasis f.toLinearMap := by
  apply Matrix.toEuclideanLin.injective
  rw [← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin, StarAlgEquiv.apply_symm_apply,
    Matrix.toEuclideanLin_eq_toLin_orthonormal, Matrix.toLin_toMatrix]

/-- The matrix of a continuous linear map has entries given by its action on coordinate units. -/
@[simp] theorem toEuclideanCLM_symm_apply_single {ι 𝕜 : Type*} [RCLike 𝕜] [Fintype ι]
    [DecidableEq ι] (T : EuclideanSpace 𝕜 ι →L[𝕜] EuclideanSpace 𝕜 ι) (i j : ι) :
    (Matrix.toEuclideanCLM (𝕜 := 𝕜)).symm T i j = T (EuclideanSpace.single j 1) i := by
  rw [toEuclideanCLM_symm_eq_toMatrix, LinearMap.toMatrix_apply]
  simp

end ContinuousLinearMap

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

/-- The form `y ↦ ⟪A y, y⟫`, the conjugate of the quadratic form `⟪y, A y⟫`, at a vector extended
by zero along `f` is the same form of the principal submatrix `A.submatrix f f` at the original
vector. -/
theorem inner_toEuclideanLin_piLpExtendByZero (A : Matrix κ κ 𝕜) (f : ι ↪ κ)
    (x : EuclideanSpace 𝕜 ι) :
    ⟪A.toEuclideanLin (LinearIsometry.piLpExtendByZero 2 𝕜 𝕜 f x),
        LinearIsometry.piLpExtendByZero 2 𝕜 𝕜 f x⟫_𝕜 =
      ⟪(A.submatrix f f).toEuclideanLin x, x⟫_𝕜 := by
  simp only [PiLp.inner_apply, toLpLin_apply, RCLike.inner_apply',
    LinearIsometry.sum_mul_piLpExtendByZero]
  rw [funext (LinearIsometry.piLpExtendByZero_apply_ofLp 2 𝕜 𝕜 f x),
    mulVec_extend_zero f.injective]
  have h := submatrix_mulVec_equiv (A.submatrix id f) x.ofLp f (Equiv.refl ι)
  simp only [submatrix_submatrix, Function.id_comp, Equiv.coe_refl, Function.comp_id,
    Equiv.refl_symm] at h
  simp only [h, Function.comp_apply]

/-- The quadratic form `x ↦ ⟪x, diag(w) x⟫` of the diagonal operator `diag(w)` on Euclidean space
is `x ↦ ∑ᵢ |xᵢ|² wᵢ`. -/
theorem _root_.TauCeti.inner_self_toEuclideanLin_diagonal_apply (w : ι → 𝕜)
    (x : EuclideanSpace 𝕜 ι) :
    ⟪x, toEuclideanLin (diagonal w) x⟫_𝕜 = ∑ i, (‖x i‖ : 𝕜) ^ 2 * w i := by
  simp only [toLpLin_apply, PiLp.inner_apply, mulVec_diagonal, RCLike.inner_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [mul_assoc, RCLike.mul_conj, mul_comm]

/-- For real weights `w`, the real part of `⟪diag(w) x, x⟫`, with the operator in the first slot
of the inner product, is `∑ᵢ |xᵢ|² wᵢ`. It agrees with the real part of the quadratic form
`⟪x, diag(w) x⟫`, since the two inner products are complex conjugates. -/
theorem re_inner_toEuclideanLin_diagonal_apply_self (w : ι → ℝ) (x : EuclideanSpace 𝕜 ι) :
    RCLike.re ⟪toEuclideanLin (diagonal fun i ↦ (w i : 𝕜)) x, x⟫_𝕜 = ∑ i, ‖x i‖ ^ 2 * w i := by
  rw [inner_re_symm]
  simp only [TauCeti.inner_self_toEuclideanLin_diagonal_apply, ← RCLike.ofReal_pow,
    ← RCLike.ofReal_mul, ← RCLike.ofReal_sum, RCLike.ofReal_re]

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
  -- `toEuclideanLin` is by definition the `arrowCongr` of `toLin'` with the `WithLp` equivalences,
  -- and `toLin'` is `mulVecLin`
  have h : toEuclideanLin A = (WithLp.linearEquiv 2 𝕜 (κ → 𝕜)).symm.toLinearMap ∘ₗ
      A.mulVecLin ∘ₗ (WithLp.linearEquiv 2 𝕜 (ι → 𝕜)).toLinearMap := rfl
  rw [h, LinearMap.range_comp, LinearEquiv.range_comp, LinearEquiv.finrank_map_eq,
    Matrix.finrank_range_mulVecLin]

omit [Fintype ι] [DecidableEq ι] in
/-- The kernel of the map of the conjugate transpose of a matrix is the orthogonal complement of
the span of the columns of the matrix. -/
theorem ker_toEuclideanLin_conjTranspose (A : Matrix κ ι 𝕜) :
    LinearMap.ker (toEuclideanLin Aᴴ) =
      (Submodule.span 𝕜 (Set.range fun j ↦ WithLp.toLp 2 fun i ↦ A i j))ᗮ := by
  ext x
  -- A vector is orthogonal to a span exactly when it is orthogonal to each spanning column.
  rw [LinearMap.mem_ker, ← Submodule.span_singleton_le_iff_mem, ← Submodule.isOrtho_iff_le,
    Submodule.isOrtho_comm, Submodule.isOrtho_span]
  simp only [Set.forall_mem_range, Set.mem_singleton_iff, forall_eq]
  simp [WithLp.ext_iff, funext_iff, EuclideanSpace.inner_eq_star_dotProduct, mulVec, dotProduct,
    mul_comm]

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

/-- A matrix operator sends a coordinate unit vector to the corresponding column. -/
theorem toEuclideanCLM_apply_single (A : Matrix ι ι 𝕜) (j : ι) :
    toEuclideanCLM (𝕜 := 𝕜) A (EuclideanSpace.single j 1) =
      WithLp.toLp 2 (fun i => A i j) := by
  rw [toEuclideanCLM_apply, toLpLin_apply, PiLp.ofLp_single,
    Matrix.mulVec_single_one, Matrix.col_apply']

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

/-- The adjoint of the continuous linear map of a square matrix is the map of its conjugate
transpose. -/
theorem adjoint_toEuclideanCLM (A : Matrix ι ι 𝕜) :
    (toEuclideanCLM (𝕜 := 𝕜) A).adjoint = toEuclideanCLM (𝕜 := 𝕜) Aᴴ := by
  rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star, star_eq_conjTranspose]

/-- Congruence by `A` on the operator side: the sesquilinear form of `A * B * Aᴴ` at `x, y` is
the sesquilinear form of `B` at `Aᴴ x, Aᴴ y`. -/
theorem inner_toEuclideanCLM_mul_mul_conjTranspose (A B : Matrix ι ι 𝕜)
    (x y : EuclideanSpace 𝕜 ι) :
    ⟪x, toEuclideanCLM (𝕜 := 𝕜) (A * B * Aᴴ) y⟫_𝕜 =
      ⟪toEuclideanCLM (𝕜 := 𝕜) Aᴴ x,
        toEuclideanCLM (𝕜 := 𝕜) B (toEuclideanCLM (𝕜 := 𝕜) Aᴴ y)⟫_𝕜 := by
  rw [map_mul, map_mul, mul_apply_eq_comp, mul_apply_eq_comp, ← adjoint_toEuclideanCLM,
    ContinuousLinearMap.adjoint_inner_left]

/-- The operator `toEuclideanLin A` of a normal matrix `A` on `EuclideanSpace 𝕜 ι` is normal.
The underlying linear equivalence of the inverse of the star algebra equivalence
`LinearMap.toMatrixOrthonormal` of the standard orthonormal basis is `toEuclideanLin`, and star
algebra equivalences preserve normality. -/
instance isStarNormal_toEuclideanLin (A : Matrix ι ι 𝕜) [IsStarNormal A] :
    IsStarNormal (toEuclideanLin A) := by
  rw [toEuclideanLin_eq_toLin_orthonormal, ← LinearMap.toMatrix_symm, ← LinearEquiv.invFun_eq_symm,
    ← LinearMap.toMatrixOrthonormal_symm_apply]
  exact IsStarNormal.map (LinearMap.toMatrixOrthonormal (EuclideanSpace.basisFun ι 𝕜)).symm A

/-- A unitary matrix acts on `EuclideanSpace 𝕜 ι` as a linear isometry equivalence, and this is a
group isomorphism from the unitary group to the linear isometry group: the continuous linear map
of a unitary matrix is a unitary operator, and every unitary operator arises this way. -/
noncomputable def UnitaryGroup.toLinearIsometryEquiv :
    unitaryGroup ι 𝕜 ≃* (EuclideanSpace 𝕜 ι ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 ι) :=
  (Unitary.mapEquiv (.ofClass (toEuclideanCLM (n := ι) (𝕜 := 𝕜)))).toMulEquiv.trans
    Unitary.linearIsometryEquiv

/-- The linear isometry of a unitary matrix acts by matrix-vector multiplication in Euclidean
coordinates. -/
@[simp]
theorem UnitaryGroup.toLinearIsometryEquiv_apply (A : unitaryGroup ι 𝕜)
    (x : EuclideanSpace 𝕜 ι) :
    UnitaryGroup.toLinearIsometryEquiv A x = WithLp.toLp 2 ((A : Matrix ι ι 𝕜) *ᵥ x.ofLp) :=
  (rfl)

/-- The linear isometry of a unitary matrix sends the standard basis vector `e_j` to the column
`j` of the matrix. -/
theorem UnitaryGroup.toLinearIsometryEquiv_single (A : unitaryGroup ι 𝕜) (j : ι) :
    UnitaryGroup.toLinearIsometryEquiv A (EuclideanSpace.single j 1) =
      WithLp.toLp 2 ((A : Matrix ι ι 𝕜).col j) := by
  rw [UnitaryGroup.toLinearIsometryEquiv_apply, EuclideanSpace.single, PiLp.ofLp_single,
    mulVec_single_one]

/-- The linear isometry of a product of unitary matrices acts as the composite of the actions of
the factors. -/
theorem UnitaryGroup.toLinearIsometryEquiv_mul_apply (A B : unitaryGroup ι 𝕜)
    (x : EuclideanSpace 𝕜 ι) :
    UnitaryGroup.toLinearIsometryEquiv (A * B) x =
      UnitaryGroup.toLinearIsometryEquiv A (UnitaryGroup.toLinearIsometryEquiv B x) := by
  rw [map_mul, LinearIsometryEquiv.coe_mul, Function.comp_apply]

/-- The linear isometry of the inverse of a unitary matrix is the inverse of its linear
isometry. -/
theorem UnitaryGroup.toLinearIsometryEquiv_inv_apply (A : unitaryGroup ι 𝕜)
    (x : EuclideanSpace 𝕜 ι) :
    UnitaryGroup.toLinearIsometryEquiv A⁻¹ x = (UnitaryGroup.toLinearIsometryEquiv A).symm x := by
  rw [map_inv, LinearIsometryEquiv.coe_inv]

/-- The linear isometry of a unitary matrix has the determinant of the matrix. -/
@[simp]
theorem UnitaryGroup.det_toLinearIsometryEquiv (A : unitaryGroup ι 𝕜) :
    LinearMap.det (UnitaryGroup.toLinearIsometryEquiv A).toLinearIsometry.toLinearMap =
      (A : Matrix ι ι 𝕜).det := by
  have : (UnitaryGroup.toLinearIsometryEquiv A).toLinearIsometry.toLinearMap =
      toEuclideanLin (A : Matrix ι ι 𝕜) := by
    ext x
    simp [toLpLin_apply]
  rw [this, LinearMap.det_toLpLin]

/-- The linear isometry of a unitary matrix depends continuously on the matrix, for the subspace
topology on the unitary group and the operator-norm topology. -/
theorem UnitaryGroup.continuous_toLinearIsometryEquiv :
    Continuous fun A : unitaryGroup ι 𝕜 ↦
      ((UnitaryGroup.toLinearIsometryEquiv A).toContinuousLinearEquiv :
        EuclideanSpace 𝕜 ι →L[𝕜] EuclideanSpace 𝕜 ι) := by
  refine (continuous_toEuclideanCLM.comp continuous_subtypeVal).congr fun A ↦ ?_
  ext x
  simp

/-- The action of the unitary group on the unit sphere of Euclidean space, through the linear
isometries of unitary matrices, is jointly continuous. -/
theorem UnitaryGroup.continuous_toLinearIsometryEquiv_smul_unitSphere :
    Continuous fun p : unitaryGroup ι 𝕜 × Metric.sphere (0 : EuclideanSpace 𝕜 ι) 1 ↦
      UnitaryGroup.toLinearIsometryEquiv p.1 • p.2 := by
  refine continuous_induced_rng.2 <| (continuous_uncurry_toEuclideanCLM.comp
    ((continuous_subtypeVal.comp continuous_fst).prodMk
      (continuous_subtypeVal.comp continuous_snd))).congr fun p ↦ ?_
  simp [toLpLin_apply]

/-- **The unitary matrix of a linear isometry** of `EuclideanSpace 𝕜 ι`, its matrix in the standard
basis, as a group isomorphism: the inverse of `Matrix.UnitaryGroup.toLinearIsometryEquiv`. -/
noncomputable def UnitaryGroup.ofLinearIsometryEquiv :
    (EuclideanSpace 𝕜 ι ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 ι) ≃* unitaryGroup ι 𝕜 :=
  UnitaryGroup.toLinearIsometryEquiv.symm

/-- The inverse of `Matrix.UnitaryGroup.toLinearIsometryEquiv` is
`Matrix.UnitaryGroup.ofLinearIsometryEquiv`. -/
@[simp]
theorem UnitaryGroup.symm_toLinearIsometryEquiv :
    (UnitaryGroup.toLinearIsometryEquiv (ι := ι) (𝕜 := 𝕜)).symm =
      UnitaryGroup.ofLinearIsometryEquiv :=
  (rfl)

/-- The inverse of `Matrix.UnitaryGroup.ofLinearIsometryEquiv` is
`Matrix.UnitaryGroup.toLinearIsometryEquiv`. -/
@[simp]
theorem UnitaryGroup.symm_ofLinearIsometryEquiv :
    (UnitaryGroup.ofLinearIsometryEquiv (ι := ι) (𝕜 := 𝕜)).symm =
      UnitaryGroup.toLinearIsometryEquiv :=
  (rfl)

/-- The linear isometry of the unitary matrix of a linear isometry is the linear isometry. -/
@[simp]
theorem UnitaryGroup.toLinearIsometryEquiv_ofLinearIsometryEquiv
    (g : EuclideanSpace 𝕜 ι ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 ι) :
    UnitaryGroup.toLinearIsometryEquiv (UnitaryGroup.ofLinearIsometryEquiv g) = g :=
  UnitaryGroup.toLinearIsometryEquiv.apply_symm_apply g

/-- The unitary matrix of the linear isometry of a unitary matrix is the matrix. -/
@[simp]
theorem UnitaryGroup.ofLinearIsometryEquiv_toLinearIsometryEquiv (A : unitaryGroup ι 𝕜) :
    UnitaryGroup.ofLinearIsometryEquiv (UnitaryGroup.toLinearIsometryEquiv A) = A :=
  UnitaryGroup.toLinearIsometryEquiv.symm_apply_apply A

/-- The entry `(i, j)` of the unitary matrix of a linear isometry `g` is the coordinate `i` of the
image under `g` of the standard basis vector `e_j`. -/
@[simp]
theorem UnitaryGroup.ofLinearIsometryEquiv_apply
    (g : EuclideanSpace 𝕜 ι ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 ι) (i j : ι) :
    (UnitaryGroup.ofLinearIsometryEquiv g : Matrix ι ι 𝕜) i j =
      g (EuclideanSpace.single j 1) i := by
  conv_rhs => rw [← UnitaryGroup.toLinearIsometryEquiv_ofLinearIsometryEquiv g]
  rw [UnitaryGroup.toLinearIsometryEquiv_single, PiLp.toLp_apply, col_apply]

/-- The unitary matrix of a linear isometry acts on `EuclideanSpace 𝕜 ι` as the linear
isometry. -/
@[simp]
theorem UnitaryGroup.toLp_ofLinearIsometryEquiv_mulVec
    (g : EuclideanSpace 𝕜 ι ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 ι) (x : EuclideanSpace 𝕜 ι) :
    WithLp.toLp 2 ((UnitaryGroup.ofLinearIsometryEquiv g : Matrix ι ι 𝕜) *ᵥ x.ofLp) = g x := by
  rw [← UnitaryGroup.toLinearIsometryEquiv_apply,
    UnitaryGroup.toLinearIsometryEquiv_ofLinearIsometryEquiv]

/-- The unitary matrix of a linear isometry is the matrix of its continuous linear map. -/
theorem UnitaryGroup.coe_ofLinearIsometryEquiv
    (g : EuclideanSpace 𝕜 ι ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 ι) :
    (UnitaryGroup.ofLinearIsometryEquiv g : Matrix ι ι 𝕜) =
      (toEuclideanCLM (n := ι) (𝕜 := 𝕜)).symm
        (g.toContinuousLinearEquiv : EuclideanSpace 𝕜 ι →L[𝕜] EuclideanSpace 𝕜 ι) := by
  rw [StarAlgEquiv.eq_symm_apply]
  ext x : 1
  rw [toEuclideanCLM_apply, toLpLin_apply, toLp_ofLinearIsometryEquiv_mulVec,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv]

/-- The unitary matrix of a family of linear isometries, continuous in the operator norm, depends
continuously on the parameter. -/
theorem UnitaryGroup.continuous_ofLinearIsometryEquiv {X : Type*} [TopologicalSpace X]
    {g : X → EuclideanSpace 𝕜 ι ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 ι}
    (hg : Continuous fun x ↦
      ((g x).toContinuousLinearEquiv : EuclideanSpace 𝕜 ι →L[𝕜] EuclideanSpace 𝕜 ι)) :
    Continuous fun x ↦ UnitaryGroup.ofLinearIsometryEquiv (g x) :=
  continuous_induced_rng.2 <| (continuous_toEuclideanCLM_symm.comp hg).congr fun x ↦
    (UnitaryGroup.coe_ofLinearIsometryEquiv (g x)).symm

/-- The unitary group acts on the unit sphere of `EuclideanSpace 𝕜 ι` through the linear
isometries of its matrices. -/
noncomputable instance UnitaryGroup.instMulActionUnitSphere :
    MulAction (unitaryGroup ι 𝕜) (Metric.sphere (0 : EuclideanSpace 𝕜 ι) 1) :=
  MulAction.compHom _ UnitaryGroup.toLinearIsometryEquiv.toMonoidHom

/-- A unitary matrix acts on the unit sphere through its linear isometry. -/
theorem UnitaryGroup.smul_unitSphere_def (A : unitaryGroup ι 𝕜)
    (x : Metric.sphere (0 : EuclideanSpace 𝕜 ι) 1) :
    A • x = UnitaryGroup.toLinearIsometryEquiv A • x :=
  (rfl)

/-- The unitary matrix of a linear isometry acts on the unit sphere as the linear isometry. -/
@[simp]
theorem UnitaryGroup.ofLinearIsometryEquiv_smul_unitSphere
    (g : EuclideanSpace 𝕜 ι ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 ι)
    (x : Metric.sphere (0 : EuclideanSpace 𝕜 ι) 1) :
    UnitaryGroup.ofLinearIsometryEquiv g • x = g • x := by
  rw [UnitaryGroup.smul_unitSphere_def, UnitaryGroup.toLinearIsometryEquiv_ofLinearIsometryEquiv]

/-- A unitary matrix acts on the unit sphere by matrix-vector multiplication. -/
@[simp]
theorem UnitaryGroup.coe_smul_unitSphere (A : unitaryGroup ι 𝕜)
    (x : Metric.sphere (0 : EuclideanSpace 𝕜 ι) 1) :
    ((A • x : Metric.sphere (0 : EuclideanSpace 𝕜 ι) 1) : EuclideanSpace 𝕜 ι) =
      WithLp.toLp 2 ((A : Matrix ι ι 𝕜) *ᵥ WithLp.ofLp (x : EuclideanSpace 𝕜 ι)) :=
  (LinearIsometryEquiv.coe_smul_unitSphere _ x).trans
    (UnitaryGroup.toLinearIsometryEquiv_apply A x)

/-- The action of the unitary group on the unit sphere is jointly continuous. -/
instance UnitaryGroup.instContinuousSMulUnitSphere :
    ContinuousSMul (unitaryGroup ι 𝕜) (Metric.sphere (0 : EuclideanSpace 𝕜 ι) 1) :=
  ⟨UnitaryGroup.continuous_toLinearIsometryEquiv_smul_unitSphere⟩

/-- The special unitary group acts on the unit sphere of `EuclideanSpace 𝕜 ι` as a subgroup of the
unitary group. -/
noncomputable instance instMulActionSpecialUnitaryGroupUnitSphere :
    MulAction (specialUnitaryGroup ι 𝕜) (Metric.sphere (0 : EuclideanSpace 𝕜 ι) 1) :=
  MulAction.compHom _ (Submonoid.inclusion (specialUnitaryGroup_le_unitaryGroup (n := ι) (α := 𝕜)))

/-- A special unitary matrix acts on the unit sphere by matrix-vector multiplication. -/
@[simp]
theorem coe_specialUnitaryGroup_smul_unitSphere (A : specialUnitaryGroup ι 𝕜)
    (x : Metric.sphere (0 : EuclideanSpace 𝕜 ι) 1) :
    ((A • x : Metric.sphere (0 : EuclideanSpace 𝕜 ι) 1) : EuclideanSpace 𝕜 ι) =
      WithLp.toLp 2 ((A : Matrix ι ι 𝕜) *ᵥ WithLp.ofLp (x : EuclideanSpace 𝕜 ι)) :=
  UnitaryGroup.coe_smul_unitSphere (Submonoid.inclusion specialUnitaryGroup_le_unitaryGroup A) x

/-- The action of the special unitary group on the unit sphere is jointly continuous. -/
instance instContinuousSMulSpecialUnitaryGroupUnitSphere :
    ContinuousSMul (specialUnitaryGroup ι 𝕜) (Metric.sphere (0 : EuclideanSpace 𝕜 ι) 1) :=
  ⟨continuous_induced_rng.2 <| (show Continuous fun p : specialUnitaryGroup ι 𝕜 ×
      Metric.sphere (0 : EuclideanSpace 𝕜 ι) 1 ↦
        WithLp.toLp 2 ((p.1 : Matrix ι ι 𝕜) *ᵥ WithLp.ofLp (p.2 : EuclideanSpace 𝕜 ι)) by
      fun_prop).congr fun p ↦ (coe_specialUnitaryGroup_smul_unitSphere p.1 p.2).symm⟩

/-- The determinant of the continuous linear map of a square matrix is the determinant of the
matrix. -/
@[simp]
theorem det_toEuclideanCLM (A : Matrix ι ι 𝕜) : (toEuclideanCLM (𝕜 := 𝕜) A).det = A.det := by
  rw [ContinuousLinearMap.det, coe_toEuclideanCLM_eq_toEuclideanLin, LinearMap.det_toLpLin]

/-- The determinant of a diagonal continuous linear map is the product of its diagonal entries. -/
theorem det_toEuclideanCLM_diagonal (d : ι → 𝕜) :
    (toEuclideanCLM (𝕜 := 𝕜) (diagonal d)).det = ∏ i, d i := by
  rw [det_toEuclideanCLM, det_diagonal]

/-- The trace of the continuous linear map of a square matrix is the trace of the matrix. -/
@[simp]
theorem trace_toEuclideanCLM (A : Matrix ι ι 𝕜) :
    LinearMap.trace 𝕜 _ (toEuclideanCLM (𝕜 := 𝕜) A).toLinearMap = A.trace := by
  rw [coe_toEuclideanCLM_eq_toEuclideanLin, toEuclideanLin_eq_toLin_orthonormal, trace_toLin_eq]

section Invertible

/-- **The continuous linear equivalence of an invertible matrix** on Euclidean space, defined
when `A.det` is a unit. It acts as `A` does, and its inverse is the map of `A⁻¹`, so a change of
variables along it substitutes `A⁻¹`. -/
noncomputable def toEuclideanCLE (A : Matrix ι ι 𝕜) (hA : A.det ≠ 0) :
    EuclideanSpace 𝕜 ι ≃L[𝕜] EuclideanSpace 𝕜 ι :=
  (toEuclideanCLM (𝕜 := 𝕜) A).toContinuousLinearEquivOfDetNeZero <| by
    rwa [det_toEuclideanCLM]

/-- The equivalence acts as the matrix does. -/
@[simp]
theorem toEuclideanCLE_apply (A : Matrix ι ι 𝕜) (hA : A.det ≠ 0) (x : EuclideanSpace 𝕜 ι) :
    A.toEuclideanCLE hA x = A.toEuclideanLin x := by
  rw [toEuclideanCLE, ContinuousLinearMap.toContinuousLinearEquivOfDetNeZero_apply,
    toEuclideanCLM_apply]

/-- The map of an invertible matrix undoes the map of its inverse. -/
theorem toEuclideanCLM_apply_toEuclideanCLM_nonsing_inv_apply {A : Matrix ι ι 𝕜}
    (hA : A.det ≠ 0) (y : EuclideanSpace 𝕜 ι) :
    toEuclideanCLM (𝕜 := 𝕜) A (toEuclideanCLM (𝕜 := 𝕜) A⁻¹ y) = y := by
  rw [← mul_apply_eq_comp, ← map_mul, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hA), map_one,
    one_apply_eq_self]

/-- The inverse of the equivalence is the map of the inverse matrix. -/
@[simp]
theorem toEuclideanCLE_symm_apply (A : Matrix ι ι 𝕜) (hA : A.det ≠ 0)
    (y : EuclideanSpace 𝕜 ι) : (A.toEuclideanCLE hA).symm y = A⁻¹.toEuclideanLin y := by
  rw [ContinuousLinearEquiv.symm_apply_eq, toEuclideanCLE_apply, ← toEuclideanCLM_apply,
    ← toEuclideanCLM_apply, toEuclideanCLM_apply_toEuclideanCLM_nonsing_inv_apply hA]

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

namespace TauCeti

noncomputable section

section MatrixUnitary

variable (ι 𝕜 : Type*) [RCLike 𝕜] [Fintype ι] [DecidableEq ι]

/-- Unitary `ι × ι` matrices over `𝕜` and unitary operators on `EuclideanSpace 𝕜 ι` are isomorphic
as topological groups via `Matrix.toEuclideanCLM`. -/
def matrixUnitaryContinuousMulEquivEuclidean :
    Matrix.unitaryGroup ι 𝕜 ≃ₜ*
      unitary (EuclideanSpace 𝕜 ι →L[𝕜] EuclideanSpace 𝕜 ι) :=
  { (Unitary.mapEquiv (StarMulEquiv.ofClass (Matrix.toEuclideanCLM (n := ι) (𝕜 := 𝕜)))).toMulEquiv
    with
    continuous_toFun :=
      (Matrix.continuous_toEuclideanCLM.comp continuous_subtypeVal).subtype_mk _
    continuous_invFun :=
      (Matrix.continuous_toEuclideanCLM_symm.comp continuous_subtypeVal).subtype_mk _ }

variable {ι 𝕜}

/-- The underlying continuous linear map of `matrixUnitaryContinuousMulEquivEuclidean` is
`Matrix.toEuclideanCLM`. -/
@[simp]
theorem coe_matrixUnitaryContinuousMulEquivEuclidean (A : Matrix.unitaryGroup ι 𝕜) :
    (matrixUnitaryContinuousMulEquivEuclidean ι 𝕜 A :
        EuclideanSpace 𝕜 ι →L[𝕜] EuclideanSpace 𝕜 ι) =
      Matrix.toEuclideanCLM (n := ι) (𝕜 := 𝕜) (A : Matrix ι ι 𝕜) :=
  (rfl)

/-- The underlying matrix of `(matrixUnitaryContinuousMulEquivEuclidean ι 𝕜).symm` is given by
`Matrix.toEuclideanCLM.symm`. -/
@[simp]
theorem coe_matrixUnitaryContinuousMulEquivEuclidean_symm
    (u : unitary (EuclideanSpace 𝕜 ι →L[𝕜] EuclideanSpace 𝕜 ι)) :
    ((matrixUnitaryContinuousMulEquivEuclidean ι 𝕜).symm u : Matrix ι ι 𝕜) =
      (Matrix.toEuclideanCLM (n := ι) (𝕜 := 𝕜)).symm
        (u : EuclideanSpace 𝕜 ι →L[𝕜] EuclideanSpace 𝕜 ι) :=
  (rfl)

/-- The unitary operator of a unitary matrix acts on `EuclideanSpace 𝕜 ι` by
`Matrix.toEuclideanLin`. -/
theorem matrixUnitaryContinuousMulEquivEuclidean_apply_apply (A : Matrix.unitaryGroup ι 𝕜)
    (v : EuclideanSpace 𝕜 ι) :
    (matrixUnitaryContinuousMulEquivEuclidean ι 𝕜 A :
        EuclideanSpace 𝕜 ι →L[𝕜] EuclideanSpace 𝕜 ι) v =
      Matrix.toEuclideanLin (A : Matrix ι ι 𝕜) v :=
  Matrix.toEuclideanCLM_apply (A : Matrix ι ι 𝕜) v

end MatrixUnitary

end

end TauCeti
