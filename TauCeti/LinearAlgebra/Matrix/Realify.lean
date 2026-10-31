/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import TauCeti.LinearAlgebra.SymplecticGroup

/-!
# The realification of a matrix over an RCLike field

An `m × n` matrix `A` over an `RCLike` field induces an `ℝ`-linear map, and splitting its entries
into real and imaginary parts gives the real `(m ⊕ m) × (n ⊕ n)` matrix

`Matrix.realify A = !![Re A, -Im A; Im A, Re A]`,

the *realification* of `A`. It is additive and multiplicative and turns the conjugate transpose
into the transpose, so it carries Hermitian matrices to symmetric ones and `*`-congruence to
congruence. This is what lets real quadratic-form theory be applied to Hermitian forms.

Realification is injective, so on square matrices it is an embedding of `ℝ`-algebras. Its values
commute with the standard alternating matrix `Matrix.J`, the realification of multiplication by
`i` when `𝕜 = ℂ`. A matrix is therefore unitary exactly when its realification is orthogonal, and
exactly when its realification is symplectic.

## Main definitions

* `Matrix.realify`: the real matrix of the `ℝ`-linear map a complex matrix induces.
* `Matrix.realifyLinearMap`: realification, as an `ℝ`-linear map.
* `Matrix.realifyAlgHom`: realification of square matrices, as an `ℝ`-algebra homomorphism.
* `Matrix.GeneralLinearGroup.realify`: the injective group homomorphism `GL n 𝕜 →* GL (n ⊕ n) ℝ`
  that realification induces on invertible matrices.
* `TauCeti.realifyReflection`: the reflection of `ℝ^ι ⊕ ℝ^ι` negating the second summand, which
  realises entrywise conjugation as a congruence of realifications.

## Main results

* `Matrix.realify_mul`, `Matrix.realify_one`, `Matrix.realify_add`, `Matrix.realify_smul`:
  realification is real-linear and multiplicative.
* `Matrix.realify_conjTranspose`: the conjugate transpose becomes the transpose.
* `Matrix.IsHermitian.isSymm_realify`: a Hermitian matrix realifies to a symmetric one.
* `Matrix.realify_map_ofReal`: a real matrix realifies to two diagonal copies of itself.
* `Matrix.isUnit_det_realify`: realification preserves invertibility.
* `Matrix.realify_map_starRingEnd`: entrywise conjugation becomes congruence by the reflection
  `TauCeti.realifyReflection` that negates the imaginary coordinates.
* `Matrix.realify_injective` and `Matrix.realifyAlgHom`: realification is injective, and on square
  matrices it is a homomorphism of `ℝ`-algebras.
* `Matrix.commute_J_realify`: realifications commute with `Matrix.J`.
* `Matrix.realify_mem_orthogonalGroup_iff` and `Matrix.realify_mem_symplecticGroup_iff`: a matrix
  is unitary exactly when its realification is orthogonal, and exactly when it is symplectic.
-/

public section

open scoped Matrix

variable {l m n ι : Type*}

namespace TauCeti

/-- The reflection of `ℝ^ι ⊕ ℝ^ι` negating the second summand, which realises conjugation as a
congruence of realifications. -/
def realifyReflection (ι : Type*) [DecidableEq ι] : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ :=
  Matrix.fromBlocks 1 0 0 (-1)

@[simp]
theorem realifyReflection_transpose [DecidableEq ι] :
    (realifyReflection ι)ᵀ = realifyReflection ι := by
  simp [realifyReflection, Matrix.fromBlocks_transpose]

@[simp]
theorem realifyReflection_mul_self [Fintype ι] [DecidableEq ι] :
    realifyReflection ι * realifyReflection ι = 1 := by
  simp [realifyReflection, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]

theorem isUnit_det_realifyReflection [Fintype ι] [DecidableEq ι] :
    IsUnit (realifyReflection ι).det :=
  Matrix.isUnit_det_of_left_inverse realifyReflection_mul_self

end TauCeti

namespace Matrix

open TauCeti

/-- The realification of a matrix over an `RCLike` field, obtained by splitting its entries into
real and imaginary parts. -/
def realify {𝕜 : Type*} [RCLike 𝕜] (A : Matrix m n 𝕜) : Matrix (m ⊕ m) (n ⊕ n) ℝ :=
  fromBlocks (A.map RCLike.re) (-(A.map RCLike.im)) (A.map RCLike.im) (A.map RCLike.re)

@[simp]
theorem realify_apply_inl_inl {𝕜 : Type*} [RCLike 𝕜] (A : Matrix m n 𝕜) (i : m) (j : n) :
    A.realify (Sum.inl i) (Sum.inl j) = RCLike.re (A i j) := by simp [realify]

@[simp]
theorem realify_apply_inl_inr {𝕜 : Type*} [RCLike 𝕜] (A : Matrix m n 𝕜) (i : m) (j : n) :
    A.realify (Sum.inl i) (Sum.inr j) = -RCLike.im (A i j) := by simp [realify]

@[simp]
theorem realify_apply_inr_inl {𝕜 : Type*} [RCLike 𝕜] (A : Matrix m n 𝕜) (i : m) (j : n) :
    A.realify (Sum.inr i) (Sum.inl j) = RCLike.im (A i j) := by simp [realify]

@[simp]
theorem realify_apply_inr_inr {𝕜 : Type*} [RCLike 𝕜] (A : Matrix m n 𝕜) (i : m) (j : n) :
    A.realify (Sum.inr i) (Sum.inr j) = RCLike.re (A i j) := by simp [realify]

@[simp]
theorem realify_zero {𝕜 : Type*} [RCLike 𝕜] : (0 : Matrix m n 𝕜).realify = 0 := by
  ext p q
  rcases p with i | i <;> rcases q with j | j <;> simp

/-- Realification preserves addition. -/
@[simp]
theorem realify_add {𝕜 : Type*} [RCLike 𝕜] (A B : Matrix m n 𝕜) :
    (A + B).realify = A.realify + B.realify := by
  ext p q
  rcases p with i | i <;> rcases q with j | j <;> simp
  ring

@[simp]
theorem realify_neg {𝕜 : Type*} [RCLike 𝕜] (A : Matrix m n 𝕜) :
    (-A).realify = -A.realify := by
  ext p q
  rcases p with i | i <;> rcases q with j | j <;> simp

/-- Realification commutes with real scalar multiplication. -/
@[simp]
theorem realify_smul {𝕜 : Type*} [RCLike 𝕜] (r : ℝ) (A : Matrix m n 𝕜) :
    (r • A).realify = r • A.realify := by
  ext p q
  rcases p with i | i <;> rcases q with j | j <;>
    simp [RCLike.smul_re, RCLike.smul_im]

/-- A matrix with real entries realifies to two diagonal copies of itself. -/
@[simp]
theorem realify_map_ofReal {𝕜 : Type*} [RCLike 𝕜] (M : Matrix m n ℝ) :
    (M.map (algebraMap ℝ 𝕜)).realify = fromBlocks M 0 0 M := by
  ext p q
  rcases p with i | i <;> rcases q with j | j <;> simp

/-- Realification preserves the identity matrix. -/
@[simp]
theorem realify_one {𝕜 : Type*} [RCLike 𝕜] [DecidableEq ι] :
    (1 : Matrix ι ι 𝕜).realify = 1 := by
  rw [← Matrix.map_one (algebraMap ℝ 𝕜) (by simp) (by simp), realify_map_ofReal, fromBlocks_one]

/-- Realification preserves matrix multiplication. -/
@[simp]
theorem realify_mul {𝕜 : Type*} [RCLike 𝕜] [Fintype n] (A : Matrix m n 𝕜)
    (B : Matrix n l 𝕜) :
    (A * B).realify = A.realify * B.realify := by
  ext p q
  rcases p with i | i <;> rcases q with j | j <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, RCLike.mul_re, RCLike.mul_im,
      Finset.sum_sub_distrib, Finset.sum_add_distrib] <;> ring

/-- Realification turns the conjugate transpose into the transpose. -/
@[simp]
theorem realify_conjTranspose {𝕜 : Type*} [RCLike 𝕜] (A : Matrix m n 𝕜) :
    (Aᴴ).realify = (A.realify)ᵀ := by
  ext p q
  rcases p with i | i <;> rcases q with j | j <;> simp [conjTranspose_apply]

/-- Realification carries Hermitian matrices to symmetric ones. -/
theorem IsHermitian.isSymm_realify {𝕜 : Type*} [RCLike 𝕜] {A : Matrix ι ι 𝕜}
    (hA : Matrix.IsHermitian A) :
    A.realify.IsSymm := by
  rw [Matrix.IsSymm, ← realify_conjTranspose, hA.eq]

/-- Realification preserves invertibility. -/
theorem isUnit_det_realify {𝕜 : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι 𝕜} (h : IsUnit A.det) :
    IsUnit (A.realify).det := by
  refine Matrix.isUnit_det_of_left_inverse (B := (A⁻¹).realify) ?_
  rw [← realify_mul, Matrix.nonsing_inv_mul _ h, realify_one]

/-- Entrywise conjugation becomes congruence by the reflection negating the imaginary
coordinates. -/
theorem realify_map_starRingEnd {𝕜 : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι 𝕜) :
    (A.map (starRingEnd 𝕜)).realify =
      realifyReflection ι * A.realify * (realifyReflection ι)ᵀ := by
  rw [realifyReflection_transpose]
  ext p q
  rcases p with i | i <;> rcases q with j | j <;>
    simp [realifyReflection, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply,
      Finset.sum_ite_eq', Finset.sum_ite_eq]

/-- The quadratic form of a realified matrix is the real part of its original quadratic
form, evaluated at the split real and imaginary coordinates. -/
theorem dotProduct_realify_mulVec {𝕜 : Type*} [RCLike 𝕜] [Fintype n]
    (A : Matrix n n 𝕜) (z : n → 𝕜) :
    Sum.elim (fun i ↦ RCLike.re (z i)) (fun i ↦ RCLike.im (z i)) ⬝ᵥ
        A.realify *ᵥ Sum.elim (fun i ↦ RCLike.re (z i)) (fun i ↦ RCLike.im (z i)) =
      RCLike.re (star z ⬝ᵥ A *ᵥ z) := by
  simp only [dotProduct, mulVec, Fintype.sum_sum_type, RCLike.mul_re, RCLike.mul_im,
    Sum.elim_inl, Sum.elim_inr, realify_apply_inl_inl, realify_apply_inl_inr,
    realify_apply_inr_inl, realify_apply_inr_inr, Pi.star_apply, map_sum,
    RCLike.star_def, RCLike.conj_re, RCLike.conj_im]
  simp_rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Realification is injective: the real and imaginary parts of the entries are read off the first
block column. -/
theorem realify_injective {𝕜 : Type*} [RCLike 𝕜] :
    Function.Injective (realify : Matrix m n 𝕜 → Matrix (m ⊕ m) (n ⊕ n) ℝ) := by
  intro A B h
  ext i j
  apply RCLike.ext
  · simpa using congr_fun₂ h (Sum.inl i) (Sum.inl j)
  · simpa using congr_fun₂ h (Sum.inr i) (Sum.inl j)

@[simp]
theorem realify_inj {𝕜 : Type*} [RCLike 𝕜] {A B : Matrix m n 𝕜} :
    A.realify = B.realify ↔ A = B :=
  realify_injective.eq_iff

variable (m n) in
/-- Realification of matrices, as an `ℝ`-linear map. -/
def realifyLinearMap (𝕜 : Type*) [RCLike 𝕜] : Matrix m n 𝕜 →ₗ[ℝ] Matrix (m ⊕ m) (n ⊕ n) ℝ where
  toFun := realify
  map_add' := realify_add
  map_smul' := realify_smul

@[simp]
theorem realifyLinearMap_apply {𝕜 : Type*} [RCLike 𝕜] (A : Matrix m n 𝕜) :
    realifyLinearMap m n 𝕜 A = A.realify :=
  (rfl)

variable (ι) in
/-- Realification of square matrices, as a homomorphism of `ℝ`-algebras. -/
def realifyAlgHom (𝕜 : Type*) [RCLike 𝕜] [Fintype ι] [DecidableEq ι] :
    Matrix ι ι 𝕜 →ₐ[ℝ] Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ :=
  AlgHom.ofLinearMap (realifyLinearMap ι ι 𝕜) realify_one realify_mul

@[simp]
theorem realifyAlgHom_apply {𝕜 : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι 𝕜) : realifyAlgHom ι 𝕜 A = A.realify :=
  (rfl)

/-- Realifications commute with the standard alternating matrix `J`. -/
theorem commute_J_realify {𝕜 : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι 𝕜) : Commute (J ι ℝ) A.realify := by
  simp [Commute, SemiconjBy, J, realify, fromBlocks_multiply]

/-- A square matrix is unitary exactly when its realification is orthogonal. -/
@[simp]
theorem realify_mem_orthogonalGroup_iff {𝕜 : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι 𝕜} : A.realify ∈ orthogonalGroup (ι ⊕ ι) ℝ ↔ A ∈ unitaryGroup ι 𝕜 := by
  rw [mem_orthogonalGroup_iff, mem_unitaryGroup_iff, star_eq_conjTranspose,
    ← realify_conjTranspose, ← realify_mul, ← realify_one (𝕜 := 𝕜), realify_inj]

/-- A square matrix is unitary exactly when its realification is symplectic. -/
@[simp]
theorem realify_mem_symplecticGroup_iff {𝕜 : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι 𝕜} : A.realify ∈ symplecticGroup ι ℝ ↔ A ∈ unitaryGroup ι 𝕜 := by
  rw [SymplecticGroup.mem_iff_mem_orthogonalGroup_of_commute (commute_J_realify A),
    realify_mem_orthogonalGroup_iff]

namespace GeneralLinearGroup

variable (ι) (𝕜 : Type*) [RCLike 𝕜] [Fintype ι] [DecidableEq ι]

/-- Realification of invertible matrices: the group homomorphism `GL ι 𝕜 →* GL (ι ⊕ ι) ℝ` that
`Matrix.realifyAlgHom` induces on units. -/
def realify : GL ι 𝕜 →* GL (ι ⊕ ι) ℝ :=
  Units.map (realifyAlgHom ι 𝕜 : Matrix ι ι 𝕜 →* Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ)

theorem realify_def :
    realify ι 𝕜 = Units.map (realifyAlgHom ι 𝕜 : Matrix ι ι 𝕜 →* Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) :=
  (rfl)

variable {ι 𝕜}

@[simp]
theorem coe_realify (A : GL ι 𝕜) :
    (realify ι 𝕜 A : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) = (A : Matrix ι ι 𝕜).realify :=
  (rfl)

theorem realify_injective : Function.Injective (realify ι 𝕜) := fun _ _ h ↦
  Units.ext <| Matrix.realify_injective <| by simpa using congrArg Units.val h

@[simp]
theorem realify_inj {A B : GL ι 𝕜} : realify ι 𝕜 A = realify ι 𝕜 B ↔ A = B :=
  realify_injective.eq_iff

end GeneralLinearGroup

end Matrix
