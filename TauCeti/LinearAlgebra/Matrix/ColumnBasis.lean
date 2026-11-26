/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Convex.Cone.Basis
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import TauCeti.LinearAlgebra.Matrix.Determinant.Basic
import TauCeti.Logic.Function.Extend
import TauCeti.LinearAlgebra.Matrix.MaximalMinor
import TauCeti.LinearAlgebra.Matrix.MulVec

/-!
# Column bases of integer matrices

Let `A` be an integer matrix with rows indexed by `κ` and columns by `ι`. A *column basis* of `A`
(`Matrix.ColumnBasis`) chooses a column `e k` for every row index `k` so that the square submatrix
`A_e` on these columns is invertible. Its columns form a basis of `κ → ℝ`
(`Matrix.ColumnBasis.basis`), the coordinates of `b` in this basis are `(A_e)⁻¹ *ᵥ b`
(`Matrix.ColumnBasis.basisCoordinates`), and putting them on the columns of `e` and `0` elsewhere
gives the *basic solution* of `A *ᵥ x = b` (`Matrix.ColumnBasis.basicSolution`), the only solution
supported on these columns. The basis coordinates are nonnegative exactly when `b` lies in the
*basis cone* spanned by the columns of `e` (`Matrix.ColumnBasis.basisCone`). When `A_e` has
determinant `±1`, the basis coordinates of integer vectors are integers.

## Main definitions

* `Matrix.ColumnBasis A`: the column bases of `A`.
* `Matrix.ColumnBasis.basisCoordinates`, `Matrix.ColumnBasis.basicSolution`,
  `Matrix.ColumnBasis.basisCone`: basis coordinates, basic solutions and basis cones.

## Main results

* `Matrix.ColumnBasis.eq_basicSolution_iff`: basic solutions are the solutions supported on a
  column basis.
* `Matrix.ColumnBasis.mem_basisCone_iff`: the basis cone consists of the vectors with nonnegative
  basis coordinates.
* `Matrix.ColumnBasis.basisCoordinates_intCast_of_isUnit`: integral basis coordinates.

## References

* A. Schrijver, *Theory of Linear and Integer Programming*, Wiley, 1986, §8.5 (basic solutions).
-/

public section

open Function

namespace Matrix

variable {κ ι : Type*} [Fintype κ] [DecidableEq κ]

/-- A *column basis* of an integer matrix `A` with rows indexed by `κ`: a choice of a column
`e k` of `A` for every row index `k` such that the square submatrix of `A` on these columns has
nonzero determinant. Its columns form a basis of `κ → ℝ`. The columns are listed in the order
given by `κ`, so each set of columns forming a basis is presented by `Fintype.card κ !` column
bases. -/
@[ext]
structure ColumnBasis (A : Matrix κ ι ℤ) where
  /-- The column chosen for each row index. -/
  toFun : κ → ι
  det_ne_zero : (A.submatrix id toFun).det ≠ 0

namespace ColumnBasis

variable {A : Matrix κ ι ℤ}

instance : FunLike A.ColumnBasis κ ι where
  coe := toFun
  coe_injective _ _ := ColumnBasis.ext

@[simp] theorem toFun_eq_coe (e : A.ColumnBasis) : e.toFun = ⇑e := (rfl)

@[simp] theorem coe_mk (f : κ → ι) (h : (A.submatrix id f).det ≠ 0) :
    ⇑(⟨f, h⟩ : A.ColumnBasis) = f := (rfl)

theorem det_submatrix_ne_zero (e : A.ColumnBasis) : (A.submatrix id e).det ≠ 0 := e.det_ne_zero

instance [Finite ι] : Finite A.ColumnBasis :=
  Finite.of_injective _ DFunLike.coe_injective

/-- The columns of a column basis are distinct. -/
theorem injective (e : A.ColumnBasis) : Injective e := by
  intro k l hkl
  by_contra hne
  exact e.det_submatrix_ne_zero (det_zero_of_column_eq hne fun i => by simp [hkl])

/-- The real square matrix of a column basis is invertible. -/
theorem isUnit_det_map (e : A.ColumnBasis) :
    IsUnit ((A.map (Int.cast : ℤ → ℝ)).submatrix id e).det := by
  rw [submatrix_map]
  exact isUnit_det_map_intCast e.det_submatrix_ne_zero

/-- If the square submatrix `A_e` of a column basis has determinant `±1`, then the integer vector
`(A_e)⁻¹ *ᵥ b`, cast to any commutative ring, is mapped by `A_e` to `b`. -/
theorem submatrix_mulVec_intCast_nonsing_inv_mulVec {K : Type*} [CommRing K] (e : A.ColumnBasis)
    (he : IsUnit (A.submatrix id e).det) (b : κ → ℤ) :
    (A.map (Int.cast : ℤ → K)).submatrix id e *ᵥ (fun k => (((A.submatrix id e)⁻¹ *ᵥ b) k : K)) =
      fun i => (b i : K) := by
  rw [submatrix_map, map_intCast_mulVec, mulVec_mulVec, mul_nonsing_inv _ he, one_mulVec]

/-- The coordinates of a real vector `b` in the basis of `κ → ℝ` formed by the columns of a column
basis `e`: the unique `t` with `∑ k, t k • A.col (e k) = b`, given by Cramer's rule as
`(A_e)⁻¹ *ᵥ b` for the square submatrix `A_e` of `A` on the columns of `e`. -/
noncomputable def basisCoordinates (e : A.ColumnBasis) (b : κ → ℝ) : κ → ℝ :=
  ((A.map (Int.cast : ℤ → ℝ)).submatrix id e)⁻¹ *ᵥ b

theorem basisCoordinates_def (e : A.ColumnBasis) (b : κ → ℝ) :
    e.basisCoordinates b = ((A.map (Int.cast : ℤ → ℝ)).submatrix id e)⁻¹ *ᵥ b := (rfl)

/-- The basis coordinates of `b` recombine the columns of the basis to `b`. -/
@[simp] theorem submatrix_mulVec_basisCoordinates (e : A.ColumnBasis) (b : κ → ℝ) :
    (A.map (Int.cast : ℤ → ℝ)).submatrix id e *ᵥ e.basisCoordinates b = b := by
  rw [basisCoordinates_def, mulVec_mulVec, mul_nonsing_inv _ e.isUnit_det_map, one_mulVec]

/-- The basis coordinates of a combination of the columns of the basis are its coefficients. -/
@[simp] theorem basisCoordinates_submatrix_mulVec (e : A.ColumnBasis) (t : κ → ℝ) :
    e.basisCoordinates ((A.map (Int.cast : ℤ → ℝ)).submatrix id e *ᵥ t) = t := by
  rw [basisCoordinates_def, mulVec_mulVec, nonsing_inv_mul _ e.isUnit_det_map, one_mulVec]

/-- The basis coordinates of `b` are the unique coefficients recombining the columns to `b`. -/
theorem basisCoordinates_eq_iff (e : A.ColumnBasis) {b t : κ → ℝ} :
    e.basisCoordinates b = t ↔ (A.map (Int.cast : ℤ → ℝ)).submatrix id e *ᵥ t = b := by
  constructor
  · rintro rfl
    exact e.submatrix_mulVec_basisCoordinates b
  · rintro rfl
    exact e.basisCoordinates_submatrix_mulVec t

@[simp] theorem basisCoordinates_add (e : A.ColumnBasis) (b b' : κ → ℝ) :
    e.basisCoordinates (b + b') = e.basisCoordinates b + e.basisCoordinates b' :=
  mulVec_add _ _ _

@[simp] theorem basisCoordinates_smul (e : A.ColumnBasis) (c : ℝ) (b : κ → ℝ) :
    e.basisCoordinates (c • b) = c • e.basisCoordinates b :=
  mulVec_smul _ _ _

/-- **Integral basis coordinates.** If the square submatrix of a column basis has determinant `±1`,
the basis coordinates of an integer vector are the integers given by the integer inverse
matrix. -/
theorem basisCoordinates_intCast_of_isUnit (e : A.ColumnBasis)
    (he : IsUnit (A.submatrix id e).det) (b : κ → ℤ) :
    e.basisCoordinates (fun i => (b i : ℝ)) = fun k => (((A.submatrix id e)⁻¹ *ᵥ b) k : ℝ) :=
  e.basisCoordinates_eq_iff.2 (e.submatrix_mulVec_intCast_nonsing_inv_mulVec he b)

/-- The *basic solution* of a column basis `e` for the right-hand side `b`: the vector with the
basis coordinates of `b` on the columns of `e` and `0` on all other columns. -/
noncomputable def basicSolution (e : A.ColumnBasis) (b : κ → ℝ) : ι → ℝ :=
  extend e (e.basisCoordinates b) 0

@[simp] theorem basicSolution_apply_self (e : A.ColumnBasis) (b : κ → ℝ) (k : κ) :
    e.basicSolution b (e k) = e.basisCoordinates b k :=
  e.injective.extend_apply _ _ k

theorem basicSolution_apply_of_notMem_range (e : A.ColumnBasis) (b : κ → ℝ) {j : ι}
    (hj : j ∉ Set.range e) : e.basicSolution b j = 0 :=
  extend_apply' _ _ _ hj

/-- The columns of a column basis, as a basis of `κ → ℝ`; the coordinates of a vector in this basis
are its basis coordinates. -/
noncomputable def basis (e : A.ColumnBasis) : Module.Basis κ ℝ (κ → ℝ) :=
  .ofEquivFun
    { toFun := e.basisCoordinates
      invFun := ((A.map (Int.cast : ℤ → ℝ)).submatrix id e *ᵥ ·)
      map_add' := e.basisCoordinates_add
      map_smul' := e.basisCoordinates_smul
      left_inv := e.submatrix_mulVec_basisCoordinates
      right_inv := e.basisCoordinates_submatrix_mulVec }

theorem basis_apply (e : A.ColumnBasis) (k : κ) :
    e.basis k = fun i => (A i (e k) : ℝ) := by
  ext i
  simp [basis]

@[simp] theorem basis_repr_apply (e : A.ColumnBasis) (b : κ → ℝ) (k : κ) :
    e.basis.repr b k = e.basisCoordinates b k := by
  simp [basis]

/-- The basis coordinates of the column `e k` are those of the `k`-th standard basis vector. -/
@[simp] theorem basisCoordinates_basis (e : A.ColumnBasis) (k : κ) :
    e.basisCoordinates (e.basis k) = Pi.single k 1 := by
  ext l
  rw [← basis_repr_apply, e.basis.repr_self]
  simp [Finsupp.single_apply, Pi.single_apply, eq_comm]

/-- The *basis cone* of a column basis: the cone spanned by its columns. -/
noncomputable def basisCone (e : A.ColumnBasis) : PointedCone ℝ (κ → ℝ) :=
  PointedCone.hull ℝ (Set.range fun k i => (A i (e k) : ℝ))

/-- A vector lies in the basis cone of `e` exactly when its basis coordinates are nonnegative. -/
theorem mem_basisCone_iff (e : A.ColumnBasis) {b : κ → ℝ} :
    b ∈ e.basisCone ↔ 0 ≤ e.basisCoordinates b := by
  have hb : ⇑e.basis = fun k i => (A i (e k) : ℝ) := funext e.basis_apply
  rw [basisCone, ← hb, e.basis.mem_pointedCone_hull_range_iff, Pi.le_def]
  simp

variable [Fintype ι]

/-- The basic solution of `e` for `b` solves `A *ᵥ x = b`. -/
@[simp] theorem mulVec_basicSolution (e : A.ColumnBasis) (b : κ → ℝ) :
    A.map (Int.cast : ℤ → ℝ) *ᵥ e.basicSolution b = b :=
  mulVec_extend_zero_nonsing_inv_mulVec _ e.injective e.isUnit_det_map b

/-- The basic solution of `e` for `b` is the only solution of `A *ᵥ x = b` supported on the columns
of `e`. -/
theorem eq_basicSolution_iff (e : A.ColumnBasis) {b : κ → ℝ} {x : ι → ℝ}
    (hx : ∀ j ∉ Set.range e, x j = 0) :
    x = e.basicSolution b ↔ A.map (Int.cast : ℤ → ℝ) *ᵥ x = b := by
  refine ⟨fun h => h ▸ e.mulVec_basicSolution b, fun h => ?_⟩
  have hext : x = extend e (x ∘ e) 0 := (extend_comp_eq_of_forall_notMem_range hx).symm
  rw [hext, mulVec_extend_zero e.injective, ← basisCoordinates_eq_iff] at h
  rw [basicSolution, h]
  exact hext

end ColumnBasis

end Matrix
