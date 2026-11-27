/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import TauCeti.Geometry.Symplectic.Complex.ImInner.Basic
public import TauCeti.Geometry.Symplectic.Darboux.Basis
public import TauCeti.LinearAlgebra.Complex.Orientation
public import TauCeti.LinearAlgebra.Matrix.Realify

/-!
# The symplectic basis `(i e, e)` of `Im ⟪·, ·⟫_ℂ`

Let `G` be a complex inner product space and `e` an orthonormal basis of `G` indexed by `ι`. The
real basis `(i e, e)` of `G`, with `i e_j` at `Sum.inl j` and `e_j` at `Sum.inr j`
(`OrthonormalBasis.imInnerSymplecticBasis`), is the real basis underlying `e`
(`Module.Basis.complexToReal`) reindexed by `ι ⊕ ι`. It is a symplectic basis of the form
`Im ⟪·, ·⟫_ℂ` (`TauCeti.imInnerSymplecticForm`): the form has the standard matrix
`Matrix.J ι ℝ = !![0, -1; 1, 0]` in it.

Multiplication by `i` sends `i e_j` to `-e_j`, so in this basis the real matrix of a
complex-linear map with complex matrix `U` in `e` is the realification of the conjugate matrix
`Ū`, not of `U`.

Listing the two halves in the other order gives the real basis `(e, i e)`, with `e_j` at
`Sum.inl j` and `i e_j` at `Sum.inr j`, the real and imaginary parts of the coordinates of `ℂⁿ`.
In it `Im ⟪·, ·⟫_ℂ` has the matrix `-J`, and a complex-linear map with complex matrix `U` has the
realification of `U` itself as its real matrix.

## Main declarations

* `OrthonormalBasis.imInnerSymplecticBasis`: the real basis `(i e, e)`.
* `OrthonormalBasis.toMatrix_imInnerSymplecticForm`: `Im ⟪·, ·⟫_ℂ` has the matrix `Matrix.J` in
  it.
* `OrthonormalBasis.toMatrix_imInnerSymplecticBasis_restrictScalars`: a complex-linear map has
  the realified conjugate matrix in it.
* `OrthonormalBasis.toMatrix_reindex_sumComm_imInnerSymplecticForm`,
  `OrthonormalBasis.toMatrix_reindex_sumComm_imInnerSymplecticBasis_restrictScalars`: in the basis
  `(e, i e)` the form has the matrix `-J`, and a complex-linear map has the realified matrix.
* `OrthonormalBasis.toMatrix_imInnerSymplecticBasis_lsmul`,
  `OrthonormalBasis.toMatrix_reindex_sumComm_imInnerSymplecticBasis_lsmul`: multiplication by a
  complex scalar `c` has the matrix of the realified `diag (conj c)` in `(i e, e)` and of the
  realified `diag c` in `(e, i e)`.
-/

public section

noncomputable section

open Module Matrix TauCeti

namespace OrthonormalBasis

variable {ι G : Type*} [Fintype ι] [NormedAddCommGroup G] [InnerProductSpace ℂ G]

/-- The real basis `(i e, e)` of a complex inner product space attached to an orthonormal basis
`e`: `i e_j` at `Sum.inl j` and `e_j` at `Sum.inr j`. It is the real basis underlying `e`
reindexed by `ι ⊕ ι` through the Darboux relabelling `TauCeti.SymplecticForm.darbouxIndexEquiv`
(`i e_j` sits at `(j, 1)` in `Module.Basis.complexToReal`, and `e_j` at `(j, 0)`), and a symplectic
basis of `Im ⟪·, ·⟫_ℂ` (`OrthonormalBasis.toMatrix_imInnerSymplecticForm`). -/
def imInnerSymplecticBasis (e : OrthonormalBasis ι ℂ G) : Basis (ι ⊕ ι) ℝ G :=
  e.toBasis.complexToReal.reindex (SymplecticForm.darbouxIndexEquiv ι)

/-- The vector of the basis `(i e, e)` at `Sum.inl j` is `i e_j`. -/
@[simp]
theorem imInnerSymplecticBasis_inl (e : OrthonormalBasis ι ℂ G) (j : ι) :
    e.imInnerSymplecticBasis (Sum.inl j) = Complex.I • e j := by
  simp [imInnerSymplecticBasis]

/-- The vector of the basis `(i e, e)` at `Sum.inr j` is `e_j`. -/
@[simp]
theorem imInnerSymplecticBasis_inr (e : OrthonormalBasis ι ℂ G) (j : ι) :
    e.imInnerSymplecticBasis (Sum.inr j) = e j := by
  simp [imInnerSymplecticBasis]

/-- The coordinate of a vector `v` along `i e_j` in the basis `(i e, e)` is the imaginary part of
its complex coordinate along `e_j`. -/
@[simp]
theorem imInnerSymplecticBasis_repr_inl (e : OrthonormalBasis ι ℂ G) (v : G) (j : ι) :
    e.imInnerSymplecticBasis.repr v (Sum.inl j) = (e.repr v j).im := by
  simp [imInnerSymplecticBasis]

/-- The coordinate of a vector `v` along `e_j` in the basis `(i e, e)` is the real part of its
complex coordinate along `e_j`. -/
@[simp]
theorem imInnerSymplecticBasis_repr_inr (e : OrthonormalBasis ι ℂ G) (v : G) (j : ι) :
    e.imInnerSymplecticBasis.repr v (Sum.inr j) = (e.repr v j).re := by
  simp [imInnerSymplecticBasis]

variable [DecidableEq ι]

/-- The real basis `(i e, e)` attached to an orthonormal basis `e` is a symplectic basis of
`Im ⟪·, ·⟫_ℂ`: the form has the matrix `Matrix.J` in it. -/
theorem toMatrix_imInnerSymplecticForm (e : OrthonormalBasis ι ℂ G) :
    LinearMap.BilinForm.toMatrix e.imInnerSymplecticBasis (imInnerSymplecticForm G).toBilinForm =
      J ι ℝ := by
  ext (i | i) (j | j) <;>
    simp [LinearMap.BilinForm.toMatrix_apply, inner_smul_left, inner_smul_right, J,
      orthonormal_iff_ite.1 e.orthonormal, apply_ite Complex.im, Matrix.one_apply]
  split_ifs <;> simp

/-- In the basis `(i e, e)`, the real matrix of a complex-linear map with complex matrix `U` in
`e` is the realification of the conjugate matrix `Ū`. -/
theorem toMatrix_imInnerSymplecticBasis_restrictScalars (e : OrthonormalBasis ι ℂ G)
    (f : G →ₗ[ℂ] G) :
    LinearMap.toMatrix e.imInnerSymplecticBasis e.imInnerSymplecticBasis (f.restrictScalars ℝ) =
      ((LinearMap.toMatrix e.toBasis e.toBasis f).map (starRingEnd ℂ)).realify := by
  ext (i | i) (j | j) <;> simp [LinearMap.toMatrix_apply]

/-- In the real basis `(e, i e)` attached to an orthonormal basis `e`, with `e_j` at `Sum.inl j`
and `i e_j` at `Sum.inr j`, the form `Im ⟪·, ·⟫_ℂ` has the matrix `-J`. -/
theorem toMatrix_reindex_sumComm_imInnerSymplecticForm (e : OrthonormalBasis ι ℂ G) :
    LinearMap.BilinForm.toMatrix (e.imInnerSymplecticBasis.reindex (Equiv.sumComm ι ι))
      (imInnerSymplecticForm G).toBilinForm = -J ι ℝ := by
  ext (i | i) (j | j) <;>
    simp [LinearMap.BilinForm.toMatrix_apply, inner_smul_left, inner_smul_right, J,
      orthonormal_iff_ite.1 e.orthonormal, apply_ite Complex.im, Matrix.one_apply]
  split_ifs <;> simp

/-- In the real basis `(e, i e)`, the real matrix of a complex-linear map with complex matrix `U`
in `e` is the realification of `U`. -/
theorem toMatrix_reindex_sumComm_imInnerSymplecticBasis_restrictScalars
    (e : OrthonormalBasis ι ℂ G) (f : G →ₗ[ℂ] G) :
    LinearMap.toMatrix (e.imInnerSymplecticBasis.reindex (Equiv.sumComm ι ι))
        (e.imInnerSymplecticBasis.reindex (Equiv.sumComm ι ι)) (f.restrictScalars ℝ) =
      (LinearMap.toMatrix e.toBasis e.toBasis f).realify := by
  ext (i | i) (j | j) <;> simp [LinearMap.toMatrix_apply]

/-- In the basis `(i e, e)`, multiplication by a complex scalar `c` has the matrix of the realified
`diag (conj c)`. -/
theorem toMatrix_imInnerSymplecticBasis_lsmul (e : OrthonormalBasis ι ℂ G) (c : ℂ) :
    LinearMap.toMatrix e.imInnerSymplecticBasis e.imInnerSymplecticBasis
        (ContinuousLinearMap.lsmul ℝ ℂ c : G →L[ℝ] G) =
      (diagonal fun _ ↦ starRingEnd ℂ c).realify := by
  -- As a real-linear map, multiplication by `c` is the complex-linear map `c • id`.
  rw [show ((ContinuousLinearMap.lsmul ℝ ℂ c : G →L[ℝ] G) : G →ₗ[ℝ] G) =
      (c • LinearMap.id : G →ₗ[ℂ] G).restrictScalars ℝ from LinearMap.ext fun _ ↦ rfl,
    e.toMatrix_imInnerSymplecticBasis_restrictScalars, map_smul, LinearMap.toMatrix_id,
    smul_one_eq_diagonal, diagonal_map (map_zero _)]

/-- In the basis `(e, i e)`, multiplication by a complex scalar `c` has the matrix of the realified
`diag c`. -/
theorem toMatrix_reindex_sumComm_imInnerSymplecticBasis_lsmul (e : OrthonormalBasis ι ℂ G)
    (c : ℂ) :
    LinearMap.toMatrix (e.imInnerSymplecticBasis.reindex (Equiv.sumComm ι ι))
        (e.imInnerSymplecticBasis.reindex (Equiv.sumComm ι ι))
        (ContinuousLinearMap.lsmul ℝ ℂ c : G →L[ℝ] G) =
      (diagonal fun _ ↦ c).realify := by
  -- As a real-linear map, multiplication by `c` is the complex-linear map `c • id`.
  rw [show ((ContinuousLinearMap.lsmul ℝ ℂ c : G →L[ℝ] G) : G →ₗ[ℝ] G) =
      (c • LinearMap.id : G →ₗ[ℂ] G).restrictScalars ℝ from LinearMap.ext fun _ ↦ rfl,
    e.toMatrix_reindex_sumComm_imInnerSymplecticBasis_restrictScalars, map_smul,
    LinearMap.toMatrix_id, smul_one_eq_diagonal]

end OrthonormalBasis
