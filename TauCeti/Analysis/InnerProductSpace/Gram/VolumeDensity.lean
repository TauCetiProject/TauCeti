/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import TauCeti.Analysis.Calculus.ContDiff.Matrix

/-!
# Volume density of a bilinear form in a basis

For a basis `b` of a real normed space `F` and a continuous bilinear form `g` on `F`, the volume
density of `g` in the basis `b` is the square root of the Gram determinant `det (g (b i) (b j))`.
For a metric written in coordinates it is the coefficient of the Riemannian volume with respect to
the Haar measure of `F` normalized by `b`, as for `TauCeti.chartVolumeDensity` in a chart.

The density depends smoothly on `g` wherever the Gram determinant does not vanish, in particular
near every positive definite form, and the density of the inner product in an orthonormal basis is
one.

## Main results

* `Module.Basis.metricVolumeDensity`: the square root of the Gram determinant of `g` in the
  basis `b`.
* `OrthonormalBasis.metricVolumeDensity_innerSL`: the density of the inner product in an
  orthonormal basis is one.
* `Module.Basis.metricVolumeDensity_change_basis`: the density scales by the absolute
  determinant of the change-of-basis matrix.
* `Module.Basis.contDiffAt_metricVolumeDensity`: the density is smooth in the form wherever the
  Gram determinant is nonzero.
* `Module.Basis.contDiffAt_metricVolumeDensity_innerSL`: smoothness at the inner product in
  any basis.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Proposition 2.41.
-/

public section

open scoped ContDiff

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace Module.Basis

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The volume density `√ det (g (b i) (b j))` of a bilinear form `g` in the basis `b`. -/
def metricVolumeDensity (b : Module.Basis ι ℝ F) (g : F →L[ℝ] F →L[ℝ] ℝ) : ℝ :=
  √(Matrix.det fun i j ↦ g (b i) (b j))

/-- The defining formula of the volume density. -/
theorem metricVolumeDensity_def (b : Module.Basis ι ℝ F) (g : F →L[ℝ] F →L[ℝ] ℝ) :
    metricVolumeDensity b g = √(Matrix.det fun i j ↦ g (b i) (b j)) :=
  (rfl)

/-- The volume density is nonnegative. -/
@[simp]
theorem metricVolumeDensity_nonneg (b : Module.Basis ι ℝ F) (g : F →L[ℝ] F →L[ℝ] ℝ) :
    0 ≤ metricVolumeDensity b g :=
  Real.sqrt_nonneg _

/-- The volume density is positive exactly when the Gram determinant is positive. -/
@[simp]
theorem metricVolumeDensity_pos (b : Module.Basis ι ℝ F) (g : F →L[ℝ] F →L[ℝ] ℝ) :
    0 < b.metricVolumeDensity g ↔ 0 < Matrix.det (fun i j ↦ g (b i) (b j)) :=
  Real.sqrt_pos

/-- The square of the volume density is the Gram determinant when it is nonnegative. -/
theorem metricVolumeDensity_sq (b : Module.Basis ι ℝ F) {g : F →L[ℝ] F →L[ℝ] ℝ}
    (hg : 0 ≤ Matrix.det (fun i j ↦ g (b i) (b j))) :
    b.metricVolumeDensity g ^ 2 = Matrix.det (fun i j ↦ g (b i) (b j)) :=
  Real.sq_sqrt hg

/-- The volume density of a symmetric positive-definite bilinear form is positive. -/
theorem metricVolumeDensity_pos_of_posDef (b : Module.Basis ι ℝ F)
    {g : F →L[ℝ] F →L[ℝ] ℝ} (hs : g.toBilinForm.IsSymm)
    (hg : ∀ v, v ≠ 0 → 0 < g v v) : 0 < b.metricVolumeDensity g := by
  apply (b.metricVolumeDensity_pos g).2
  convert ((g.toBilinForm.posDef_toQuadraticMap_iff_matrix b hs).1 hg).det_pos using 1
  congr 2
  ext i j
  simp [LinearMap.BilinForm.toMatrix_apply]

/-- Under a change of basis, the volume density scales by the absolute determinant. -/
theorem metricVolumeDensity_change_basis (b c : Module.Basis ι ℝ F)
    (g : F →L[ℝ] F →L[ℝ] ℝ) :
    c.metricVolumeDensity g = |(b.toMatrix c).det| * b.metricVolumeDensity g := by
  have hmatrix (d : Module.Basis ι ℝ F) : g.toBilinForm.toMatrix d =
      (fun i j ↦ g (d i) (d j) : Matrix ι ι ℝ) := by
    ext i j
    simp [LinearMap.BilinForm.toMatrix_apply]
  have h := congrArg Matrix.det (g.toBilinForm.toMatrix_mul_basis_toMatrix b c)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hmatrix b, hmatrix c] at h
  have hdet : Matrix.det (fun i j ↦ g (c i) (c j)) =
      (b.toMatrix c).det ^ 2 * Matrix.det (fun i j ↦ g (b i) (b j)) := by
    rw [← h]
    ring
  rw [metricVolumeDensity_def, hdet, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
    metricVolumeDensity_def]

/-- Reindexing a basis does not change the volume density. -/
@[simp]
theorem metricVolumeDensity_reindex {κ : Type*} [Fintype κ] [DecidableEq κ]
    (b : Module.Basis ι ℝ F) (e : ι ≃ κ) (g : F →L[ℝ] F →L[ℝ] ℝ) :
    (b.reindex e).metricVolumeDensity g = b.metricVolumeDensity g := by
  rw [metricVolumeDensity_def, metricVolumeDensity_def]
  convert congrArg Real.sqrt (Matrix.det_submatrix_equiv_self e.symm
    (Matrix.of fun i j ↦ g (b i) (b j))) using 1 <;> congr 2
  ext i j
  simp [Matrix.submatrix_apply]

/-- The volume density is smooth in the bilinear form wherever the Gram determinant is nonzero. -/
theorem contDiffAt_metricVolumeDensity (b : Module.Basis ι ℝ F) {g : F →L[ℝ] F →L[ℝ] ℝ}
    (hg : Matrix.det (fun i j ↦ g (b i) (b j)) ≠ 0) {n : ℕ∞ω} :
    ContDiffAt ℝ n (metricVolumeDensity b) g := by
  have hdet : ContDiff ℝ n fun g : F →L[ℝ] F →L[ℝ] ℝ ↦ Matrix.det fun i j ↦ g (b i) (b j) :=
    ContDiff.matrix_det fun i j ↦ by fun_prop
  exact hdet.contDiffAt.sqrt hg

/-- The volume density is smooth at every nondegenerate bilinear form. -/
theorem contDiffAt_metricVolumeDensity_of_nondegenerate (b : Module.Basis ι ℝ F)
    {g : F →L[ℝ] F →L[ℝ] ℝ} (hg : g.toBilinForm.Nondegenerate) {n : ℕ∞ω} :
    ContDiffAt ℝ n (metricVolumeDensity b) g := by
  apply b.contDiffAt_metricVolumeDensity
  convert (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).1 hg using 1
  congr 2
  ext i j
  simp [LinearMap.BilinForm.toMatrix_apply]

/-- The volume density is smooth at every positive-definite bilinear form, even without symmetry. -/
theorem contDiffAt_metricVolumeDensity_of_posDef (b : Module.Basis ι ℝ F)
    {g : F →L[ℝ] F →L[ℝ] ℝ} (hg : ∀ v, v ≠ 0 → 0 < g v v) {n : ℕ∞ω} :
    ContDiffAt ℝ n (metricVolumeDensity b) g := by
  apply b.contDiffAt_metricVolumeDensity_of_nondegenerate
  constructor <;> intro v hv <;> by_contra h <;> exact (ne_of_gt (hg v h)) (hv v)

/-- The volume density in any basis is smooth at the inner product. -/
theorem contDiffAt_metricVolumeDensity_innerSL {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (b : Module.Basis ι ℝ F) {n : ℕ∞ω} :
    ContDiffAt ℝ n (metricVolumeDensity b) (innerSL ℝ) :=
  b.contDiffAt_metricVolumeDensity_of_posDef fun _ hv ↦ real_inner_self_pos.mpr hv

/-- The volume density of the inner product is positive in every basis. -/
@[simp high]
theorem metricVolumeDensity_innerSL_pos {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (b : Module.Basis ι ℝ F) :
    0 < b.metricVolumeDensity (innerSL ℝ) := by
  apply b.metricVolumeDensity_pos_of_posDef _ (fun _ hv ↦ real_inner_self_pos.mpr hv)
  constructor
  intro v w
  simp only [ContinuousLinearMap.toBilinForm_apply]
  exact real_inner_comm w v

end Module.Basis

namespace OrthonormalBasis

/-- The volume density of the inner product in an orthonormal basis is one. -/
@[simp, grind =]
theorem metricVolumeDensity_innerSL {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (b : OrthonormalBasis ι ℝ F) : b.toBasis.metricVolumeDensity (innerSL ℝ) = 1 := by
  have h : (fun i j ↦ innerSL ℝ (b.toBasis i) (b.toBasis j) : Matrix ι ι ℝ) = Matrix.gram ℝ b := by
    ext i j
    simp [Matrix.gram_apply]
  rw [Module.Basis.metricVolumeDensity_def, h, Matrix.gram_eq_one_iff_orthonormal.2 b.orthonormal,
    Matrix.det_one, Real.sqrt_one]

/-- The volume density is independent of the choice of orthonormal basis. -/
theorem metricVolumeDensity_eq {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (b c : OrthonormalBasis ι ℝ F) (g : F →L[ℝ] F →L[ℝ] ℝ) :
    b.toBasis.metricVolumeDensity g = c.toBasis.metricVolumeDensity g := by
  rw [b.toBasis.metricVolumeDensity_change_basis c.toBasis, ← Module.Basis.det_apply,
    ← Real.norm_eq_abs, c.coe_toBasis, b.det_to_matrix_orthonormalBasis c, one_mul]

end OrthonormalBasis
