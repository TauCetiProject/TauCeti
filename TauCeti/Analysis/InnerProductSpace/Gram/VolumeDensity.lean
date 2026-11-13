/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Analysis.Calculus.ContDiff.Matrix

/-!
# Volume density of a bilinear form in a basis

For a basis `b` of a real topological vector space `F` and a continuous bilinear form `g` on `F`,
the volume density of `g` in `b` is the square root of the absolute Gram determinant
`|det (g (b i) (b j))|`.
For a metric written in coordinates it is the coefficient of the Riemannian volume with respect to
the Haar measure of `F` normalized by `b`, as for `TauCeti.chartVolumeDensity` in a chart.

The density depends smoothly on `g` wherever the Gram determinant does not vanish, in particular
near every positive definite form, and the density of the inner product in an orthonormal basis is
one.

## Main results

* `Module.Basis.metricVolumeDensity`: the square root of the absolute Gram determinant of `g` in the
  basis `b`.
* `OrthonormalBasis.metricVolumeDensity_innerSL`: the density of the inner product in an
  orthonormal basis is one.
* `Module.Basis.metricVolumeDensity_eq_abs_det_toMatrix_mul`: the density scales by the absolute
  determinant of the change-of-basis matrix.
* `Module.Basis.metricVolumeDensity_bilinearComp`: pullbacks scale the density by the absolute
  coordinate determinant.
* `Module.Basis.metricVolumeDensity_smul`: scaling of the form by a scalar.
* `Module.Basis.continuous_metricVolumeDensity`: continuity, including at degenerate forms.
* `Module.Basis.contDiffAt_metricVolumeDensity`: the density is smooth in the form wherever the
  Gram determinant is nonzero.
* `Module.Basis.contDiffAt_metricVolumeDensity_innerSL`: smoothness at the inner product in
  any basis.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Proposition 2.41.
-/

public section

open scoped ContDiff Matrix

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace Module.Basis

section

variable {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]

/-- The volume density `√|det (g (b i) (b j))|` of a bilinear form `g` in the basis `b`. -/
def metricVolumeDensity (b : Module.Basis ι ℝ F) (g : F →L[ℝ] F →L[ℝ] ℝ) : ℝ :=
  √|(Matrix.of fun i j ↦ g (b i) (b j)).det|

/-- The defining formula of the volume density. -/
theorem metricVolumeDensity_def (b : Module.Basis ι ℝ F) (g : F →L[ℝ] F →L[ℝ] ℝ) :
    metricVolumeDensity b g = √|(Matrix.of fun i j ↦ g (b i) (b j)).det| :=
  (rfl)

/-- The volume density expressed using the matrix of the underlying bilinear form. -/
theorem metricVolumeDensity_eq_sqrt_abs_det_toMatrix (b : Module.Basis ι ℝ F)
    (g : F →L[ℝ] F →L[ℝ] ℝ) :
    b.metricVolumeDensity g = √|(g.toBilinForm.toMatrix b).det| := by
  rw [metricVolumeDensity_def]
  congr 3
  ext i j
  simp only [Matrix.of_apply, LinearMap.BilinForm.toMatrix_apply,
    ContinuousLinearMap.toBilinForm_apply]

/-- For a nonnegative Gram determinant, the absolute value can be omitted. -/
theorem metricVolumeDensity_eq_sqrt_det_of_nonneg (b : Module.Basis ι ℝ F)
    {g : F →L[ℝ] F →L[ℝ] ℝ} (hg : 0 ≤ (Matrix.of fun i j ↦ g (b i) (b j)).det) :
    b.metricVolumeDensity g = √(Matrix.of fun i j ↦ g (b i) (b j)).det := by
  rw [metricVolumeDensity_def, abs_of_nonneg hg]

/-- The volume density is nonnegative. -/
@[simp]
theorem metricVolumeDensity_nonneg (b : Module.Basis ι ℝ F) (g : F →L[ℝ] F →L[ℝ] ℝ) :
    0 ≤ metricVolumeDensity b g :=
  Real.sqrt_nonneg _

/-- The volume density is positive exactly when the Gram determinant is nonzero. -/
theorem metricVolumeDensity_pos (b : Module.Basis ι ℝ F) (g : F →L[ℝ] F →L[ℝ] ℝ) :
    0 < b.metricVolumeDensity g ↔ (Matrix.of fun i j ↦ g (b i) (b j)).det ≠ 0 := by
  rw [metricVolumeDensity_def, Real.sqrt_pos, abs_pos]

/-- The square of the volume density is the absolute Gram determinant. -/
theorem metricVolumeDensity_sq (b : Module.Basis ι ℝ F) (g : F →L[ℝ] F →L[ℝ] ℝ) :
    b.metricVolumeDensity g ^ 2 = |(Matrix.of fun i j ↦ g (b i) (b j)).det| :=
  Real.sq_sqrt (abs_nonneg _)

/-- The volume density of a nondegenerate bilinear form is positive. -/
theorem metricVolumeDensity_pos_of_nondegenerate (b : Module.Basis ι ℝ F)
    {g : F →L[ℝ] F →L[ℝ] ℝ} (hg : g.toBilinForm.Nondegenerate) :
    0 < b.metricVolumeDensity g := by
  rw [metricVolumeDensity_eq_sqrt_abs_det_toMatrix, Real.sqrt_pos, abs_pos]
  exact (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).1 hg

/-- The volume density of a positive-definite bilinear form is positive, without symmetry. -/
theorem metricVolumeDensity_pos_of_posDef (b : Module.Basis ι ℝ F)
    {g : F →L[ℝ] F →L[ℝ] ℝ} (hg : ∀ v, v ≠ 0 → 0 < g v v) :
    0 < b.metricVolumeDensity g := by
  apply b.metricVolumeDensity_pos_of_nondegenerate
  constructor <;> intro v hv <;> by_contra h
  all_goals
    have hvv := hv v
    rw [ContinuousLinearMap.toBilinForm_apply] at hvv
    exact (ne_of_gt (hg v h)) hvv

/-- Under a change of basis, the volume density scales by the absolute determinant. -/
theorem metricVolumeDensity_eq_abs_det_toMatrix_mul (b c : Module.Basis ι ℝ F)
    (g : F →L[ℝ] F →L[ℝ] ℝ) :
    b.metricVolumeDensity g = |(c.toMatrix b).det| * c.metricVolumeDensity g := by
  have h := congrArg Matrix.det (g.toBilinForm.toMatrix_mul_basis_toMatrix c b)
  have hdet : (g.toBilinForm.toMatrix b).det =
      (c.toMatrix b).det ^ 2 * (g.toBilinForm.toMatrix c).det := by
    rw [← h, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    ring
  rw [metricVolumeDensity_eq_sqrt_abs_det_toMatrix, hdet, abs_mul,
    abs_of_nonneg (sq_nonneg _), Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
    metricVolumeDensity_eq_sqrt_abs_det_toMatrix]

/-- Reindexing a basis does not change the volume density. -/
@[simp]
theorem metricVolumeDensity_reindex {κ : Type*} [Fintype κ] [DecidableEq κ]
    (b : Module.Basis ι ℝ F) (e : ι ≃ κ) (g : F →L[ℝ] F →L[ℝ] ℝ) :
    (b.reindex e).metricVolumeDensity g = b.metricVolumeDensity g := by
  rw [metricVolumeDensity_def, metricVolumeDensity_def]
  rw [← Matrix.det_submatrix_equiv_self e.symm
    (Matrix.of fun i j ↦ g (b i) (b j))]
  congr 3
  ext i j
  simp only [Matrix.of_apply, Matrix.submatrix_apply, coe_reindex, Function.comp_apply]

/-- The volume density in dimension zero is one. -/
@[simp]
theorem metricVolumeDensity_of_isEmpty [IsEmpty ι] (b : Module.Basis ι ℝ F)
    (g : F →L[ℝ] F →L[ℝ] ℝ) : b.metricVolumeDensity g = 1 := by
  rw [metricVolumeDensity_def, Matrix.det_isEmpty, abs_one, Real.sqrt_one]

/-- The zero form has zero volume density in positive dimension. -/
@[simp]
theorem metricVolumeDensity_zero [Nonempty ι] (b : Module.Basis ι ℝ F) :
    b.metricVolumeDensity 0 = 0 := by
  rw [metricVolumeDensity_def]
  have hm : (Matrix.of fun i j ↦ (0 : F →L[ℝ] F →L[ℝ] ℝ) (b i) (b j)) = 0 := by
    ext i j
    simp
  rw [hm, Matrix.det_zero, abs_zero, Real.sqrt_zero]

/-- Scaling a form scales its volume density by the square root of the absolute scalar,
raised to the dimension. In particular, nonnegative scalars need no absolute value. -/
@[simp]
theorem metricVolumeDensity_smul (b : Module.Basis ι ℝ F) (c : ℝ)
    (g : F →L[ℝ] F →L[ℝ] ℝ) :
    b.metricVolumeDensity (c • g) = √|c| ^ Fintype.card ι * b.metricVolumeDensity g := by
  have hm : (Matrix.of fun i j ↦ (c • g) (b i) (b j)) =
      c • (Matrix.of fun i j ↦ g (b i) (b j)) := by
    ext i j
    simp
  rw [metricVolumeDensity_def, hm, Matrix.det_smul, abs_mul, abs_pow,
    Real.sqrt_mul (pow_nonneg (abs_nonneg _) _), metricVolumeDensity_def]
  congr 1
  apply (Real.sqrt_eq_iff_eq_sq (pow_nonneg (abs_nonneg _) _)
    (pow_nonneg (Real.sqrt_nonneg _) _)).2
  rw [← pow_mul, mul_comm (Fintype.card ι), pow_mul, Real.sq_sqrt (abs_nonneg _)]

end

section

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Pullback along a linear map scales the density by its absolute coordinate determinant. -/
theorem metricVolumeDensity_bilinearComp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (b : Module.Basis ι ℝ E) (c : Module.Basis ι ℝ F)
    (g : F →L[ℝ] F →L[ℝ] ℝ) (L : E →L[ℝ] F) :
    b.metricVolumeDensity (g.bilinearComp L L) =
      |(LinearMap.toMatrix b c L.toLinearMap).det| * c.metricVolumeDensity g := by
  have hm : (g.bilinearComp L L).toBilinForm =
      g.toBilinForm.comp L.toLinearMap L.toLinearMap := by
    ext x y
    simp
  rw [metricVolumeDensity_eq_sqrt_abs_det_toMatrix, hm,
    LinearMap.BilinForm.toMatrix_comp c b]
  have hdet : ((LinearMap.toMatrix b c L.toLinearMap)ᵀ * g.toBilinForm.toMatrix c *
      LinearMap.toMatrix b c L.toLinearMap).det =
      (LinearMap.toMatrix b c L.toLinearMap).det ^ 2 * (g.toBilinForm.toMatrix c).det := by
    simp only [Matrix.det_mul, Matrix.det_transpose]
    ring
  rw [hdet, abs_mul, abs_of_nonneg (sq_nonneg _), Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq_eq_abs, metricVolumeDensity_eq_sqrt_abs_det_toMatrix]

/-- Pullback by an endomorphism scales the density by the absolute determinant. -/
theorem metricVolumeDensity_bilinearComp_self (b : Module.Basis ι ℝ F)
    (g : F →L[ℝ] F →L[ℝ] ℝ) (L : F →L[ℝ] F) :
    b.metricVolumeDensity (g.bilinearComp L L) = |L.det| * b.metricVolumeDensity g := by
  rw [b.metricVolumeDensity_bilinearComp b, LinearMap.det_toMatrix]

/-- Mapping a basis and pulling back the form give the same density. -/
@[simp]
theorem metricVolumeDensity_map {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (b : Module.Basis ι ℝ E) (e : E ≃L[ℝ] F) (g : F →L[ℝ] F →L[ℝ] ℝ) :
    (b.map e.toLinearEquiv).metricVolumeDensity g =
      b.metricVolumeDensity (g.bilinearComp (e : E →L[ℝ] F) (e : E →L[ℝ] F)) := by
  simp only [metricVolumeDensity_def, map_apply, ContinuousLinearEquiv.coe_toLinearEquiv,
    ContinuousLinearMap.bilinearComp_apply, ContinuousLinearEquiv.coe_coe]

/-- The volume density is continuous in the bilinear form, including at degenerate forms. -/
@[continuity, fun_prop]
theorem continuous_metricVolumeDensity (b : Module.Basis ι ℝ F) :
    Continuous (metricVolumeDensity b) := by
  rw [funext b.metricVolumeDensity_def]
  exact (continuous_matrix fun i j ↦ by fun_prop).matrix_det.abs.sqrt

/-- The volume density is smooth in the bilinear form wherever the Gram determinant is nonzero. -/
theorem contDiffAt_metricVolumeDensity (b : Module.Basis ι ℝ F) {g : F →L[ℝ] F →L[ℝ] ℝ}
    (hg : (Matrix.of fun i j ↦ g (b i) (b j)).det ≠ 0) {n : ℕ∞ω} :
    ContDiffAt ℝ n (metricVolumeDensity b) g := by
  have hdet : ContDiff ℝ n fun g : F →L[ℝ] F →L[ℝ] ℝ ↦ (Matrix.of fun i j ↦ g (b i) (b j)).det :=
    ContDiff.matrix_det fun i j ↦ by
      simp only [Matrix.of_apply]
      fun_prop
  rw [funext b.metricVolumeDensity_def]
  simpa only [Real.norm_eq_abs] using
    (hdet.contDiffAt.norm ℝ hg).sqrt (norm_ne_zero_iff.mpr hg)

/-- The volume density is smooth at every nondegenerate bilinear form. -/
theorem contDiffAt_metricVolumeDensity_of_nondegenerate (b : Module.Basis ι ℝ F)
    {g : F →L[ℝ] F →L[ℝ] ℝ} (hg : g.toBilinForm.Nondegenerate) {n : ℕ∞ω} :
    ContDiffAt ℝ n (metricVolumeDensity b) g := by
  exact b.contDiffAt_metricVolumeDensity
    ((b.metricVolumeDensity_pos g).1 (b.metricVolumeDensity_pos_of_nondegenerate hg))

/-- The volume density is smooth at every positive-definite bilinear form, even without symmetry. -/
theorem contDiffAt_metricVolumeDensity_of_posDef (b : Module.Basis ι ℝ F)
    {g : F →L[ℝ] F →L[ℝ] ℝ} (hg : ∀ v, v ≠ 0 → 0 < g v v) {n : ℕ∞ω} :
    ContDiffAt ℝ n (metricVolumeDensity b) g :=
  b.contDiffAt_metricVolumeDensity ((b.metricVolumeDensity_pos g).1
    (b.metricVolumeDensity_pos_of_posDef hg))

/-- The volume density in any basis is smooth at the inner product. -/
theorem contDiffAt_metricVolumeDensity_innerSL {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (b : Module.Basis ι ℝ F) {n : ℕ∞ω} :
    ContDiffAt ℝ n (metricVolumeDensity b) (innerSL ℝ) :=
  b.contDiffAt_metricVolumeDensity_of_posDef fun _ hv ↦ by
    rw [innerSL_apply_apply]
    exact real_inner_self_pos.mpr hv

/-- The volume density of the inner product is positive in every basis. -/
@[simp]
theorem metricVolumeDensity_innerSL_pos {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (b : Module.Basis ι ℝ F) :
    0 < b.metricVolumeDensity (innerSL ℝ) := by
  exact b.metricVolumeDensity_pos_of_posDef fun _ hv ↦ by
    rw [innerSL_apply_apply]
    exact real_inner_self_pos.mpr hv

end

end Module.Basis

namespace OrthonormalBasis

/-- The volume density of the inner product in an orthonormal basis is one. -/
@[simp, grind =]
theorem metricVolumeDensity_innerSL {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (b : OrthonormalBasis ι ℝ F) : b.toBasis.metricVolumeDensity (innerSL ℝ) = 1 := by
  have h : (Matrix.of fun i j ↦ innerSL ℝ (b.toBasis i) (b.toBasis j)) =
      Matrix.gram ℝ b := by
    ext i j
    simp [Matrix.gram_apply, Matrix.of_apply, innerSL_apply_apply]
  rw [Module.Basis.metricVolumeDensity_def, h, Matrix.gram_eq_one_iff_orthonormal.2 b.orthonormal,
    Matrix.det_one, abs_one, Real.sqrt_one]

/-- The volume density is independent of the choice of orthonormal basis. -/
theorem metricVolumeDensity_eq {κ : Type*} [Fintype κ] [DecidableEq κ]
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (b : OrthonormalBasis ι ℝ F) (c : OrthonormalBasis κ ℝ F) (g : F →L[ℝ] F →L[ℝ] ℝ) :
    b.toBasis.metricVolumeDensity g = c.toBasis.metricVolumeDensity g := by
  let b' := b.reindex (b.toBasis.indexEquiv c.toBasis)
  have h : b'.toBasis.metricVolumeDensity g = c.toBasis.metricVolumeDensity g := by
    rw [b'.toBasis.metricVolumeDensity_eq_abs_det_toMatrix_mul c.toBasis,
      ← Module.Basis.det_apply, ← Real.norm_eq_abs, b'.coe_toBasis,
      c.det_to_matrix_orthonormalBasis b', one_mul]
  simpa only [b', OrthonormalBasis.reindex_toBasis,
    Module.Basis.metricVolumeDensity_reindex] using h

end OrthonormalBasis
