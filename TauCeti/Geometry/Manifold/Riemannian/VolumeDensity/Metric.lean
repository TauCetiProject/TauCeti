/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Sqrt
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

* `TauCeti.metricVolumeDensity`: the square root of the Gram determinant of `g` in the basis `b`.
* `TauCeti.metricVolumeDensity_innerSL`: the density of the inner product in an orthonormal basis
  is one.
* `TauCeti.contDiffAt_metricVolumeDensity`: the density is smooth in the form wherever the Gram
  determinant is nonzero.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Proposition 2.41.
-/

public section

open scoped ContDiff

noncomputable section

namespace TauCeti

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section NormedSpace

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The volume density `√ det (g (b i) (b j))` of a bilinear form `g` in the basis `b`. -/
def metricVolumeDensity (b : Module.Basis ι ℝ F) (g : F →L[ℝ] F →L[ℝ] ℝ) : ℝ :=
  √(Matrix.det fun i j ↦ g (b i) (b j))

/-- The defining formula of the volume density. -/
theorem metricVolumeDensity_def (b : Module.Basis ι ℝ F) (g : F →L[ℝ] F →L[ℝ] ℝ) :
    metricVolumeDensity b g = √(Matrix.det fun i j ↦ g (b i) (b j)) :=
  (rfl)

/-- The volume density is nonnegative. -/
theorem metricVolumeDensity_nonneg (b : Module.Basis ι ℝ F) (g : F →L[ℝ] F →L[ℝ] ℝ) :
    0 ≤ metricVolumeDensity b g :=
  Real.sqrt_nonneg _

/-- The volume density is smooth in the bilinear form wherever the Gram determinant is nonzero. -/
theorem contDiffAt_metricVolumeDensity (b : Module.Basis ι ℝ F) {g : F →L[ℝ] F →L[ℝ] ℝ}
    (hg : Matrix.det (fun i j ↦ g (b i) (b j)) ≠ 0) {n : ℕ∞ω} :
    ContDiffAt ℝ n (metricVolumeDensity b) g := by
  have hdet : ContDiff ℝ n fun g : F →L[ℝ] F →L[ℝ] ℝ ↦ Matrix.det fun i j ↦ g (b i) (b j) :=
    ContDiff.matrix_det fun i j ↦ by fun_prop
  exact hdet.contDiffAt.sqrt hg

end NormedSpace

/-- The volume density of the inner product in an orthonormal basis is one. -/
@[simp]
theorem metricVolumeDensity_innerSL {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (b : OrthonormalBasis ι ℝ F) : metricVolumeDensity b.toBasis (innerSL ℝ) = 1 := by
  have h : (fun i j ↦ innerSL ℝ (b.toBasis i) (b.toBasis j) : Matrix ι ι ℝ) = Matrix.gram ℝ b := by
    ext i j
    simp [Matrix.gram_apply]
  rw [metricVolumeDensity_def, h, Matrix.gram_eq_one_iff_orthonormal.2 b.orthonormal,
    Matrix.det_one, Real.sqrt_one]

end TauCeti
