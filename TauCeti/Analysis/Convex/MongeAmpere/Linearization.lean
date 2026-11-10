/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Topology.Algebra.Module.Determinant
public import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.Calculus.FDeriv.Det
import TauCeti.Analysis.Calculus.Morse.Linearization
import TauCeti.LinearAlgebra.Matrix.Trace.NonsingularInverse

/-!
# First variation of the classical Monge–Ampère equation

For a `C³` potential `u` with invertible Hessian, differentiating `det D²u = f` in direction `v`
gives `tr((D²u)⁻¹ D²(∂ᵥu)) = ∂ᵥf / f`. The determinant equation uses the same Hessian
`fderiv ℝ (∇ u)` as the classical density formula for the Aleksandrov measure. In an orthonormal
basis, the trace is the contraction with the inverse Hessian in the nondivergence-form operator.

## Main statements

* `TauCeti.trace_ringInverse_hessian_directional_eq` gives the basis-free trace form of the
  differentiated equation, assuming the determinant equation holds near the point.
* `OrthonormalBasis.sum_inv_hessian_directional_eq` gives its coordinate form for the
  nondivergence operator.

The use of Jacobi's formula and symmetry of third derivatives follows the
[KLS formalization](https://github.com/human-ai-mathematics/kls-lean/blob/9cde7938fc09cd017519c7c8a498bee99c12f717/formalization/FunctionalInequalities/Analysis/BakryEmery/LinearizedEquation.lean).
-/

public section

namespace TauCeti

open Filter
open scoped Gradient Matrix.Norms.Operator Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- If `u` is `C³` at `x` with invertible Hessian and `det D²u = f` near `x`, the trace of
`(D²u)⁻¹` composed with the Hessian of `∂ᵥu` equals `∂ᵥf / f` at `x`. -/
theorem trace_ringInverse_hessian_directional_eq [FiniteDimensional ℝ E] {u f : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 3 u x) (hne : (fderiv ℝ (∇ u) x).det ≠ 0)
    (heq : (fun y ↦ (fderiv ℝ (∇ u) y).det) =ᶠ[𝓝 x] f) (v : E) :
    LinearMap.trace ℝ E (Ring.inverse (fderiv ℝ (∇ u) x).toLinearMap *
      (fderiv ℝ (∇ fun y ↦ fderiv ℝ u y v) x).toLinearMap) = fderiv ℝ f x v / f x := by
  simp only [fderiv_gradient] at hne heq ⊢
  -- Use an orthonormal basis to apply the matrix Jacobi formula to the Hessian field.
  let b := (stdOrthonormalBasis ℝ E).toBasis
  let M := ((LinearMap.toMatrix b b).toLinearMap.comp
    (ContinuousLinearMap.coeLM ℝ : (E →L[ℝ] E) →ₗ[ℝ] (E →ₗ[ℝ] E))).toContinuousLinearMap
  -- The continuous lift leaves the underlying matrix representation unchanged.
  have hM (A : E →L[ℝ] E) : M A = LinearMap.toMatrix b b A.toLinearMap := rfl
  have hdet (y : E) : (M (hessianOperator u y)).det = (hessianOperator u y).det := by
    rw [hM, LinearMap.det_toMatrix]
  have hlocal : (fun y ↦ (M (hessianOperator u y)).det) =ᶠ[𝓝 x] f :=
    heq.mono fun y hy ↦ (hdet y).trans hy
  have hdet_ne : (M (hessianOperator u x)).det ≠ 0 := by rwa [hdet]
  have hH := (hu.contDiffAt_hessianOperator (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hJacobi : fderiv ℝ f x v = (M (hessianOperator u x)).det * Matrix.trace
      ((M (hessianOperator u x))⁻¹ * M (hessianOperator (fun y ↦ fderiv ℝ u y v) x)) := by
    have hchain : HasFDerivAt (fun y ↦ (M (hessianOperator u y)).det)
        ((fderiv ℝ Matrix.det (M (hessianOperator u x))).comp
          (M.comp (fderiv ℝ (hessianOperator u) x))) x :=
      Matrix.differentiable_det.differentiableAt.hasFDerivAt.comp x
        (M.hasFDerivAt.comp x hH.hasFDerivAt)
    rw [(hchain.congr_of_eventuallyEq hlocal.symm).fderiv]
    simp only [ContinuousLinearMap.comp_apply, hu.fderiv_hessianOperator_apply]
    exact Matrix.fderiv_det_apply (isUnit_iff_ne_zero.mpr hdet_ne) _
  rw [LinearMap.trace_ringInverse_mul_eq_matrix_trace b, ← hlocal.eq_of_nhds, hJacobi, mul_comm,
    mul_div_cancel_right₀ _ hdet_ne]
  simp only [hM]

/-- The differentiated Monge–Ampère equation as a coordinate contraction, in the form used by
nondivergence-form Schauder estimates. -/
theorem _root_.OrthonormalBasis.sum_inv_hessian_directional_eq {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : OrthonormalBasis ι ℝ E) {u f : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 3 u x) (hne : (fderiv ℝ (∇ u) x).det ≠ 0)
    (heq : (fun y ↦ (fderiv ℝ (∇ u) y).det) =ᶠ[𝓝 x] f) (v : E) :
    (∑ i, ∑ j,
      (LinearMap.toMatrix b.toBasis b.toBasis (fderiv ℝ (∇ u) x).toLinearMap)⁻¹ i j •
      fderiv ℝ (fderiv ℝ (fun y ↦ fderiv ℝ u y v)) x (b i) (b j)) = fderiv ℝ f x v / f x := by
  let _ : FiniteDimensional ℝ E := Module.Finite.of_basis b.toBasis
  have h := trace_ringInverse_hessian_directional_eq hu hne heq v
  rw [LinearMap.trace_ringInverse_mul_eq_matrix_trace b.toBasis] at h
  simpa only [fderiv_gradient, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    b.toMatrix_hessianOperator_apply, smul_eq_mul] using h

end TauCeti
