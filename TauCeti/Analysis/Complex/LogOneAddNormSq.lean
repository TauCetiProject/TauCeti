/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import TauCeti.Analysis.Calculus.FDeriv.RestrictScalars

/-!
# The Laplacian of `log (1 + ‖f‖²)` for a holomorphic function

For a function `f : ℂ → ℂ` that is complex analytic at `z`, the squared modulus has Laplacian
`Δ ‖f‖² = 4 ‖f'‖²` at `z`, and

`Δ log (1 + ‖f‖²) = 4 ‖f'‖² / (1 + ‖f‖²)²`.

The right-hand side is the pullback by `f` of the density of the Fubini–Study area form of the
Riemann sphere, up to the constant `4`. The first-order identity
`‖∇ ‖f‖²‖² = 4 ‖f‖² ‖f'‖²` used on the way only needs `f` to be complex differentiable at `z`.

When `f` is entire, `-log (1 + ‖f‖²) / 2` is a smooth real function on the whole plane. When `f`
is moreover a monic polynomial of degree `m ≥ 1`, it differs from `-m log ‖z‖` by a function
tending to zero at infinity; this makes it a background for semilinear equations whose
solutions have logarithmic growth prescribed by the zeros of `f`.

## Main results

* `TauCeti.laplacian_norm_sq_of_analyticAt`: `Δ ‖f‖² = 4 ‖f'‖²`.
* `TauCeti.norm_gradient_norm_sq_sq_of_differentiableAt`: `‖∇ ‖f‖²‖² = 4 ‖f‖² ‖f'‖²`.
* `TauCeti.laplacian_log_one_add_norm_sq_of_analyticAt`:
  `Δ log (1 + ‖f‖²) = 4 ‖f'‖² / (1 + ‖f‖²)²`.
-/

public section

namespace TauCeti

open Complex InnerProductSpace Laplacian Filter Topology Gradient

variable {f : ℂ → ℂ} {z : ℂ}

/-- The squared modulus of a holomorphic function has Laplacian `4 ‖f'‖²`. -/
theorem laplacian_norm_sq_of_analyticAt (hf : AnalyticAt ℂ f z) :
    Δ (fun w ↦ ‖f w‖ ^ 2) z = 4 * ‖deriv f z‖ ^ 2 := by
  have hfR : ContDiffAt ℝ 2 f z := hf.contDiffAt.restrict_scalars ℝ
  have hΔ : Δ f z = 0 := hf.harmonicAt.2.self_of_nhds
  have h1 := hf.differentiableAt.fderiv_restrictScalars_eq_smul_deriv ℝ 1
  have hI := hf.differentiableAt.fderiv_restrictScalars_eq_smul_deriv ℝ I
  rw [one_smul] at h1
  rw [hfR.laplacian_norm_sq Complex.orthonormalBasisOneI, hΔ, Fin.sum_univ_two]
  simp only [Complex.coe_orthonormalBasisOneI, Matrix.cons_val_zero, Matrix.cons_val_one,
    h1, hI, smul_eq_mul, norm_mul, norm_I, one_mul, inner_zero_right]
  ring

/-- The squared norm of the gradient of `‖f‖²` for a complex differentiable function `f` is
`4 ‖f‖² ‖f'‖²`. -/
theorem norm_gradient_norm_sq_sq_of_differentiableAt (hf : DifferentiableAt ℂ f z) :
    ‖∇ (fun w ↦ ‖f w‖ ^ 2) z‖ ^ 2 = 4 * ‖f z‖ ^ 2 * ‖deriv f z‖ ^ 2 := by
  have hfd : DifferentiableAt ℝ f z := hf.restrictScalars ℝ
  have h1 := hf.fderiv_restrictScalars_eq_smul_deriv ℝ 1
  have hI := hf.fderiv_restrictScalars_eq_smul_deriv ℝ I
  rw [one_smul] at h1
  set b := Complex.orthonormalBasisOneI
  have hgrad : ‖∇ (fun w ↦ ‖f w‖ ^ 2) z‖ ^ 2 =
      ∑ i, fderiv ℝ (fun w ↦ ‖f w‖ ^ 2) z (b i) ^ 2 := by
    rw [← b.sum_sq_inner_left]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [inner_gradient_left]
  rw [hgrad, hfd.hasFDerivAt.norm_sq.fderiv, Fin.sum_univ_two]
  simp only [b, Complex.coe_orthonormalBasisOneI, Matrix.cons_val_zero, Matrix.cons_val_one,
    smul_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply, h1, hI, smul_eq_mul,
    Complex.inner, Complex.sq_norm, Complex.normSq_apply]
  simp only [mul_re, mul_im, conj_re, conj_im, I_re, I_im]
  ring

/-- **The Laplacian of `log (1 + ‖f‖²)`.** For a holomorphic function `f`,
`Δ log (1 + ‖f‖²) = 4 ‖f'‖² / (1 + ‖f‖²)²`. -/
theorem laplacian_log_one_add_norm_sq_of_analyticAt (hf : AnalyticAt ℂ f z) :
    Δ (fun w ↦ Real.log (1 + ‖f w‖ ^ 2)) z = 4 * ‖deriv f z‖ ^ 2 / (1 + ‖f z‖ ^ 2) ^ 2 := by
  set q : ℂ → ℝ := fun w ↦ ‖f w‖ ^ 2
  have hq : ContDiffAt ℝ 2 q z := (hf.contDiffAt.restrict_scalars ℝ).norm_sq ℝ
  have hpos : 0 < 1 + q z := by positivity
  have hF : ContDiffAt ℝ 2 (fun t : ℝ ↦ Real.log (1 + t)) (q z) :=
    (contDiffAt_const.add contDiffAt_id).log hpos.ne'
  have hd (t : ℝ) (ht : 0 < 1 + t) :
      HasDerivAt (fun t : ℝ ↦ Real.log (1 + t)) (1 + t)⁻¹ t := by
    simpa using ((hasDerivAt_id t).const_add 1).log ht.ne'
  have hdF : deriv (fun t : ℝ ↦ Real.log (1 + t)) =ᶠ[𝓝 (q z)] fun t ↦ (1 + t)⁻¹ := by
    filter_upwards [(continuous_const.add continuous_id).continuousAt.eventually
      (lt_mem_nhds hpos)] with t ht
    exact (hd t ht).deriv
  have hdd : deriv (deriv fun t : ℝ ↦ Real.log (1 + t)) (q z) = -1 / (1 + q z) ^ 2 := by
    rw [hdF.deriv_eq]
    exact (((hasDerivAt_id (q z)).const_add 1).inv hpos.ne').deriv.trans (by simp)
  have hcomp := hF.laplacian_comp hq
  simp only [Function.comp_def, q] at hcomp
  rw [hdd, (hd _ hpos).deriv, norm_gradient_norm_sq_sq_of_differentiableAt hf.differentiableAt,
    laplacian_norm_sq_of_analyticAt hf] at hcomp
  rw [hcomp]
  field_simp
  ring

end TauCeti
