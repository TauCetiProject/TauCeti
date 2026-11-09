/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.TaylorIntegral
public import TauCeti.Analysis.Calculus.Deriv.Second
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Second derivatives along a line

Mathlib's `DifferentiableAt.deriv_comp_add_smul` computes the derivative of the restriction
`s ↦ f (x + s • y)` of a function to a line. This file records the second derivative: it is the
diagonal entry `fderiv 𝕜 (fderiv 𝕜 f) (x + t • y) y y` of the Hessian.

## Main results

* `DifferentiableAt.hasDerivAt_deriv_comp_add_smul`: if `f` is differentiable near `x + t • y`
  and `fderiv 𝕜 f` is differentiable at `x + t • y`, then the derivative of
  `s ↦ f (x + s • y)` has derivative `fderiv 𝕜 (fderiv 𝕜 f) (x + t • y) y y` at `t`.
* `ContDiffAt.deriv_deriv_comp_add_smul`: the second derivative of `s ↦ f (x + s • y)` at `t` is
  `fderiv 𝕜 (fderiv 𝕜 f) (x + t • y) y y`, for `f` of class `C²` at `x + t • y`.
-/

public section

open Topology

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {f : E → F} {x y : E} {t : 𝕜}

/-- If `f` is differentiable near `x + t • y` and `fderiv 𝕜 f` is differentiable at
`x + t • y`, then the derivative of the restriction `s ↦ f (x + s • y)` of `f` to a line has
derivative the diagonal Hessian entry `fderiv 𝕜 (fderiv 𝕜 f) (x + t • y) y y` at `t`. -/
theorem DifferentiableAt.hasDerivAt_deriv_comp_add_smul
    (hf' : DifferentiableAt 𝕜 (fderiv 𝕜 f) (x + t • y))
    (hf : ∀ᶠ z in 𝓝 (x + t • y), DifferentiableAt 𝕜 f z) :
    HasDerivAt (deriv fun s : 𝕜 => f (x + s • y)) (fderiv 𝕜 (fderiv 𝕜 f) (x + t • y) y y) t := by
  have hline : HasDerivAt (fun s : 𝕜 => x + s • y) y t := by
    simpa using ((hasDerivAt_id t).smul_const y).const_add x
  have hev : (fun s => fderiv 𝕜 f (x + s • y) y) =ᶠ[𝓝 t] deriv fun s : 𝕜 => f (x + s • y) := by
    filter_upwards [hline.continuousAt.tendsto.eventually hf] with s hs
    exact hs.deriv_comp_add_smul.symm
  simpa using ((hf'.hasFDerivAt.comp_hasDerivAt t hline).clm_apply
    (hasDerivAt_const t y)).congr_of_eventuallyEq hev.symm

/-- The second derivative of the restriction `s ↦ f (x + s • y)` of a `C²` function to a line is
the diagonal Hessian entry `fderiv 𝕜 (fderiv 𝕜 f) (x + t • y) y y`. -/
theorem ContDiffAt.deriv_deriv_comp_add_smul (hf : ContDiffAt 𝕜 2 f (x + t • y)) :
    deriv (deriv fun s : 𝕜 => f (x + s • y)) t = fderiv 𝕜 (fderiv 𝕜 f) (x + t • y) y y :=
  ((hf.fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero).hasDerivAt_deriv_comp_add_smul
    (hf.eventually (by simp) |>.mono fun _ hz => hz.differentiableAt two_ne_zero) |>.deriv

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Along `s ↦ x + s • v`, subtracting `K * ‖·‖² / 2` lowers the second derivative
by `K * ‖v‖²`. -/
theorem deriv_deriv_comp_add_smul_sub_norm_sq {f : E → ℝ} (x v : E) {t : ℝ}
    (hf : ContDiffAt ℝ 2 f (x + t • v)) (K : ℝ) :
    deriv (deriv (fun s : ℝ ↦ f (x + s • v) - K * ‖x + s • v‖ ^ 2 / 2)) t =
      fderiv ℝ (fderiv ℝ f) (x + t • v) v v - K * ‖v‖ ^ 2 := by
  have hnorm (s : ℝ) : K * ‖x + s • v‖ ^ 2 / 2 =
      K * ‖x‖ ^ 2 / 2 + (K * inner ℝ x v) * s + (K * ‖v‖ ^ 2 / 2) * s ^ 2 := by
    rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
      mul_pow, sq_abs]
    ring
  simp_rw [hnorm]
  have hline : ContDiffAt ℝ 2 (fun s : ℝ ↦ f (x + s • v)) t :=
    hf.comp t (by fun_prop)
  rw [hline.deriv_deriv_sub_quadratic, hf.deriv_deriv_comp_add_smul]
  ring

end TauCeti
