/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.TaylorIntegral

/-!
# Second derivatives along a line

Mathlib's `DifferentiableAt.deriv_comp_add_smul` computes the derivative of the restriction
`s ↦ f (x + s • y)` of a function to a line. This file records the second derivative: it is the
diagonal entry `fderiv 𝕜 (fderiv 𝕜 f) (x + t • y) y y` of the Hessian.

## Main results

* `ContDiffAt.deriv_deriv_comp_add_smul`: the second derivative of `s ↦ f (x + s • y)` at `t` is
  `fderiv 𝕜 (fderiv 𝕜 f) (x + t • y) y y`, for `f` of class `C²` at `x + t • y`.
-/

public section

open Topology

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {f : E → F} {x y : E} {t : 𝕜}

/-- The second derivative of the restriction `s ↦ f (x + s • y)` of a `C²` function to a line is
the diagonal Hessian entry `fderiv 𝕜 (fderiv 𝕜 f) (x + t • y) y y`. -/
theorem ContDiffAt.deriv_deriv_comp_add_smul (hf : ContDiffAt 𝕜 2 f (x + t • y)) :
    deriv (deriv fun s : 𝕜 => f (x + s • y)) t = fderiv 𝕜 (fderiv 𝕜 f) (x + t • y) y y := by
  have hfev : ∀ᶠ z in 𝓝 (x + t • y), DifferentiableAt 𝕜 f z := by
    filter_upwards [hf.eventually (by norm_num)] with z hz using hz.differentiableAt (by norm_num)
  have hline : ContinuousAt (fun s : 𝕜 => x + s • y) t := by fun_prop
  have hdiff : ∀ᶠ s in 𝓝 t, DifferentiableAt 𝕜 f (x + s • y) := hline.tendsto.eventually hfev
  have hev : (deriv fun s : 𝕜 => f (x + s • y)) =ᶠ[𝓝 t] fun s => fderiv 𝕜 f (x + s • y) y := by
    filter_upwards [hdiff] with s hs using hs.deriv_comp_add_smul
  rw [hev.deriv_eq]
  simpa [iteratedFDeriv_two_apply] using (hf : ContDiffAt 𝕜 (1 + 1 : ℕ) f _).deriv_fderiv_add_smul
