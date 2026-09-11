/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Iterated derivatives in one variable of a product

The iterated derivative of a slice `x ↦ f (p, x)` is the total iterated derivative of `f`
restricted to directions in the second factor. Consequently these partial derivatives vary
continuously in both variables when `f` is sufficiently differentiable. This gives the
joint derivative continuity needed for smooth families in function spaces.
-/

public section

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {P : Type*} [NormedAddCommGroup P] [NormedSpace 𝕜 P]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : WithTop ℕ∞} {f : P × E → F}

/-- The iterated derivative in the second variable is the total iterated derivative restricted
to directions with zero first component. -/
theorem iteratedFDeriv_prod_right (hf : ContDiff 𝕜 n f) (m : ℕ) (hm : m ≤ n)
    (p : P) (x : E) :
    iteratedFDeriv 𝕜 m (fun y ↦ f (p, y)) x =
      (iteratedFDeriv 𝕜 m f (p, x)).compContinuousLinearMap
        (fun _ ↦ ContinuousLinearMap.inr 𝕜 P E) := by
  have h := (ContinuousLinearMap.inr 𝕜 P E).iteratedFDeriv_comp_right
    (hf.comp (contDiff_const.add contDiff_id) :
      ContDiff 𝕜 n (fun z : P × E ↦ f ((p, 0) + z))) x hm
  simpa only [Function.comp_def, ContinuousLinearMap.inr_apply, Prod.mk_add_mk,
    add_zero, zero_add, iteratedFDeriv_comp_add_left] using h

/-- The iterated derivatives in the second variable of a `C^n` function are jointly continuous
in the parameter and the evaluation point, through order `n`. -/
theorem continuous_iteratedFDeriv_prod_right (hf : ContDiff 𝕜 n f) (m : ℕ) (hm : m ≤ n) :
    Continuous (fun z : P × E ↦ iteratedFDeriv 𝕜 m (fun y ↦ f (z.1, y)) z.2) := by
  simp_rw [iteratedFDeriv_prod_right hf m hm]
  exact (ContinuousMultilinearMap.compContinuousLinearMapL
    (fun _ : Fin m ↦ ContinuousLinearMap.inr 𝕜 P E)).continuous.comp
      (hf.continuous_iteratedFDeriv hm)

end TauCeti
