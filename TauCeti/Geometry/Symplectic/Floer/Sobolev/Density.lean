/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.Line
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import TauCeti.MeasureTheory.Integral.Rectangle

/-!
# The `W^{1,2}` energy density of a section of the Floer cylinder

For a map `ξ : ℝ × ℝ → E` into a normed space, the `W^{1,2}` energy density
`‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²` is the integrand of the Sobolev norm on which the linear estimates for
the linearized Floer operator are stated. This file records the elementary facts about it shared by
those estimates, together with the derivatives of a section cut off by a function of `s`.

## Main results

* `Floer.continuous_sobolev`: the density of a `C¹` map is continuous.
* `Floer.fderiv_smul_fst_apply_stdComplexLineReal`,
  `Floer.fderiv_smul_fst_apply_stdComplexLineImag`: the derivatives of a section cut off by a
  function `β(s)` are `∂s (β ξ) = β ∂s ξ + β' ξ` and `∂t (β ξ) = β ∂t ξ`.
* `Floer.sobolev_add_le`: the density of `ξ₁ + ξ₂` is at most twice the sum of the densities of
  `ξ₁` and `ξ₂`.
* `Floer.setIntegral_norm_sq_le_sobolev`: the density bounds `‖ξ‖²`, so its integral over a
  rectangle bounds the `L²` norm.
-/

public section

open MeasureTheory Set ContinuousLinearMap

namespace TauCeti.Floer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The `W^{1,2}` energy density `‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²` of a `C¹` map `ξ : ℝ × ℝ → E` is
continuous. -/
theorem continuous_sobolev {ξ : ℝ × ℝ → E} (hξ : ContDiff ℝ 1 ξ) :
    Continuous fun z ↦ ‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
      ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2 := by
  have := hξ.continuous_fderiv one_ne_zero
  have := hξ.continuous
  fun_prop

/-- The `s`-derivative of a section cut off by a function `β(s)`: `∂s (β ξ) = β ∂s ξ + β' ξ`. -/
theorem fderiv_smul_fst_apply_stdComplexLineReal {ξ : ℝ × ℝ → E} {β : ℝ → ℝ} {β' : ℝ}
    {z : ℝ × ℝ} (hβ : HasDerivAt β β' z.1) (hξ : DifferentiableAt ℝ ξ z) :
    fderiv ℝ (fun w ↦ β w.1 • ξ w) z stdComplexLineReal =
      β z.1 • fderiv ℝ ξ z stdComplexLineReal + β' • ξ z := by
  have hd : HasFDerivAt (fun w : ℝ × ℝ ↦ β w.1 • ξ w) _ z :=
    (hβ.hasFDerivAt.comp z hasFDerivAt_fst).smul hξ.hasFDerivAt
  rw [hd.fderiv]
  simp [stdComplexLineReal_eq, add_comm]

/-- The `t`-derivative of a section cut off by a function `β(s)`: `∂t (β ξ) = β ∂t ξ`. -/
theorem fderiv_smul_fst_apply_stdComplexLineImag {ξ : ℝ × ℝ → E} {β : ℝ → ℝ} {z : ℝ × ℝ}
    (hβ : DifferentiableAt ℝ β z.1) (hξ : DifferentiableAt ℝ ξ z) :
    fderiv ℝ (fun w ↦ β w.1 • ξ w) z stdComplexLineImag =
      β z.1 • fderiv ℝ ξ z stdComplexLineImag := by
  have hd : HasFDerivAt (fun w : ℝ × ℝ ↦ β w.1 • ξ w) _ z :=
    (hβ.hasDerivAt.hasFDerivAt.comp z hasFDerivAt_fst).smul hξ.hasFDerivAt
  rw [hd.fderiv]
  simp [stdComplexLineImag_eq]

/-- The `W^{1,2}` energy density of a section splits over a sum: the density of `ξ₁ + ξ₂` is at
most twice the sum of the densities of `ξ₁` and `ξ₂`. -/
theorem sobolev_add_le {ξ₁ ξ₂ : ℝ × ℝ → E} {z : ℝ × ℝ} (h₁ : DifferentiableAt ℝ ξ₁ z)
    (h₂ : DifferentiableAt ℝ ξ₂ z) :
    ‖fderiv ℝ (ξ₁ + ξ₂) z stdComplexLineReal‖ ^ 2 + ‖fderiv ℝ (ξ₁ + ξ₂) z stdComplexLineImag‖ ^ 2 +
        ‖(ξ₁ + ξ₂) z‖ ^ 2 ≤
      2 * (‖fderiv ℝ ξ₁ z stdComplexLineReal‖ ^ 2 + ‖fderiv ℝ ξ₁ z stdComplexLineImag‖ ^ 2 +
          ‖ξ₁ z‖ ^ 2) +
        2 * (‖fderiv ℝ ξ₂ z stdComplexLineReal‖ ^ 2 + ‖fderiv ℝ ξ₂ z stdComplexLineImag‖ ^ 2 +
          ‖ξ₂ z‖ ^ 2) := by
  have hsq (x y : E) : ‖x + y‖ ^ 2 ≤ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) :=
    (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le x y) 2).trans add_sq_le
  rw [fderiv_add h₁ h₂]
  simp only [add_apply, Pi.add_apply]
  linarith [hsq (fderiv ℝ ξ₁ z stdComplexLineReal) (fderiv ℝ ξ₂ z stdComplexLineReal),
    hsq (fderiv ℝ ξ₁ z stdComplexLineImag) (fderiv ℝ ξ₂ z stdComplexLineImag), hsq (ξ₁ z) (ξ₂ z)]

/-- The `L²` norm of a `C¹` map over a rectangle is at most its `W^{1,2}` energy. -/
theorem setIntegral_norm_sq_le_sobolev {ξ : ℝ × ℝ → E} (hξ : ContDiff ℝ 1 ξ) (a b : ℝ) :
    ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖ξ z‖ ^ 2 ≤
      ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
        ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) :=
  setIntegral_mono_on (Continuous.integrableOn_Icc_prod_Icc (by have := hξ.continuous; fun_prop))
    (continuous_sobolev hξ).integrableOn_Icc_prod_Icc (measurableSet_Icc.prod measurableSet_Icc)
    fun z _ ↦ by
      have := sq_nonneg ‖fderiv ℝ ξ z stdComplexLineReal‖
      have := sq_nonneg ‖fderiv ℝ ξ z stdComplexLineImag‖
      linarith

end TauCeti.Floer
