/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.Calculus.ParametricIntegral.Basic

/-!
# Smoothness of parametric primitives

If `f : H → ℝ → E` is jointly `C^n`, then so is its parametric primitive
`(x, b) ↦ ∫ t in a₀..b, f x t` (`intervalIntegral.contDiff_parametric_primitive_of_contDiff`).
This is the smooth counterpart of Mathlib's
`intervalIntegral.continuous_parametric_primitive_of_continuous`. Composing with a `C^n` map
`x ↦ (x, c x)` gives the smoothness of integrals `∫ t in a₀..c x, f x t` whose upper limit
depends on the parameter.

It is the case `s = t = univ` of `Convex.contDiffOn_parametric_primitive`, which proves smoothness
up to the boundary on a product of convex sets by rescaling the variable interval `[a₀, b]` to
the fixed interval `[0, 1]`.

Without a parameter one derivative is gained: the primitive `b ↦ ∫ t in a₀..b, f t` of a `C^n`
function `f : ℝ → E` is `C^{n+1}` (`intervalIntegral.contDiff_primitive_of_contDiff`), by the
fundamental theorem of calculus.
-/

public section

open MeasureTheory Set

namespace intervalIntegral

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup H]
  [NormedSpace ℝ H]

/-- **Smoothness of a parametric primitive.** If `f : H → ℝ → E` is jointly `C^n`, then the
parametric primitive `(x, b) ↦ ∫ t in a₀..b, f x t` is `C^n`. -/
theorem contDiff_parametric_primitive_of_contDiff {f : H → ℝ → E} {n : ℕ∞}
    (hf : ContDiff ℝ n (Function.uncurry f)) (a₀ : ℝ) :
    ContDiff ℝ n fun p : H × ℝ ↦ ∫ t in a₀..p.2, f p.1 t :=
  contDiffOn_univ.1 <| by
    simpa only [univ_prod_univ, Function.uncurry_apply_pair] using
      Convex.contDiffOn_parametric_primitive convex_univ convex_univ uniqueDiffOn_univ
        (mem_univ a₀) (f := Function.uncurry f) (by simpa only [univ_prod_univ] using hf.contDiffOn)

/-- **Smoothness of a primitive.** If `f : ℝ → E` is `C^n`, then its primitive
`b ↦ ∫ t in a₀..b, f t` is `C^{n+1}`. -/
theorem contDiff_primitive_of_contDiff [CompleteSpace E] {f : ℝ → E} {n : ℕ∞}
    (hf : ContDiff ℝ n f) (a₀ : ℝ) : ContDiff ℝ (n + 1) fun b ↦ ∫ t in a₀..b, f t := by
  have hd : deriv (fun b ↦ ∫ t in a₀..b, f t) = f :=
    funext (hf.continuous.deriv_integral f a₀)
  exact contDiff_succ_iff_deriv.2
    ⟨differentiable_integral_of_continuous hf.continuous, by simp, by rwa [hd]⟩

end intervalIntegral
