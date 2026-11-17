/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# Smoothness of parametric primitives

If `f : H → ℝ → E` is jointly `C^n`, then so is its parametric primitive
`(x, b) ↦ ∫ t in a₀..b, f x t` (`intervalIntegral.contDiff_parametric_primitive_of_contDiff`).
This is the smooth counterpart of Mathlib's
`intervalIntegral.continuous_parametric_primitive_of_continuous`. Composing with a `C^n` map
`x ↦ (x, c x)` gives the smoothness of integrals `∫ t in a₀..c x, f x t` whose upper limit
depends on the parameter.

The proof rescales the variable interval `[a₀, b]` to the fixed interval `[0, 1]`:

`∫ t in a₀..b, f x t = (b - a₀) • ∫ u in 0..1, f x (a₀ + (b - a₀) u)`,

and applies Mathlib's `ContDiff.parametric_intervalIntegral` to the integral over `[0, 1]`.
-/

public section

open MeasureTheory

namespace intervalIntegral

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup H]
  [NormedSpace ℝ H]

/-- **Smoothness of a parametric primitive.** If `f : H → ℝ → E` is jointly `C^n`, then the
parametric primitive `(x, b) ↦ ∫ t in a₀..b, f x t` is `C^n`. -/
theorem contDiff_parametric_primitive_of_contDiff {f : H → ℝ → E} {n : ℕ∞}
    (hf : ContDiff ℝ n (Function.uncurry f)) (a₀ : ℝ) :
    ContDiff ℝ n fun p : H × ℝ ↦ ∫ t in a₀..p.2, f p.1 t := by
  have h : (fun p : H × ℝ ↦ ∫ t in a₀..p.2, f p.1 t) =
      fun p ↦ (p.2 - a₀) • ∫ u in (0 : ℝ)..1, f p.1 (a₀ + (p.2 - a₀) * u) := by
    funext p
    rw [smul_integral_comp_add_mul (fun t ↦ f p.1 t)]
    simp
  rw [h]
  refine (contDiff_snd.sub contDiff_const).smul ?_
  exact ContDiff.parametric_intervalIntegral
    (f := fun q : (H × ℝ) × ℝ ↦ f q.1.1 (a₀ + (q.1.2 - a₀) * q.2))
    (hf.comp (contDiff_fst.fst.prodMk
      (contDiff_const.add ((contDiff_fst.snd.sub contDiff_const).mul contDiff_snd))))

end intervalIntegral
