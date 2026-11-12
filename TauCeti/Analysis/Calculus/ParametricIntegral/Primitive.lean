/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# Smoothness of parametric primitives

If `f : E → ℝ → F` is jointly `C^n`, then so is the parametric primitive
`(x, y) ↦ ∫ t in a₀..y, f x t`, jointly in the parameter `x` and the upper limit `y`
(`TauCeti.contDiff_parametric_primitive_of_contDiff`). This is the smooth counterpart of
Mathlib's `intervalIntegral.continuous_parametric_primitive_of_continuous`.

The substitution `t = a₀ + (y - a₀) s` writes the primitive as
`(y - a₀) • ∫ s in 0..1, f x (a₀ + (y - a₀) s)`, an integral over a fixed interval of a jointly
`C^n` integrand, to which Mathlib's `ContDiff.parametric_intervalIntegral` applies.
-/

public section

open MeasureTheory

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- A parametric primitive `(x, y) ↦ ∫ t in a₀..y, f x t` of a jointly `C^n` function is jointly
`C^n` in the parameter and the upper limit. -/
theorem contDiff_parametric_primitive_of_contDiff {f : E → ℝ → F} {n : ℕ∞}
    (hf : ContDiff ℝ n f.uncurry) (a₀ : ℝ) :
    ContDiff ℝ n fun p : E × ℝ ↦ ∫ t in a₀..p.2, f p.1 t := by
  have hsub (p : E × ℝ) : ∫ t in a₀..p.2, f p.1 t =
      (p.2 - a₀) • ∫ s in (0 : ℝ)..1, f p.1 (a₀ + (p.2 - a₀) * s) := by
    rw [intervalIntegral.smul_integral_comp_add_mul]
    simp
  simp_rw [hsub]
  refine (contDiff_snd.sub contDiff_const).smul ?_
  have hg : ContDiff ℝ n fun q : (E × ℝ) × ℝ ↦ (q.1.1, a₀ + (q.1.2 - a₀) * q.2) := by fun_prop
  exact ContDiff.parametric_intervalIntegral (f := fun q : (E × ℝ) × ℝ ↦
    f q.1.1 (a₀ + (q.1.2 - a₀) * q.2)) (hf.comp hg)

end TauCeti
