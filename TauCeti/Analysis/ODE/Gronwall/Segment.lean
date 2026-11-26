/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import TauCeti.Analysis.ODE.Gronwall.TwoSided

/-!
# Grönwall's inequality along a segment

A function on a real normed space whose derivative satisfies `‖f′‖ ≤ K ‖f‖` along the segment
`[a, b]` grows by at most a factor `exp (K ‖b - a‖)` from `a` to `b`. Restricting `f` to the
affine parametrization `θ ↦ a + θ (b - a)` of the segment reduces this to the closed-interval
Grönwall bound `TauCeti.norm_le_gronwallBound_of_norm_derivWithin_le`. The derivative is only
needed within the segment.

## Main results

* `TauCeti.norm_le_norm_mul_exp_of_hasFDerivWithinAt_segment`: the bound for Fréchet
  derivatives within the segment.
* `TauCeti.norm_le_norm_mul_exp_of_norm_deriv_le`: the bound for a function of one variable over
  a normed field such as `ℂ`, differentiable along the segment.
-/

public section

open Set

namespace TauCeti

section Fderiv

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- **Grönwall's inequality along a segment.** If `f` has derivative `f' z` within the segment
`[a, b]` at each of its points and `‖f' z‖ ≤ K ‖f z‖` there, then
`‖f b‖ ≤ ‖f a‖ exp (K ‖b - a‖)`. -/
theorem norm_le_norm_mul_exp_of_hasFDerivWithinAt_segment {f : E → F} {f' : E → E →L[ℝ] F}
    {a b : E} {K : ℝ} (hf : ∀ z ∈ segment ℝ a b, HasFDerivWithinAt f (f' z) (segment ℝ a b) z)
    (hK : ∀ z ∈ segment ℝ a b, ‖f' z‖ ≤ K * ‖f z‖) :
    ‖f b‖ ≤ ‖f a‖ * Real.exp (K * ‖b - a‖) := by
  set p : ℝ → E := ⇑(AffineMap.lineMap a b : ℝ →ᵃ[ℝ] E)
  have hp : MapsTo p (Icc 0 1) (segment ℝ a b) := by
    rw [segment_eq_image_lineMap]
    exact mapsTo_image _ _
  have h := norm_le_gronwallBound_of_norm_derivWithin_le (f := f ∘ p)
    (f' := fun θ ↦ f' (p θ) (b - a)) (δ := ‖f a‖) (K := K * ‖b - a‖) (ε := 0)
    (left_mem_Icc.2 zero_le_one)
    (fun θ hθ ↦ (hf _ (hp hθ)).comp_hasDerivWithinAt θ AffineMap.hasDerivWithinAt_lineMap hp)
    (by simp [p]) (fun θ hθ ↦ by
      rw [add_zero, Function.comp_apply]
      calc ‖f' (p θ) (b - a)‖ ≤ ‖f' (p θ)‖ * ‖b - a‖ := (f' (p θ)).le_opNorm _
        _ ≤ K * ‖f (p θ)‖ * ‖b - a‖ := by gcongr; exact hK _ (hp hθ)
        _ = _ := by ring)
    1 (right_mem_Icc.2 zero_le_one)
  simpa [p, gronwallBound_ε0] using h

end Fderiv

/-- **Grönwall's inequality along a segment, one variable.** If `f : 𝕜 → F` is differentiable at
each point of the segment `[a, b]` and `‖f′‖ ≤ K ‖f‖` there, then
`‖f b‖ ≤ ‖f a‖ exp (K ‖b - a‖)`. -/
theorem norm_le_norm_mul_exp_of_norm_deriv_le {𝕜 F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAlgebra ℝ 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace ℝ F]
    [IsScalarTower ℝ 𝕜 F] {f : 𝕜 → F} {a b : 𝕜} {K : ℝ}
    (hf : ∀ z ∈ segment ℝ a b, DifferentiableAt 𝕜 f z)
    (hK : ∀ z ∈ segment ℝ a b, ‖deriv f z‖ ≤ K * ‖f z‖) :
    ‖f b‖ ≤ ‖f a‖ * Real.exp (K * ‖b - a‖) :=
  norm_le_norm_mul_exp_of_hasFDerivWithinAt_segment
    (f' := fun z ↦ (fderiv 𝕜 f z).restrictScalars ℝ)
    (fun z hz ↦ ((hf z hz).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt)
    (fun z hz ↦ by
      rw [ContinuousLinearMap.norm_restrictScalars, ← norm_deriv_eq_norm_fderiv]
      exact hK z hz)

end TauCeti
