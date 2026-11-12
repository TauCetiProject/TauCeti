/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.MaximumPrinciple.Parabolic.QuadraticReaction

/-!
# The scalar curvature lower bound for three-dimensional Ricci flow

Under a Ricci flow `∂ₜg = -2 Ric` on a closed three-manifold, the scalar curvature evolves by
`∂ₜR = ΔR + 2|Ric|²`, and `|Ric|² ≥ R² / 3`. So at every spatial minimum `∂ₜR ≥ (2/3) R²`. For
normalized initial metrics `R ≥ -6` at time zero, and the quadratic-reaction comparison
`TauCeti.div_one_sub_mul_le_of_mul_sq_le_deriv_of_isLocalMin` with `c = 2/3` and `ρ = -6`
propagates this to `R ≥ -6 / (1 + 4t)`.

This is a scalar statement about a function satisfying the differential inequality at spatial
local minima: no existence of a geometric flow or evolution equation is asserted here.

## Main results

* `TauCeti.neg_six_div_one_add_four_mul_le_of_mul_sq_le_deriv_of_isLocalMin`: the
  three-dimensional scalar curvature bound `-6 / (1 + 4t)`.

## References

* J. W. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Clay Mathematics
  Monographs 3 (2007), Chapter 4 (the maximum principle and the scalar curvature lower bound
  for normalized initial metrics).
-/

public section

namespace TauCeti

open Set

variable {X : Type*} [TopologicalSpace X] {T : ℝ} {u : ℝ → X → ℝ}

/-- **The scalar curvature lower bound in dimension three.**

On a compact space `X`, let `u` be continuous on `[0, T] × X` and differentiable in time, with
`∂ₜu ≥ (2/3) u²` at every spatial local minimum lying below the bound. If `u ≥ -6` at time zero,
then `u ≥ -6 / (1 + 4t)` for every `t ∈ [0, T]`. For the scalar curvature of a Ricci flow on a
closed three-manifold, `-6` is the lower bound for normalized initial metrics. -/
theorem neg_six_div_one_add_four_mul_le_of_mul_sq_le_deriv_of_isLocalMin [CompactSpace X]
    (hcont : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ))
    (hdiff : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, DifferentiableAt ℝ (fun s ↦ u s x) t)
    (hloc : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, IsLocalMin (u t) x →
      u t x < -6 / (1 + 4 * t) → 2 / 3 * u t x ^ 2 ≤ deriv (fun s ↦ u s x) t)
    (hinit : ∀ x, -6 ≤ u 0 x) :
    ∀ ⦃t⦄, t ∈ Icc 0 T → ∀ x, -6 / (1 + 4 * t) ≤ u t x := by
  have hden (t : ℝ) : 1 - 2 / 3 * -6 * t = 1 + 4 * t := by ring
  intro t ht x
  rw [← hden]
  exact div_one_sub_mul_le_of_mul_sq_le_deriv_of_isLocalMin (by norm_num) (by norm_num) hcont
    hdiff (fun s hs y hmin hlt ↦ hloc hs y hmin (by rwa [← hden])) hinit ht x

end TauCeti
