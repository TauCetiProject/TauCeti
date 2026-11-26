/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.ODE.Basic
import TauCeti.Analysis.ODE.Gronwall.TwoSided

/-!
# Two-sided Grönwall comparison of integral curves

For two integral curves of the same spatially Lipschitz field, their distance at one time
controls their distance at any other time in a closed interval. The estimate follows from
`TauCeti.norm_le_gronwallBound_of_norm_derivWithin_le` applied to their difference and does
not require completeness of the state space.
-/

public section

open Set
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The distance between two integral curves of a spatially Lipschitz field grows at most
exponentially, in either time direction from any reference time in the interval. -/
theorem IsIntegralCurveOn.dist_le_mul_exp {v : ℝ → E → E} {γ₁ γ₂ : ℝ → E}
    {a b : ℝ} {K : ℝ≥0}
    (h₁ : IsIntegralCurveOn γ₁ v (Icc a b)) (h₂ : IsIntegralCurveOn γ₂ v (Icc a b))
    (hLip : ∀ r ∈ Icc a b, LipschitzWith K (v r))
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    dist (γ₁ t) (γ₂ t) ≤ dist (γ₁ s) (γ₂ s) * Real.exp (K * |t - s|) := by
  have h := TauCeti.norm_le_gronwallBound_of_norm_derivWithin_le (f := fun r ↦ γ₁ r - γ₂ r)
    (K := (K : ℝ)) (ε := 0) hs (fun r hr ↦ (h₁ r hr).sub (h₂ r hr)) le_rfl
    (fun r hr ↦ by simpa only [add_zero] using (hLip r hr).norm_sub_le (γ₁ r) (γ₂ r)) t ht
  simpa only [gronwallBound_ε0, dist_eq_norm] using h

end
