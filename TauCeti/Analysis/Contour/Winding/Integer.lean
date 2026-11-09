/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Winding.Number.Basic
public import TauCeti.Analysis.Calculus.ContDiff.PiecewiseC1On
import TauCeti.Analysis.Contour.Winding.AbsolutelyContinuous.Basic
import TauCeti.Analysis.Contour.AbsolutelyContinuous

/-!
# The winding number of a closed curve is an integer

For a curve `γ` on an interval that returns to its start (`γ a = γ b`), avoids a point `w`, and is
regular enough — continuous, differentiable off a countable set, with an interval-integrable index
integrand — its generalized winding number about `w` is an integer (see
`exists_int_windingNumber_of_closed` for the exact hypotheses). This is the integrality step on the
Hungerbühler–Wasem path (HW Thm 3.3): combined with continuity of the winding number in the point,
it makes the winding number locally constant on the complement of the curve — the input to the
homology form of Cauchy's theorem.

The proof recovers absolute continuity from the countable-exception hypotheses and then uses
`AbsolutelyContinuousOnInterval.exists_int_windingNumber`. In that theorem, the endpoint ratio
of a closed curve is `1`, so its winding number is an integer.

## Main results

* `TauCeti.Contour.exists_int_windingNumber_of_closed` — the generalized winding number of a closed
  curve is an integer.
* `TauCeti.IsPiecewiseC1On.exists_int_windingNumber` — the same for a closed piecewise-`C¹`
  curve, whose regularity supplies the raw hypotheses on its own.

## Provenance

Adapted from `hasGeneralizedWindingNumber_integer_of_closed` in `WindingInteger.lean` of the AINTLIB
`LeanModularForms` development, restated for a raw `γ : ℝ → ℂ` on an oriented interval. The
integrality statement is now derived from its absolutely continuous form through the
countable-exception fundamental theorem of calculus.
-/

public section

open Filter MeasureTheory Set Topology

open scoped Interval

namespace TauCeti.Contour

/-- **The winding number of a closed curve is an integer.** For a curve `γ` on the oriented interval
with endpoints `a`, `b` that returns to its start (`γ a = γ b`), is continuous on `Set.uIcc a b`,
differentiable off a countable set `P`, and avoids `w` throughout `Set.uIcc a b`, the generalized
winding number `windingNumber γ a b w` is an integer: it is `0` unless the index integrand
`(γ · - w)⁻¹ * deriv γ` is interval integrable, in which case it is the integer of
`AbsolutelyContinuousOnInterval.exists_int_windingNumber`. -/
theorem exists_int_windingNumber_of_closed {γ : ℝ → ℂ} {w : ℂ} {a b : ℝ} {P : Set ℝ}
    (hclosed : γ a = γ b) (hP : P.Countable) (hγ_cont : ContinuousOn γ (uIcc a b))
    (hγ_diff : ∀ t ∈ Ioo (min a b) (max a b) \ P, DifferentiableAt ℝ γ t)
    (h_avoid : ∀ t ∈ uIcc a b, γ t ≠ w) :
    ∃ n : ℤ, windingNumber γ a b w = n := by
  by_cases h_int : IntervalIntegrable (fun t ↦ (γ t - w)⁻¹ * deriv γ t) volume a b
  swap
  · -- without integrability the truncated integrals all vanish, so the value is `0`
    refine ⟨0, ?_⟩
    obtain ⟨δ, hδ, hδ'⟩ : ∃ δ > 0, ∀ t ∈ uIcc a b, δ ≤ ‖γ t - w‖ := by
      obtain ⟨t₀, ht₀, hmin⟩ := isCompact_uIcc.exists_isMinOn nonempty_uIcc
        (hγ_cont.sub continuousOn_const).norm
      exact ⟨‖γ t₀ - w‖, norm_pos_iff.mpr (sub_ne_zero.mpr (h_avoid t₀ ht₀)), fun t ht ↦ hmin ht⟩
    have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (∫ t in a..b,
        if ‖γ t - w‖ > ε then (γ t - w)⁻¹ * deriv γ t else 0) = 0 := by
      filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
      have hlt (t : ℝ) (ht : t ∈ uIcc a b) : ε < ‖γ t - w‖ := hε.2.trans_le (hδ' t ht)
      have hcongr : (∫ t in a..b, if ‖γ t - w‖ > ε then (γ t - w)⁻¹ * deriv γ t else 0) =
          ∫ t in a..b, (γ t - w)⁻¹ * deriv γ t :=
        intervalIntegral.integral_congr fun t ht ↦ by simp [hlt t ht]
      rw [hcongr]
      exact intervalIntegral.integral_undef h_int
    have hpv : cauchyPVAt γ a b (fun z ↦ (z - w)⁻¹) w = 0 :=
      cauchyPVAt_eq_of_tendsto (F := fun _ ↦ 0) tendsto_const_nhds hev
    simp [windingNumber_eq_cauchyPVAt, hpv]
  exact (hγ_cont.absolutelyContinuousOnInterval_of_intervalIntegrable_inv_sub_mul_deriv hP
    hγ_diff h_avoid h_int).exists_int_windingNumber hclosed
      (by simpa only [mem_image, not_exists, not_and] using h_avoid)

/-- **Piecewise-`C¹` form of winding-number integrality.** For a closed piecewise-`C¹` curve that
avoids `w`, the winding number about `w` is an integer. Piecewise-`C¹` regularity supplies the
continuity, differentiability and integrability hypotheses of
`exists_int_windingNumber_of_closed`. -/
theorem _root_.TauCeti.IsPiecewiseC1On.exists_int_windingNumber {γ : ℝ → ℂ} {a b : ℝ} {w : ℂ}
    (hγ : IsPiecewiseC1On γ a b) (hclosed : γ a = γ b)
    (h_avoid : ∀ t ∈ uIcc a b, γ t ≠ w) :
    ∃ n : ℤ, windingNumber γ a b w = n := by
  obtain ⟨P, hP, hγ_diff⟩ := hγ.exists_countable_differentiableAt
  exact exists_int_windingNumber_of_closed hclosed hP hγ.continuousOn hγ_diff h_avoid

end TauCeti.Contour

end
