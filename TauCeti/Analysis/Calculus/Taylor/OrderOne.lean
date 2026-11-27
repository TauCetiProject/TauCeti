/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import TauCeti.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Taylor's formula of order one with integral remainder

For a function `a` on `ℝ` with values in a real Banach space, whose derivative `b` is
differentiable with derivative `c` continuous on `[t₀, t]`, Taylor's formula of order one with
integral remainder reads

`a t = a t₀ + (t - t₀) b t₀ + ∫_{t₀}^t (t - r) c r dr`

(`TauCeti.intervalIntegral.eq_add_sub_smul_add_integral_sub_smul`). It follows from the
fundamental theorem of calculus and an integration by parts against `r ↦ t - r`.

Conversely, the remainder term `σ ↦ ∫_{t₀}^σ (σ - r) A r dr` of a function `A` continuous on a
compact interval `[a, b]` containing `t₀` has derivative `∫_{t₀}^τ A r dr` within `[a, b]` at
every `τ ∈ [a, b]` (`TauCeti.intervalIntegral.hasDerivWithinAt_integral_sub_smul`), and that
primitive in turn has derivative `A τ` within `[a, b]`
(`TauCeti.intervalIntegral.hasDerivWithinAt_integral`, in
`TauCeti.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus`). So the remainder term is twice
differentiable within `[a, b]` with second derivative `A`.

## Main declarations

* `TauCeti.intervalIntegral.eq_add_sub_smul_add_integral_sub_smul`: Taylor's formula of order one
  with integral remainder.
* `TauCeti.intervalIntegral.intervalIntegrable_sub_smul`: the integrand of the remainder term is
  interval integrable.
* `TauCeti.intervalIntegral.hasDerivWithinAt_integral_sub_smul`: the derivative of the remainder
  term `σ ↦ ∫_{t₀}^σ (σ - r) A r dr`.
-/

public section

open MeasureTheory Set

namespace TauCeti

namespace intervalIntegral

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The weighted function `r ↦ (t - r) v r` is interval integrable on `[t₀, t]` when `v` is
continuous there. -/
theorem intervalIntegrable_sub_smul {v : ℝ → X} {t₀ t : ℝ} (hv : ContinuousOn v (uIcc t₀ t)) :
    IntervalIntegrable (fun r ↦ (t - r) • v r) volume t₀ t :=
  ((continuous_const.sub continuous_id).continuousOn.smul hv).intervalIntegrable

variable [CompleteSpace X]

/-- **Taylor's formula of order one with integral remainder**: if `a' = b` and `b' = c` on
`[t₀, t]`, with `c` continuous there, then
`a t = a t₀ + (t - t₀) b t₀ + ∫_{t₀}^t (t - r) c r dr`. -/
theorem eq_add_sub_smul_add_integral_sub_smul {a b c : ℝ → X} {t₀ t : ℝ}
    (ha : ∀ τ ∈ uIcc t₀ t, HasDerivAt a (b τ) τ) (hb : ∀ τ ∈ uIcc t₀ t, HasDerivAt b (c τ) τ)
    (hc : ContinuousOn c (uIcc t₀ t)) :
    a t = a t₀ + (t - t₀) • b t₀ + ∫ r in t₀..t, (t - r) • c r := by
  have hbc : ContinuousOn b (uIcc t₀ t) := fun τ hτ ↦ (hb τ hτ).continuousAt.continuousWithinAt
  -- Integrate by parts against `r ↦ t - r`, whose derivative is `-1`.
  have hparts := _root_.intervalIntegral.integral_smul_deriv_eq_deriv_smul_of_hasDerivAt
    (u := fun r ↦ t - r) (u' := fun _ ↦ (-1 : ℝ)) (v := b) (v' := c)
    (continuous_const.sub continuous_id).continuousOn hbc
    (fun r _ ↦ by simpa using (hasDerivAt_id r).const_sub t)
    (fun r hr ↦ hb r (Ioo_subset_Icc_self hr))
    intervalIntegrable_const hc.intervalIntegrable
  have hftc : ∫ r in t₀..t, b r = a t - a t₀ :=
    _root_.intervalIntegral.integral_eq_sub_of_hasDerivAt ha hbc.intervalIntegrable
  rw [hparts, sub_self, zero_smul, zero_sub]
  simp only [neg_smul, one_smul, _root_.intervalIntegral.integral_neg, hftc]
  abel

/-- Within a compact interval `[a, b]` containing the base point `t₀`, the remainder term
`σ ↦ ∫_{t₀}^σ (σ - r) A r dr` of a continuous `A` has derivative `∫_{t₀}^τ A r dr` at `τ`. -/
theorem hasDerivWithinAt_integral_sub_smul {A : ℝ → X} {a b t₀ τ : ℝ}
    (hA : ContinuousOn A (Icc a b)) (ht₀ : t₀ ∈ Icc a b) (hτ : τ ∈ Icc a b) :
    HasDerivWithinAt (fun σ ↦ ∫ r in t₀..σ, (σ - r) • A r) (∫ r in t₀..τ, A r) (Icc a b) τ := by
  have hrA : ContinuousOn (fun r ↦ r • A r) (Icc a b) := continuousOn_id.smul hA
  -- On `[a, b]`, `∫_{t₀}^σ (σ - r) A r dr = σ ∫_{t₀}^σ A r dr - ∫_{t₀}^σ r A r dr`.
  have hsplit (σ : ℝ) (hσ : σ ∈ Icc a b) : ∫ r in t₀..σ, (σ - r) • A r =
      σ • (∫ r in t₀..σ, A r) - ∫ r in t₀..σ, r • A r := by
    have h₁ : IntervalIntegrable (fun r ↦ σ • A r) volume t₀ σ :=
      (continuousOn_const.smul (hA.mono (uIcc_subset_Icc ht₀ hσ))).intervalIntegrable
    simp_rw [sub_smul]
    rw [_root_.intervalIntegral.integral_sub h₁
      (hrA.mono (uIcc_subset_Icc ht₀ hσ)).intervalIntegrable,
      _root_.intervalIntegral.integral_smul]
  have h := ((hasDerivWithinAt_id τ (Icc a b)).smul (hasDerivWithinAt_integral hA ht₀ hτ)).sub
    (hasDerivWithinAt_integral hrA ht₀ hτ)
  refine (h.congr hsplit (hsplit τ hτ)).congr_deriv ?_
  simp

end intervalIntegral

end TauCeti
