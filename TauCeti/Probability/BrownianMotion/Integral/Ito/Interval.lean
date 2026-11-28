/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Ito.Stopping
public import TauCeti.Probability.BrownianMotion.Integral.Ito.Substitution
import TauCeti.Probability.Process.Stopping

/-!
# Interval multiplier rules for continuous Brownian Itô integrals

Combining optional stopping (`TauCeti.Probability.BrownianMotion.Integral.Ito.Stopping`) and
simple-integrand substitution (`TauCeti.Probability.BrownianMotion.Integral.Ito.Substitution`),
this module provides the left-measurable multiplier rule directly for Itô integrals of `(s, t]`
cutoff integrands.

## Main results

* `TauCeti.Probability.IsItoIntegral.mul_ite_Ioc`: for `s ≤ t` and an `ℱ s`-measurable
  multiplier `ξ`, if `J` is an Itô integral of `1_{(s, t]} · H`, then `ξ · J` is an Itô
  integral of `1_{(s, t]} · ξ · H`, without assuming path continuity of `W` or boundedness of
  `ξ`.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.D.
* D. Revuz and M. Yor, *Continuous Martingales and Brownian Motion*, third edition,
  Springer, 1999, Chapter IV, §2.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped NNReal

namespace TauCeti.Probability.IsItoIntegral

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {W H J : ℝ≥0 → Ω → ℝ}

/-- **Left-measurable multiplier rule for local interval integrals** stated directly for any
Itô integral `J` of the `(s, t]` cutoff `1_{(s, t]} · H`, without assuming path continuity of
`W` or boundedness of `ξ`. -/
theorem mul_ite_Ioc
    (hW : IsFilteredPreBrownianReal ℱ W P)
    {s t : ℝ≥0} (hst : s ≤ t)
    (hJ : IsItoIntegral ℱ P W (fun u ω ↦ if s < u ∧ u ≤ t then H u ω else 0) J)
    {ξ : Ω → ℝ} (hξ : StronglyMeasurable[ℱ s] ξ) :
    IsItoIntegral ℱ P W (fun u ω ↦ if s < u ∧ u ≤ t then ξ ω * H u ω else 0)
      (fun u ω ↦ ξ ω * J u ω) := by
  have hJs : MeasureTheory.stoppedProcess J (fun _ ↦ (s : WithTop ℝ≥0)) ≡ᵐ[P] 0 := by
    have hstop := hJ.stoppedProcess hW (isStoppingTime_const ℱ s)
    have hzero : (fun (u : ℝ≥0) ω ↦ if (u : WithTop ℝ≥0) ≤ s then
        (if s < u ∧ u ≤ t then H u ω else 0) else 0) = 0 := by
      ext u ω
      split_ifs with h1 h2
      · exact absurd (WithTop.coe_le_coe.mp h1) h2.1.not_ge
      all_goals simp only [Pi.zero_apply]
    rw [hzero] at hstop
    exact isItoIntegral_unique hW hstop (IsItoIntegral.zero)
  have hJt : MeasureTheory.stoppedProcess J (fun _ ↦ (t : WithTop ℝ≥0)) ≡ᵐ[P] J := by
    have hstop := hJ.stoppedProcess hW (isStoppingTime_const ℱ t)
    have hid : (fun (u : ℝ≥0) ω ↦ if (u : WithTop ℝ≥0) ≤ t then
        (if s < u ∧ u ≤ t then H u ω else 0) else 0) =
        fun (u : ℝ≥0) ω ↦ if s < u ∧ u ≤ t then H u ω else 0 := by
      ext u ω
      by_cases h : s < u ∧ u ≤ t
      · simp only [h, (by exact_mod_cast h.2 : (u : WithTop ℝ≥0) ≤ t), ↓reduceIte]
      · simp only [h, ↓reduceIte, ite_self]
    rw [hid] at hstop
    exact isItoIntegral_unique hW hstop hJ
  have hmul := hJ.mul_sub_min hW hst hξ
  have hK : (fun (u : ℝ≥0) ω ↦ (Set.Ioc s t).indicator (fun _ ↦ ξ ω) u *
      (if s < u ∧ u ≤ t then H u ω else 0)) =
      fun (u : ℝ≥0) ω ↦ if s < u ∧ u ≤ t then ξ ω * H u ω else 0 := by
    ext u ω
    by_cases h : s < u ∧ u ≤ t <;> simp [h]
  rw [hK] at hmul
  refine hmul.congr ?_
  filter_upwards [hJs, hJt] with ω hsω htω u
  have hJu : J (min t u) ω = J u ω := by
    simpa only [MeasureTheory.stoppedProcess_const_time, min_comm] using htω u
  have hJs0 : J (min s u) ω = 0 := by
    simpa only [MeasureTheory.stoppedProcess_const_time, Pi.zero_apply, min_comm] using hsω u
  rw [hJu, hJs0, sub_zero]

end TauCeti.Probability.IsItoIntegral
