/-
Copyright (c) 2026 Vincent Quenneville-Belair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Quenneville-Belair
-/
module

public import TauCeti.Probability.Distributions.Bernoulli.CondVar

/-!
# Conditional moments for certificate-success indicators

The conditional-mean formulation makes the Bernoulli conditional variance
API directly usable for a success indicator conditioned on a trial history.
-/

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory unitInterval

@[expose] public section

namespace TauCeti

/-- A Bernoulli variable's conditional variance is `q_history * (1 - q_history)`. -/
theorem condVar_eq_condMean_mul_one_sub
    {Ω : Type*} {m m₀ : MeasurableSpace Ω} (hm : m ≤ m₀)
    {P : Measure[m₀] Ω} {X : Ω → ℝ} {p : I}
    (hX : HasLaw X Ber(1, 0, p) P) :
    Var[X; P | m] =ᵐ[P] P[X | m] * (1 - P[X | m]) := by
  have := hX.isProbabilityMeasure
  have hXi : Integrable X P :=
    hX.integrable (ProbabilityTheory.integrable_bernoulliMeasure 1 0 p id)
  have hcomp : P[1 - X | m] =ᵐ[P] 1 - P[X | m] := by
    simpa only [Pi.one_def, condExp_const hm] using
      condExp_sub (integrable_const (1 : ℝ)) hXi m
  exact (ProbabilityTheory.condVar_of_hasLaw_bernoulliMeasure hm hX).trans
    (ae_eq_rfl.mul hcomp)


end TauCeti
