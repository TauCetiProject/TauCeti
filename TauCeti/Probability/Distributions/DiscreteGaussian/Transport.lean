/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.HasLaw
public import TauCeti.Probability.Distributions.DiscreteGaussian.Basic

/-!
# Transport of discrete Gaussian random variables

Integer translation and reflection preserve the discrete Gaussian family, shifting or negating
its real center. This file transfers the measure-level identities to random variables with a
discrete Gaussian law.

## References

* C. L. Canonne, G. Kamath and T. Steinke, *The Discrete Gaussian for Differential Privacy*,
  Advances in Cryptology -- EUROCRYPT 2020, 552--578.
-/

public section

noncomputable section

open MeasureTheory TauCeti.Probability

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℤ} {c s : ℝ}

/-- Translating an integer-valued random variable with discrete Gaussian law translates its
real center. -/
theorem HasLaw.add_const_discreteGaussianMeasure
    (hX : HasLaw X (discreteGaussianMeasure c s) P) (n : ℤ) :
    HasLaw (fun ω ↦ X ω + n) (discreteGaussianMeasure (c + n) s) P :=
  HasLaw.comp ⟨by fun_prop, map_add_const_discreteGaussianMeasure c s n⟩ hX

/-- Negating an integer-valued random variable with discrete Gaussian law negates its real
center. -/
theorem HasLaw.neg_discreteGaussianMeasure
    (hX : HasLaw X (discreteGaussianMeasure c s) P) :
    HasLaw (fun ω ↦ -X ω) (discreteGaussianMeasure (-c) s) P :=
  HasLaw.comp ⟨by fun_prop, map_neg_discreteGaussianMeasure c s⟩ hX

end ProbabilityTheory
