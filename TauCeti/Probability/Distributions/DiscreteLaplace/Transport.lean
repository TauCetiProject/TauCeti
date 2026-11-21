/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.HasLaw
public import TauCeti.Probability.Distributions.DiscreteLaplace.Basic

/-!
# Transport of discrete Laplace random variables

Integer translation and reflection preserve the discrete Laplace family, shifting or negating
its integer center. This file transfers the measure-level identities to random variables with a
discrete Laplace law.

## References

* S. Inusah and T. J. Kozubowski, *A discrete analogue of the Laplace distribution*, Journal of
  Statistical Planning and Inference 136 (2006), 1090--1102.
-/

public section

noncomputable section

open MeasureTheory TauCeti.Probability

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℤ} {m : ℤ} {q : ℝ}

/-- Translating an integer-valued random variable with discrete Laplace law translates its
center. -/
theorem HasLaw.add_const_discreteLaplaceMeasure
    (hX : HasLaw X (discreteLaplaceMeasure m q) P) (n : ℤ) :
    HasLaw (fun ω ↦ X ω + n) (discreteLaplaceMeasure (m + n) q) P :=
  HasLaw.comp ⟨by fun_prop, map_add_const_discreteLaplaceMeasure m n q⟩ hX

/-- Negating an integer-valued random variable with discrete Laplace law negates its center. -/
theorem HasLaw.neg_discreteLaplaceMeasure
    (hX : HasLaw X (discreteLaplaceMeasure m q) P) :
    HasLaw (fun ω ↦ -X ω) (discreteLaplaceMeasure (-m) q) P :=
  HasLaw.comp ⟨by fun_prop, map_neg_discreteLaplaceMeasure m q⟩ hX

end ProbabilityTheory
