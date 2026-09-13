/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import TauCeti.Probability.Distributions.Gamma.Basic

/-!
# Finite products of Gamma distributions

This file records the almost-sure positivity inherited by finite products of Gamma measures.
The coordinatewise result holds for arbitrary shape and rate vectors because
`ae_pos_gammaMeasure` is parameter-independent, and every Gamma measure is sigma-finite.  For a
nonempty index type, coordinatewise positivity makes the coordinate sum positive.

These facts supply the null-denominator statement for the normalized-Gamma construction of the
Dirichlet distribution.

## Main results

* `TauCeti.ae_pos_pi_gammaMeasure` gives coordinatewise positivity in a finite Gamma product.
* `TauCeti.ae_pos_sum_pi_gammaMeasure` gives positivity of the coordinate sum for a nonempty
  finite Gamma product.
-/

public section

open MeasureTheory ProbabilityTheory

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- Every coordinate in a finite product of Gamma measures is almost everywhere strictly
positive. -/
theorem ae_pos_pi_gammaMeasure (a r : ι → ℝ) :
    ∀ᵐ x ∂Measure.pi (fun i ↦ gammaMeasure (a i) (r i)), ∀ i, 0 < x i := by
  exact ae_all_iff.mpr fun i ↦
    Measure.tendsto_eval_ae_ae.eventually (ae_pos_gammaMeasure (a i) (r i))

/-- The coordinate sum in a nonempty finite product of Gamma measures is almost everywhere
strictly positive. -/
theorem ae_pos_sum_pi_gammaMeasure [Nonempty ι] (a r : ι → ℝ) :
    ∀ᵐ x ∂Measure.pi (fun i ↦ gammaMeasure (a i) (r i)), 0 < ∑ i, x i := by
  filter_upwards [ae_pos_pi_gammaMeasure a r] with x hx
  exact Finset.sum_pos (fun i _ ↦ hx i) Finset.univ_nonempty

end TauCeti
