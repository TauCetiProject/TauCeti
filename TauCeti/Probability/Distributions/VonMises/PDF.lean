/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.VonMises.Basic
public import TauCeti.Probability.Density

/-!
# Probability densities of von Mises random angles

A circle-valued random variable with law `vonMisesMeasure m κ` has a density relative to
`AddCircle.haarAddCircle`. At nonnegative concentration its canonical `pdf` agrees almost
everywhere with `vonMisesPDF m κ`, including the Haar-uniform boundary at concentration zero.
These interfaces use the circle's Haar probability measure, not real-line volume or a choice
of angle representative.

The `HasPDF` conclusion also holds at negative concentration, where the totalized law is zero.
The identification with `vonMisesPDF` requires nonnegative concentration: that named density
is positive even at negative concentrations, whereas the totalized measure is zero there.
No probability assumption on the source measure is needed.

## References

* K. V. Mardia, P. E. Jupp, *Directional Statistics*, Wiley (2000), section 3.5.4.
-/

public section

open MeasureTheory ProbabilityTheory Real AddCircle

namespace ProbabilityTheory

open TauCeti.Probability

local instance factTwoPiPos : Fact (0 < 2 * π) := ⟨two_pi_pos⟩

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X : Ω → AddCircle (2 * π)} {m : AddCircle (2 * π)} {κ : ℝ}

/-- A von Mises random angle has a density relative to Haar probability measure, including
at zero concentration and for the zero law at negative concentration. -/
theorem HasLaw.hasPDF_vonMisesMeasure (hX : HasLaw X (vonMisesMeasure m κ) P) :
    HasPDF X P haarAddCircle := by
  by_cases hκ : 0 ≤ κ
  · exact hasPDF_of_hasLaw_withDensity (measurable_vonMisesPDF m κ).aemeasurable
      (by rwa [vonMisesMeasure_of_nonneg hκ] at hX)
  · apply hasPDF_of_hasLaw_withDensity (f := fun _ ↦ 0) aemeasurable_const
    simpa [vonMisesMeasure_of_neg (not_le.mp hκ)] using hX

/-- At nonnegative concentration, the canonical Haar density of a von Mises random angle is
`vonMisesPDF`, also at the Haar-uniform boundary `κ = 0`. -/
theorem HasLaw.pdf_eq_vonMisesPDF (hX : HasLaw X (vonMisesMeasure m κ) P) (hκ : 0 ≤ κ) :
    pdf X P haarAddCircle =ᵐ[haarAddCircle] vonMisesPDF m κ :=
  pdf_eq_of_hasLaw_withDensity (measurable_vonMisesPDF m κ).aemeasurable
    (by rwa [vonMisesMeasure_of_nonneg hκ] at hX)

end ProbabilityTheory
