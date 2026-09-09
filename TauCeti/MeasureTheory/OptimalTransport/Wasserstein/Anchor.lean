/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Space

/-!
# Finite-moment anchors for Wasserstein components

An anchored finite-distance component of probability measures need not be the usual finite-moment
Wasserstein space: this identification requires the anchor itself to have finite moment, and
`TauCeti.hasFiniteMoment_iff_forall_hasFiniteMoment_iff_wassersteinEDist_ne_top` shows that this
hypothesis is exactly the right one. Under it, this file identifies `TauCeti.WassersteinSpace p X`
with `TauCeti.WassersteinComponent p μ₀` without changing the underlying probability measure.

The identification is measurable in both directions, because both carriers inherit their
measurable structures from `ProbabilityMeasure`, so it is packaged as a `MeasurableEquiv`. When
the ground distance is Borel measurable and `1 ≤ p`, it is also an isometric equivalence for the
Wasserstein pseudometrics. These results let an argument choose a convenient finite-moment
reference law without changing the carrier on which it works.

## Main statements

* `TauCeti.WassersteinSpace.measurableEquivComponentOfFiniteMoment` — the measurable equivalence
  between the finite-moment space and the component anchored at a finite-moment law;
* `TauCeti.WassersteinSpace.isometryEquivComponentOfFiniteMoment` — its isometric form.

## References

* C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, Springer 2009, Chapter 6.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace TauCeti

universe u

variable {X : Type u} [MeasurableSpace X] {p : ℝ≥0∞}

namespace WassersteinSpace

section Equiv

variable [PseudoMetricSpace X] [StandardBorelSpace X]
  {μ₀ : ProbabilityMeasure X}

/-- A finite-moment anchor identifies the usual finite-moment Wasserstein space with its
finite-distance component. The equivalence leaves the underlying probability measure unchanged,
hence is measurable in both directions: both carriers inherit the measurable structure of
`ProbabilityMeasure`. -/
def measurableEquivComponentOfFiniteMoment
    (hd : Measurable fun z : X × X ↦ edist z.1 z.2) (hp : 1 ≤ p)
    (hμ₀ : HasFiniteMoment p (μ₀ : Measure X)) :
    WassersteinSpace p X ≃ᵐ WassersteinComponent p μ₀ where
  toFun μ := WassersteinComponent.mk (μ : ProbabilityMeasure X)
    ((hasFiniteMoment_iff_wassersteinEDist_ne_top_of_hasFiniteMoment hd hp hμ₀).mp
      μ.hasFiniteMoment)
  invFun μ := mk (μ : ProbabilityMeasure X)
    ((hasFiniteMoment_iff_wassersteinEDist_ne_top_of_hasFiniteMoment hd hp hμ₀).mpr
      μ.wassersteinEDist_anchor_ne_top)
  left_inv μ := ext <| by
    rw [coe_mk]
    exact WassersteinComponent.coe_mk _ _
  right_inv μ := WassersteinComponent.ext <| by
    rw [WassersteinComponent.coe_mk]
    exact coe_mk _ _
  measurable_toFun := WassersteinComponent.measurable_mk measurable_toProbabilityMeasure _
  measurable_invFun := measurable_mk WassersteinComponent.measurable_toProbabilityMeasure _

@[simp]
theorem coe_measurableEquivComponentOfFiniteMoment
    (hd : Measurable fun z : X × X ↦ edist z.1 z.2) (hp : 1 ≤ p)
    (hμ₀ : HasFiniteMoment p (μ₀ : Measure X)) (μ : WassersteinSpace p X) :
    WassersteinComponent.toProbabilityMeasure
        (measurableEquivComponentOfFiniteMoment hd hp hμ₀ μ) =
      (μ : ProbabilityMeasure X) :=
  WassersteinComponent.coe_mk _ _

@[simp]
theorem coe_measurableEquivComponentOfFiniteMoment_symm
    (hd : Measurable fun z : X × X ↦ edist z.1 z.2) (hp : 1 ≤ p)
    (hμ₀ : HasFiniteMoment p (μ₀ : Measure X)) (μ : WassersteinComponent p μ₀) :
    toProbabilityMeasure ((measurableEquivComponentOfFiniteMoment hd hp hμ₀).symm μ) =
      WassersteinComponent.toProbabilityMeasure μ :=
  coe_mk _ _

end Equiv

section Isometry

variable [PseudoMetricSpace X] [StandardBorelSpace X] [BorelSpace X]
  [SecondCountableTopology X] [Fact (1 ≤ p)] {μ₀ : ProbabilityMeasure X}

/-- The identification with a finite-moment anchored component preserves the Wasserstein extended
distance. -/
theorem edist_measurableEquivComponentOfFiniteMoment
    (hμ₀ : HasFiniteMoment p (μ₀ : Measure X)) (μ ν : WassersteinSpace p X) :
    edist (measurableEquivComponentOfFiniteMoment measurable_edist Fact.out hμ₀ μ)
        (measurableEquivComponentOfFiniteMoment measurable_edist Fact.out hμ₀ ν) =
      edist μ ν := by
  rw [WassersteinComponent.edist_def, edist_def,
    coe_measurableEquivComponentOfFiniteMoment, coe_measurableEquivComponentOfFiniteMoment]

/-- The identification with a finite-moment anchored component is an isometry. -/
theorem isometry_measurableEquivComponentOfFiniteMoment
    (hμ₀ : HasFiniteMoment p (μ₀ : Measure X)) :
    Isometry (measurableEquivComponentOfFiniteMoment measurable_edist Fact.out hμ₀) :=
  edist_measurableEquivComponentOfFiniteMoment hμ₀

/-- A finite-moment anchor gives an isometric equivalence from `P_p(X)` to its finite-distance
component. -/
def isometryEquivComponentOfFiniteMoment
    (hμ₀ : HasFiniteMoment p (μ₀ : Measure X)) :
    WassersteinSpace p X ≃ᵢ WassersteinComponent p μ₀ :=
  ⟨(measurableEquivComponentOfFiniteMoment measurable_edist Fact.out hμ₀).toEquiv,
    isometry_measurableEquivComponentOfFiniteMoment hμ₀⟩

/-- The finite-moment-anchor identification preserves the real-valued Wasserstein distance. -/
theorem dist_measurableEquivComponentOfFiniteMoment
    (hμ₀ : HasFiniteMoment p (μ₀ : Measure X)) (μ ν : WassersteinSpace p X) :
    dist (measurableEquivComponentOfFiniteMoment measurable_edist Fact.out hμ₀ μ)
        (measurableEquivComponentOfFiniteMoment measurable_edist Fact.out hμ₀ ν) =
      dist μ ν :=
  (isometry_measurableEquivComponentOfFiniteMoment hμ₀).dist_eq μ ν

end Isometry

end WassersteinSpace

end TauCeti
