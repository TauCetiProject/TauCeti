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
Wasserstein space: this identification requires the anchor itself to have finite moment. This file
proves the exact criterion and, under it, identifies `TauCeti.WassersteinSpace p X` with
`TauCeti.WassersteinComponent p μ₀` without changing the underlying probability measure.

The identification is measurable because both carriers inherit their measurable structures from
`ProbabilityMeasure`. When the ground distance is Borel measurable and `1 ≤ p`, it is also an
isometric equivalence for the Wasserstein pseudometrics. These results let an argument choose a
convenient finite-moment reference law without changing the carrier on which it works.

## Main statements

* `TauCeti.hasFiniteMoment_iff_wassersteinEDist_ne_top_of_hasFiniteMoment` — a law lies at finite
  Wasserstein distance from a finite-moment anchor exactly when it has finite moment;
* `TauCeti.WassersteinSpace.equivComponentOfFiniteMoment` — the resulting measurable equivalence
  between the finite-moment space and the anchored component;
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

section Criterion

variable [PseudoMetricSpace X] [StandardBorelSpace X]
  {μ₀ μ : Measure X} [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ]

/-- A probability measure has finite `p`-moment exactly when it lies at finite `p`-Wasserstein
distance from a finite-moment anchor.

The hypothesis on the anchor is necessary: an infinite-moment probability law always belongs to
its own finite-distance component, but it does not belong to `P_p(X)`. -/
theorem hasFiniteMoment_iff_wassersteinEDist_ne_top_of_hasFiniteMoment
    (hd : Measurable fun z : X × X ↦ edist z.1 z.2) (hp : 1 ≤ p)
    (hμ₀ : HasFiniteMoment p μ₀) :
    HasFiniteMoment p μ ↔ wassersteinEDist p μ₀ μ ≠ ∞ := by
  obtain ⟨x₀, hx₀⟩ := hasFiniteMoment_def.mp hμ₀
  have hdirac₀ : wassersteinEDist p (Measure.dirac x₀) μ₀ ≠ ∞ :=
    (memLp_edist_iff_wassersteinEDist_dirac_ne_top hd x₀ μ₀).mp hx₀
  constructor
  · intro hμ
    have hleft : wassersteinEDist p μ₀ (Measure.dirac x₀) ≠ ∞ := by
      rw [wassersteinEDist_comm hd]
      exact hdirac₀
    have hright : wassersteinEDist p (Measure.dirac x₀) μ ≠ ∞ :=
      (hasFiniteMoment_iff_wassersteinEDist_dirac_ne_top hd x₀ μ).mp hμ
    apply ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hleft, hright⟩)
    exact wassersteinEDist_triangle hd hp μ₀ (Measure.dirac x₀) μ
  · intro hμ
    apply (hasFiniteMoment_iff_wassersteinEDist_dirac_ne_top hd x₀ _).mpr
    apply ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hdirac₀, hμ⟩)
    exact wassersteinEDist_triangle hd hp (Measure.dirac x₀) μ₀ μ

end Criterion

namespace WassersteinSpace

section Equiv

variable [PseudoMetricSpace X] [StandardBorelSpace X]
  {μ₀ : ProbabilityMeasure X}

/-- A finite-moment anchor identifies the usual finite-moment Wasserstein space with its
finite-distance component. The equivalence leaves the underlying probability measure unchanged. -/
def equivComponentOfFiniteMoment
    (hd : Measurable fun z : X × X ↦ edist z.1 z.2) (hp : 1 ≤ p)
    (hμ₀ : HasFiniteMoment p (μ₀ : Measure X)) :
    WassersteinSpace p X ≃ WassersteinComponent p μ₀ where
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

@[simp]
theorem coe_equivComponentOfFiniteMoment
    (hd : Measurable fun z : X × X ↦ edist z.1 z.2) (hp : 1 ≤ p)
    (hμ₀ : HasFiniteMoment p (μ₀ : Measure X)) (μ : WassersteinSpace p X) :
    WassersteinComponent.toProbabilityMeasure
        (equivComponentOfFiniteMoment hd hp hμ₀ μ) =
      (μ : ProbabilityMeasure X) :=
  WassersteinComponent.coe_mk _ _

@[simp]
theorem coe_equivComponentOfFiniteMoment_symm
    (hd : Measurable fun z : X × X ↦ edist z.1 z.2) (hp : 1 ≤ p)
    (hμ₀ : HasFiniteMoment p (μ₀ : Measure X)) (μ : WassersteinComponent p μ₀) :
    toProbabilityMeasure ((equivComponentOfFiniteMoment hd hp hμ₀).symm μ) =
      WassersteinComponent.toProbabilityMeasure μ :=
  coe_mk _ _

/-- The finite-moment-anchor identification is measurable. -/
theorem measurable_equivComponentOfFiniteMoment
    (hd : Measurable fun z : X × X ↦ edist z.1 z.2) (hp : 1 ≤ p)
    (hμ₀ : HasFiniteMoment p (μ₀ : Measure X)) :
    Measurable (equivComponentOfFiniteMoment hd hp hμ₀) := by
  have heq : (equivComponentOfFiniteMoment hd hp hμ₀ :
      WassersteinSpace p X → WassersteinComponent p μ₀) =
      fun (μ : WassersteinSpace p X) ↦ WassersteinComponent.mk (μ : ProbabilityMeasure X)
        ((hasFiniteMoment_iff_wassersteinEDist_ne_top_of_hasFiniteMoment hd hp hμ₀).mp
          μ.hasFiniteMoment) := by
    funext μ
    exact WassersteinComponent.ext <| by
      rw [coe_equivComponentOfFiniteMoment, WassersteinComponent.coe_mk]
  rw [heq]
  exact WassersteinComponent.measurable_mk measurable_toProbabilityMeasure _

/-- The inverse finite-moment-anchor identification is measurable. -/
theorem measurable_equivComponentOfFiniteMoment_symm
    (hd : Measurable fun z : X × X ↦ edist z.1 z.2) (hp : 1 ≤ p)
    (hμ₀ : HasFiniteMoment p (μ₀ : Measure X)) :
    Measurable (equivComponentOfFiniteMoment hd hp hμ₀).symm := by
  have heq : ((equivComponentOfFiniteMoment hd hp hμ₀).symm :
      WassersteinComponent p μ₀ → WassersteinSpace p X) =
      fun (μ : WassersteinComponent p μ₀) ↦ mk (μ : ProbabilityMeasure X)
        ((hasFiniteMoment_iff_wassersteinEDist_ne_top_of_hasFiniteMoment hd hp hμ₀).mpr
          μ.wassersteinEDist_anchor_ne_top) := by
    funext μ
    exact ext <| by
      rw [coe_equivComponentOfFiniteMoment_symm, coe_mk]
  rw [heq]
  exact measurable_mk WassersteinComponent.measurable_toProbabilityMeasure _

end Equiv

section Isometry

variable [PseudoMetricSpace X] [StandardBorelSpace X] [BorelSpace X]
  [SecondCountableTopology X] [Fact (1 ≤ p)] {μ₀ : ProbabilityMeasure X}

/-- The identification with a finite-moment anchored component preserves the Wasserstein extended
distance. -/
theorem edist_equivComponentOfFiniteMoment
    (hμ₀ : HasFiniteMoment p (μ₀ : Measure X)) (μ ν : WassersteinSpace p X) :
    edist (equivComponentOfFiniteMoment measurable_edist Fact.out hμ₀ μ)
        (equivComponentOfFiniteMoment measurable_edist Fact.out hμ₀ ν) =
      edist μ ν := by
  rw [WassersteinComponent.edist_def, edist_def,
    coe_equivComponentOfFiniteMoment, coe_equivComponentOfFiniteMoment]

/-- The identification with a finite-moment anchored component is an isometry. -/
theorem isometry_equivComponentOfFiniteMoment
    (hμ₀ : HasFiniteMoment p (μ₀ : Measure X)) :
    Isometry (equivComponentOfFiniteMoment measurable_edist Fact.out hμ₀) :=
  edist_equivComponentOfFiniteMoment hμ₀

/-- A finite-moment anchor gives an isometric equivalence from `P_p(X)` to its finite-distance
component. -/
def isometryEquivComponentOfFiniteMoment
    (hμ₀ : HasFiniteMoment p (μ₀ : Measure X)) :
    WassersteinSpace p X ≃ᵢ WassersteinComponent p μ₀ :=
  ⟨equivComponentOfFiniteMoment measurable_edist Fact.out hμ₀,
    isometry_equivComponentOfFiniteMoment hμ₀⟩

/-- The finite-moment-anchor identification preserves the real-valued Wasserstein distance. -/
theorem dist_equivComponentOfFiniteMoment
    (hμ₀ : HasFiniteMoment p (μ₀ : Measure X)) (μ ν : WassersteinSpace p X) :
    dist (equivComponentOfFiniteMoment measurable_edist Fact.out hμ₀ μ)
        (equivComponentOfFiniteMoment measurable_edist Fact.out hμ₀ ν) =
      dist μ ν :=
  (isometry_equivComponentOfFiniteMoment hμ₀).dist_eq μ ν

end Isometry

end WassersteinSpace

end TauCeti
