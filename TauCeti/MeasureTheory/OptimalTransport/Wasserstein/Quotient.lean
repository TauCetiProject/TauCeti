/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Basic

/-!
# Wasserstein separation on pseudometric spaces

On a pseudometric ground space, zero Wasserstein distance identifies probability laws only after
the ground space itself is separated. This file expresses that statement using Mathlib's
`SeparationQuotient`: for a complete second-countable pseudometric space carrying its Borel
sigma-algebra, `W_p μ ν = 0` if and only if the pushforwards of `μ` and `ν` to the separation
quotient agree.

The reverse implication uses a feature of the Borel measurable structure of a pseudometric space:
every open set is saturated under zero distance. Since open sets generate the Borel sigma-algebra,
pushforward along `SeparationQuotient.mk` is injective on finite Borel measures. The forward
implication contracts Wasserstein distance along the quotient map and applies metric separation on
the complete separable metric quotient.

This completes the pseudometric-base separation requirement in Layer 3, item 1 of the optimal
transport roadmap.

## Main statements

* `MeasureTheory.Measure.separationQuotient` is pushforward along Mathlib's separation-quotient map,
  carrying the quotient's Borel measurable structure.
* `MeasureTheory.Measure.separationQuotient_eq_iff` says that two finite Borel measures on a
  pseudometric space have the same quotient pushforward exactly when they agree.
* `TauCeti.wassersteinEDist_eq_zero_iff_map_separationQuotient_mk` characterizes zero Wasserstein
  distance by equality after pushforward to the metric separation quotient, for every nonzero
  exponent, including `p = ∞`.
* `TauCeti.wassersteinEDist_dirac_eq_zero_of_dist_eq_zero` records the pseudometric
  regression case of two zero-distance points.

## References

* C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, Springer 2009, Chapter 6.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

universe u

namespace MeasureTheory.Measure

variable {X : Type u} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The pushforward of a measure to the metric separation quotient, carrying the quotient's
Borel measurable structure. -/
noncomputable def separationQuotient (μ : Measure X) :
    @Measure (SeparationQuotient X) (borel (SeparationQuotient X)) :=
  @Measure.map X (SeparationQuotient X) _ (borel (SeparationQuotient X))
    SeparationQuotient.mk μ

/-- Pushforward to the metric separation quotient is injective on finite Borel measures on a
pseudometric space. Equivalently, such measures agree exactly when their quotient laws agree.

Every open set in `X` is saturated under the zero-distance relation, so it is the preimage of its
open image in `SeparationQuotient X`. Equality of the pushforwards therefore gives equality on
open sets, which determine finite Borel measures. -/
theorem separationQuotient_eq_iff (μ ν : Measure X) [IsFiniteMeasure μ] :
    separationQuotient μ = separationQuotient ν ↔ μ = ν := by
  let _ : MeasurableSpace (SeparationQuotient X) := borel (SeparationQuotient X)
  let _ : BorelSpace (SeparationQuotient X) := ⟨rfl⟩
  have hmk : Measurable (SeparationQuotient.mk : X → SeparationQuotient X) :=
    SeparationQuotient.continuous_mk.measurable
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h]⟩
  change μ.map SeparationQuotient.mk = ν.map SeparationQuotient.mk at h
  apply ext_of_generate_finite {s : Set X | IsOpen s}
    BorelSpace.measurable_eq isPiSystem_isOpen
  · intro s hs
    have hqs : MeasurableSet (SeparationQuotient.mk '' s) :=
      (SeparationQuotient.isOpenMap_mk s hs).measurableSet
    have heval := congrArg (fun m : Measure (SeparationQuotient X) ↦
      m (SeparationQuotient.mk '' s)) h
    simpa only [Measure.map_apply hmk hqs, SeparationQuotient.preimage_image_mk_open hs] using heval
  · have heval := congrArg (fun m : Measure (SeparationQuotient X) ↦ m univ) h
    simpa only [Measure.map_apply_of_aemeasurable hmk.aemeasurable MeasurableSet.univ,
      preimage_univ] using heval

/-- Dirac measures at zero-distance points of a Borel pseudometric space agree. This does not
require measurable singletons: every Borel set is saturated under the zero-distance relation. -/
theorem dirac_eq_dirac_of_dist_eq_zero {x y : X} (hxy : dist x y = 0) :
    Measure.dirac x = Measure.dirac y := by
  classical
  apply ext_of_generate_finite {s : Set X | IsOpen s}
    BorelSpace.measurable_eq isPiSystem_isOpen
  · intro s hs
    rw [Measure.dirac_apply' _ hs.measurableSet, Measure.dirac_apply' _ hs.measurableSet]
    exact if_congr ((Metric.inseparable_iff.2 hxy).mem_open_iff hs) rfl rfl
  · simp

end MeasureTheory.Measure

namespace TauCeti

variable {X : Type u} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] {p : ℝ≥0∞}

omit [BorelSpace X] [SecondCountableTopology X] in
/-- Wasserstein distance from a measure to itself vanishes when the ground extended distance is
measurable. Unlike `TauCeti.wassersteinEDist_self`, this form does not require a measurable
diagonal, which need not exist on a non-separated pseudometric Borel space. -/
theorem wassersteinEDist_self_of_measurable_edist
    (hd : Measurable fun z : X × X ↦ edist z.1 z.2) (p : ℝ≥0∞) (μ : Measure X) :
    wassersteinEDist p μ μ = 0 := by
  apply nonpos_iff_eq_zero.mp
  refine (wassersteinEDist_le (isCoupling_graphPlan_id μ) p).trans_eq ?_
  have hgraph : AEMeasurable (fun x : X ↦ (x, id x)) μ := by fun_prop
  calc
    eLpNorm (fun z : X × X ↦ edist z.1 z.2) p (graphPlan id μ) =
        eLpNorm ((fun z : X × X ↦ edist z.1 z.2) ∘ fun x : X ↦ (x, id x)) p μ := by
      rw [graphPlan_def]
      exact eLpNorm_map_measure hd.aestronglyMeasurable hgraph
    _ = 0 := eLpNorm_eq_zero_of_ae_zero (.of_forall fun z ↦ by simp)

/-- **Separation on a pseudometric base.** For every nonzero exponent, Wasserstein distance
vanishes exactly when the two laws have equal pushforwards to the metric separation quotient.
The statement includes the essential-supremum endpoint `p = ∞`. -/
theorem wassersteinEDist_eq_zero_iff_map_separationQuotient_mk (hp : p ≠ 0)
    (μ ν : Measure X) [CompleteSpace X] [IsFiniteMeasure μ] :
    wassersteinEDist p μ ν = 0 ↔
      Measure.separationQuotient μ = Measure.separationQuotient ν := by
  let _ : TopologicalSpace.SeparableSpace (SeparationQuotient X) :=
    SeparationQuotient.surjective_mk.denseRange.separableSpace
      SeparationQuotient.continuous_mk
  let _ : SecondCountableTopology (SeparationQuotient X) :=
    UniformSpace.secondCountable_of_separable (SeparationQuotient X)
  let _ : MeasurableSpace (SeparationQuotient X) := borel (SeparationQuotient X)
  let _ : BorelSpace (SeparationQuotient X) := ⟨rfl⟩
  have hmk : Measurable (SeparationQuotient.mk : X → SeparationQuotient X) :=
    SeparationQuotient.continuous_mk.measurable
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · change μ.map SeparationQuotient.mk = ν.map SeparationQuotient.mk
    have hmap : wassersteinEDist p (μ.map SeparationQuotient.mk)
        (ν.map SeparationQuotient.mk) = 0 := by
      apply nonpos_iff_eq_zero.mp
      refine (le_wassersteinEDist fun π hπ ↦ ?_).trans_eq h
      calc
        wassersteinEDist p (μ.map SeparationQuotient.mk) (ν.map SeparationQuotient.mk)
            ≤ eLpNorm (fun z : SeparationQuotient X × SeparationQuotient X ↦
                edist z.1 z.2) p (π.map (Prod.map SeparationQuotient.mk SeparationQuotient.mk)) :=
          wassersteinEDist_le (hπ.map hmk hmk) p
        _ = eLpNorm (fun z : X × X ↦ edist z.1 z.2) p π := by
          rw [eLpNorm_map_measure measurable_edist.aestronglyMeasurable
            (hmk.prodMap hmk).aemeasurable]
          exact eLpNorm_congr_ae (.of_forall fun z ↦ SeparationQuotient.edist_mk z.1 z.2)
    exact eq_of_wassersteinEDist_eq_zero hp _ _ hmap
  · have hμν : μ = ν := (Measure.separationQuotient_eq_iff μ ν).1 h
    subst ν
    exact wassersteinEDist_self_of_measurable_edist measurable_edist p μ

/-- **Pseudometric regression.** Dirac laws at two zero-distance points have zero Wasserstein
distance for every exponent, even when the points are not equal. -/
theorem wassersteinEDist_dirac_eq_zero_of_dist_eq_zero {x y : X} (hxy : dist x y = 0) :
    wassersteinEDist p (Measure.dirac x) (Measure.dirac y) = 0 := by
  rw [Measure.dirac_eq_dirac_of_dist_eq_zero hxy]
  exact wassersteinEDist_self_of_measurable_edist measurable_edist p (Measure.dirac y)

end TauCeti
