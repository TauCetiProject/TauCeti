/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.ExchangeableGraphLaw.Infinite.Correspondence
public import TauCeti.Combinatorics.DenseGraphLimits.GraphonSpace.Measurable
import TauCeti.MeasureTheory.Measure.GiryMonad

/-!
# Exchangeable laws on infinite graphs are integrals of joint sampling laws

A probability measure `P` on graphon space describes a two-stage infinite random graph: draw a
graphon class from `P`, then run the joint sampler of that class on all of `ℕ` at once. This file
identifies the two-stage law with the Giry-monad bind, so that the correspondence between mixing
measures and exchangeable laws on infinite graphs reads as a genuine mixture on `SimpleGraph ℕ`.

With the mixture identity in hand, every exchangeable law on infinite graphs is the integral of
joint sampling laws against one mixing measure on graphon space, and that mixing measure is
unique. This is the integral form of the Diaconis–Janson correspondence; its finite-window form
is `mixtureExchangeableLaw`.

A random graphon, given as a family of graphons over a probability space of parameters whose class
depends almost-everywhere measurably on the parameter, produces such a mixture directly: sample
the parameter, then run the joint sampler of the graphon it selects. The mixing measure of that
law is the law of the class of the random graphon, carried into the unit-interval graphon space
by `toGraphonSpaceI`; for graphons on the unit interval it is the law of the class itself. A
jointly measurable family of graphons has a measurable class (`measurable_graphonSpace_mk`).

## Main results

* `TauCeti.DenseGraphLimits.exchangeableGraphLawEquivInfinite_mixtureExchangeableLaw_law` — the
  extension of a graphon mixture over an arbitrary probability carrier is the integral of the
  joint sampling laws;
* `TauCeti.DenseGraphLimits.graphonMixtureLawEquiv_law` — the law attached to a mixing measure is
  the integral of the joint sampling laws against it;
* `TauCeti.DenseGraphLimits.InfiniteExchangeableGraphLaw.existsUnique_bind_infiniteSampleLawOnSpace`
  — every exchangeable law on infinite graphs is such an integral, for exactly one mixing measure;
* `TauCeti.DenseGraphLimits.bind_map_graphonSpace_mk_infiniteSampleLawOnSpace` — mixing over the
  class of a random graphon is mixing over its representatives;
* `TauCeti.DenseGraphLimits.graphonMixtureLawEquiv_symm_eq_map` — the mixing measure of a mixture
  of joint sampling laws over a random graphon is the law of the class of that random graphon in
  the unit-interval graphon space.

## References

* P. Diaconis, S. Janson, *Graph limits and exchangeable random graphs*, Rend. Mat. Appl. (7) 28
  (2008), 33--61, Theorem 5.3.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace DenseGraphLimits

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **A graphon mixture is an integral of joint sampling laws.** Extending the finite graphon
mixture over an arbitrary probability carrier gives the bind of its mixing measure against the
descended joint sampling law. -/
@[simp]
theorem exchangeableGraphLawEquivInfinite_mixtureExchangeableLaw_law
    (P : ProbabilityMeasure (GraphonSpace Ω μ)) :
    (exchangeableGraphLawEquivInfinite (mixtureExchangeableLaw P)).law =
      (P : Measure (GraphonSpace Ω μ)).bind infiniteSampleLawOnSpace := by
  refine measure_ext_of_map_restrictFin fun n => ?_
  rw [TauCeti.MeasureTheory.map_bind measurable_infiniteSampleLawOnSpace.aemeasurable
    (SimpleGraph.measurable_restrictFin n)]
  simp_rw [infiniteSampleLawOnSpace_map_restrictFin]
  rw [exchangeableGraphLawEquivInfinite_law_map_restrictFin, mixtureExchangeableLaw_law]

/-- **A graphon mixture is an integral of joint sampling laws.** The exchangeable law on infinite
graphs attached to a mixing measure `P` on graphon space is the bind of `P` against the descended
joint sampling law: draw a graphon class from `P`, then run the infinite sampler. -/
theorem graphonMixtureLawEquiv_law (P : ProbabilityMeasure GraphonSpaceI) :
    (graphonMixtureLawEquiv P).law =
      (P : Measure GraphonSpaceI).bind infiniteSampleLawOnSpace := by
  rw [graphonMixtureLawEquiv_apply,
    exchangeableGraphLawEquivInfinite_mixtureExchangeableLaw_law]

/-- **Every exchangeable law on infinite graphs is a graphon mixture, for exactly one mixing
measure.** The integral form of the Diaconis–Janson correspondence: the law is the bind of a
unique probability measure on graphon space against the joint sampling laws. -/
theorem InfiniteExchangeableGraphLaw.existsUnique_bind_infiniteSampleLawOnSpace
    (L : InfiniteExchangeableGraphLaw) :
    ∃! P : ProbabilityMeasure GraphonSpaceI,
      (P : Measure GraphonSpaceI).bind infiniteSampleLawOnSpace = L.law := by
  refine ⟨graphonMixtureLawEquiv.symm L, ?_, fun Q hQ => ?_⟩
  · have hP := graphonMixtureLawEquiv_law (graphonMixtureLawEquiv.symm L)
    rw [Equiv.apply_symm_apply] at hP
    exact hP.symm
  · refine graphonMixtureLawEquiv.injective ?_
    rw [Equiv.apply_symm_apply]
    exact InfiniteExchangeableGraphLaw.ext (by rw [graphonMixtureLawEquiv_law, hQ])

section RandomGraphon

variable {T : Type*} [MeasurableSpace T]

/-- **Mixing over a random graphon.** For a measure `ν` on parameters and a family of graphons `W`
whose class is `ν`-almost-everywhere measurable in the parameter, mixing the descended joint
sampling laws against the law of the class of `W t` is mixing the joint sampling laws of the
graphons `W t` against `ν`. -/
theorem bind_map_graphonSpace_mk_infiniteSampleLawOnSpace (ν : Measure T) {W : T → Graphon Ω μ}
    (hW : AEMeasurable (fun t => (SeparationQuotient.mk (W t) : GraphonSpace Ω μ)) ν) :
    (ν.map fun t => SeparationQuotient.mk (W t)).bind infiniteSampleLawOnSpace =
      ν.bind fun t => infiniteSampleLaw (W t) := by
  rw [TauCeti.MeasureTheory.bind_map hW measurable_infiniteSampleLawOnSpace.aemeasurable]
  simp only [Function.comp_def, infiniteSampleLawOnSpace_mk]

/-- **The mixing measure of a random graphon.** If an exchangeable law on infinite graphs is the
mixture, against a probability measure `ν`, of the joint sampling laws of a family `W` of graphons
whose class is `ν`-almost-everywhere measurable in the parameter, then the mixing measure the
Diaconis–Janson correspondence assigns to it is the law under `ν` of the class of `W t` in the
unit-interval graphon space. For graphons on the unit interval, `toGraphonSpaceI_eq_self` removes
the embedding. -/
theorem graphonMixtureLawEquiv_symm_eq_map (L : InfiniteExchangeableGraphLaw)
    (ν : ProbabilityMeasure T) {W : T → Graphon Ω μ}
    (hW : AEMeasurable (fun t => (SeparationQuotient.mk (W t) : GraphonSpace Ω μ)) ν)
    (hL : L.law = (ν : Measure T).bind fun t => infiniteSampleLaw (W t)) :
    graphonMixtureLawEquiv.symm L =
      ν.map fun t => toGraphonSpaceI (SeparationQuotient.mk (W t)) := by
  rw [Equiv.symm_apply_eq]
  refine InfiniteExchangeableGraphLaw.ext ?_
  simp only [toGraphonSpaceI_mk]
  rw [hL, graphonMixtureLawEquiv_law, ProbabilityMeasure.toMeasure_map,
    bind_map_graphonSpace_mk_infiniteSampleLawOnSpace _
      (by simpa only [Function.comp_def, toGraphonSpaceI_mk] using
        isometry_toGraphonSpaceI.continuous.measurable.comp_aemeasurable hW)]
  congr 1
  funext t
  exact infiniteSampleLaw_eq_of_cutDist_eq_zero _ _ (Graphon.cutDist_unitIntervalRepr _)

end RandomGraphon

end DenseGraphLimits

end TauCeti
