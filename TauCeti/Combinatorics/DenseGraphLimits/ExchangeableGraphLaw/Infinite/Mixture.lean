/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.ExchangeableGraphLaw.Infinite.Correspondence
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

## Main results

* `TauCeti.DenseGraphLimits.exchangeableGraphLawEquivInfinite_mixtureExchangeableLaw_law` — the
  extension of a graphon mixture over an arbitrary probability carrier is the integral of the
  joint sampling laws;
* `TauCeti.DenseGraphLimits.graphonMixtureLawEquiv_law` — the law attached to a mixing measure is
  the integral of the joint sampling laws against it;
* `TauCeti.DenseGraphLimits.InfiniteExchangeableGraphLaw.existsUnique_bind_infiniteSampleLawOnSpace`
  — every exchangeable law on infinite graphs is such an integral, for exactly one mixing measure.

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

end DenseGraphLimits

end TauCeti
