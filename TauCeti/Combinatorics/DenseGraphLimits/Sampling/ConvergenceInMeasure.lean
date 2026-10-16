/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.Sampling.CutDistance
public import TauCeti.Combinatorics.DenseGraphLimits.Sampling.Infinite
public import TauCeti.Combinatorics.DenseGraphLimits.GraphonSpace.UnitIntervalEmbedding
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Convergence in measure of graphon samples

The finite sampling laws of a graphon are the marginals of one infinite random graph. Applying the
finite-graph graphon construction to its growing windows gives a sequence of points in the
unit-interval cut-distance quotient `GraphonSpaceI`. The second sampling lemma says that this
sequence converges in measure to the original graphon's class. The generating graphon may live on
any probability carrier: its class is taken in `GraphonSpaceI` through the isometric embedding
`toGraphonSpaceI`. The joint-law formulation allows the same random graph to be used at every
window size.

## Main results

* `TauCeti.DenseGraphLimits.infiniteSampleLaw_tendstoInMeasure_toGraphonSpaceI` packages the
  second sampling lemma on the joint probability space, for a graphon on any probability carrier.
* `TauCeti.DenseGraphLimits.infiniteSampleLaw_tendstoInMeasure_cutDist` is its specialization to
  graphons on the unit interval.

## References

* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012),
  Lemma 10.16.
-/

public section

noncomputable section

open Filter MeasureTheory

open scoped Topology unitInterval

namespace TauCeti

namespace DenseGraphLimits

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Under the joint sampling law of a graphon `W` on any probability carrier, the graphon classes
of the finite windows converge in measure, in `GraphonSpaceI`, to the image of the class of `W`
under the isometric embedding `toGraphonSpaceI`. The window has `n + 1` vertices, so the
construction also covers the first term without a nonempty-carrier convention. -/
theorem infiniteSampleLaw_tendstoInMeasure_toGraphonSpaceI (W : Graphon Ω μ) :
    TendstoInMeasure (infiniteSampleLaw W)
      (fun n G => (SeparationQuotient.mk
        (finiteGraphGraphon (SimpleGraph.restrictFin G (n + 1))) : GraphonSpaceI))
      atTop (fun _ => toGraphonSpaceI (SeparationQuotient.mk W)) := by
  rw [tendstoInMeasure_iff_measureReal_dist]
  intro ε hε
  refine ((tendsto_add_atTop_iff_nat 1).2
    (sampleGraph_cutDist_tendsto_inProbability W hε)).congr fun n => ?_
  rw [← infiniteSampleLaw_map_restrictFin W (n + 1),
    map_measureReal_apply (SimpleGraph.measurable_restrictFin (n + 1))
      MeasurableSet.of_discrete]
  simp only [Set.preimage_ofPred_eq, toGraphonSpaceI_mk, dist_graphonSpace_mk_mk,
    Graphon.cutDist_unitIntervalRepr_right]

/-- Under the joint sampling law of a unit-interval graphon, the graphon classes of the finite
windows converge in measure to the class of the generating graphon. -/
theorem infiniteSampleLaw_tendstoInMeasure_cutDist
    (W : Graphon I (volume : Measure I)) :
    TendstoInMeasure (infiniteSampleLaw W)
      (fun n G => (SeparationQuotient.mk
        (finiteGraphGraphon (SimpleGraph.restrictFin G (n + 1))) : GraphonSpaceI))
      atTop (fun _ => (SeparationQuotient.mk W : GraphonSpaceI)) := by
  simpa only [toGraphonSpaceI_eq_self] using infiniteSampleLaw_tendstoInMeasure_toGraphonSpaceI W

end DenseGraphLimits

end TauCeti
