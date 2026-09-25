/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.Sampling.CutDistance
public import TauCeti.Combinatorics.DenseGraphLimits.Sampling.Infinite
public import TauCeti.Combinatorics.DenseGraphLimits.GraphonSpace.Basic
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Convergence in measure of graphon samples

The finite sampling laws of a graphon are the marginals of one infinite random graph. Applying the
finite-graph graphon construction to its growing windows gives a sequence of points in the
cut-distance quotient. The second sampling lemma says that this sequence converges in measure to
the original graphon's class. The joint-law formulation allows the same random graph to be used
at every window size.

## Main result

* `TauCeti.DenseGraphLimits.infiniteSampleLaw_tendstoInMeasure_cutDist` packages the second
  sampling lemma on the joint probability space.

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

/-- Under the joint sampling law, the graphon classes of the finite windows converge in measure
to the class of the generating graphon. The window has `n + 1` vertices, so the construction also
covers the first term without a nonempty-carrier convention. -/
theorem infiniteSampleLaw_tendstoInMeasure_cutDist
    (W : Graphon I (volume : Measure I)) :
    TendstoInMeasure (infiniteSampleLaw W)
      (fun n G => (SeparationQuotient.mk
        (finiteGraphGraphon (SimpleGraph.restrictFin G (n + 1))) : GraphonSpaceI))
      atTop (fun _ => (SeparationQuotient.mk W : GraphonSpaceI)) := by
  rw [tendstoInMeasure_iff_measureReal_dist]
  intro ε hε
  have h := sampleGraph_cutDist_tendsto_inProbability W hε
  rw [← tendsto_add_atTop_iff_nat 1] at h
  have heq :
      (fun n => (infiniteSampleLaw W).real
        {G | ε ≤ dist (SeparationQuotient.mk
          (finiteGraphGraphon (SimpleGraph.restrictFin G (n + 1))))
          (SeparationQuotient.mk W)}) =
      (fun n => (sampleGraph W (n + 1)).real
        {G | ε ≤ cutDist (finiteGraphGraphon G) W}) := by
    funext n
    rw [← infiniteSampleLaw_map_restrictFin W (n + 1),
      map_measureReal_apply (SimpleGraph.measurable_restrictFin (n + 1))
        MeasurableSet.of_discrete]
    simp only [dist_graphonSpace_mk_mk]
    rfl
  exact heq ▸ h

end DenseGraphLimits

end TauCeti
