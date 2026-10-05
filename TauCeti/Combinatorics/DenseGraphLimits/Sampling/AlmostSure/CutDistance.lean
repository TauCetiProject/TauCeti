/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.Sampling.AlmostSure.Basic
public import TauCeti.Combinatorics.DenseGraphLimits.GraphonSpace.UnitIntervalEmbedding
import TauCeti.Combinatorics.DenseGraphLimits.GraphonSpace.Convergence

/-!
# Almost-sure convergence of sampled graphons

The growing finite windows of one infinite graph sampled from a graphon converge almost surely
to that graphon in cut distance. The generating graphon may have any probability carrier.
Equivalently, the windows converge in the metric quotient `GraphonSpaceI` to the image of the
graphon's class under the isometric embedding `toGraphonSpaceI`; for a graphon on the unit
interval, that image is its own class.

This is the simultaneous strong law for homomorphism densities, since convergence in cut distance
is convergence of all homomorphism densities (`tendsto_cutDist_iff_forall_homDensity_tendsto`).

## References

* L. Lovász, *Large Networks and Graph Limits* (2012), §10.1 and Theorem 11.5.
-/

public section

noncomputable section

open Filter MeasureTheory
open scoped Topology unitInterval

namespace TauCeti.DenseGraphLimits

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Almost every infinite `W`-random graph has finite windows converging to `W` in cut distance.
No standard-Borel or atomlessness assumption is needed on the generating probability space. -/
theorem infiniteSampleLaw_ae_tendsto_cutDist (W : Graphon Ω μ) :
    ∀ᵐ G ∂infiniteSampleLaw W,
      Tendsto (fun n => cutDist (finiteGraphGraphon (G.restrictFin n)) W) atTop (𝓝 0) := by
  filter_upwards [tendsto_homDensity_finiteGraphGraphon_infiniteSampleLaw_ae_forall W]
    with G hG
  rw [← tendsto_add_atTop_iff_nat 1]
  exact (tendsto_cutDist_iff_forall_homDensity_tendsto
    (fun n => finiteGraphGraphon (G.restrictFin (n + 1))) W).2 fun k F _ => hG k F

/-- The growing nonempty windows of almost every infinite `W`-random graph converge in
`GraphonSpaceI` to the image of the class of `W` under the isometric embedding
`toGraphonSpaceI`, for a graphon `W` on any probability carrier. -/
theorem infiniteSampleLaw_ae_tendsto_toGraphonSpaceI (W : Graphon Ω μ) :
    ∀ᵐ G ∂infiniteSampleLaw W,
      Tendsto (fun n => (SeparationQuotient.mk
        (finiteGraphGraphon (G.restrictFin (n + 1))) : GraphonSpaceI)) atTop
        (𝓝 (toGraphonSpaceI (SeparationQuotient.mk W))) := by
  filter_upwards [infiniteSampleLaw_ae_tendsto_cutDist W] with G hG
  rw [tendsto_iff_dist_tendsto_zero]
  simpa only [toGraphonSpaceI_mk, dist_graphonSpace_mk_mk,
    Graphon.cutDist_unitIntervalRepr_right] using (tendsto_add_atTop_iff_nat 1).2 hG

/-- On the unit interval, the growing nonempty sampled windows converge almost surely in
graphon space to the class of the generating graphon. -/
theorem infiniteSampleLaw_ae_tendsto_graphonSpace
    (W : Graphon I (volume : Measure I)) :
    ∀ᵐ G ∂infiniteSampleLaw W,
      Tendsto (fun n => (SeparationQuotient.mk
        (finiteGraphGraphon (G.restrictFin (n + 1))) : GraphonSpaceI)) atTop
        (𝓝 (SeparationQuotient.mk W)) := by
  simpa only [toGraphonSpaceI_eq_self] using infiniteSampleLaw_ae_tendsto_toGraphonSpaceI W

end TauCeti.DenseGraphLimits
