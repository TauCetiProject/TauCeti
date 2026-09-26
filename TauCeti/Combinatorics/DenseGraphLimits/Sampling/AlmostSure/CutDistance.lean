/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.Sampling.AlmostSure.Basic
public import TauCeti.Combinatorics.DenseGraphLimits.GraphonSpace.Basic
import TauCeti.Combinatorics.DenseGraphLimits.GraphonSpace.Convergence

/-!
# Almost-sure convergence of sampled graphons

The growing finite windows of one infinite graph sampled from a graphon converge almost surely
to that graphon in cut distance. The generating graphon may have any probability carrier.
For a graphon on the unit interval, this is convergence in the metric quotient `GraphonSpaceI`.

On the unit interval this is the simultaneous strong law for homomorphism densities, since
convergence in `GraphonSpaceI` is convergence of all homomorphism densities
(`tendsto_graphonSpace_iff_forall_homDensity`). A unit-interval representative transfers the result
to arbitrary carriers.

## References

* L. Lovász, *Large Networks and Graph Limits* (2012), §10.1 and Theorem 11.5.
* S. Janson, *Graphons, cut norm and distance, couplings and rearrangements* (2013),
  Theorem 7.1 (representation on the unit interval).
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
  obtain ⟨V, hWV⟩ := exists_graphon_unitInterval_cutDist_eq_zero W
  have hden := forall_homDensity_eq_of_cutDist_eq_zero W V hWV
  filter_upwards [tendsto_homDensity_finiteGraphGraphon_infiniteSampleLaw_ae_forall W]
    with G hG
  let u : ℕ → GraphonSpaceI := fun n =>
    SeparationQuotient.mk (finiteGraphGraphon (G.restrictFin (n + 1)))
  have hu : Tendsto u atTop (𝓝 (SeparationQuotient.mk V)) :=
    (tendsto_graphonSpace_iff_forall_homDensity u _).2 fun k F _ => by
      simpa only [u, homDensityOnSpace_mk, ← hden k F] using hG k F
  have hdist : Tendsto
      (fun n => cutDist (finiteGraphGraphon (G.restrictFin (n + 1))) V) atTop (𝓝 0) := by
    simpa only [u, dist_graphonSpace_mk_mk] using tendsto_iff_dist_tendsto_zero.1 hu
  rw [← tendsto_add_atTop_iff_nat 1]
  refine squeeze_zero (fun n => cutDist_nonneg _ _) (fun n => ?_) hdist
  calc
    cutDist (finiteGraphGraphon (G.restrictFin (n + 1))) W ≤
        cutDist (finiteGraphGraphon (G.restrictFin (n + 1))) V + cutDist V W :=
      cutDist_triangle _ _ _
    _ = cutDist (finiteGraphGraphon (G.restrictFin (n + 1))) V := by
      rw [cutDist_comm V W, hWV, add_zero]

/-- On the unit interval, the growing nonempty sampled windows converge almost surely in
graphon space to the class of the generating graphon. -/
theorem infiniteSampleLaw_ae_tendsto_graphonSpace
    (W : Graphon I (volume : Measure I)) :
    ∀ᵐ G ∂infiniteSampleLaw W,
      Tendsto (fun n => (SeparationQuotient.mk
        (finiteGraphGraphon (G.restrictFin (n + 1))) : GraphonSpaceI)) atTop
        (𝓝 (SeparationQuotient.mk W)) := by
  filter_upwards [infiniteSampleLaw_ae_tendsto_cutDist W] with G hG
  rw [tendsto_iff_dist_tendsto_zero]
  simpa only [dist_graphonSpace_mk_mk] using (tendsto_add_atTop_iff_nat 1).2 hG

end TauCeti.DenseGraphLimits
