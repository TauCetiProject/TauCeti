/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Realization
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.WeakConvergence

import TauCeti.MeasureTheory.Measure.LevyProkhorovMetric

/-!
# Density of graph plans among couplings

If the source law is atomless and the source and target are Polish, every coupling is a weak limit
of graph plans of measurable, law-preserving maps. A countable quantization of the source changes
each point by a uniformly small distance. Realizing the coupling exactly after this quantization
then makes its graph realization close in the Lévy--Prokhorov metric.

It does not assert that a limiting coupling is itself a graph plan.

Integration of a bounded continuous cost is continuous in the weak topology, so this density is
the classical route to the equality of the Monge and Kantorovich values for such costs. Density
alone does not reach unbounded or infinite costs; Pratelli's theorem
`TauCeti.mongeCost_eq_transportCost_of_continuous` proves the equality for every continuous cost
by a direct construction.

## Main statements

* `TauCeti.Coupling.dense_graphPlans` — graph plans are dense among the couplings of an atomless
  source law;
* `TauCeti.Coupling.mem_closure_graphPlans` — every coupling lies in the weak closure of the graph
  plans of transport maps.

## References

* A. Pratelli, *On the equality between Monge's infimum and Kantorovich's minimum in optimal mass
  transportation*, Ann. I. H. Poincaré Probab. Statist. 43 (2007), 1--13; the realization step
  follows §1.1, and Theorem B there is the general continuous-cost equality.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal Topology

namespace TauCeti

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MetricSpace X] [MetricSpace Y] [PolishSpace X] [PolishSpace Y]
  [BorelSpace X] [BorelSpace Y]
  {μ : Measure X} {ν : Measure Y} {π : Measure (X × Y)}

section Probability

variable [IsProbabilityMeasure μ] [NullSingletonClass μ]

/-- Every coupling with an atomless source has a graph realization arbitrarily close in the
Lévy--Prokhorov metric. The source and target marginals of the realization are exact. -/
theorem exists_graphPlan_levyProkhorovEDist_lt (hπ : IsCoupling π μ ν)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T : X → Y, MeasurePreserving T μ ν ∧
      levyProkhorovEDist π (graphPlan T μ) < ENNReal.ofReal ε := by
  let : IsProbabilityMeasure π := hπ.isProbabilityMeasure
  let : IsProbabilityMeasure ν := hπ.snd_eq ▸ inferInstance
  let : Nonempty X := nonempty_of_isProbabilityMeasure μ
  let : Nonempty Y := nonempty_of_isProbabilityMeasure ν
  classical
  let u : ℕ → X := TopologicalSpace.denseSeq X
  have hu : DenseRange u := TopologicalSpace.denseRange_denseSeq X
  let r : ℝ := ε / 4
  have hr : 0 < r := by dsimp [r]; positivity
  have hidx : ∀ x : X, ∃ i, dist x (u i) < r :=
    fun x ↦ Metric.denseRange_iff.1 hu x r hr
  let q : X → ℕ := fun x ↦ Nat.find (hidx x)
  have hq : Measurable q := measurable_find hidx fun _ ↦ measurableSet_ball
  let F : X × Y → X × Y := Prod.map (u ∘ q) id
  have hF : Measurable F := (Measurable.of_discrete.comp hq).prodMap measurable_id
  have hdist (z : X × Y) : edist z (F z) ≤ ENNReal.ofReal r := by
    rcases z with ⟨x, y⟩
    simpa [F, Prod.edist_eq, edist_dist] using
      (ENNReal.ofReal_le_ofReal (Nat.find_spec (hidx x)).le)
  obtain ⟨T, hT, hqmap⟩ := hπ.exists_measurePreserving_map_graphPlan_eq hq
  have hmap : π.map F = (graphPlan T μ).map F := by
    have hu' : Measurable (Prod.map u (id : Y → Y)) :=
      Measurable.of_discrete.prodMap measurable_id
    have hq' := hq.prodMap (measurable_id : Measurable (id : Y → Y))
    have hcomp : (Prod.map u (id : Y → Y)) ∘ (Prod.map q id) = F := rfl
    simpa only [Measure.map_map hu' hq', hcomp] using
      congrArg (Measure.map (Prod.map u (id : Y → Y))) hqmap.symm
  have hdistleft : levyProkhorovEDist π (π.map F) ≤ ENNReal.ofReal (ε / 4) :=
    π.levyProkhorovEDist_map_le_of_edist_le hF.aemeasurable (Filter.Eventually.of_forall hdist)
  have hdistright : levyProkhorovEDist (graphPlan T μ) ((graphPlan T μ).map F) ≤
      ENNReal.ofReal (ε / 4) :=
    (graphPlan T μ).levyProkhorovEDist_map_le_of_edist_le hF.aemeasurable
      (Filter.Eventually.of_forall hdist)
  refine ⟨T, hT, ?_⟩
  calc
    levyProkhorovEDist π (graphPlan T μ) ≤
        levyProkhorovEDist π (π.map F) +
          levyProkhorovEDist (π.map F) (graphPlan T μ) :=
      levyProkhorovEDist_triangle _ _ _
    _ = levyProkhorovEDist π (π.map F) +
          levyProkhorovEDist (graphPlan T μ) ((graphPlan T μ).map F) := by
      rw [hmap, levyProkhorovEDist_comm (graphPlan T μ) ((graphPlan T μ).map F)]
    _ ≤ ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) :=
      add_le_add hdistleft hdistright
    _ = ENNReal.ofReal (ε / 2) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
    _ < ENNReal.ofReal ε := (ENNReal.ofReal_lt_ofReal_iff hε).2 (by linarith)

/-- Graph plans of law-preserving measurable maps are narrowly dense among couplings with
nonatomic source. The closure is taken in the weak topology of probability measures on the
product; every approximating graph plan has exactly the prescribed marginals. -/
theorem Coupling.mem_closure_graphPlans {μ₀ : ProbabilityMeasure X}
    {ν₀ : ProbabilityMeasure Y} (π₀ : Coupling μ₀ ν₀)
    [NullSingletonClass (μ₀ : Measure X)] :
    (π₀.1 : ProbabilityMeasure (X × Y)) ∈
      closure {ρ : ProbabilityMeasure (X × Y) |
        ∃ T : X → Y, MeasurePreserving T (μ₀ : Measure X) (ν₀ : Measure Y) ∧
          ρ.toMeasure = graphPlan T (μ₀ : Measure X)} := by
  let G : Set (ProbabilityMeasure (X × Y)) :=
    {ρ | ∃ T : X → Y, MeasurePreserving T (μ₀ : Measure X) (ν₀ : Measure Y) ∧
      ρ.toMeasure = graphPlan T (μ₀ : Measure X)}
  let e := LevyProkhorov.probabilityMeasureHomeomorph (Ω := X × Y)
  have he : e π₀.1 ∈ closure (e '' G) := by
    apply Metric.mem_closure_iff.2
    intro ε hε
    obtain ⟨T, hT, hdist⟩ :=
      exists_graphPlan_levyProkhorovEDist_lt π₀.2 hε
    let ρ : ProbabilityMeasure (X × Y) := ⟨graphPlan T (μ₀ : Measure X), inferInstance⟩
    refine ⟨e ρ, ⟨ρ, ⟨T, hT, rfl⟩, rfl⟩, ?_⟩
    rw [LevyProkhorov.dist_probabilityMeasure_def, levyProkhorovDist]
    exact ENNReal.toReal_lt_of_lt_ofReal hdist
  have : π₀.1 ∈ e ⁻¹' closure (e '' G) := he
  rw [e.preimage_closure, Set.preimage_image_eq _ e.injective] at this
  exact this

/-- With the topology inherited from probability measures, graph couplings are dense in the
space of couplings of an atomless source law with a prescribed target law. -/
theorem Coupling.dense_graphPlans {μ₀ : ProbabilityMeasure X} {ν₀ : ProbabilityMeasure Y}
    [NullSingletonClass (μ₀ : Measure X)] :
    Dense {π₀ : Coupling μ₀ ν₀ |
      ∃ T : X → Y, MeasurePreserving T (μ₀ : Measure X) (ν₀ : Measure Y) ∧
        π₀.1.toMeasure = graphPlan T (μ₀ : Measure X)} := by
  refine Topology.IsEmbedding.subtypeVal.isInducing.dense_iff.2 ?_
  rintro ⟨ρ, hρ⟩
  have hclosure := Coupling.mem_closure_graphPlans (⟨ρ, hρ⟩ : Coupling μ₀ ν₀)
  apply closure_mono _ hclosure
  intro σ hσ
  obtain ⟨T, hT, hσ⟩ := hσ
  refine ⟨⟨σ, ?_⟩, ⟨T, hT, hσ⟩, rfl⟩
  exact hσ.symm ▸ isCoupling_graphPlan hT.hasLaw

end Probability

end TauCeti
