/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.Sampling.Finite
public import TauCeti.Combinatorics.SimpleGraph.Maps
public import TauCeti.Combinatorics.SimpleGraph.Measurable
public import TauCeti.MeasureTheory.Constructions.Pi

/-!
# Consistency of graphon sampling under restriction of labels

Sampling `l` independent points from a graphon and then tossing an independent coin for each
unordered pair produces a law on `SimpleGraph (Fin l)`. Restricting such a sample to a window of
`k` labels is the same as running the `k`-point sampling procedure from the start: the window
reads `k` of the `l` independent points, which are again independent with the same law, and the
coins outside the window are simply not looked at.

The combinatorial half is that the graphs on `Fin l` restricting to a fixed `H` along an
injection `f` are exactly the graphs whose edges meet the window `⊤.map f` in the image of the
edges of `H`. Summing the conditional masses over that family collapses the coins outside the
window, leaving the conditional mass of `H` at the restricted positions. The probabilistic half is
that restricting an independent family of positions along an injection is measure preserving.

## Main results

* `TauCeti.DenseGraphLimits.sum_sampleIntegrand_comap_eq` — at fixed positions, the conditional
  masses of the graphs restricting to `H` sum to the conditional mass of `H` at the restricted
  positions;
* `TauCeti.DenseGraphLimits.sum_sampleMass_comap_eq` — the same identity after integrating out
  the positions;
* `TauCeti.DenseGraphLimits.sampleGraph_map_comap` — the sampling laws are consistent under
  restriction along every injection of labels.

## References

* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012),
  Section 10.1.
* P. Diaconis, S. Janson, *Graph limits and exchangeable random graphs*, Rend. Mat. Appl. (7) 28
  (2008), 33--61, Section 5.
* C. Freer, `cameronfreer/graphon` at commit
  `6eccca5bbe5c9df46d7129bf59575b8b9b1d6699`, Apache-2.0,
  `Graphon/ExchangeableGraphLaw.lean`. The consistency statement follows that source; the proof
  here is written for Tau Ceti's strict graphon carrier and reduces the combinatorial step to the
  prescribed-trace mass formula.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace DenseGraphLimits

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {k l : ℕ} (W : Graphon Ω μ) (f : Fin k ↪ Fin l) (H : SimpleGraph (Fin k))

open Classical in
/-- At fixed vertex positions, the conditional masses of the graphs restricting to `H` along `f`
sum to the conditional mass of `H` at the restricted positions: such a graph is prescribed on the
window seen by `f` and free outside it, and the free coins contribute `1`. -/
theorem sum_sampleIntegrand_comap_eq (x : Fin l → Ω) :
    ∑ G ∈ Finset.univ.filter (fun G : SimpleGraph (Fin l) => SimpleGraph.comap ⇑f G = H),
        sampleIntegrand W G x = sampleIntegrand W H (x ∘ ⇑f) := by
  have hA : ((⊤ : SimpleGraph (Fin k)).map ⇑f).edgeFinset ⊆
      (⊤ : SimpleGraph (Fin l)).edgeFinset := SimpleGraph.edgeFinset_mono le_top
  have hBA : (H.map ⇑f).edgeFinset ⊆ ((⊤ : SimpleGraph (Fin k)).map ⇑f).edgeFinset :=
    SimpleGraph.edgeFinset_mono (SimpleGraph.map_monotone _ le_top)
  -- Restricting to `H` along `f` prescribes exactly the edges inside the window.
  have hfilter :
      Finset.univ.filter (fun G : SimpleGraph (Fin l) => SimpleGraph.comap ⇑f G = H) =
        Finset.univ.filter (fun G : SimpleGraph (Fin l) =>
          G.edgeFinset ∩ ((⊤ : SimpleGraph (Fin k)).map ⇑f).edgeFinset =
            (H.map ⇑f).edgeFinset) :=
    Finset.filter_congr fun G _ => by
      rw [SimpleGraph.comap_eq_iff_inf_map_top, ← SimpleGraph.edgeFinset_inj,
        SimpleGraph.edgeFinset_inf]
  -- Inside the window the edges of the pattern are read through the injection `Sym2.map f`.
  have hinj : Function.Injective (Sym2.map ⇑f) := Sym2.map.injective f.injective
  have hmapTop : ((⊤ : SimpleGraph (Fin k)).map ⇑f).edgeFinset =
      (⊤ : SimpleGraph (Fin k)).edgeFinset.image (Sym2.map ⇑f) := by
    ext e
    simp [SimpleGraph.edgeSet_map]
  have hmapH : (H.map ⇑f).edgeFinset = H.edgeFinset.image (Sym2.map ⇑f) := by
    ext e
    simp [SimpleGraph.edgeSet_map]
  rw [hfilter, sum_sampleIntegrand_inter_eq W _ _ hA hBA, hmapTop, hmapH,
    ← Finset.image_sdiff _ _ hinj, Finset.prod_image fun _ _ _ _ h => hinj h,
    Finset.prod_image fun _ _ _ _ h => hinj h, sampleIntegrand_def]
  simp_rw [edgeFactor_map]

open Classical in
/-- The masses of the graphs restricting to `H` along `f` sum to the mass of `H`: integrating the
conditional identity over the positions, which the restriction to the window redistributes without
changing their law. -/
theorem sum_sampleMass_comap_eq :
    ∑ G ∈ Finset.univ.filter (fun G : SimpleGraph (Fin l) => SimpleGraph.comap ⇑f G = H),
        sampleMass W G = sampleMass W H := by
  -- Restricting an independent family of positions to the window is measure preserving.
  have hmp : MeasurePreserving (fun x : Fin l → Ω => fun i : Fin k => x (f i))
      (Measure.pi fun _ : Fin l => μ) (Measure.pi fun _ : Fin k => μ) :=
    TauCeti.measurePreserving_pi_comp_embedding (fun _ : Fin l => μ) f
  calc ∑ G ∈ Finset.univ.filter
        (fun G : SimpleGraph (Fin l) => SimpleGraph.comap ⇑f G = H), sampleMass W G
      = ∫ x : Fin l → Ω, ∑ G ∈ Finset.univ.filter
            (fun G : SimpleGraph (Fin l) => SimpleGraph.comap ⇑f G = H),
          sampleIntegrand W G x ∂Measure.pi fun _ => μ := by
        simp_rw [sampleMass_def]
        exact (integral_finsetSum _ fun G _ => integrable_sampleIntegrand W G).symm
    _ = ∫ x : Fin l → Ω, sampleIntegrand W H (x ∘ ⇑f) ∂Measure.pi fun _ => μ :=
        integral_congr_ae (Filter.Eventually.of_forall (sum_sampleIntegrand_comap_eq W f H))
    _ = ∫ y : Fin k → Ω, sampleIntegrand W H y ∂Measure.pi fun _ => μ := by
        rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable
          (measurable_sampleIntegrand W H).aestronglyMeasurable]
        rfl
    _ = sampleMass W H := (sampleMass_def W H).symm

/-- **Consistency of graphon sampling.** Restricting a sample on `Fin l` to a window of `k`
labels has the law of a sample on `Fin k`. -/
@[simp]
theorem sampleGraph_map_comap :
    (sampleGraph W l).map (SimpleGraph.comap ⇑f) = sampleGraph W k := by
  classical
  refine Measure.ext_of_singleton fun H => ?_
  have hpre : SimpleGraph.comap ⇑f ⁻¹' {H} =
      ↑(Finset.univ.filter (fun G : SimpleGraph (Fin l) => SimpleGraph.comap ⇑f G = H)) := by
    ext G
    simp
  rw [Measure.map_apply (SimpleGraph.measurable_comap ⇑f) (MeasurableSet.singleton H), hpre,
    ← sum_measure_singleton]
  simp_rw [sampleGraph_singleton]
  rw [← ENNReal.ofReal_sum_of_nonneg fun G _ => sampleMass_nonneg W G,
    sum_sampleMass_comap_eq W f H]

end DenseGraphLimits

end TauCeti
