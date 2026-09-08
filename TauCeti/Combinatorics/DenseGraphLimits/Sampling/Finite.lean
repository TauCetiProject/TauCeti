/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.HomDensity.Basic
public import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Finite sampling from a graphon

The `W`-random graph on `Fin n` is obtained in two stages: first sample `n` independent points
from the graphon's probability space, then include each unordered pair independently with
probability given by the value of `W` at its two sampled points. This file integrates out both
stages and packages the resulting masses as a probability measure on finite simple graphs.

The mass of a graph `G` is the integral of a finite product. Its edges contribute factors `W`,
while its nonedges contribute factors `1 - W`. At fixed vertex positions, summing this product
over every graph expands as `∏ₑ (Wₑ + (1 - Wₑ)) = 1`; this gives normalization without imposing
any extra regularity on the graphon's carrier.

## Main definitions

* `TauCeti.DenseGraphLimits.sampleIntegrand` — the conditional mass of a graph at fixed sampled
  vertex positions;
* `TauCeti.DenseGraphLimits.sampleMass` — that mass after integrating over the positions;
* `TauCeti.DenseGraphLimits.sampleGraph` — the resulting probability measure.

## Main results

* `sampleMass_nonneg` and `sum_sampleMass_eq_one` show that the masses form a probability law;
* `sampleGraph_apply_singleton` computes the probability of an individual graph;
* `sampleGraph_const` identifies sampling a constant graphon with Mathlib's binomial random graph.

## References

* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012),
  Sections 10.1--10.2.
* C. Freer, `cameronfreer/graphon` at commit
  `6eccca5bbe5c9df46d7129bf59575b8b9b1d6699`, Apache-2.0,
  `Graphon/Sampling.lean`, `Graphon/SamplingLaw.lean`, and `Graphon/SamplingExamples.lean`.
  The definitions and normalization argument are adapted to Tau Ceti's strict graphon carrier;
  the constant-law proof reuses the same reduction to Mathlib's singleton-mass formula.
-/

public section

noncomputable section

open MeasureTheory

open scoped ENNReal unitInterval

namespace TauCeti

namespace DenseGraphLimits

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

open Classical in
/-- The conditional mass of `G` at fixed sampled vertex positions. Edges contribute `W` and
nonedges contribute `1 - W`. -/
def sampleIntegrand {n : ℕ} (W : Graphon Ω μ) (G : SimpleGraph (Fin n))
    (x : Fin n → Ω) : ℝ :=
  (∏ e ∈ G.edgeFinset, edgeFactor W x e) *
    ∏ e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset \ G.edgeFinset, (1 - edgeFactor W x e)

open Classical in
/-- The probability mass assigned to `G` by the `W`-random graph: integrate its conditional mass
over the independently sampled vertex positions. -/
def sampleMass {n : ℕ} (W : Graphon Ω μ) (G : SimpleGraph (Fin n)) : ℝ :=
  ∫ x : Fin n → Ω, sampleIntegrand W G x ∂Measure.pi fun _ => μ

section Mass

variable {n : ℕ} (W : Graphon Ω μ) (G : SimpleGraph (Fin n))

open Classical in
/-- The defining edge/nonedge product of the sampled-graph integrand. -/
theorem sampleIntegrand_def (x : Fin n → Ω) :
    sampleIntegrand W G x =
      (∏ e ∈ G.edgeFinset, edgeFactor W x e) *
        ∏ e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset \ G.edgeFinset,
          (1 - edgeFactor W x e) := (rfl)

/-- The defining integral of a sampled graph's mass. -/
theorem sampleMass_def :
    sampleMass W G = ∫ x : Fin n → Ω, sampleIntegrand W G x ∂Measure.pi fun _ => μ := (rfl)

/-- The sampled-graph integrand is measurable in the vertex positions. -/
theorem measurable_sampleIntegrand : Measurable (sampleIntegrand W G) := by
  classical
  apply Measurable.mul
  · exact measurable_prod_edgeFactor G.edgeFinset fun _ => W
  · exact Finset.measurable_prod _ fun e _ =>
      measurable_const.sub (measurable_edgeFactor W e)

/-- The sampled-graph integrand is nonnegative. -/
theorem sampleIntegrand_nonneg (x : Fin n → Ω) : 0 ≤ sampleIntegrand W G x := by
  classical
  rw [sampleIntegrand]
  refine mul_nonneg (prod_edgeFactor_nonneg G.edgeFinset (fun _ => W) x)
    (Finset.prod_nonneg fun e _ => ?_)
  linarith [edgeFactor_le_one W x e]

/-- The sampled-graph integrand is at most `1`. -/
theorem sampleIntegrand_le_one (x : Fin n → Ω) : sampleIntegrand W G x ≤ 1 := by
  classical
  rw [sampleIntegrand]
  have hnonneg : 0 ≤ ∏ e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset \ G.edgeFinset,
      (1 - edgeFactor W x e) := Finset.prod_nonneg fun e _ => by
    linarith [edgeFactor_le_one W x e]
  have hle : (∏ e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset \ G.edgeFinset,
      (1 - edgeFactor W x e)) ≤ 1 :=
    Finset.prod_le_one (fun e _ => by linarith [edgeFactor_le_one W x e])
      fun e _ => by linarith [edgeFactor_nonneg W x e]
  calc
    (∏ e ∈ G.edgeFinset, edgeFactor W x e) *
          ∏ e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset \ G.edgeFinset,
            (1 - edgeFactor W x e) ≤ 1 * 1 :=
      mul_le_mul (prod_edgeFactor_le_one G.edgeFinset (fun _ => W) x) hle hnonneg zero_le_one
    _ = 1 := one_mul 1

/-- The sampled-graph integrand is integrable against the product probability measure. -/
theorem integrable_sampleIntegrand :
    Integrable (sampleIntegrand W G) (Measure.pi fun _ : Fin n => μ) := by
  classical
  refine Integrable.mono' (integrable_const 1)
    (measurable_sampleIntegrand W G).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sampleIntegrand_nonneg W G x)]
  exact sampleIntegrand_le_one W G x

/-- Sampled-graph masses are nonnegative. -/
theorem sampleMass_nonneg : 0 ≤ sampleMass W G := by
  classical
  rw [sampleMass_def]
  exact integral_nonneg fun x => sampleIntegrand_nonneg W G x

/-- A sampled-graph mass is at most `1`. -/
theorem sampleMass_le_one : sampleMass W G ≤ 1 := by
  classical
  rw [sampleMass_def]
  have h := integral_mono (integrable_sampleIntegrand W G) (integrable_const 1)
    (sampleIntegrand_le_one W G)
  simpa using h

open Classical in
/-- At fixed vertex positions, the conditional masses sum to `1` over all simple graphs. -/
theorem sum_sampleIntegrand_eq_one (x : Fin n → Ω) :
    ∑ H : SimpleGraph (Fin n), sampleIntegrand W H x = 1 := by
  let w : Sym2 (Fin n) → ℝ := fun e => edgeFactor W x e
  have hsum : ∑ H : SimpleGraph (Fin n), sampleIntegrand W H x =
      ∑ S ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset.powerset,
        (∏ e ∈ S, w e) *
          ∏ e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset \ S, (1 - w e) := by
    refine Finset.sum_nbij' (fun H => H.edgeFinset)
      (fun S => SimpleGraph.fromEdgeSet (↑S : Set (Sym2 (Fin n)))) ?_ ?_ ?_ ?_ ?_
    · exact fun H _ => Finset.mem_powerset.mpr (SimpleGraph.edgeFinset_mono le_top)
    · exact fun S _ => Finset.mem_univ _
    · intro H _
      rw [SimpleGraph.coe_edgeFinset, SimpleGraph.fromEdgeSet_edgeSet]
    · intro S hS
      ext e
      simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_fromEdgeSet, Set.mem_sdiff,
        Finset.mem_coe, Sym2.mem_diagSet]
      constructor
      · exact fun h => h.1
      · intro he
        refine ⟨he, ?_⟩
        exact (⊤ : SimpleGraph (Fin n)).not_isDiag_of_mem_edgeSet
          (SimpleGraph.mem_edgeFinset.mp ((Finset.mem_powerset.mp hS) he))
    · exact fun H _ => rfl
  rw [hsum, ← Finset.prod_add]
  calc
    ∏ e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset, (w e + (1 - w e)) =
        ∏ _e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset, (1 : ℝ) := by
          exact Finset.prod_congr rfl fun _ _ => by ring
    _ = 1 := Finset.prod_const_one

open Classical in
/-- The sampled-graph masses sum to `1`. -/
theorem sum_sampleMass_eq_one : ∑ H : SimpleGraph (Fin n), sampleMass W H = 1 := by
  simp_rw [sampleMass_def]
  rw [← integral_finsetSum _ fun H _ => integrable_sampleIntegrand W H]
  simp_rw [sum_sampleIntegrand_eq_one W]
  simp

end Mass

section Law

open Classical in
/-- The probability mass function used to construct the `W`-random graph law. -/
private def samplePMF (W : Graphon Ω μ) (n : ℕ) : PMF (SimpleGraph (Fin n)) :=
  PMF.ofFintype (fun G => ENNReal.ofReal (sampleMass W G)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun G _ => sampleMass_nonneg W G),
      sum_sampleMass_eq_one, ENNReal.ofReal_one])

/-- The probability assigned to a graph by `samplePMF`. -/
@[simp]
private theorem samplePMF_apply (W : Graphon Ω μ) (n : ℕ) (G : SimpleGraph (Fin n)) :
    samplePMF W n G = ENNReal.ofReal (sampleMass W G) := (rfl)

/-- The `W`-random graph law on `Fin n`. -/
def sampleGraph (W : Graphon Ω μ) (n : ℕ) : Measure (SimpleGraph (Fin n)) :=
  (samplePMF W n).toMeasure

/-- A sampled graph law is a probability measure. -/
instance sampleGraph_isProbabilityMeasure (W : Graphon Ω μ) (n : ℕ) :
    IsProbabilityMeasure (sampleGraph W n) := by
  rw [sampleGraph]
  infer_instance

/-- The probability that the sampled graph equals `G`. -/
@[simp]
theorem sampleGraph_apply_singleton (W : Graphon Ω μ) (n : ℕ) (G : SimpleGraph (Fin n)) :
    sampleGraph W n {G} = ENNReal.ofReal (sampleMass W G) := by
  classical
  rw [sampleGraph, PMF.toMeasure_apply_singleton, samplePMF_apply]
  have h : MeasurableSet ({G.edgeSet} : Set (Set (Sym2 (Fin n)))) :=
    MeasurableSet.singleton G.edgeSet
  have heq : SimpleGraph.edgeSet ⁻¹' {G.edgeSet} = {G} := by
    ext H
    simp only [Set.mem_preimage, Set.mem_singleton_iff,
      SimpleGraph.edgeSet_injective.eq_iff]
  rw [← heq]
  exact h.preimage SimpleGraph.measurable_edgeSet

end Law

section Constant

open Classical in
/-- The sampled mass of a constant graphon is the usual independent-edge mass. -/
@[simp]
theorem sampleMass_const (p : I) (G : SimpleGraph (Fin n)) :
    sampleMass (Graphon.const μ p) G =
      (p : ℝ) ^ G.edgeFinset.card *
        (1 - (p : ℝ)) ^ (n.choose 2 - G.edgeFinset.card) := by
  have hfactor (x : Fin n → Ω) (e : Sym2 (Fin n)) :
      edgeFactor (Graphon.const μ p) x e = (p : ℝ) := by
    induction e using Sym2.ind with
    | _ a b => simp
  have hcard : ((⊤ : SimpleGraph (Fin n)).edgeFinset \ G.edgeFinset).card =
      n.choose 2 - G.edgeFinset.card := by
    rw [Finset.card_sdiff,
      Finset.inter_eq_left.mpr (SimpleGraph.edgeFinset_mono le_top)]
    congr 1
    rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]
  rw [sampleMass_def]
  have hintegrand : sampleIntegrand (Graphon.const μ p) G = fun _ =>
      (p : ℝ) ^ G.edgeFinset.card *
        (1 - (p : ℝ)) ^ (n.choose 2 - G.edgeFinset.card) := by
    funext x
    rw [sampleIntegrand]
    simp_rw [hfactor x]
    rw [Finset.prod_const, Finset.prod_const, hcard]
  rw [hintegrand]
  simp

/-- Sampling a constant graphon gives Mathlib's binomial random graph law. -/
@[simp]
theorem sampleGraph_const (p : I) (n : ℕ) :
    sampleGraph (Graphon.const μ p) n = SimpleGraph.binomialRandom (Fin n) p := by
  classical
  refine Measure.ext_of_singleton fun G => ?_
  rw [sampleGraph_apply_singleton, sampleMass_const,
    SimpleGraph.binomialRandom_singleton]
  have hp : 0 ≤ (p : ℝ) := p.2.1
  have hσ : 0 ≤ 1 - (p : ℝ) := sub_nonneg.mpr p.2.2
  rw [ENNReal.ofReal_mul (pow_nonneg hp _), ENNReal.ofReal_pow hp,
    ENNReal.ofReal_pow hσ]
  have hncard : G.edgeSet.ncard = G.edgeFinset.card := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  have hp' : ENNReal.ofReal (p : ℝ) = (unitInterval.toNNReal p : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_coe_nnreal]
    congr 1
  have hσ' : ENNReal.ofReal (1 - (p : ℝ)) =
      (unitInterval.toNNReal (σ p) : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_coe_nnreal]
    congr 1
  rw [hp', hσ', hncard]
  simp

end Constant

end DenseGraphLimits

end TauCeti
