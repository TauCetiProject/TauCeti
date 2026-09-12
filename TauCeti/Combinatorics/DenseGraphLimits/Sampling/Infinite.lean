/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.Sampling.Finite
public import TauCeti.Combinatorics.SimpleGraph.Measurable
public import TauCeti.Probability.Distributions.Uniform
public import Mathlib.Probability.ProductMeasure
import TauCeti.MeasureTheory.Measure.ProductKernel

/-!
# The joint sampling law of a graphon

The finite sampling laws `sampleGraph W n` are one probability measure for each `n`, on a
different space each time, so a statement comparing the samples across `n` cannot even be
expressed for that family. This file builds the single random object they are all windows of: an
infinite `W`-random graph on the label set `ℕ`, sampled once, from which every finite sample is
read off by restriction.

The randomness is explicit. A position `x i` is drawn from the graphon's carrier independently for
each label `i`, and an independent coin `u e` is drawn for each unordered pair `e` from the uniform
law on the unit interval, `TauCeti.Probability.uniformMeasure 0 1`; the pair `{i, j}` becomes an
edge exactly when its coin falls below the graphon value at the two positions. Both families are
infinite products of probability measures, so
`MeasureTheory.Measure.infinitePi` carries them, and the resulting law on `SimpleGraph ℕ` uses the
adjacency sigma-algebra Mathlib already provides.

The finite-marginal identification is the theorem of the file. For a fixed pattern `H` on `Fin n`
the event that the window of the infinite graph equals `H` is a box: it constrains the coin of
each pair of distinct labels below `n` to an interval — below the graphon value for the pairs `H`
joins, above it for the pairs it does not — and constrains nothing else. The coin product of that
box is the conditional mass `sampleIntegrand W H` at the sampled positions, and averaging over the
positions is `sampleMass W H`.

## Main definitions

* `TauCeti.DenseGraphLimits.infiniteSampleLaw` — its law, the joint sampling object;
* `TauCeti.SimpleGraph.restrictFin` — the initial `n`-label window of a graph on `ℕ`.

## Main results

* `infiniteSampleLaw_map_restrictFin` — every finite sampling law is a window of the joint law.

## References

* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012), §10.1.
* S. Janson, *Graphons, cut norm and distance, couplings and rearrangements*, NYJM Monographs 4
  (2013), §7.
-/

public section

noncomputable section

open MeasureTheory

open scoped ENNReal

namespace TauCeti

namespace SimpleGraph

/-- The window of a graph on `ℕ` spanned by the first `n` labels. -/
def restrictFin (G : SimpleGraph ℕ) (n : ℕ) : SimpleGraph (Fin n) :=
  SimpleGraph.comap (fun i => (i : ℕ)) G

@[simp]
theorem restrictFin_adj {n : ℕ} (G : SimpleGraph ℕ) (a b : Fin n) :
    (restrictFin G n).Adj a b ↔ G.Adj a b := Iff.rfl

/-- Taking a window is measurable. -/
theorem measurable_restrictFin (n : ℕ) : Measurable fun G : SimpleGraph ℕ => restrictFin G n := by
  rw [SimpleGraph.measurable_iff_adj]
  intro a b
  exact (measurable_pi_apply (b : ℕ)).comp
    ((measurable_pi_apply (a : ℕ)).comp SimpleGraph.measurable_adj)

end SimpleGraph

namespace DenseGraphLimits

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

section Source

/-- The randomness the infinite `W`-random graph is read off: an independent position in the
graphon's carrier for every label, and an independent uniform coin for every unordered pair of
labels. -/
private def infiniteSampleSource (μ : Measure Ω) : Measure ((ℕ → Ω) × (Sym2 ℕ → ℝ)) :=
  (Measure.infinitePi fun _ : ℕ => μ).prod
    (Measure.infinitePi fun _ : Sym2 ℕ => Probability.uniformMeasure 0 1)

private instance infiniteSampleSource_isProbabilityMeasure :
    IsProbabilityMeasure (infiniteSampleSource μ) := by
  rw [infiniteSampleSource]
  infer_instance

/-- The infinite `W`-random graph attached to a family of positions and a family of coins: the
pair `{i, j}` is an edge when its coin falls below the graphon value at the two positions. -/
private def infiniteSampleGraph (W : Graphon Ω μ) (x : ℕ → Ω) (u : Sym2 ℕ → ℝ) : SimpleGraph ℕ where
  Adj i j := i ≠ j ∧ u s(i, j) < edgeFactor W x s(i, j)
  symm := ⟨by
    rintro i j ⟨hne, hlt⟩
    refine ⟨hne.symm, ?_⟩
    rwa [Sym2.eq_swap]⟩
  loopless := ⟨fun i h => h.1 rfl⟩

@[simp]
private theorem infiniteSampleGraph_adj (W : Graphon Ω μ) (x : ℕ → Ω) (u : Sym2 ℕ → ℝ) (i j : ℕ) :
    (infiniteSampleGraph W x u).Adj i j ↔ i ≠ j ∧ u s(i, j) < edgeFactor W x s(i, j) := Iff.rfl

/-- The sampled graph depends measurably on the positions and the coins. -/
private theorem measurable_infiniteSampleGraph (W : Graphon Ω μ) :
    Measurable fun p : (ℕ → Ω) × (Sym2 ℕ → ℝ) => infiniteSampleGraph W p.1 p.2 := by
  rw [SimpleGraph.measurable_iff_adj]
  intro i j
  refine measurableSet_setOfPred.mp ?_
  by_cases hij : i = j
  · simp [hij]
  · have hcoin : Measurable fun p : (ℕ → Ω) × (Sym2 ℕ → ℝ) => p.2 s(i, j) :=
      (measurable_pi_apply _).comp measurable_snd
    have hvalue : Measurable fun p : (ℕ → Ω) × (Sym2 ℕ → ℝ) => edgeFactor W p.1 s(i, j) :=
      (measurable_edgeFactor W _).comp measurable_fst
    simpa [hij] using measurableSet_lt hcoin hvalue

end Source

section Law

/-- The **joint sampling law** of a graphon: the law of the infinite `W`-random graph on `ℕ`. All
the finite sampling laws are windows of this single random object. -/
def infiniteSampleLaw (W : Graphon Ω μ) : Measure (SimpleGraph ℕ) :=
  (infiniteSampleSource μ).map fun p => infiniteSampleGraph W p.1 p.2

instance infiniteSampleLaw_isProbabilityMeasure (W : Graphon Ω μ) :
    IsProbabilityMeasure (infiniteSampleLaw W) := by
  rw [infiniteSampleLaw]
  infer_instance

end Law

section Window

variable {n : ℕ}

/-- A window of the sampled graph is a prescribed pattern exactly when, for every pair of distinct
labels in the window, the coin of that pair falls below the graphon value precisely when the
pattern joins the pair. -/
private theorem restrictFin_infiniteSampleGraph_eq_iff (W : Graphon Ω μ) (x : ℕ → Ω)
    (u : Sym2 ℕ → ℝ)
    (H : SimpleGraph (Fin n)) :
    SimpleGraph.restrictFin (infiniteSampleGraph W x u) n = H ↔
      ∀ a b : Fin n, a ≠ b →
        (u s((a : ℕ), (b : ℕ)) < edgeFactor W x s((a : ℕ), (b : ℕ)) ↔ H.Adj a b) := by
  rw [SimpleGraph.ext_iff, funext_iff]
  simp only [funext_iff, eq_iff_iff, SimpleGraph.restrictFin_adj, infiniteSampleGraph_adj, ne_eq,
    Fin.val_inj]
  constructor
  · intro h a b hab
    rw [← h a b]
    simp [hab]
  · intro h a b
    by_cases hab : a = b
    · subst hab
      simp
    · rw [← h a b hab]
      simp [hab]

open Classical in
/-- The unordered pairs of distinct labels inside the window of the first `n` labels, read as
pairs of naturals. -/
private def windowPairs (n : ℕ) : Finset (Sym2 ℕ) :=
  Finset.image (Sym2.map (Fin.val : Fin n → ℕ)) (⊤ : SimpleGraph (Fin n)).edgeFinset

private theorem mem_windowPairs {e : Sym2 ℕ} :
    e ∈ windowPairs n ↔ ∃ a b : Fin n, a ≠ b ∧ e = s((a : ℕ), (b : ℕ)) := by
  classical
  rw [windowPairs, Finset.mem_image]
  constructor
  · rintro ⟨f, hf, rfl⟩
    induction f using Sym2.ind with
    | _ a b =>
      refine ⟨a, b, ?_, by simp⟩
      simpa using hf
  · rintro ⟨a, b, hab, rfl⟩
    exact ⟨s(a, b), by simpa using hab, by simp⟩

/-- The interval a pair's coin has to land in for the sampled graph to reproduce the pattern `K`
at that pair. -/
private def coinTarget (W : Graphon Ω μ) (x : ℕ → Ω) (K : SimpleGraph ℕ) (e : Sym2 ℕ) : Set ℝ :=
  open Classical in
  if e ∈ K.edgeSet then Set.Iio (edgeFactor W x e) else Set.Ici (edgeFactor W x e)

private theorem mem_coinTarget {W : Graphon Ω μ} {x : ℕ → Ω} {K : SimpleGraph ℕ} {e : Sym2 ℕ}
    {t : ℝ} : t ∈ coinTarget W x K e ↔ (t < edgeFactor W x e ↔ e ∈ K.edgeSet) := by
  classical
  rw [coinTarget]
  split_ifs with h <;> simp [h, not_lt]

private theorem measurableSet_coinTarget (W : Graphon Ω μ) (x : ℕ → Ω) (K : SimpleGraph ℕ)
    (e : Sym2 ℕ) : MeasurableSet (coinTarget W x K e) := by
  classical
  rw [coinTarget]
  split_ifs
  · exact measurableSet_Iio
  · exact measurableSet_Ici

private theorem uniformMeasure_coinTarget (W : Graphon Ω μ) (x : ℕ → Ω) (K : SimpleGraph ℕ)
    (e : Sym2 ℕ) :
    Probability.uniformMeasure 0 1 (coinTarget W x K e) =
      ENNReal.ofReal (open Classical in
        if e ∈ K.edgeSet then edgeFactor W x e else 1 - edgeFactor W x e) := by
  classical
  rw [coinTarget]
  split_ifs
  · rw [Probability.uniformMeasure_Iio zero_lt_one (edgeFactor_le_one W x e)]
    norm_num
  · rw [Probability.uniformMeasure_Ici zero_lt_one (edgeFactor_nonneg W x e)]
    norm_num

/-- The event that a window of the sampled graph is a prescribed pattern is a box in the coins. -/
private theorem setOf_restrictFin_eq (W : Graphon Ω μ) (x : ℕ → Ω) (H : SimpleGraph (Fin n)) :
    {u : Sym2 ℕ → ℝ | SimpleGraph.restrictFin (infiniteSampleGraph W x u) n = H} =
      Set.pi (windowPairs n) (coinTarget W x (H.map (Fin.val : Fin n → ℕ))) := by
  ext u
  rw [Set.mem_ofPred_eq, restrictFin_infiniteSampleGraph_eq_iff]
  simp only [Set.mem_pi, Finset.mem_coe, mem_coinTarget]
  constructor
  · intro h e he
    obtain ⟨a, b, hab, rfl⟩ := mem_windowPairs.mp he
    rw [h a b hab]
    simp [SimpleGraph.mem_edgeSet, ← SimpleGraph.map_adj_apply (f := Fin.valEmbedding)]
  · intro h a b hab
    have he : s((a : ℕ), (b : ℕ)) ∈ windowPairs n := mem_windowPairs.mpr ⟨a, b, hab, rfl⟩
    rw [h _ he]
    simp [SimpleGraph.mem_edgeSet, ← SimpleGraph.map_adj_apply (f := Fin.valEmbedding)]

end Window

section Marginal

variable {n : ℕ}

private theorem mem_edgeSet_map_val {H : SimpleGraph (Fin n)} {e : Sym2 (Fin n)} :
    Sym2.map (Fin.val : Fin n → ℕ) e ∈ (H.map (Fin.val : Fin n → ℕ)).edgeSet ↔ e ∈ H.edgeSet := by
  induction e using Sym2.ind with
  | _ a b =>
    simp only [Sym2.map_mk, SimpleGraph.mem_edgeSet]
    exact SimpleGraph.map_adj_apply (f := Fin.valEmbedding)

open Classical in
/-- At fixed positions, the coins reproduce a prescribed window with probability the conditional
mass of that pattern: each pair contributes its graphon value or the complementary value. -/
private theorem infinitePi_uniformMeasure_setOf_restrictFin_eq (W : Graphon Ω μ) (x : ℕ → Ω)
    (H : SimpleGraph (Fin n)) :
    (Measure.infinitePi fun _ : Sym2 ℕ => Probability.uniformMeasure 0 1)
        {u : Sym2 ℕ → ℝ | SimpleGraph.restrictFin (infiniteSampleGraph W x u) n = H} =
      ENNReal.ofReal (sampleIntegrand W H fun i : Fin n => x (i : ℕ)) := by
  set y : Fin n → Ω := fun i : Fin n => x (i : ℕ) with hy
  have hnonneg : ∀ e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset,
      0 ≤ (if e ∈ H.edgeFinset then edgeFactor W y e else 1 - edgeFactor W y e) := by
    intro e _
    by_cases hmem : e ∈ H.edgeFinset
    · simpa [hmem] using edgeFactor_nonneg W y e
    · have := edgeFactor_le_one W y e
      simp only [hmem, ite_false]
      linarith
  have hfactor : ∀ e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset,
      Probability.uniformMeasure 0 1
          (coinTarget W x (H.map (Fin.val : Fin n → ℕ)) (Sym2.map (Fin.val : Fin n → ℕ) e)) =
        ENNReal.ofReal (if e ∈ H.edgeFinset then edgeFactor W y e else 1 - edgeFactor W y e) := by
    intro e _
    rw [uniformMeasure_coinTarget]
    have hval : edgeFactor W x (Sym2.map (Fin.val : Fin n → ℕ) e) = edgeFactor W y e :=
      edgeFactor_map W _ x e
    by_cases hmem : e ∈ H.edgeFinset
    · have hmem' : Sym2.map (Fin.val : Fin n → ℕ) e ∈ (H.map (Fin.val : Fin n → ℕ)).edgeSet :=
        mem_edgeSet_map_val.mpr (SimpleGraph.mem_edgeFinset.mp hmem)
      simp [hmem, hmem', hval]
    · have hmem' : Sym2.map (Fin.val : Fin n → ℕ) e ∉ (H.map (Fin.val : Fin n → ℕ)).edgeSet :=
        fun h => hmem (SimpleGraph.mem_edgeFinset.mpr (mem_edgeSet_map_val.mp h))
      simp [hmem, hmem', hval]
  rw [setOf_restrictFin_eq, Measure.infinitePi_pi _
      (fun e _ => measurableSet_coinTarget W x (H.map (Fin.val : Fin n → ℕ)) e),
    sampleIntegrand_eq_prod_edgeFinset_top, windowPairs,
    Finset.prod_image fun e _ f _ h => Sym2.map.injective Fin.val_injective h,
    Finset.prod_congr rfl hfactor, ENNReal.ofReal_prod_of_nonneg hnonneg]

/-- **The finite marginals of the joint sampling law.** The window of the infinite `W`-random
graph spanned by the first `n` labels has the law of the `W`-random graph on `Fin n`: every finite
sampling law is a restriction of this one random object. -/
theorem infiniteSampleLaw_map_restrictFin (W : Graphon Ω μ) (n : ℕ) :
    (infiniteSampleLaw W).map (fun G => SimpleGraph.restrictFin G n) = sampleGraph W n := by
  refine Measure.ext_of_singleton fun H => ?_
  have hfiber : MeasurableSet ((fun G : SimpleGraph ℕ => SimpleGraph.restrictFin G n) ⁻¹' {H}) :=
    SimpleGraph.measurable_restrictFin n (measurableSet_singleton H)
  rw [Measure.map_apply (SimpleGraph.measurable_restrictFin n) (measurableSet_singleton H),
    infiniteSampleLaw, Measure.map_apply (measurable_infiniteSampleGraph W) hfiber,
    infiniteSampleSource, Measure.prod_apply
      ((measurable_infiniteSampleGraph W) hfiber), sampleGraph_singleton]
  have hslice : ∀ x : ℕ → Ω, (Prod.mk x) ⁻¹'
      ((fun p : (ℕ → Ω) × (Sym2 ℕ → ℝ) => infiniteSampleGraph W p.1 p.2) ⁻¹'
        ((fun G : SimpleGraph ℕ => SimpleGraph.restrictFin G n) ⁻¹' {H})) =
      {u : Sym2 ℕ → ℝ | SimpleGraph.restrictFin (infiniteSampleGraph W x u) n = H} := fun _ => rfl
  simp_rw [hslice, infinitePi_uniformMeasure_setOf_restrictFin_eq]
  have hmap : (Measure.infinitePi fun _ : ℕ => μ).map (fun x (i : Fin n) => x (i : ℕ)) =
      Measure.pi fun _ : Fin n => μ :=
    TauCeti.MeasureTheory.map_prefixProj_infinitePi_const
      (⟨μ, inferInstance⟩ : ProbabilityMeasure Ω) n
  have hmeasurable : Measurable fun y : Fin n → Ω => ENNReal.ofReal (sampleIntegrand W H y) :=
    (measurable_sampleIntegrand W H).ennreal_ofReal
  rw [← lintegral_map hmeasurable (by fun_prop), hmap,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_sampleIntegrand W H)
      (Filter.Eventually.of_forall (sampleIntegrand_nonneg W H)), sampleMass_def]

end Marginal

end DenseGraphLimits

end TauCeti

end

end
