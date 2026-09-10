/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.HomDensity.Finite
public import TauCeti.Combinatorics.DenseGraphLimits.HomDensity.Structural
public import TauCeti.Combinatorics.DenseGraphLimits.Sampling.Finite
public import TauCeti.Combinatorics.SimpleGraph.Measurable
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Unbiased injective homomorphism densities

The injective homomorphism density of a finite pattern in a graph sampled from a graphon is an
unbiased estimator of the graphon's homomorphism density. The proof first establishes the basic
upper-event identity: the total sampling mass of all supergraphs of `F` is `t(F, W)`. It then
averages that identity over every embedding of the pattern's vertices into the sampled vertex set.

The falling factorial counts ordered vertex embeddings and therefore matches the injective maps in
the numerator of `injHomDensity`. The hypothesis that the sample contains at least as many vertices
as the pattern makes this denominator nonzero.

## Main results

* `TauCeti.DenseGraphLimits.sum_sampleMass_supergraph_eq_homDensity` — the probability that the
  sample contains every edge of `F` is `t(F, W)`;
* `TauCeti.DenseGraphLimits.injHomDensity_integral_sampleGraph` — injective homomorphism density is
  unbiased under graphon sampling.

## References

* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012), Sections
  5.2 and 10.2.
* C. Freer, `cameronfreer/graphon` at commit
  `6eccca5bbe5c9df46d7129bf59575b8b9b1d6699`, Apache-2.0, `Graphon/Sampling.lean`. The
  supergraph-mass proof is adapted from its Boolean-cube argument to Tau Ceti's strict graphon
  carrier.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace DenseGraphLimits

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

open Classical in
/-- Reindex the supergraph sum by the optional edges outside the fixed graph. -/
private theorem sum_sampleIntegrand_supergraph_bij {n : ℕ} (W : Graphon Ω μ)
    (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] (x : Fin n → Ω) :
    ∑ G ∈ Finset.univ.filter (F ≤ ·), sampleIntegrand W G x =
      ∑ S ∈ ((⊤ : SimpleGraph (Fin n)).edgeFinset \ F.edgeFinset).powerset,
        (∏ e ∈ F.edgeFinset, edgeFactor W x e) *
          ((∏ e ∈ S, edgeFactor W x e) *
            ∏ e ∈ ((⊤ : SimpleGraph (Fin n)).edgeFinset \ F.edgeFinset) \ S,
              (1 - edgeFactor W x e)) := by
  let decF := ‹DecidableRel F.Adj›
  let _ : DecidableRel F.Adj := decF
  have hFtop : F.edgeFinset ⊆ (⊤ : SimpleGraph (Fin n)).edgeFinset :=
    SimpleGraph.edgeFinset_mono le_top
  refine Finset.sum_nbij'
    (fun G => G.edgeFinset \ F.edgeFinset)
    (fun S => SimpleGraph.fromEdgeSet (↑(F.edgeFinset ∪ S) : Set (Sym2 (Fin n))))
    ?_ ?_ ?_ ?_ ?_
  · intro G hG
    rw [Finset.mem_filter] at hG
    rw [Finset.mem_powerset]
    intro e he
    rw [Finset.mem_sdiff] at he ⊢
    exact ⟨SimpleGraph.edgeFinset_mono le_top he.1, he.2⟩
  · intro S hS
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [← SimpleGraph.edgeFinset_subset_edgeFinset,
      SimpleGraph.edgeFinset_fromEdgeSet_eq_of_subset_top]
    · exact Finset.subset_union_left
    · exact Finset.union_subset hFtop
        ((Finset.mem_powerset.mp hS).trans Finset.sdiff_subset)
  · intro G hG
    rw [Finset.mem_filter] at hG
    apply SimpleGraph.edgeFinset_inj.mp
    rw [SimpleGraph.edgeFinset_fromEdgeSet_eq_of_subset_top]
    · exact Finset.union_sdiff_of_subset (SimpleGraph.edgeFinset_mono hG.2)
    · exact Finset.union_subset hFtop
        (Finset.sdiff_subset.trans (SimpleGraph.edgeFinset_mono le_top))
  · intro S hS
    ext e
    simp only [Finset.mem_sdiff, SimpleGraph.mem_edgeFinset,
      SimpleGraph.edgeSet_fromEdgeSet, Set.mem_sdiff, Finset.mem_coe,
      Finset.mem_union, Sym2.mem_diagSet]
    have hSsub := Finset.mem_powerset.mp hS
    constructor
    · rintro ⟨⟨heF | heS, _⟩, hnF⟩
      · exact (hnF heF).elim
      · exact heS
    · intro heS
      have heSDiff := hSsub heS
      refine ⟨⟨Or.inr heS,
        (⊤ : SimpleGraph (Fin n)).not_isDiag_of_mem_edgeSet
          (SimpleGraph.mem_edgeFinset.mp (Finset.sdiff_subset heSDiff))⟩, ?_⟩
      intro heFset
      exact (Finset.mem_sdiff.mp heSDiff).2
        (SimpleGraph.mem_edgeFinset.mpr heFset)
  · intro G hG
    rw [Finset.mem_filter] at hG
    have hFG : F.edgeFinset ⊆ G.edgeFinset := SimpleGraph.edgeFinset_mono hG.2
    have hunion : F.edgeFinset ∪ (G.edgeFinset \ F.edgeFinset) = G.edgeFinset :=
      Finset.union_sdiff_of_subset hFG
    have hdisj : Disjoint F.edgeFinset (G.edgeFinset \ F.edgeFinset) :=
      Finset.disjoint_sdiff
    have hdiff :
        (⊤ : SimpleGraph (Fin n)).edgeFinset \ G.edgeFinset =
          ((⊤ : SimpleGraph (Fin n)).edgeFinset \ F.edgeFinset) \
            (G.edgeFinset \ F.edgeFinset) := by
      ext e
      simp only [Finset.mem_sdiff]
      tauto
    have hprod :
        (∏ e ∈ G.edgeFinset, edgeFactor W x e) =
          (∏ e ∈ F.edgeFinset, edgeFactor W x e) *
            ∏ e ∈ G.edgeFinset \ F.edgeFinset, edgeFactor W x e := by
      calc
        (∏ e ∈ G.edgeFinset, edgeFactor W x e) =
            ∏ e ∈ F.edgeFinset ∪ (G.edgeFinset \ F.edgeFinset), edgeFactor W x e := by
              exact congrArg
                (fun s : Finset (Sym2 (Fin n)) => ∏ e ∈ s, edgeFactor W x e) hunion.symm
        _ = _ := Finset.prod_union hdisj
    rw [sampleIntegrand_def, hprod, hdiff]
    ring

open Classical in
/-- At fixed vertex positions, summing the sampling integrand over all supergraphs of `F`
collapses to the homomorphism-density integrand of `F`. -/
private theorem sum_sampleIntegrand_supergraph {n : ℕ} (W : Graphon Ω μ)
    (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] (x : Fin n → Ω) :
    ∑ G : SimpleGraph (Fin n), (if F ≤ G then sampleIntegrand W G x else 0) =
      ∏ e ∈ F.edgeFinset, edgeFactor W x e := by
  let decF := ‹DecidableRel F.Adj›
  let _ : DecidableRel F.Adj := decF
  rw [← Finset.sum_filter, sum_sampleIntegrand_supergraph_bij, ← Finset.mul_sum,
    ← Finset.prod_add]
  simp

open Classical in
/-- The total mass of all sampled graphs containing a fixed graph `F` is its graphon
homomorphism density. Equivalently, the probability that every edge of `F` appears in the sample
is `t(F, W)`. -/
theorem sum_sampleMass_supergraph_eq_homDensity {n : ℕ} (W : Graphon Ω μ)
    (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] :
    ∑ G ∈ Finset.univ.filter (F ≤ ·), sampleMass W G = homDensity F W := by
  let decF := ‹DecidableRel F.Adj›
  let _ : DecidableRel F.Adj := decF
  calc
    (∑ G ∈ Finset.univ.filter (F ≤ ·), sampleMass W G) =
        ∫ x : Fin n → Ω,
          ∑ G ∈ Finset.univ.filter (F ≤ ·), sampleIntegrand W G x
            ∂Measure.pi fun _ => μ := by
              simp_rw [sampleMass_def]
              exact (integral_finsetSum _ fun G _ => integrable_sampleIntegrand W G).symm
    _ = ∫ x : Fin n → Ω, ∏ e ∈ F.edgeFinset, edgeFactor W x e
          ∂Measure.pi fun _ => μ := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
            simp only
            have h := sum_sampleIntegrand_supergraph W F x
            rw [← Finset.sum_filter] at h
            exact h
    _ = homDensity F W := (homDensity_def F W).symm

/-- The injective homomorphism density of a graphon sample is an unbiased estimator of the
graphon's homomorphism density, provided the sample has at least as many vertices as the pattern.
The size condition is exactly the nonvanishing condition for the falling-factorial denominator. -/
theorem injHomDensity_integral_sampleGraph (W : Graphon Ω μ) {V : Type*} [Fintype V]
    (F : SimpleGraph V) [DecidableRel F.Adj] {m : ℕ}
    (hkm : Fintype.card V ≤ m) :
    ∫ G, injHomDensity F G ∂sampleGraph W m = homDensity F W := by
  classical
  rw [integral_fintype Integrable.of_finite]
  simp_rw [Measure.real_def, sampleGraph_singleton,
    ENNReal.toReal_ofReal (sampleMass_nonneg W _), smul_eq_mul]
  simp_rw [injHomDensity_def, SimpleGraph.card_injective_hom_eq_sum_map_le]
  simp only [Fintype.card_fin]
  have hd : (m.descFactorial (Fintype.card V) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_pos.mpr hkm).ne'
  calc
    (∑ G : SimpleGraph (Fin m), sampleMass W G *
        ((∑ f : V ↪ Fin m, if F.map f ≤ G then 1 else 0) /
          (m.descFactorial (Fintype.card V) : ℝ))) =
        (∑ G : SimpleGraph (Fin m), ∑ f : V ↪ Fin m,
          if F.map f ≤ G then sampleMass W G else 0) /
            (m.descFactorial (Fintype.card V) : ℝ) := by
              simp_rw [Finset.sum_div, Finset.mul_sum]
              refine Finset.sum_congr rfl fun G _ => ?_
              exact Finset.sum_congr rfl fun f _ => by split <;> simp [div_eq_mul_inv]
    _ = (∑ f : V ↪ Fin m, ∑ G : SimpleGraph (Fin m),
          if F.map f ≤ G then sampleMass W G else 0) /
            (m.descFactorial (Fintype.card V) : ℝ) := by
              rw [Finset.sum_comm]
    _ = (∑ _f : V ↪ Fin m, homDensity F W) /
            (m.descFactorial (Fintype.card V) : ℝ) := by
              congr 1
              refine Finset.sum_congr rfl fun f _ => ?_
              rw [← Finset.sum_filter]
              exact (sum_sampleMass_supergraph_eq_homDensity W (F.map f)).trans
                (homDensity_map_embedding W F f)
    _ = homDensity F W := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_embedding_eq,
        Fintype.card_fin]
      exact mul_div_cancel_left₀ (homDensity F W) hd

end DenseGraphLimits

end TauCeti
