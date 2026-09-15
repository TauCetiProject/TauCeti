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
* `TauCeti.DenseGraphLimits.integral_injHomDensity_sampleGraph` — injective homomorphism density is
  unbiased under graphon sampling.

## References

* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012), Sections
  5.2 and 10.2.
* C. Freer, `cameronfreer/graphon` at commit
  `6eccca5bbe5c9df46d7129bf59575b8b9b1d6699`, Apache-2.0, `Graphon/Sampling.lean`. The
  supergraph-mass proof is adapted from its Boolean-cube argument to Tau Ceti's strict graphon
  carrier.
-/

-- The statement of `integral_injHomDensity_sampleGraph` follows the `E_{G(m,W)}[t₀(F, ·)] =
-- t(F, W)` signature written down in the Tau Ceti `DenseGraphLimits` roadmap's `Suggested.lean`.

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace DenseGraphLimits

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

open Classical in
/-- The total mass of all sampled graphs containing a fixed graph `F` is its graphon
homomorphism density. Equivalently, the probability that every edge of `F` appears in the sample
is `t(F, W)`. -/
theorem sum_sampleMass_supergraph_eq_homDensity {n : ℕ} (W : Graphon Ω μ)
    (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] :
    ∑ G ∈ Finset.univ.filter (F ≤ ·), sampleMass W G = homDensity F W := by
  let decF := ‹DecidableRel F.Adj›
  let _ : DecidableRel F.Adj := decF
  have hfilter : Finset.univ.filter (F ≤ ·) =
      Finset.univ.filter
        (fun G : SimpleGraph (Fin n) => (F.edgeFinset : Set (Sym2 (Fin n))) ⊆ G.edgeSet) :=
    Finset.filter_congr fun G _ => by
      rw [SimpleGraph.coe_edgeFinset, SimpleGraph.edgeSet_subset_edgeSet]
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
            -- The supergraphs of `F` are exactly the graphs whose edges include those of `F`.
            rw [hfilter]
            exact sum_sampleIntegrand_superset_eq_prod_edgeFactor W F.edgeFinset
              (SimpleGraph.edgeFinset_mono le_top) x
    _ = homDensity F W := (homDensity_def F W).symm

/-- The injective homomorphism density of a graphon sample is an unbiased estimator of the
graphon's homomorphism density, provided the sample has at least as many vertices as the pattern.
The size condition is exactly the nonvanishing condition for the falling-factorial denominator. -/
theorem integral_injHomDensity_sampleGraph (W : Graphon Ω μ) {V : Type*} [Fintype V]
    (F : SimpleGraph V) [DecidableRel F.Adj] {m : ℕ}
    (hkm : Fintype.card V ≤ m) :
    ∫ G, injHomDensity F G ∂sampleGraph W m = homDensity F W := by
  classical
  rw [integral_fintype Integrable.of_finite]
  simp_rw [Measure.real_def, sampleGraph_singleton,
    ENNReal.toReal_ofReal (sampleMass_nonneg W _), smul_eq_mul]
  simp_rw [injHomDensity_def, SimpleGraph.card_injective_hom_eq_sum_map_le, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
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
