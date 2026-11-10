/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.HomDensity.Finite
public import TauCeti.Combinatorics.DenseGraphLimits.HomDensity.Structural
public import TauCeti.Combinatorics.DenseGraphLimits.Sampling.Finite
public import TauCeti.Combinatorics.SimpleGraph.Measurable
import TauCeti.Combinatorics.DenseGraphLimits.HomDensity.Closeness
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
* `TauCeti.DenseGraphLimits.integral_injHomDensity_eq_sum_div` — the average of the injective
  homomorphism density against any finite measure on host graphs, as an average over vertex
  embeddings of the mass of the hosts containing the embedded pattern;
* `TauCeti.DenseGraphLimits.integral_injHomDensity_eq_of_forall` — if every embedded copy of the
  pattern has the same host mass `c`, the average injective homomorphism density is `c`;
* `TauCeti.DenseGraphLimits.abs_integral_homDensityFin_sub_integral_injHomDensity_le` — under any
  probability measure on host graphs, the mean ordinary and injective homomorphism densities differ
  by at most `C(k, 2) / n`;
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

open Classical in
/-- Averaging the injective homomorphism density of a fixed pattern against any finite measure on
host graphs averages, over the vertex embeddings of the pattern, the mass of the hosts that contain
the embedded pattern. -/
theorem integral_injHomDensity_eq_sum_div {V W : Type*} [Fintype V] [Fintype W]
    (F : SimpleGraph V) (ν : Measure (SimpleGraph W)) [IsFiniteMeasure ν] :
    ∫ G, injHomDensity F G ∂ν =
      (∑ f : V ↪ W, ν.real {G | F.map f ≤ G}) /
        ((Fintype.card W).descFactorial (Fintype.card V) : ℝ) := by
  rw [integral_fintype Integrable.of_finite]
  simp_rw [injHomDensity_def, SimpleGraph.card_injective_hom_eq_sum_map_le, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero, smul_eq_mul, ← mul_div_assoc, Finset.mul_sum,
    mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_div, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [← Finset.sum_filter, sum_measureReal_singleton]
  congr 1
  ext G
  simp

/-- If every embedded copy of a pattern is contained in hosts of the same mass `c`, the average
injective homomorphism density of the pattern is `c`, provided the host has at least as many
vertices as the pattern. -/
theorem integral_injHomDensity_eq_of_forall {V W : Type*} [Fintype V] [Fintype W]
    (F : SimpleGraph V) (ν : Measure (SimpleGraph W)) {c : ℝ}
    (hVW : Fintype.card V ≤ Fintype.card W) (h : ∀ f : V ↪ W, ν.real {G | F.map f ≤ G} = c) :
    ∫ G, injHomDensity F G ∂ν = c := by
  classical
  have hd : ((Fintype.card W).descFactorial (Fintype.card V) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_pos.mpr hVW).ne'
  -- A host graph has nonzero density exactly when some embedded copy of the pattern lies in it.
  have hpos (G : SimpleGraph W) : injHomDensity F G ≠ 0 ↔ ∃ f : V ↪ W, F.map f ≤ G := by
    rw [injHomDensity_def, SimpleGraph.card_injective_hom_eq_sum_map_le]
    simp [hd]
  by_cases hinf : ∃ G, ν {G} = ⊤ ∧ ∃ f : V ↪ W, F.map f ≤ G
  · -- An atom of infinite mass carrying the pattern makes `c` and the integral both vanish.
    obtain ⟨G, hG, f, hf⟩ := hinf
    have hc : c = 0 := by
      rw [← h f, Measure.real, ENNReal.toReal_eq_zero_iff]
      exact Or.inr (top_unique (hG ▸ measure_mono fun x hx ↦ by
        rw [Set.mem_singleton_iff] at hx
        exact hx ▸ hf))
    rw [hc]
    refine integral_undef fun hint ↦ ?_
    have hfin := hint.2
    have hge : ‖injHomDensity F G‖ₑ * ν {G} ≤ ∫⁻ x, ‖injHomDensity F x‖ₑ ∂ν := by
      calc ‖injHomDensity F G‖ₑ * ν {G}
          = ∫⁻ x in {G}, ‖injHomDensity F x‖ₑ ∂ν :=
            (lintegral_singleton (fun x ↦ ‖injHomDensity F x‖ₑ) G).symm
        _ ≤ _ := setLIntegral_le_lintegral _ _
    rw [hG, ENNReal.mul_top (by simpa using (hpos G).2 ⟨f, hf⟩)] at hge
    exact hfin.ne (top_unique hge)
  · push Not at hinf
    let s : Set (SimpleGraph W) := {G | ν {G} ≠ ⊤}
    have hs : MeasurableSet s := (Set.toFinite s).measurableSet
    have hg0 : ∀ G, G ∉ s → injHomDensity F G = 0 := fun G hG ↦ by
      by_contra hne
      obtain ⟨f, hf⟩ := (hpos G).1 hne
      exact hinf G (not_not.1 hG) f hf
    have : IsFiniteMeasure (ν.restrict s) := ⟨by
      rw [Measure.restrict_apply_univ]
      have hsum := sum_measure_singleton (μ := ν) (s := (Set.toFinite s).toFinset)
      rw [Set.Finite.coe_toFinset] at hsum
      rw [← hsum]
      exact ENNReal.sum_lt_top.2 fun G hG ↦ lt_top_iff_ne_top.2 (by simpa [s] using hG)⟩
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hg0,
      integral_injHomDensity_eq_sum_div F (ν.restrict s)]
    have hS (f : V ↪ W) : (ν.restrict s).real {G | F.map f ≤ G} = c := by
      rw [← h f, Measure.real, Measure.real, Measure.restrict_apply' hs]
      congr 2
      refine Set.inter_eq_left.2 fun G hG ↦ ?_
      exact fun hG' ↦ hinf G hG' f hG
    rw [Finset.sum_congr rfl fun f _ ↦ hS f, Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
      Fintype.card_embedding_eq]
    exact mul_div_cancel_left₀ c hd

/-- Under any probability measure on host graphs, the mean ordinary and injective homomorphism
densities of a pattern differ by at most `C(k, 2) / n`, the union bound on the proportion of
non-injective vertex maps, where `k` and `n` are the numbers of pattern and host vertices. -/
theorem abs_integral_homDensityFin_sub_integral_injHomDensity_le {V W : Type*} [Fintype V]
    [Fintype W] (F : SimpleGraph V) (ν : Measure (SimpleGraph W)) [IsProbabilityMeasure ν] :
    |(∫ G, homDensityFin F G ∂ν) - ∫ G, injHomDensity F G ∂ν| ≤
      ((Fintype.card V).choose 2 : ℝ) / Fintype.card W := by
  rw [← integral_sub Integrable.of_finite Integrable.of_finite]
  calc
    |∫ G, homDensityFin F G - injHomDensity F G ∂ν|
        ≤ ∫ G, |homDensityFin F G - injHomDensity F G| ∂ν :=
      abs_integral_le_integral_abs
    _ ≤ ∫ _G, ((Fintype.card V).choose 2 : ℝ) / Fintype.card W ∂ν :=
      integral_mono Integrable.of_finite (integrable_const _) fun G =>
        homDensityFin_sub_injHomDensity_le F G
    _ = ((Fintype.card V).choose 2 : ℝ) / Fintype.card W := by simp

/-- The injective homomorphism density of a graphon sample is an unbiased estimator of the
graphon's homomorphism density, provided the sample has at least as many vertices as the pattern.
The size condition is exactly the nonvanishing condition for the falling-factorial denominator. -/
theorem integral_injHomDensity_sampleGraph (W : Graphon Ω μ) {V : Type*} [Fintype V]
    (F : SimpleGraph V) [DecidableRel F.Adj] {m : ℕ}
    (hkm : Fintype.card V ≤ m) :
    ∫ G, injHomDensity F G ∂sampleGraph W m = homDensity F W := by
  classical
  refine integral_injHomDensity_eq_of_forall F _ (by simpa using hkm) fun f => ?_
  have hset : {G : SimpleGraph (Fin m) | F.map f ≤ G} =
      ↑(Finset.univ.filter (F.map f ≤ ·)) := by
    ext G
    simp
  rw [hset, ← sum_measureReal_singleton]
  simp_rw [measureReal_def, sampleGraph_singleton, ENNReal.toReal_ofReal (sampleMass_nonneg W _)]
  exact (sum_sampleMass_supergraph_eq_homDensity W (F.map f)).trans
    (homDensity_map_embedding W F f)

end DenseGraphLimits

end TauCeti
