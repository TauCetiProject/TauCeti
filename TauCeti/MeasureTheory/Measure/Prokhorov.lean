/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

/-!
# Weak cluster limits of tight finite measures

This file contains a generic finite-measure extraction lemma based on Mathlib's Prokhorov
compactness theorem for finite measures. It has no real-line support condition and no
normalization step: tightness and a uniform mass bound place the sequence in a compact set of
`FiniteMeasure`s, and compactness gives a weak cluster limit.

## Main declarations

* `TauCeti.finite_measure_cluster_limit`: a tight, mass-bounded sequence of finite measures has a
  weak cluster limit along an ultrafilter below `atTop`.
* `TauCeti.finite_measure_subseq_limit`: the corresponding subsequence form when the weak topology
  on `FiniteMeasure α` is first-countable.

## References

* Roadmap: `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part B (Bernstein theorem milestone).
-/

public section

open MeasureTheory Set Filter Topology
open scoped NNReal Topology

namespace TauCeti

variable {α : Type*} [MeasurableSpace α] [TopologicalSpace α]
  [T2Space α] [BorelSpace α]

/-- A tight, uniformly mass-bounded sequence of finite measures has a weak cluster limit.

The compactness input is Mathlib's
`isCompact_setOf_finiteMeasure_mass_le_compl_isCompact_le`; the conclusion is phrased as
convergence along an ultrafilter `U ≤ atTop`, which is enough for diagonal limit arguments and does
not require a metrizability instance for `FiniteMeasure α`. -/
lemma finite_measure_cluster_limit
    (σ : ℕ → Measure α) (C : ℝ)
    [hfin : ∀ n, IsFiniteMeasure (σ n)]
    (hmass : ∀ n, (σ n) univ ≤ ENNReal.ofReal C)
    (htight : ∀ ε : ℝ, 0 < ε →
      ∃ K : Set α, IsCompact K ∧ ∀ n, (σ n) Kᶜ ≤ ENNReal.ofReal ε) :
    ∃ (μ₀ : Measure α) (U : Ultrafilter ℕ), (U : Filter ℕ) ≤ atTop ∧ IsFiniteMeasure μ₀ ∧
      μ₀ univ ≤ ENNReal.ofReal C ∧
      ∀ g : BoundedContinuousFunction α ℝ,
        Tendsto (fun n => ∫ x, g x ∂(σ n)) (U : Filter ℕ)
          (nhds (∫ x, g x ∂μ₀)) := by
  let σf : ℕ → FiniteMeasure α := fun n => ⟨σ n, hfin n⟩
  let Cnn : ℝ≥0 := Real.toNNReal C
  obtain ⟨u, -, hu_pos, hu_lim⟩ :
      ∃ u : ℕ → ℝ≥0, StrictAnti u ∧ (∀ n, 0 < u n) ∧ Tendsto u atTop (𝓝 0) :=
    exists_seq_strictAnti_tendsto 0
  have hchoose : ∀ j, ∃ K : Set α, IsCompact K ∧
      ∀ n, (σ n) Kᶜ ≤ (u j : ENNReal) := by
    intro j
    obtain ⟨K, hK, htail⟩ := htight (u j : ℝ) (by exact_mod_cast hu_pos j)
    refine ⟨K, hK, fun n => ?_⟩
    simpa using htail n
  choose K hK_comp hK_tail using hchoose
  let Kacc : ℕ → Set α := Set.accumulate K
  let S : Set (FiniteMeasure α) :=
    {μ | μ.mass ≤ Cnn ∧ ∀ j, μ (Kacc j)ᶜ ≤ u j}
  have hKacc_comp : ∀ j, IsCompact (Kacc j) := by
    intro j
    exact isCompact_accumulate hK_comp j
  have hcompact : IsCompact S := by
    simpa [S] using
      isCompact_setOf_finiteMeasure_mass_le_compl_isCompact_le
        (E := α) (C := Cnn) (u := u) (K := Kacc) hu_lim hKacc_comp
        (Or.inr Set.monotone_accumulate)
  have hσ_mem : ∀ n, σf n ∈ S := by
    intro n
    constructor
    · dsimp [σf, S, Cnn, FiniteMeasure.mass]
      exact ENNReal.toNNReal_mono ENNReal.ofReal_ne_top (hmass n)
    · intro j
      have hsubset : (Kacc j)ᶜ ⊆ (K j)ᶜ :=
        compl_subset_compl.mpr (Set.subset_accumulate (s := K) (x := j))
      have htail : (σ n) (Kacc j)ᶜ ≤ (u j : ENNReal) :=
        (measure_mono hsubset).trans (hK_tail j n)
      exact ENNReal.coe_le_coe.mp (by simpa [σf] using htail)
  have hmap_le : map σf atTop ≤ 𝓟 S :=
    tendsto_principal.mpr (Eventually.of_forall hσ_mem)
  obtain ⟨μf, hμfS, hcluster⟩ := hcompact hmap_le
  have hmapcluster : MapClusterPt μf atTop σf := hcluster
  obtain ⟨U, hUle, hUtend⟩ := mapClusterPt_iff_ultrafilter.mp hmapcluster
  refine ⟨(μf : Measure α), U, hUle, inferInstance, ?_, ?_⟩
  · have hle : (μf.mass : ENNReal) ≤ (Cnn : ENNReal) := ENNReal.coe_le_coe.mpr hμfS.1
    rw [← FiniteMeasure.ennreal_mass]
    simpa [Cnn, ENNReal.ofNNReal_toNNReal] using hle
  · intro g
    have hweak :=
      (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hUtend) g
    simpa [σf] using hweak

/-- Sequential form of `finite_measure_cluster_limit` when `FiniteMeasure α` is first-countable. -/
lemma finite_measure_subseq_limit
    [FirstCountableTopology (FiniteMeasure α)]
    (σ : ℕ → Measure α) (C : ℝ)
    [hfin : ∀ n, IsFiniteMeasure (σ n)]
    (hmass : ∀ n, (σ n) univ ≤ ENNReal.ofReal C)
    (htight : ∀ ε : ℝ, 0 < ε →
      ∃ K : Set α, IsCompact K ∧ ∀ n, (σ n) Kᶜ ≤ ENNReal.ofReal ε) :
    ∃ (μ₀ : Measure α) (φ : ℕ → ℕ), IsFiniteMeasure μ₀ ∧ StrictMono φ ∧
      μ₀ univ ≤ ENNReal.ofReal C ∧
      ∀ g : BoundedContinuousFunction α ℝ,
        Tendsto (fun k => ∫ x, g x ∂(σ (φ k))) atTop
          (nhds (∫ x, g x ∂μ₀)) := by
  obtain ⟨μ₀, U, hUle, hμ₀_fin, hmass_μ₀, hweakU⟩ :=
    finite_measure_cluster_limit (α := α) σ C hmass htight
  let σf : ℕ → FiniteMeasure α := fun n => ⟨σ n, hfin n⟩
  let μf : FiniteMeasure α := ⟨μ₀, hμ₀_fin⟩
  have hUtend : Tendsto σf (U : Filter ℕ) (nhds μf) := by
    rw [FiniteMeasure.tendsto_iff_forall_integral_tendsto]
    intro g
    simpa [σf, μf] using hweakU g
  have hclusterU : MapClusterPt μf (U : Filter ℕ) σf := hUtend.mapClusterPt
  have hcluster : MapClusterPt μf atTop σf := hclusterU.mono hUle
  obtain ⟨φ, hφ, hφ_tendsto⟩ := hcluster.tendsto_subseq
  refine ⟨μ₀, φ, hμ₀_fin, hφ, hmass_μ₀, fun g => ?_⟩
  have hweak :=
    (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hφ_tendsto) g
  simpa [σf, μf, Function.comp_def] using hweak

end TauCeti
