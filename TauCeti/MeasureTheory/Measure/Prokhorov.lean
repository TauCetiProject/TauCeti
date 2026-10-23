/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.Topology.MetricSpace.Polish

/-!
# Prokhorov compactness lemmas for sequences of measures

This file contains generic consequences of Mathlib's Prokhorov compactness theorem. For finite
measures, tightness and a uniform mass bound give a weak cluster limit without a real-line support
condition or normalization step. For probability measures on a Polish space, a weakly convergent
sequence is tight.

## Main declarations

* `TauCeti.isCompact_closure_of_isTightMeasureSet_of_mass_le`: Prokhorov's theorem for finite
  measures, a tight set with uniformly bounded mass has compact closure.
* `TauCeti.finite_measure_cluster_limit`: a tight, mass-bounded sequence of finite measures has a
  weak cluster limit along an ultrafilter below `atTop`.
* `TauCeti.finite_measure_subseq_limit`: the corresponding subsequence form when the weak topology
  on `FiniteMeasure α` is first-countable.
* `TauCeti.isTightMeasureSet_range_of_tendsto`: a weakly convergent sequence of probability
  measures on a Polish space is tight.

## References

* Roadmap: `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part B (Bernstein theorem milestone).
* Roadmap: `TauCetiRoadmap/OptimalTransport/README.md`, Layer 1, item 6 (stability).
-/

public section

open MeasureTheory Set Filter Topology
open scoped NNReal Topology

namespace TauCeti

variable {α : Type*} [MeasurableSpace α] [TopologicalSpace α]
  [T2Space α] [BorelSpace α]

/-- **Prokhorov's theorem for finite measures.** A tight set of finite measures with uniformly
bounded total mass has compact closure in the topology of weak convergence.

This is the finite-measure counterpart of Mathlib's `isCompact_closure_of_isTightMeasureSet`
for probability measures. -/
theorem isCompact_closure_of_isTightMeasureSet_of_mass_le {S : Set (FiniteMeasure α)} {C : ℝ≥0}
    (hTight : IsTightMeasureSet {(μ : Measure α) | μ ∈ S}) (hmass : ∀ μ ∈ S, μ.mass ≤ C) :
    IsCompact (closure S) := by
  -- Choose a positive sequence decreasing to zero; these values are the tail tolerances in
  -- Prokhorov's compact set criterion.
  obtain ⟨u, -, hu_pos, hu_lim⟩ :
      ∃ u : ℕ → ℝ≥0, StrictAnti u ∧ (∀ n, 0 < u n) ∧ Tendsto u atTop (𝓝 0) :=
    exists_seq_strictAnti_tendsto 0
  have hchoose : ∀ j, ∃ K : Set α, IsCompact K ∧ ∀ μ ∈ S, (μ : Measure α) Kᶜ ≤ u j := fun j => by
    obtain ⟨K, hK, htail⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp hTight
      (u j : ENNReal) (by exact_mod_cast hu_pos j)
    exact ⟨K, hK, fun μ hμ => htail μ ⟨μ, hμ, rfl⟩⟩
  choose K hK_comp hK_tail using hchoose
  -- Accumulating the compact sets supplied by tightness gives the monotone exhaustion that
  -- Mathlib's Prokhorov criterion expects.
  refine (isCompact_setOfPred_finiteMeasure_mass_le_compl_isCompact_le (E := α) C hu_lim
    (isCompact_accumulate hK_comp) (Or.inr Set.monotone_accumulate)).closure_of_subset
    fun μ hμ => ⟨hmass μ hμ, fun j => ENNReal.coe_le_coe.mp ?_⟩
  simpa using (measure_mono (compl_subset_compl.mpr
    (Set.subset_accumulate (s := K) (x := j)))).trans (hK_tail j μ hμ)

/-- A tight, uniformly mass-bounded sequence of finite measures has a weak cluster limit.

Given tightness of the sequence and a common total-mass bound, the conclusion is a finite limiting
measure with the same mass bound and weak convergence of all bounded-continuous test-function
integrals along an ultrafilter `U ≤ atTop`; no first-countability assumption on `FiniteMeasure α`
is needed. -/
lemma finite_measure_cluster_limit (σ : ℕ → Measure α) (C : ℝ≥0)
    (hmass : ∀ n, (σ n) univ ≤ (C : ENNReal)) (hTight : IsTightMeasureSet (Set.range σ)) :
    ∃ (μ₀ : Measure α) (U : Ultrafilter ℕ), (U : Filter ℕ) ≤ atTop ∧ IsFiniteMeasure μ₀ ∧
      μ₀ univ ≤ (C : ENNReal) ∧
      ∀ g : BoundedContinuousFunction α ℝ,
        Tendsto (fun n => ∫ x, g x ∂(σ n)) (U : Filter ℕ)
          (nhds (∫ x, g x ∂μ₀)) := by
  -- First coerce the sequence to `FiniteMeasure`; the uniform mass bound supplies finiteness.
  have hfin : ∀ n, IsFiniteMeasure (σ n) := fun n =>
    ⟨(hmass n).trans_lt ENNReal.coe_lt_top⟩
  let σf : ℕ → FiniteMeasure α := fun n => ⟨σ n, hfin n⟩
  have hσf_mass : range σf ⊆ {μ | μ.mass ≤ C} := by
    rintro - ⟨n, rfl⟩
    rw [mem_ofPred_eq, ← ENNReal.coe_le_coe, FiniteMeasure.ennreal_mass]
    exact hmass n
  have hcompact : IsCompact (closure (range σf)) :=
    isCompact_closure_of_isTightMeasureSet_of_mass_le
      (hTight.subset (by rintro - ⟨-, ⟨n, rfl⟩, rfl⟩; exact ⟨n, rfl⟩)) hσf_mass
  -- Compactness gives a cluster point and an ultrafilter below `atTop` along which `σf`
  -- converges weakly.
  obtain ⟨μf, hμf, hcluster⟩ := hcompact (f := map σf atTop)
    (tendsto_principal.mpr (.of_forall fun n => subset_closure (mem_range_self n)))
  obtain ⟨U, hUle, hUtend⟩ := mapClusterPt_iff_ultrafilter.mp hcluster
  refine ⟨(μf : Measure α), U, hUle, inferInstance, ?_, ?_⟩
  -- Finally unwrap the closure membership into the mass bound and weak convergence of
  -- integrals against bounded continuous test functions.
  · have hle : μf.mass ≤ C := closure_minimal hσf_mass
      (isClosed_le FiniteMeasure.continuous_mass continuous_const) hμf
    rw [← FiniteMeasure.ennreal_mass]
    exact_mod_cast hle
  · intro g
    have hweak :=
      (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hUtend) g
    simpa [σf] using hweak

/-- Sequential form of `finite_measure_cluster_limit` when `FiniteMeasure α` is first-countable. -/
lemma finite_measure_subseq_limit [FirstCountableTopology (FiniteMeasure α)]
    (σ : ℕ → Measure α) (C : ℝ≥0) (hmass : ∀ n, (σ n) univ ≤ (C : ENNReal))
    (hTight : IsTightMeasureSet (Set.range σ)) :
    ∃ (μ₀ : Measure α) (φ : ℕ → ℕ), IsFiniteMeasure μ₀ ∧ StrictMono φ ∧
      μ₀ univ ≤ (C : ENNReal) ∧
      ∀ g : BoundedContinuousFunction α ℝ,
        Tendsto (fun k => ∫ x, g x ∂(σ (φ k))) atTop
          (nhds (∫ x, g x ∂μ₀)) := by
  -- Start from the ultrafilter cluster limit supplied by compactness.
  obtain ⟨μ₀, U, hUle, hμ₀_fin, hmass_μ₀, hweakU⟩ :=
    finite_measure_cluster_limit (α := α) σ C hmass hTight
  -- Repackage the sequence and limit as finite measures so that weak convergence can be read
  -- through bounded-continuous integrals.
  have hfin : ∀ n, IsFiniteMeasure (σ n) := fun n =>
    ⟨(hmass n).trans_lt ENNReal.coe_lt_top⟩
  let σf : ℕ → FiniteMeasure α := fun n => ⟨σ n, hfin n⟩
  let μf : FiniteMeasure α := ⟨μ₀, hμ₀_fin⟩
  have hUtend : Tendsto σf (U : Filter ℕ) (nhds μf) := by
    rw [FiniteMeasure.tendsto_iff_forall_integral_tendsto]
    intro g
    simpa [σf, μf] using hweakU g
  have hclusterU : MapClusterPt μf (U : Filter ℕ) σf := hUtend.mapClusterPt
  have hcluster : MapClusterPt μf atTop σf := hclusterU.mono hUle
  -- First countability turns the cluster point into an ordinary subsequential limit.
  obtain ⟨φ, hφ, hφ_tendsto⟩ := hcluster.tendsto_subseq
  refine ⟨μ₀, φ, hμ₀_fin, hφ, hmass_μ₀, fun g => ?_⟩
  have hweak :=
    (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hφ_tendsto) g
  -- `hweak` is stated through the `FiniteMeasure` integral coercion; `change` reads it back as
  -- the plain Bochner integral against the underlying measures, which is the statement wanted.
  change Tendsto (fun k => ∫ x, g x ∂σ (φ k)) atTop (𝓝 (∫ x, g x ∂μ₀)) at hweak
  exact hweak

section ProbabilityMeasure

variable [PolishSpace α] {μs : ℕ → ProbabilityMeasure α} {μ : ProbabilityMeasure α}

omit [T2Space α] in
/-- **A weakly convergent sequence of probability measures on a Polish space is tight.** -/
theorem isTightMeasureSet_range_of_tendsto (hμ : Tendsto μs atTop (𝓝 μ)) :
    IsTightMeasureSet (Set.range fun n ↦ (μs n).toMeasure) := by
  -- Prokhorov's converse asks for a complete metric; a Polish topology supplies one.
  let : MetricSpace α := TopologicalSpace.completelyMetrizableMetric α
  have : CompleteSpace α := TopologicalSpace.complete_completelyMetrizableMetric α
  have hcompact : IsCompact (insert μ (Set.range μs)) := hμ.isCompact_insert_range
  refine (MeasureTheory.isTightMeasureSet_of_isCompact_closure
    (S := insert μ (Set.range μs)) (by rwa [hcompact.isClosed.closure_eq])).subset ?_
  rintro - ⟨n, rfl⟩
  exact ⟨μs n, mem_insert_of_mem _ (mem_range_self n), rfl⟩

end ProbabilityMeasure

end TauCeti
