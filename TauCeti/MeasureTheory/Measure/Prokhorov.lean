/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
public import Mathlib.MeasureTheory.Integral.CompactlySupported
public import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.MetricSpace.Polish
import TauCeti.MeasureTheory.Measure.LevyProkhorovMetric
import TauCeti.MeasureTheory.Measure.Tight.Basic
import TauCeti.MeasureTheory.Measure.Tight.ContinuousWeight
import TauCeti.Topology.Compactness.Compact

/-!
# Prokhorov compactness lemmas for sequences of measures

This file contains generic consequences of Mathlib's Prokhorov compactness theorem. For finite
measures, tightness and a uniform mass bound give a weak cluster limit without a real-line support
condition or normalization step. The extraction lemmas take a family of measures that only
frequently lies in a tight, mass-bounded set: the other terms may have infinite mass. For
measures with uniformly bounded masses on compact sets, weighting by a positive continuous
function that decays fast enough along a compact exhaustion makes them tight with bounded mass
(`TauCeti.exists_isTightMeasureSet_withDensity_of_iSup_measure_ne_top`), which gives vague
compactness. For probability measures on a Polish space, a weakly convergent
sequence is tight.

## Main declarations

* `TauCeti.isCompact_closure_of_isTightMeasureSet_of_mass_le`: Prokhorov's theorem for finite
  measures, a tight set with uniformly bounded mass has compact closure.
* `TauCeti.exists_tendsto_finiteMeasure_of_eventually_measure_compl_eq_zero`: finite measures
  eventually carried by a compact set, with bounded mass, converge along an ultrafilter to a finite
  measure carried by that set.
* `TauCeti.exists_ultrafilter_tendsto_integral_of_isTightMeasureSet`: a family of Borel measures
  on a Hausdorff space that frequently lies in a tight, uniformly mass-bounded set has a finite
  weak cluster limit along an ultrafilter below the filter, along which the family lies in the
  set.
* `TauCeti.exists_subseq_tendsto_integral_of_isTightMeasureSet`: the corresponding subsequence
  form on a metrizable space; the subsequence lies in the set and has a finite weak limit.
* `TauCeti.exists_subseq_tendsto_integral_of_withDensity`: a sequence of Borel measures on a
  metrizable space whose weightings by a strictly positive continuous function frequently lie in
  a tight, uniformly mass-bounded set has a subsequence converging against compactly supported
  continuous functions to a locally finite measure.
* `TauCeti.exists_subseq_tendsto_integral_of_iSup_measure_ne_top`: vague compactness, a sequence
  of Borel measures on a locally compact, σ-compact, metrizable space that frequently lies in a
  set of measures with uniformly bounded masses on every compact set has a subsequence in the set
  converging vaguely to a locally finite measure.
* `TauCeti.isTightMeasureSet_range_of_tendsto`: a weakly convergent sequence of probability
  measures on a Polish space is tight.
-/

public section

open MeasureTheory Set Filter Topology TopologicalSpace
open scoped ENNReal NNReal Topology

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

/-- **Prokhorov's theorem along an ultrafilter, for measures carried by a compact set.** Finite
measures eventually carried by a compact set `K`, with mass eventually at most `C`, converge along
an ultrafilter to a finite measure carried by `K`. -/
theorem exists_tendsto_finiteMeasure_of_eventually_measure_compl_eq_zero {ι : Type*}
    {U : Ultrafilter ι} {μs : ι → FiniteMeasure α} {K : Set α} (hK : IsCompact K) {C : ℝ}
    (h : ∀ᶠ i in U, (μs i : Measure α) Kᶜ = 0 ∧ (μs i : Measure α).real univ ≤ C) :
    ∃ μ : FiniteMeasure α, (μ : Measure α) Kᶜ = 0 ∧ Tendsto μs U (𝓝 μ) := by
  obtain ⟨μ, ⟨-, hμK⟩, hμ⟩ := IsCompact.exists_tendsto_of_eventually_mem
    (isCompact_setOfPred_finiteMeasure_le_of_isCompact C.toNNReal hK) <| h.mono fun i hi =>
      ⟨NNReal.le_toNNReal_of_coe_le (FiniteMeasure.measureReal_eq_coe_coeFn.symm.trans_le hi.2),
        (FiniteMeasure.null_iff_toMeasure_null _ _).2 hi.1⟩
  exact ⟨μ, (FiniteMeasure.null_iff_toMeasure_null _ _).1 hμK, hμ⟩

/-- **Prokhorov's theorem along an ultrafilter.** A family of Borel measures on a Hausdorff space
that frequently lies, along a filter `l`, in a tight set `S` with uniformly bounded mass has a weak
cluster limit along an ultrafilter `U ≤ l`, along which the family eventually lies in `S`.

The limit is a finite measure with the same mass bound, and the integrals of every bounded
continuous function converge along `U`; no first-countability assumption on `FiniteMeasure α` is
needed. The members of the family outside `S` are unconstrained and may have infinite mass. -/
lemma exists_ultrafilter_tendsto_integral_of_isTightMeasureSet {ι : Type*} (σ : ι → Measure α)
    (l : Filter ι) {S : Set (Measure α)} (C : ℝ≥0) (hmass : ∀ μ ∈ S, μ univ ≤ C)
    (hTight : IsTightMeasureSet S) (hσ : ∃ᶠ i in l, σ i ∈ S) :
    ∃ (μ₀ : Measure α) (U : Ultrafilter ι), ↑U ≤ l ∧ (∀ᶠ i in U, σ i ∈ S) ∧
      IsFiniteMeasure μ₀ ∧ μ₀ univ ≤ C ∧ ∀ g : BoundedContinuousFunction α ℝ,
        Tendsto (fun i => ∫ x, g x ∂σ i) U (𝓝 (∫ x, g x ∂μ₀)) := by
  -- The members of `S` are finite measures, and their closure in `FiniteMeasure α` is compact.
  let Sf : Set (FiniteMeasure α) := {μ | (μ : Measure α) ∈ S}
  have hSf_mass : Sf ⊆ {μ | μ.mass ≤ C} := fun μ hμ => by
    rw [mem_ofPred_eq, ← ENNReal.coe_le_coe, FiniteMeasure.ennreal_mass]
    exact hmass _ hμ
  have hcompact : IsCompact (closure Sf) := isCompact_closure_of_isTightMeasureSet_of_mass_le
    (hTight.subset (by rintro - ⟨μ, hμ, rfl⟩; exact hμ)) hSf_mass
  -- Index by the subtype of the `i` with `σ i ∈ S`; the filter `l` restricts to it because these
  -- indices are frequent in `l`.
  let s : Set ι := {i | σ i ∈ S}
  have : (comap ((↑) : s → ι) l).NeBot :=
    comap_neBot_iff_frequently.2 (by rwa [Subtype.range_coe])
  let σf : s → FiniteMeasure α := fun i => ⟨σ i, ⟨(hmass _ i.property).trans_lt ENNReal.coe_lt_top⟩⟩
  -- Along an ultrafilter below the restricted filter, `σf` converges weakly in the compact set.
  obtain ⟨U, hUle⟩ := Ultrafilter.exists_le (comap ((↑) : s → ι) l)
  obtain ⟨μf, hμf, hUtend⟩ := hcompact.exists_tendsto_of_eventually_mem (U := U) (u := σf)
    (.of_forall fun i => subset_closure i.property)
  refine ⟨μf, U.map (↑), map_le_iff_le_comap.2 hUle, ?_, inferInstance, ?_, fun g => ?_⟩
  · rw [Ultrafilter.coe_map]
    exact eventually_map.2 (.of_forall fun i => i.property)
  · rw [← FiniteMeasure.ennreal_mass, ENNReal.coe_le_coe]
    exact closure_minimal hSf_mass (isClosed_le FiniteMeasure.continuous_mass continuous_const) hμf
  · rw [Ultrafilter.coe_map, tendsto_map'_iff]
    simpa only [σf, Function.comp_def, FiniteMeasure.toMeasure_mk] using
      FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hUtend g

/-- **Prokhorov's theorem for sequences.** A sequence of Borel measures on a metrizable space
that frequently lies in a tight set `S` with uniformly bounded mass has a subsequence in `S` that
converges weakly. The limit is a finite measure with the common mass bound. The terms outside `S`
are unconstrained and may have infinite mass. -/
lemma exists_subseq_tendsto_integral_of_isTightMeasureSet [PseudoMetrizableSpace α]
    (σ : ℕ → Measure α) {S : Set (Measure α)} (C : ℝ≥0) (hmass : ∀ μ ∈ S, μ univ ≤ C)
    (hTight : IsTightMeasureSet S) (hσ : ∃ᶠ n in atTop, σ n ∈ S) :
    ∃ (μ₀ : Measure α) (φ : ℕ → ℕ), IsFiniteMeasure μ₀ ∧ StrictMono φ ∧ (∀ k, σ (φ k) ∈ S) ∧
      μ₀ univ ≤ C ∧ ∀ g : BoundedContinuousFunction α ℝ,
        Tendsto (fun k => ∫ x, g x ∂σ (φ k)) atTop (𝓝 (∫ x, g x ∂μ₀)) := by
  -- Pass to a subsequence `σ ∘ ψ` in `S`.
  obtain ⟨ψ, hψ, hψS⟩ := extraction_of_frequently_atTop hσ
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℕ → FiniteMeasure α, ∀ n, (ρ n : Measure α) = σ (ψ n) :=
    ⟨fun n => ⟨σ (ψ n), ⟨(hmass _ (hψS n)).trans_lt ENNReal.coe_lt_top⟩⟩, fun _ => rfl⟩
  -- Every measure of `S` lives on the separable measurable set `T = ⋃ j, K j`, a union of compact
  -- sets with uniform tail bounds. We find the limit on `T`, where `FiniteMeasure T` is first
  -- countable.
  obtain ⟨K, hKc, hKS, hTS⟩ := hTight.exists_seq_isCompact_measure_compl_le
  let T : Set α := ⋃ j, K j
  have hT : MeasurableSet T := .iUnion fun j => (hKc j).isClosed.measurableSet
  have : SeparableSpace T := (IsSeparable.iUnion fun j => (hKc j).isSeparable).separableSpace
  -- The restrictions `τ n` of `σ (ψ n)` to `T` push forward back to `σ (ψ n)`.
  let τ : ℕ → FiniteMeasure T := fun n => (ρ n).comap (↑)
  have hτ (n : ℕ) : ((τ n).map Subtype.val : Measure α) = σ (ψ n) := by
    dsimp only [τ]
    rw [FiniteMeasure.toMeasure_map, FiniteMeasure.toMeasure_comap, hρ, map_comap_subtypeVal hT,
      Measure.restrict_eq_self_of_ae_mem (mem_ae_iff.2 (hTS _ (hψS n)))]
  have hτ_mass : range τ ⊆ {ν | ν.mass ≤ C} := by
    rintro - ⟨n, rfl⟩
    rw [mem_ofPred_eq]
    refine (FiniteMeasure.mass_comap_le _ (ρ n)).trans ?_
    rw [← ENNReal.coe_le_coe, FiniteMeasure.ennreal_mass, hρ]
    exact hmass _ (hψS n)
  have hτTight : IsTightMeasureSet {(ν : Measure T) | ν ∈ range τ} := by
    refine isTightMeasureSet_iff_exists_isCompact_measure_compl_le.2 fun ε hε => ?_
    obtain ⟨j, hj⟩ := ENNReal.exists_inv_nat_lt hε.ne'
    refine ⟨(↑) ⁻¹' K j, IsInducing.subtypeVal.isCompact_preimage' (hKc j)
      (by rw [Subtype.range_coe]; exact subset_iUnion K j), ?_⟩
    rintro - ⟨-, ⟨n, rfl⟩, rfl⟩
    rw [← preimage_compl, ← Measure.map_apply measurable_subtypeVal
      (hKc j).isClosed.measurableSet.compl, ← FiniteMeasure.toMeasure_map, hτ n]
    exact (hKS j _ (hψS n)).trans hj.le
  -- Prokhorov compactness in the first countable space `FiniteMeasure T` gives a subsequence of
  -- `τ` converging to some `ν`.
  obtain ⟨ν, hν, φ, hφ, hlim⟩ :=
    (isCompact_closure_of_isTightMeasureSet_of_mass_le hτTight hτ_mass).tendsto_subseq
      fun n => subset_closure ⟨n, rfl⟩
  -- Push the limit forward to `α`.
  have hmap := FiniteMeasure.tendsto_map_of_tendsto_of_continuous _ _ hlim continuous_subtypeVal
  refine ⟨ν.map Subtype.val, ψ ∘ φ, inferInstance, hψ.comp hφ, fun k => hψS (φ k), ?_,
    fun g => ?_⟩
  · rw [← FiniteMeasure.ennreal_mass, ENNReal.coe_le_coe]
    exact (FiniteMeasure.mass_map_le measurable_subtypeVal.aemeasurable).trans <|
      closure_minimal hτ_mass (isClosed_le FiniteMeasure.continuous_mass continuous_const) hν
  · simpa only [Function.comp_apply, hτ] using
      FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hmap g

open scoped CompactlySupported in
/-- If weighting by a strictly positive continuous function frequently puts a sequence of Borel
measures on a metrizable space into a tight set `S` with uniformly bounded mass, then the sequence
has a subsequence whose weightings lie in `S`, with a locally finite limit against every
compactly supported continuous test function. The unweighted measures may have infinite mass. -/
theorem exists_subseq_tendsto_integral_of_withDensity [PseudoMetrizableSpace α]
    (σ : ℕ → Measure α) (w : α → ℝ≥0) (hw : Continuous w) (hpos : ∀ x, 0 < w x)
    {S : Set (Measure α)} (C : ℝ≥0) (hmass : ∀ μ ∈ S, μ univ ≤ C) (hTight : IsTightMeasureSet S)
    (hσ : ∃ᶠ n in atTop, ((σ n).withDensity fun x => w x) ∈ S) :
    ∃ (μ : Measure α) (φ : ℕ → ℕ), IsLocallyFiniteMeasure μ ∧ StrictMono φ ∧
      (∀ k, ((σ (φ k)).withDensity fun x => w x) ∈ S) ∧
      ∀ f : C_c(α, ℝ), Tendsto (fun k => ∫ x, f x ∂σ (φ k)) atTop (𝓝 (∫ x, f x ∂μ)) := by
  obtain ⟨ρ, φ, hρ, hφ, hφS, -, hlim⟩ :=
    exists_subseq_tendsto_integral_of_isTightMeasureSet (fun n => (σ n).withDensity fun x => w x)
      C hmass hTight hσ
  let μ : Measure α := ρ.withDensity fun x => ((w x)⁻¹ : ℝ≥0)
  have hwInv : Continuous fun x => (w x)⁻¹ := hw.inv₀ fun x => (hpos x).ne'
  have : IsFiniteMeasure ρ := hρ
  have hμ : IsLocallyFiniteMeasure μ := IsLocallyFiniteMeasure.withDensity_coe hwInv
  refine ⟨μ, φ, hμ, hφ, hφS, fun f => ?_⟩
  -- Test the weighted measures against `f / w`, which is still compactly supported.
  let g : C_c(α, ℝ) := (⟨fun x => (w x)⁻¹, hwInv⟩ : C(α, ℝ≥0)) • f
  have hg (x : α) : g x = (w x)⁻¹ • f x := CompactlySupportedContinuousMap.smulc_apply _ f x
  have hleft (n : ℕ) :
      (∫ x, g x ∂(σ n).withDensity (fun x => w x)) = ∫ x, f x ∂σ n := by
    rw [integral_withDensity_eq_integral_smul hw.measurable]
    exact integral_congr_ae (ae_of_all _ fun x => by simp only [hg, smul_inv_smul₀ (hpos x).ne'])
  have hright : (∫ x, g x ∂ρ) = ∫ x, f x ∂μ := by
    dsimp only [μ]
    rw [integral_withDensity_eq_integral_smul hwInv.measurable]
    exact integral_congr_ae (ae_of_all _ hg)
  simpa only [CompactlySupportedContinuousMap.toBoundedContinuousFunction_apply, hleft, hright]
    using hlim g.toBoundedContinuousFunction

open scoped CompactlySupported in
/-- **Vague compactness.** A sequence of Borel measures on a locally compact, σ-compact,
metrizable space that frequently lies in a set `S` of measures with uniformly bounded masses on
each compact set has a subsequence in `S` converging vaguely, that is against every continuous
compactly supported function, to a locally finite measure. The measures may have infinite total
mass. -/
theorem exists_subseq_tendsto_integral_of_iSup_measure_ne_top [LocallyCompactSpace α]
    [SigmaCompactSpace α] [PseudoMetrizableSpace α] (σ : ℕ → Measure α) {S : Set (Measure α)}
    (hS : ∀ K, IsCompact K → ⨆ μ ∈ S, μ K ≠ ∞) (hσ : ∃ᶠ n in atTop, σ n ∈ S) :
    ∃ (μ : Measure α) (φ : ℕ → ℕ), IsLocallyFiniteMeasure μ ∧ StrictMono φ ∧
      (∀ k, σ (φ k) ∈ S) ∧
      ∀ f : C_c(α, ℝ), Tendsto (fun k => ∫ x, f x ∂σ (φ k)) atTop (𝓝 (∫ x, f x ∂μ)) := by
  -- Weight `S` into a tight, mass-bounded set and extract from the weighted sequence.
  obtain ⟨w, hw, hpos, hmass, hTight⟩ :=
    exists_isTightMeasureSet_withDensity_of_iSup_measure_ne_top hS
  obtain ⟨μ, φ, hμ, hφ, hφS, hlim⟩ := exists_subseq_tendsto_integral_of_withDensity σ w hw hpos
    2 (forall_mem_image.2 hmass) hTight (hσ.mono fun n hn ↦ mem_image_of_mem _ hn)
  refine ⟨μ, φ, hμ, hφ, fun k ↦ ?_, hlim⟩
  -- Weighting by `w` is injective, since `w` is positive and finite.
  have hinv (ν : Measure α) :
      (ν.withDensity fun x ↦ (w x : ℝ≥0∞)).withDensity (fun x ↦ (w x : ℝ≥0∞)⁻¹) = ν :=
    withDensity_inv_same hw.measurable.coe_nnreal_ennreal
      (ae_of_all _ fun x ↦ ENNReal.coe_ne_zero.2 (hpos x).ne')
      (ae_of_all _ fun _ ↦ ENNReal.coe_ne_top)
  obtain ⟨ν, hν, hνσ⟩ := hφS k
  rwa [← hinv (σ (φ k)), ← hνσ, hinv]

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
