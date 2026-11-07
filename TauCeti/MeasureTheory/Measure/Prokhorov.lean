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
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Topology.UrysohnsLemma
import TauCeti.Topology.Compactness.Compact

/-!
# Prokhorov compactness lemmas for sequences of measures

This file contains generic consequences of Mathlib's Prokhorov compactness theorem. For finite
measures, tightness and a uniform mass bound give a weak cluster limit without a real-line support
condition or normalization step. For probability measures on a Polish space, a weakly convergent
sequence is tight.

## Main declarations

* `TauCeti.isCompact_closure_of_isTightMeasureSet_of_mass_le`: Prokhorov's theorem for finite
  measures, a tight set with uniformly bounded mass has compact closure.
* `TauCeti.exists_tendsto_finiteMeasure_of_eventually_measure_compl_eq_zero`: finite measures
  eventually carried by a compact set, with bounded mass, converge along an ultrafilter to a finite
  measure carried by that set.
* `TauCeti.finite_measure_cluster_limit`: a tight, mass-bounded sequence of finite measures has a
  weak cluster limit along an ultrafilter below `atTop`.
* `TauCeti.finite_measure_subseq_limit`: the corresponding subsequence form on a separable
  metrizable space, without requiring a first-countability instance for finite measures.
* `TauCeti.exists_subseq_tendsto_integral_of_withDensity`: compact-test subsequential convergence
  after tight weighting by a strictly positive continuous function.
* `IsCompact.measure_le_of_tendsto_integral`: compact-set mass bounds inherited from open
  neighbourhood bounds under convergence against compactly supported continuous functions.
* `TauCeti.isTightMeasureSet_range_of_tendsto`: a weakly convergent sequence of probability
  measures on a Polish space is tight.
* `MeasureTheory.ProbabilityMeasure.integral_mem_of_mapClusterPt`: bounded-continuous integrals
  preserve eventual membership in closed sets at weak cluster points.

## References

* Roadmap: `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part B (Bernstein theorem milestone).
* Roadmap: `TauCetiRoadmap/OptimalTransport/README.md`, Layer 1, item 6 (stability).
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

/-- A tight, mass-bounded sequence of finite measures on a separable metrizable space has a
weakly convergent subsequence. The limiting measure retains the common mass bound. -/
lemma finite_measure_subseq_limit [PseudoMetrizableSpace α] [SeparableSpace α]
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
  have hsubseq : ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (σf ∘ φ) atTop (𝓝 μf) := by
    by_cases hzero : μf = 0
    · -- At zero, convergence of the mass alone controls every bounded test function.
      have hmassU : Tendsto (fun n => (σf n).mass) (U : Filter ℕ) (𝓝 0) := by
        simpa [hzero] using hUtend.mass
      obtain ⟨φ, hφ, hlim⟩ := (hmassU.mapClusterPt.mono hUle).tendsto_subseq
      exact ⟨φ, hφ, hzero ▸ FiniteMeasure.tendsto_zero_of_tendsto_zero_mass hlim⟩
    · -- Away from zero, mass and normalized probability determine weak convergence.
      have : Nonempty α := by
        by_contra h
        have : IsEmpty α := not_nonempty_iff.mp h
        apply hzero
        apply Subtype.ext
        exact Measure.ext fun s _ => by simp [Set.eq_empty_of_isEmpty s]
      have hpair : Tendsto (fun n => ((σf n).mass, (σf n).normalize)) (U : Filter ℕ)
          (𝓝 (μf.mass, μf.normalize)) :=
        hUtend.mass.prodMk_nhds (FiniteMeasure.tendsto_normalize_of_tendsto hUtend hzero)
      obtain ⟨φ, hφ, hlim⟩ := (hpair.mapClusterPt.mono hUle).tendsto_subseq
      have hm : Tendsto (fun k => (σf (φ k)).mass) atTop (𝓝 μf.mass) :=
        (continuous_fst.tendsto _).comp hlim
      have hn : Tendsto (fun k => (σf (φ k)).normalize) atTop (𝓝 μf.normalize) :=
        (continuous_snd.tendsto _).comp hlim
      exact ⟨φ, hφ,
        FiniteMeasure.tendsto_of_tendsto_normalize_testAgainstNN_of_tendsto_mass
          (μ := μf) hn hm⟩
  obtain ⟨φ, hφ, hφ_tendsto⟩ := hsubseq
  refine ⟨μ₀, φ, hμ₀_fin, hφ, hmass_μ₀, fun g => ?_⟩
  have hweak :=
    (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hφ_tendsto) g
  -- `hweak` is stated through the `FiniteMeasure` integral coercion; `change` reads it back as
  -- the plain Bochner integral against the underlying measures, which is the statement wanted.
  change Tendsto (fun k => ∫ x, g x ∂σ (φ k)) atTop (𝓝 (∫ x, g x ∂μ₀)) at hweak
  exact hweak

open scoped CompactlySupported in
/-- If weighting by a strictly positive continuous function gives a tight family with bounded
mass, then a sequence of measures has a locally finite subsequential limit against every
compactly supported continuous test function. The unweighted measures may have infinite mass. -/
theorem exists_subseq_tendsto_integral_of_withDensity
    [PseudoMetrizableSpace α] [SeparableSpace α]
    (σ : ℕ → Measure α) (w : α → ℝ≥0) (hw : Continuous w) (hpos : ∀ x, 0 < w x)
    (C : ℝ≥0) (hmass : ∀ n, ((σ n).withDensity fun x => w x) univ ≤ (C : ENNReal))
    (hTight : IsTightMeasureSet (range fun n => (σ n).withDensity fun x => w x)) :
    ∃ (μ : Measure α) (φ : ℕ → ℕ), IsLocallyFiniteMeasure μ ∧ StrictMono φ ∧
      ∀ f : C_c(α, ℝ), Tendsto (fun k => ∫ x, f x ∂σ (φ k)) atTop
        (𝓝 (∫ x, f x ∂μ)) := by
  obtain ⟨ρ, φ, hρ, hφ, -, hlim⟩ :=
    finite_measure_subseq_limit (fun n => (σ n).withDensity fun x => w x) C hmass hTight
  let μ : Measure α := ρ.withDensity fun x => ((w x)⁻¹ : ℝ≥0)
  have hwInv : Continuous fun x => (w x)⁻¹ := hw.inv₀ fun x => (hpos x).ne'
  have : IsFiniteMeasure ρ := hρ
  have hμ : IsLocallyFiniteMeasure μ := IsLocallyFiniteMeasure.withDensity_coe hwInv
  refine ⟨μ, φ, hμ, hφ, fun f => ?_⟩
  let g : C_c(α, ℝ) :=
    ⟨⟨fun x => f x * ((w x : ℝ)⁻¹),
      f.continuous.mul ((NNReal.continuous_coe.comp hw).inv₀
        fun x => NNReal.coe_ne_zero.mpr (hpos x).ne')⟩,
      f.hasCompactSupport.mul_right⟩
  have hleft (n : ℕ) :
      (∫ x, g x ∂(σ n).withDensity (fun x => w x)) = ∫ x, f x ∂σ n := by
    rw [integral_withDensity_eq_integral_smul hw.measurable]
    apply integral_congr_ae
    filter_upwards [] with x
    have hx : (w x : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr (hpos x).ne'
    simp only [g, CompactlySupportedContinuousMap.coe_mk, ContinuousMap.coe_mk,
      NNReal.smul_def, smul_eq_mul]
    rw [mul_left_comm, mul_inv_cancel₀ hx, mul_one]
  have hright : (∫ x, g x ∂ρ) = ∫ x, f x ∂μ := by
    dsimp only [μ]
    rw [integral_withDensity_eq_integral_smul hwInv.measurable]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by simp [g, NNReal.smul_def, smul_eq_mul, mul_comm]
  simpa only [CompactlySupportedContinuousMap.toBoundedContinuousFunction_apply, hleft, hright]
    using hlim g.toBoundedContinuousFunction

open scoped CompactlySupported in
/-- Under convergence against compactly supported continuous functions, a mass bound on an
open neighbourhood passes to the measure of a compact subset for the limiting measure. -/
theorem _root_.IsCompact.measure_le_of_tendsto_integral [LocallyCompactSpace α]
    {ι : Type*} {l : Filter ι} [NeBot l] {K V : Set α}
    (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V)
    {μ : Measure α} [IsFiniteMeasureOnCompacts μ] {σ : ι → Measure α} {C : ℝ≥0∞}
    (hbound : ∀ᶠ i in l, σ i V ≤ C)
    (hlim : ∀ f : C_c(α, ℝ), Tendsto (fun i => ∫ x, f x ∂σ i) l
      (𝓝 (∫ x, f x ∂μ))) : μ K ≤ C := by
  obtain ⟨f, hfK, hfc, hfV, hfr⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hK hV hKV
  let g : C_c(α, ℝ) := ⟨f, hfc⟩
  refine (g.integrable.measure_le_integral (ae_of_all _ fun x => (hfr x).1)
    (fun x hx => (hfK hx).ge)).trans ?_
  apply le_of_tendsto ((ENNReal.continuous_ofReal.tendsto _).comp (hlim g))
  filter_upwards [hbound] with i hi
  refine (integral_le_measure (fun x _ => (hfr x).2) fun x hx => ?_).trans hi
  exact le_of_eq (image_eq_zero_of_notMem_tsupport fun h => hx (hfV h))

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

open scoped BoundedContinuousFunction

namespace MeasureTheory.ProbabilityMeasure

open MeasureTheory Filter Set Topology

/-- A bounded-continuous integral at a weak cluster point belongs to every closed set that
eventually contains the integrals along the sequence. -/
theorem integral_mem_of_mapClusterPt {μn : ℕ → ProbabilityMeasure ℝ}
    {ν : ProbabilityMeasure ℝ}
    (hν : MapClusterPt ν atTop μn) (g : ℝ →ᵇ ℝ) {C : Set ℝ} (hC : IsClosed C)
    (h : ∀ᶠ n in atTop, ∫ x, g x ∂(μn n : Measure ℝ) ∈ C) :
    ∫ x, g x ∂(ν : Measure ℝ) ∈ C := by
  have hc : Continuous fun p : ProbabilityMeasure ℝ => ∫ x, g x ∂(p : Measure ℝ) :=
    ProbabilityMeasure.continuous_integral_boundedContinuousFunction g
  have hcont : ContinuousAt (fun p : ProbabilityMeasure ℝ => ∫ x, g x ∂(p : Measure ℝ)) ν :=
    hc.continuousAt
  have hmap := MapClusterPt.continuousAt_comp
    (f := fun p : ProbabilityMeasure ℝ => ∫ x, g x ∂(p : Measure ℝ))
    (x := ν) hcont hν
  exact hC.mem_of_mapClusterPt hmap h

end MeasureTheory.ProbabilityMeasure
