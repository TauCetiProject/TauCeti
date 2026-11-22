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
condition or normalization step. For measures with uniformly bounded masses on
compact sets, weighting by a positive continuous function that decays fast enough along a compact
exhaustion makes them tight with bounded mass, which gives vague compactness. For probability
measures on a Polish space, a weakly convergent sequence is tight.

## Main declarations

* `TauCeti.isCompact_closure_of_isTightMeasureSet_of_mass_le`: Prokhorov's theorem for finite
  measures, a tight set with uniformly bounded mass has compact closure.
* `TauCeti.exists_tendsto_finiteMeasure_of_eventually_measure_compl_eq_zero`: finite measures
  eventually carried by a compact set, with bounded mass, converge along an ultrafilter to a finite
  measure carried by that set.
* `TauCeti.exists_ultrafilter_tendsto_integral_of_isTightMeasureSet`: a tight, mass-bounded family
  of finite measures has a weak cluster limit along an ultrafilter below any nontrivial filter.
* `TauCeti.exists_subseq_tendsto_integral_of_isTightMeasureSet`: the corresponding subsequence
  form on a metrizable space, without requiring a first-countability instance for finite
  measures.
* `TauCeti.exists_subseq_tendsto_integral_of_withDensity`: compact-test subsequential convergence
  after tight weighting by a strictly positive continuous function.
* `TauCeti.exists_subseq_tendsto_integral_of_iSup_measure_ne_top`: vague compactness, a sequence
  of measures with uniformly bounded masses on every compact set of a locally compact, σ-compact,
  metrizable space has a subsequence converging vaguely to a locally finite measure.
* `IsCompact.exists_compactlySupported_measure_le_integral_le`: a compactly supported cutoff
  whose integral lies between the masses of a compact set and of an open neighbourhood of it.
* `IsCompact.measure_le_of_tendsto_integral`: compact-set mass bounds inherited from open
  neighbourhood bounds under convergence against compactly supported continuous functions.
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

/-- A tight, uniformly mass-bounded family of finite measures has a weak cluster limit along any
nontrivial filter.

Given tightness of the family and a common total-mass bound, the conclusion is a finite limiting
measure with the same mass bound and weak convergence of all bounded-continuous test-function
integrals along an ultrafilter `U ≤ l`; no first-countability assumption on `FiniteMeasure α`
is needed. -/
lemma exists_ultrafilter_tendsto_integral_of_isTightMeasureSet {ι : Type*} (σ : ι → Measure α)
    (l : Filter ι) [l.NeBot] (C : ℝ≥0) (hmass : ∀ i, σ i univ ≤ C)
    (hTight : IsTightMeasureSet (range σ)) :
    ∃ (μ₀ : Measure α) (U : Ultrafilter ι), ↑U ≤ l ∧ IsFiniteMeasure μ₀ ∧ μ₀ univ ≤ C ∧
      ∀ g : BoundedContinuousFunction α ℝ,
        Tendsto (fun i => ∫ x, g x ∂σ i) U (𝓝 (∫ x, g x ∂μ₀)) := by
  -- First coerce the family to `FiniteMeasure`; the uniform mass bound supplies finiteness.
  have hfin : ∀ i, IsFiniteMeasure (σ i) := fun i =>
    ⟨(hmass i).trans_lt ENNReal.coe_lt_top⟩
  let σf : ι → FiniteMeasure α := fun i => ⟨σ i, hfin i⟩
  have hσf_mass : range σf ⊆ {μ | μ.mass ≤ C} := by
    rintro - ⟨i, rfl⟩
    rw [mem_ofPred_eq, ← ENNReal.coe_le_coe, FiniteMeasure.ennreal_mass]
    exact hmass i
  have hcompact : IsCompact (closure (range σf)) :=
    isCompact_closure_of_isTightMeasureSet_of_mass_le
      (hTight.subset (by rintro - ⟨-, ⟨i, rfl⟩, rfl⟩; exact ⟨i, rfl⟩)) hσf_mass
  -- Compactness gives a cluster point and an ultrafilter below `l` along which `σf`
  -- converges weakly.
  obtain ⟨μf, hμf, hcluster⟩ := hcompact (f := map σf l)
    (tendsto_principal.mpr (.of_forall fun i => subset_closure (mem_range_self i)))
  obtain ⟨U, hUle, hUtend⟩ := mapClusterPt_iff_ultrafilter.mp hcluster
  refine ⟨(μf : Measure α), U, hUle, inferInstance, ?_, ?_⟩
  -- Finally unwrap the closure membership into the mass bound and weak convergence of
  -- integrals against bounded continuous test functions.
  · have hle : μf.mass ≤ C := closure_minimal hσf_mass
      (isClosed_le FiniteMeasure.continuous_mass continuous_const) hμf
    rw [← FiniteMeasure.ennreal_mass]
    exact_mod_cast hle
  · exact fun g => by simpa [σf] using FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hUtend g

/-- The separable case of `exists_subseq_tendsto_integral_of_isTightMeasureSet`, where the space of
probability measures is metrizable. -/
private lemma exists_subseq_tendsto_integral_of_isTightMeasureSet_of_separableSpace
    [PseudoMetrizableSpace α] [SeparableSpace α] (σ : ℕ → Measure α) (C : ℝ≥0)
    (hmass : ∀ n, σ n univ ≤ C) (hTight : IsTightMeasureSet (range σ)) :
    ∃ (μ₀ : Measure α) (φ : ℕ → ℕ), IsFiniteMeasure μ₀ ∧ StrictMono φ ∧ μ₀ univ ≤ C ∧
      ∀ g : BoundedContinuousFunction α ℝ,
        Tendsto (fun k => ∫ x, g x ∂σ (φ k)) atTop (𝓝 (∫ x, g x ∂μ₀)) := by
  -- Start from the ultrafilter cluster limit supplied by compactness.
  obtain ⟨μ₀, U, hUle, hμ₀_fin, hmass_μ₀, hweakU⟩ :=
    exists_ultrafilter_tendsto_integral_of_isTightMeasureSet σ atTop C hmass hTight
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
      -- Normalization needs `α` nonempty; on an empty space every measure is zero.
      have : Nonempty α := not_isEmpty_iff.mp fun _ =>
        hzero (FiniteMeasure.toMeasure_injective (Measure.eq_zero_of_isEmpty _))
      have hpair : Tendsto (fun n => ((σf n).mass, (σf n).normalize)) (U : Filter ℕ)
          (𝓝 (μf.mass, μf.normalize)) :=
        hUtend.mass.prodMk_nhds (FiniteMeasure.tendsto_normalize_of_tendsto hUtend hzero)
      obtain ⟨φ, hφ, hlim⟩ := (hpair.mapClusterPt.mono hUle).tendsto_subseq
      exact ⟨φ, hφ, FiniteMeasure.tendsto_of_tendsto_normalize_testAgainstNN_of_tendsto_mass
        (μ := μf) hlim.snd_nhds hlim.fst_nhds⟩
  obtain ⟨φ, hφ, hφ_tendsto⟩ := hsubseq
  refine ⟨μ₀, φ, hμ₀_fin, hφ, hmass_μ₀, fun g => ?_⟩
  have hweak :=
    (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hφ_tendsto) g
  -- `hweak` is stated through the `FiniteMeasure` integral coercion; `change` reads it back as
  -- the plain Bochner integral against the underlying measures, which is the statement wanted.
  change Tendsto (fun k => ∫ x, g x ∂σ (φ k)) atTop (𝓝 (∫ x, g x ∂μ₀)) at hweak
  exact hweak

/-- A tight, mass-bounded sequence of finite measures on a metrizable space has a weakly
convergent subsequence. The limiting measure retains the common mass bound. -/
lemma exists_subseq_tendsto_integral_of_isTightMeasureSet [PseudoMetrizableSpace α]
    (σ : ℕ → Measure α) (C : ℝ≥0) (hmass : ∀ n, σ n univ ≤ C)
    (hTight : IsTightMeasureSet (range σ)) :
    ∃ (μ₀ : Measure α) (φ : ℕ → ℕ), IsFiniteMeasure μ₀ ∧ StrictMono φ ∧ μ₀ univ ≤ C ∧
      ∀ g : BoundedContinuousFunction α ℝ,
        Tendsto (fun k => ∫ x, g x ∂σ (φ k)) atTop (𝓝 (∫ x, g x ∂μ₀)) := by
  -- Tightness gives compact sets `K j` carrying each `σ n` up to mass `j⁻¹`, so every `σ n` lives
  -- on the separable measurable set `S = ⋃ j, K j`; we run the separable case on `S`.
  have hK (j : ℕ) : ∃ K, IsCompact K ∧ ∀ n, σ n Kᶜ ≤ (j : ℝ≥0∞)⁻¹ := by
    obtain ⟨K, hK, h⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp hTight
      (j : ℝ≥0∞)⁻¹ (ENNReal.inv_pos.2 (ENNReal.natCast_ne_top j))
    exact ⟨K, hK, fun n => h _ (mem_range_self n)⟩
  choose K hKc hKσ using hK
  let S : Set α := ⋃ j, K j
  have hS : MeasurableSet S := .iUnion fun j => (hKc j).isClosed.measurableSet
  have : SeparableSpace S := (IsSeparable.iUnion fun j => (hKc j).isSeparable).separableSpace
  have hσS (n : ℕ) : σ n Sᶜ = 0 := nonpos_iff_eq_zero.mp <|
    ge_of_tendsto' ENNReal.tendsto_inv_nat_nhds_zero fun j =>
      (measure_mono (compl_subset_compl.2 (subset_iUnion K j))).trans (hKσ j n)
  -- The restrictions `τ n` of `σ n` to `S` push forward back to `σ n`.
  let τ : ℕ → Measure S := fun n => (σ n).comap (↑)
  have hτ (n : ℕ) : (τ n).map (↑) = σ n := by
    rw [map_comap_subtypeVal hS, Measure.restrict_eq_self_of_ae_mem (mem_ae_iff.2 (hσS n))]
  have hτ_univ (n : ℕ) : τ n univ = σ n univ := by
    conv_rhs => rw [← hτ n, Measure.map_apply measurable_subtypeVal .univ, preimage_univ]
  have hτTight : IsTightMeasureSet (range τ) := by
    refine isTightMeasureSet_iff_exists_isCompact_measure_compl_le.2 fun ε hε => ?_
    obtain ⟨j, hj⟩ := ENNReal.exists_inv_nat_lt hε.ne'
    refine ⟨(↑) ⁻¹' K j, Subtype.isCompact_iff.2 ?_, ?_⟩
    · rw [Subtype.image_preimage_coe, inter_eq_right.2 (subset_iUnion K j)]
      exact hKc j
    · rintro - ⟨n, rfl⟩
      rw [comap_subtypeVal_apply hS, ← preimage_compl, Subtype.image_preimage_coe]
      exact (measure_mono inter_subset_right).trans ((hKσ j n).trans hj.le)
  obtain ⟨ν, φ, hν, hφ, hνC, hlim⟩ :=
    exists_subseq_tendsto_integral_of_isTightMeasureSet_of_separableSpace τ C
      (fun n => (hτ_univ n).trans_le (hmass n)) hτTight
  refine ⟨ν.map (↑), φ, inferInstance, hφ, ?_, fun g => ?_⟩
  · rwa [Measure.map_apply measurable_subtypeVal .univ, preimage_univ]
  -- Integrals of `g` against push-forwards are integrals of its restriction to `S`.
  have hint (μ : Measure S) : ∫ x, g x ∂μ.map (↑) =
      ∫ x, g.compContinuous ⟨(↑), continuous_subtypeVal⟩ x ∂μ := by
    simp only [(MeasurableEmbedding.subtypeVal hS).integral_map,
      BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk]
  simpa only [← hint, hτ] using hlim (g.compContinuous ⟨(↑), continuous_subtypeVal⟩)

open scoped CompactlySupported in
/-- If weighting by a strictly positive continuous function gives a tight family with bounded
mass, then a sequence of measures has a locally finite subsequential limit against every
compactly supported continuous test function. The unweighted measures may have infinite mass. -/
theorem exists_subseq_tendsto_integral_of_withDensity [PseudoMetrizableSpace α]
    (σ : ℕ → Measure α) (w : α → ℝ≥0) (hw : Continuous w) (hpos : ∀ x, 0 < w x)
    (C : ℝ≥0) (hmass : ∀ n, ((σ n).withDensity fun x => w x) univ ≤ (C : ENNReal))
    (hTight : IsTightMeasureSet (range fun n => (σ n).withDensity fun x => w x)) :
    ∃ (μ : Measure α) (φ : ℕ → ℕ), IsLocallyFiniteMeasure μ ∧ StrictMono φ ∧
      ∀ f : C_c(α, ℝ), Tendsto (fun k => ∫ x, f x ∂σ (φ k)) atTop
        (𝓝 (∫ x, f x ∂μ)) := by
  obtain ⟨ρ, φ, hρ, hφ, -, hlim⟩ :=
    exists_subseq_tendsto_integral_of_isTightMeasureSet (fun n => (σ n).withDensity fun x => w x)
      C hmass hTight
  let μ : Measure α := ρ.withDensity fun x => ((w x)⁻¹ : ℝ≥0)
  have hwInv : Continuous fun x => (w x)⁻¹ := hw.inv₀ fun x => (hpos x).ne'
  have : IsFiniteMeasure ρ := hρ
  have hμ : IsLocallyFiniteMeasure μ := IsLocallyFiniteMeasure.withDensity_coe hwInv
  refine ⟨μ, φ, hμ, hφ, fun f => ?_⟩
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

omit [T2Space α] [BorelSpace α] in
/-- A term of the weight built in `exists_weight_of_iSup_measure_ne_top`: a cutoff `0 ≤ f ≤ 1`
supported in `T`, scaled by `(1 / 4) ^ k / (M + 1)` where `M` bounds `ν T`, integrates over `S`
to at most `(1 / 2) ^ N (1 / 2) ^ k` when `N ≤ k`, and to zero when `T` and `S` are disjoint. -/
private lemma ofReal_mul_setLIntegral_le {ν : Measure α} {T S : Set α} (hT : MeasurableSet T)
    {f : C(α, ℝ)} (hf : ∀ x, f x ∈ Icc 0 1) (hfT : tsupport f ⊆ T) {M : ℝ} (hM : 0 ≤ M)
    (hνT : ν T ≤ ENNReal.ofReal M) {k N : ℕ} (hkN : N ≤ k ∨ Disjoint T S) :
    ENNReal.ofReal ((1 / 4) ^ k * (M + 1)⁻¹) * ∫⁻ x in S, ENNReal.ofReal (f x) ∂ν ≤
      ENNReal.ofReal ((1 / 2) ^ N * (1 / 2) ^ k) := by
  -- The cutoff is at most the indicator of `T`, so its integral over `S` is at most `ν (T ∩ S)`.
  have hint : ∫⁻ x in S, ENNReal.ofReal (f x) ∂ν ≤ ν (T ∩ S) := by
    refine (lintegral_mono fun x ↦ ?_).trans_eq
      (by rw [lintegral_indicator_one hT, Measure.restrict_apply hT])
    by_cases hx : x ∈ T
    · simpa [hx] using (hf x).2
    · simp [hx, image_eq_zero_of_notMem_tsupport fun h ↦ hx (hfT h)]
  rcases hkN with hNk | hTS
  · grw [hint, measure_mono inter_subset_left, hνT, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : M * (M + 1)⁻¹ ≤ 1 := by
      rw [mul_inv_le_iff₀ (by linarith)]
      linarith
    have h2 : ((1 : ℝ) / 2) ^ k ≤ (1 / 2) ^ N :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hNk
    calc (1 / 4) ^ k * (M + 1)⁻¹ * M = (1 / 2) ^ k * (1 / 2) ^ k * (M * (M + 1)⁻¹) := by
          rw [show (1 / 4 : ℝ) = 1 / 2 * (1 / 2) by norm_num, mul_pow]; ring
      _ ≤ (1 / 2) ^ k * (1 / 2) ^ k := mul_le_of_le_one_right (by positivity) h1
      _ ≤ (1 / 2) ^ N * (1 / 2) ^ k := by gcongr
  · have : ∫⁻ x in S, ENNReal.ofReal (f x) ∂ν = 0 :=
      le_antisymm (hint.trans (by rw [hTS.inter_eq, measure_empty])) zero_le
    simp [this]

/-- An exhausting sequence of cutoffs gives a positive continuous weight whose integrals against
measures with uniformly bounded masses on compact sets are uniformly bounded, with uniformly
small tails outside the exhaustion. -/
private lemma exists_weight_of_iSup_measure_ne_top [LocallyCompactSpace α]
    [SigmaCompactSpace α] (σ : ℕ → Measure α) (hσ : ∀ K, IsCompact K → ⨆ n, σ n K ≠ ∞) :
    ∃ (w : α → ℝ≥0) (K : CompactExhaustion α), Continuous w ∧ (∀ x, 0 < w x) ∧
      ∀ (S : Set α) (N : ℕ), (∀ k < N, Disjoint (K (k + 1)) S) → ∀ n,
        ∫⁻ x in S, w x ∂σ n ≤ ENNReal.ofReal ((1 / 2) ^ N * 2) := by
  let K := CompactExhaustion.choice α
  -- Cutoffs `0 ≤ f k ≤ 1`, equal to one on `K k` and supported in `K (k + 1)`.
  choose f hfK _ hfV hfr using fun k : ℕ ↦ exists_continuousMap_one_of_isCompact_subset_isOpen
    (K.isCompact k) isOpen_interior (K.subset_interior_succ k)
  -- The weight is `∑ a k f k`, where `a k = (1 / 4) ^ k / (M k + 1)` and `M k` bounds the masses
  -- of `K (k + 1)`.
  let M : ℕ → ℝ := fun k ↦ (⨆ n, σ n (K (k + 1))).toReal
  let a : ℕ → ℝ := fun k ↦ (1 / 4) ^ k * (M k + 1)⁻¹
  have hM (k : ℕ) : 0 ≤ M k := ENNReal.toReal_nonneg
  have ha (k : ℕ) : 0 < a k := by positivity
  have hsum : Summable a :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).of_nonneg_of_le
      (fun k ↦ (ha k).le) fun k ↦
        mul_le_of_le_one_right (by positivity) (inv_le_one_of_one_le₀ (by linarith [hM k]))
  have hterm (k : ℕ) (x : α) : 0 ≤ a k * f k x := mul_nonneg (ha k).le (hfr k x).1
  have hle (k : ℕ) (x : α) : a k * f k x ≤ a k := mul_le_of_le_one_right (ha k).le (hfr k x).2
  have hsumx (x : α) : Summable fun k ↦ a k * f k x :=
    hsum.of_nonneg_of_le (hterm · x) (hle · x)
  refine ⟨fun x ↦ (∑' k, a k * f k x).toNNReal, K, ?_, fun x ↦ ?_, fun S N hSN n ↦ ?_⟩
  · exact continuous_real_toNNReal.comp (continuous_tsum (f := fun k x ↦ a k * f k x)
      (fun k ↦ continuous_const.mul (f k).continuous) hsum fun k x ↦ by
        rw [Real.norm_of_nonneg (hterm k x)]; exact hle k x)
  · obtain ⟨k, hk⟩ := K.exists_mem x
    refine Real.toNNReal_pos.2 ((ha k).trans_le ((le_of_eq ?_).trans
      ((hsumx x).le_tsum k fun j _ ↦ hterm j x)))
    rw [hfK k hk, Pi.one_apply, mul_one]
  -- Expand the weight and bound the `k`-th term by `(1 / 2) ^ N (1 / 2) ^ k`.
  have hw (x : α) : ((∑' k, a k * f k x).toNNReal : ℝ≥0∞) =
      ∑' k, ENNReal.ofReal (a k) * ENNReal.ofReal (f k x) := by
    rw [ENNReal.ofNNReal_toNNReal, ENNReal.ofReal_tsum_of_nonneg (hterm · x) (hsumx x)]
    exact tsum_congr fun k ↦ ENNReal.ofReal_mul (ha k).le
  have hgeom : ENNReal.ofReal ((1 / 2) ^ N * 2) =
      ∑' k, ENNReal.ofReal ((1 / 2) ^ N * (1 / 2) ^ k) := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (f := fun k : ℕ ↦ (1 / 2 : ℝ) ^ N * (1 / 2) ^ k)
      (fun k ↦ by positivity) (summable_geometric_two.mul_left _), tsum_mul_left,
      tsum_geometric_two]
  simp_rw [hw]
  rw [lintegral_tsum fun k ↦
    ((f k).continuous.measurable.ennreal_ofReal.const_mul _).aemeasurable, hgeom]
  refine tsum_le_tsum fun k ↦ ?_
  rw [lintegral_const_mul _ (f k).continuous.measurable.ennreal_ofReal]
  refine ofReal_mul_setLIntegral_le (K.isCompact (k + 1)).isClosed.measurableSet (hfr k)
    ((hfV k).trans interior_subset) (hM k) ?_ ((le_or_gt N k).imp_right (hSN k))
  rw [ENNReal.ofReal_toReal (hσ _ (K.isCompact (k + 1)))]
  exact le_iSup (fun n ↦ σ n (K (k + 1))) n

open scoped CompactlySupported in
/-- **Vague compactness.** A sequence of measures on a locally compact, σ-compact, metrizable
space whose masses on each compact set are bounded uniformly in `n` has a subsequence converging
vaguely, that is against every continuous compactly supported function, to a locally finite
measure. The measures may have infinite total mass. -/
theorem exists_subseq_tendsto_integral_of_iSup_measure_ne_top [LocallyCompactSpace α]
    [SigmaCompactSpace α] [PseudoMetrizableSpace α] (σ : ℕ → Measure α)
    (hσ : ∀ K, IsCompact K → ⨆ n, σ n K ≠ ∞) :
    ∃ (μ : Measure α) (φ : ℕ → ℕ), IsLocallyFiniteMeasure μ ∧ StrictMono φ ∧
      ∀ f : C_c(α, ℝ), Tendsto (fun k => ∫ x, f x ∂σ (φ k)) atTop
        (𝓝 (∫ x, f x ∂μ)) := by
  obtain ⟨w, K, hw, hpos, htail⟩ := exists_weight_of_iSup_measure_ne_top σ hσ
  refine exists_subseq_tendsto_integral_of_withDensity σ w hw hpos 2 (fun n ↦ ?_) ?_
  · -- The total mass is the case `S = univ`, `N = 0`.
    rw [withDensity_apply _ MeasurableSet.univ]
    simpa using htail univ 0 (fun k hk ↦ absurd hk (Nat.not_lt_zero k)) n
  · -- The tails outside `K N` are uniformly small.
    refine isTightMeasureSet_iff_exists_isCompact_measure_compl_le.2 fun ε hε ↦ ?_
    have hlim : Tendsto (fun N : ℕ ↦ ENNReal.ofReal ((1 / 2) ^ N * 2)) atTop (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal ((tendsto_pow_atTop_nhds_zero_of_lt_one
        (r := (1 : ℝ) / 2) (by norm_num) (by norm_num)).mul_const 2)
    obtain ⟨N, hN⟩ := (hlim.eventually (gt_mem_nhds hε)).exists
    have hKN : MeasurableSet (K N)ᶜ := (K.isCompact N).isClosed.measurableSet.compl
    refine ⟨K N, K.isCompact N, ?_⟩
    rintro - ⟨n, rfl⟩
    rw [withDensity_apply _ hKN]
    exact (htail _ N (fun k hk ↦ disjoint_compl_right_iff_subset.2
      (K.subset (Nat.succ_le_of_lt hk))) n).trans hN.le

omit [T2Space α] [BorelSpace α] in
open scoped CompactlySupported in
/-- A compactly supported continuous function whose integral against every measure lies between
the mass of a compact set `K` and the mass of an open neighbourhood `U` of `K`; the lower bound
needs the measure to be finite on compact sets. -/
theorem _root_.IsCompact.exists_compactlySupported_measure_le_integral_le [R1Space α]
    [LocallyCompactSpace α] [OpensMeasurableSpace α] {K U : Set α} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ f : C_c(α, ℝ), (∀ (ρ : Measure α) [IsFiniteMeasureOnCompacts ρ],
      ρ K ≤ ENNReal.ofReal (∫ x, f x ∂ρ)) ∧
      ∀ ρ : Measure α, ENNReal.ofReal (∫ x, f x ∂ρ) ≤ ρ U := by
  obtain ⟨f, hf1, hfc, hfU, hfr⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK hU hKU
  refine ⟨⟨f, hfc⟩, fun ρ _ ↦ ?_, fun ρ ↦ ?_⟩
  · exact (CompactlySupportedContinuousMap.integrable ⟨f, hfc⟩).measure_le_integral
      (ae_of_all _ fun x ↦ (hfr x).1) fun _ hx ↦ (hf1 hx).ge
  · exact integral_le_measure (fun x _ ↦ (hfr x).2) fun x hx ↦
      (image_eq_zero_of_notMem_tsupport fun h ↦ hx (hfU h)).le

omit [T2Space α] [BorelSpace α] in
open scoped CompactlySupported in
/-- Under convergence against compactly supported continuous functions, a mass bound on an
open neighbourhood passes to the measure of a compact subset for the limiting measure. -/
theorem _root_.IsCompact.measure_le_of_tendsto_integral [R1Space α] [LocallyCompactSpace α]
    [OpensMeasurableSpace α]
    {ι : Type*} {l : Filter ι} [NeBot l] {K V : Set α}
    (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V)
    {μ : Measure α} [IsFiniteMeasureOnCompacts μ] {σ : ι → Measure α} {C : ℝ≥0∞}
    (hbound : ∀ᶠ i in l, σ i V ≤ C)
    (hlim : ∀ f : C_c(α, ℝ), Tendsto (fun i => ∫ x, f x ∂σ i) l
      (𝓝 (∫ x, f x ∂μ))) : μ K ≤ C := by
  obtain ⟨f, hfK, hfV⟩ := hK.exists_compactlySupported_measure_le_integral_le hV hKV
  exact (hfK μ).trans (le_of_tendsto ((ENNReal.continuous_ofReal.tendsto _).comp (hlim f))
    (hbound.mono fun i hi ↦ (hfV (σ i)).trans hi))

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
