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
* `TauCeti.exists_ultrafilter_tendsto_integral_of_isTightMeasureSet`: a family of finite Borel
  measures on a Hausdorff space that frequently lies in a tight, mass-bounded set has a weak
  cluster limit along an ultrafilter below the filter.
* `TauCeti.exists_subseq_tendsto_integral_of_isTightMeasureSet`: the corresponding subsequence
  form for finite Borel measures on a metrizable space, without requiring a first-countability
  instance for finite measures.
* `TauCeti.exists_subseq_tendsto_integral_of_withDensity`: compact-test subsequential convergence
  after tight weighting by a strictly positive continuous function.
* `TauCeti.exists_subseq_tendsto_integral_of_iSup_measure_ne_top`: vague compactness, a sequence
  of Borel measures with uniformly bounded masses on every compact set of a locally compact,
  σ-compact, metrizable space has a subsequence converging vaguely to a locally finite measure.
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

/-- **Prokhorov's theorem along an ultrafilter.** A family of finite Borel measures on a
Hausdorff space that frequently lies, along a filter `l`, in a tight set with uniformly bounded
mass has a weak cluster limit along an ultrafilter `U ≤ l`.

The limit is a finite measure with the same mass bound, and the integrals of every bounded
continuous function converge along `U`; no first-countability assumption on `FiniteMeasure α` is
needed. The members of the family outside the set are unconstrained. -/
lemma exists_ultrafilter_tendsto_integral_of_isTightMeasureSet {ι : Type*} (σ : ι → Measure α)
    (l : Filter ι) {S : Set (Measure α)} (C : ℝ≥0) (hmass : ∀ μ ∈ S, μ univ ≤ C)
    (hTight : IsTightMeasureSet S) (hσ : ∃ᶠ i in l, σ i ∈ S) :
    ∃ (μ₀ : Measure α) (U : Ultrafilter ι), ↑U ≤ l ∧ IsFiniteMeasure μ₀ ∧ μ₀ univ ≤ C ∧
      ∀ g : BoundedContinuousFunction α ℝ,
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
  -- Compactness gives a cluster point and an ultrafilter along which `σf` converges weakly.
  obtain ⟨μf, hμf, hcluster⟩ := hcompact.exists_mapClusterPt (f := comap (↑) l) (u := σf)
    (tendsto_principal.2 (.of_forall fun i => subset_closure i.property))
  obtain ⟨U, hUle, hUtend⟩ := mapClusterPt_iff_ultrafilter.mp hcluster
  refine ⟨μf, U.map (↑), map_le_iff_le_comap.2 hUle, inferInstance, ?_, fun g => ?_⟩
  · rw [← FiniteMeasure.ennreal_mass, ENNReal.coe_le_coe]
    exact closure_minimal hSf_mass (isClosed_le FiniteMeasure.continuous_mass continuous_const) hμf
  · rw [Ultrafilter.coe_map, tendsto_map'_iff]
    simpa only [σf, Function.comp_def, FiniteMeasure.toMeasure_mk] using
      FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hUtend g

/-- **Prokhorov's theorem for sequences.** A sequence of finite Borel measures on a metrizable
space that frequently lies in a tight set with uniformly bounded mass has a weakly convergent
subsequence. The limiting measure retains the common mass bound. -/
lemma exists_subseq_tendsto_integral_of_isTightMeasureSet [PseudoMetrizableSpace α]
    (σ : ℕ → Measure α) {S : Set (Measure α)} (C : ℝ≥0) (hmass : ∀ μ ∈ S, μ univ ≤ C)
    (hTight : IsTightMeasureSet S) (hσ : ∃ᶠ n in atTop, σ n ∈ S) :
    ∃ (μ₀ : Measure α) (φ : ℕ → ℕ), IsFiniteMeasure μ₀ ∧ StrictMono φ ∧ μ₀ univ ≤ C ∧
      ∀ g : BoundedContinuousFunction α ℝ,
        Tendsto (fun k => ∫ x, g x ∂σ (φ k)) atTop (𝓝 (∫ x, g x ∂μ₀)) := by
  -- Pass to a subsequence `σ ∘ ψ` in `S`.
  obtain ⟨ψ, hψ, hψS⟩ := extraction_of_frequently_atTop hσ
  have hfin (n : ℕ) : IsFiniteMeasure (σ (ψ n)) := ⟨(hmass _ (hψS n)).trans_lt ENNReal.coe_lt_top⟩
  -- Every measure of `S` lives on the separable measurable set `T = ⋃ j, K j`, a union of compact
  -- sets with uniform tail bounds. We find the limit on `T`, where `FiniteMeasure T` has
  -- subsequential limits at cluster points.
  obtain ⟨K, hKc, hKS, hTS⟩ := hTight.exists_seq_isCompact_measure_compl_le
  let T : Set α := ⋃ j, K j
  have hT : MeasurableSet T := .iUnion fun j => (hKc j).isClosed.measurableSet
  have : SeparableSpace T := (IsSeparable.iUnion fun j => (hKc j).isSeparable).separableSpace
  -- The restrictions `τ n` of `σ (ψ n)` to `T` push forward back to `σ (ψ n)`.
  let τ : ℕ → FiniteMeasure T := fun n => ⟨(σ (ψ n)).comap (↑), inferInstance⟩
  have hτ (n : ℕ) : ((τ n).map Subtype.val : Measure α) = σ (ψ n) := by
    rw [FiniteMeasure.toMeasure_map, FiniteMeasure.toMeasure_mk, map_comap_subtypeVal hT,
      Measure.restrict_eq_self_of_ae_mem (mem_ae_iff.2 (hTS _ (hψS n)))]
  have hτ_univ (n : ℕ) : (τ n : Measure T) univ = σ (ψ n) univ := by
    conv_rhs => rw [← hτ n, FiniteMeasure.toMeasure_map,
      Measure.map_apply measurable_subtypeVal .univ, preimage_univ]
  have hτ_mass : range τ ⊆ {ν | ν.mass ≤ C} := by
    rintro - ⟨n, rfl⟩
    rw [mem_ofPred_eq, ← ENNReal.coe_le_coe, FiniteMeasure.ennreal_mass, hτ_univ]
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
  -- Prokhorov compactness gives a cluster point `ν` of `τ`, which is a subsequential limit.
  obtain ⟨ν, hν, hcluster⟩ :=
    (isCompact_closure_of_isTightMeasureSet_of_mass_le hτTight hτ_mass).exists_mapClusterPt
      (f := atTop) (u := τ) (tendsto_principal.2 (.of_forall fun n => subset_closure ⟨n, rfl⟩))
  obtain ⟨φ, hφ, hlim⟩ := FiniteMeasure.tendsto_subseq_of_mapClusterPt hcluster
  -- Push the limit forward to `α`.
  have hmap := FiniteMeasure.tendsto_map_of_tendsto_of_continuous _ _ hlim continuous_subtypeVal
  refine ⟨ν.map Subtype.val, ψ ∘ φ, inferInstance, hψ.comp hφ, ?_, fun g => ?_⟩
  · rw [← FiniteMeasure.ennreal_mass, ENNReal.coe_le_coe]
    exact (FiniteMeasure.mass_map_le measurable_subtypeVal.aemeasurable).trans <|
      closure_minimal hτ_mass (isClosed_le FiniteMeasure.continuous_mass continuous_const) hν
  · simpa only [Function.comp_apply, hτ] using
      FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hmap g

open scoped CompactlySupported in
/-- If weighting by a strictly positive continuous function frequently puts a sequence of Borel
measures on a metrizable space into a tight set with bounded mass, then the sequence has a locally
finite subsequential limit against every compactly supported continuous test function. The
unweighted measures may have infinite mass. -/
theorem exists_subseq_tendsto_integral_of_withDensity [PseudoMetrizableSpace α]
    (σ : ℕ → Measure α) (w : α → ℝ≥0) (hw : Continuous w) (hpos : ∀ x, 0 < w x)
    {S : Set (Measure α)} (C : ℝ≥0) (hmass : ∀ μ ∈ S, μ univ ≤ C) (hTight : IsTightMeasureSet S)
    (hσ : ∃ᶠ n in atTop, ((σ n).withDensity fun x => w x) ∈ S) :
    ∃ (μ : Measure α) (φ : ℕ → ℕ), IsLocallyFiniteMeasure μ ∧ StrictMono φ ∧
      ∀ f : C_c(α, ℝ), Tendsto (fun k => ∫ x, f x ∂σ (φ k)) atTop
        (𝓝 (∫ x, f x ∂μ)) := by
  obtain ⟨ρ, φ, hρ, hφ, -, hlim⟩ :=
    exists_subseq_tendsto_integral_of_isTightMeasureSet (fun n => (σ n).withDensity fun x => w x)
      C hmass hTight hσ
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
/-- **Vague compactness.** A sequence of Borel measures on a locally compact, σ-compact,
metrizable space that frequently lies in a set of measures with uniformly bounded masses on each
compact set has a subsequence converging vaguely, that is against every continuous compactly
supported function, to a locally finite measure. The measures may have infinite total mass. -/
theorem exists_subseq_tendsto_integral_of_iSup_measure_ne_top [LocallyCompactSpace α]
    [SigmaCompactSpace α] [PseudoMetrizableSpace α] (σ : ℕ → Measure α) {S : Set (Measure α)}
    (hS : ∀ K, IsCompact K → ⨆ μ ∈ S, μ K ≠ ∞) (hσ : ∃ᶠ n in atTop, σ n ∈ S) :
    ∃ (μ : Measure α) (φ : ℕ → ℕ), IsLocallyFiniteMeasure μ ∧ StrictMono φ ∧
      ∀ f : C_c(α, ℝ), Tendsto (fun k => ∫ x, f x ∂σ (φ k)) atTop
        (𝓝 (∫ x, f x ∂μ)) := by
  -- Pass to a subsequence `σ ∘ ψ` in `S`, whose compact-set masses are uniformly bounded.
  obtain ⟨ψ, hψ, hψS⟩ := extraction_of_frequently_atTop hσ
  obtain ⟨w, K, hw, hpos, htail⟩ := exists_weight_of_iSup_measure_ne_top (σ ∘ ψ) fun K hK ↦
    ne_top_of_le_ne_top (hS K hK) (iSup_le fun n ↦ le_iSup₂_of_le (σ (ψ n)) (hψS n) le_rfl)
  let ρ : ℕ → Measure α := fun n ↦ (σ (ψ n)).withDensity fun x ↦ w x
  -- The total mass is the case `S = univ`, `N = 0`.
  have hmass : ∀ ν ∈ range ρ, ν univ ≤ (2 : ℝ≥0) := by
    rintro - ⟨n, rfl⟩
    rw [withDensity_apply _ MeasurableSet.univ]
    simpa using htail univ 0 (fun k hk ↦ absurd hk (Nat.not_lt_zero k)) n
  -- The tails outside `K N` are uniformly small.
  have hTight : IsTightMeasureSet (range ρ) := by
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
  obtain ⟨μ, φ, hμ, hφ, hlim⟩ := exists_subseq_tendsto_integral_of_withDensity (σ ∘ ψ) w hw hpos
    2 hmass hTight (.of_forall fun n ↦ ⟨n, rfl⟩)
  exact ⟨μ, ψ ∘ φ, hμ, hψ.comp hφ, hlim⟩

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
