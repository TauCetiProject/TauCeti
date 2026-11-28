/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import Mathlib.MeasureTheory.Integral.CompactlySupported
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.Topology.UrysohnsLemma
public import TauCeti.MeasureTheory.Function.Lp.CompactlySupported
import TauCeti.MeasureTheory.Function.Lp.InfiniteSum

/-!
# `Lᵖ` functions on a locally compact space

Let `μ` be a measure on a weakly locally compact `R₁` space `X` with its Borel σ-algebra that is
finite on compact sets and inner regular with respect to compact sets on measurable sets of finite
measure (`IsFiniteMeasureOnCompacts μ` and `μ.InnerRegularCompactLTTop`), for instance a Haar
measure on a locally compact group. This file proves that compactly supported continuous functions
are dense in `Lᵖ(X, μ)` for `p < ∞`, and that every integrable function is the `L¹` and
almost-everywhere sum of an `L¹`-absolutely convergent series of compactly supported continuous
functions.

Mathlib's `MeasureTheory.MemLp.exists_hasCompactSupport_eLpNorm_sub_le` assumes `NormalSpace X`
and `μ.Regular` in addition to `R1Space X` and `WeaklyLocallyCompactSpace X`, and Mathlib provides
no `NormalSpace` instance for locally compact groups. Neither normality nor global outer
regularity is needed here: the indicator function of a measurable set `t` of finite measure is
approximated directly. Choose a compact closed `K ⊆ t` with `μ (t \ K)` small and, by local
finiteness and inner regularity on compact sets, an open `U ⊇ K` with `μ (U \ K)` small, then
apply Urysohn's lemma for the compact set `K` inside the open set `U`, which holds in every
locally compact regular space. Mathlib's `MeasureTheory.MemLp.induction_dense` extends the
approximation from indicator functions to all of `Lᵖ`.

## Main results

* `MeasureTheory.exists_hasCompactSupport_eLpNorm_sub_indicator_le`: a constant multiple of the
  indicator function of a measurable set of finite measure is approximated in `Lᵖ` by compactly
  supported continuous functions.
* `MeasureTheory.MemLp.exists_hasCompactSupport_eLpNorm_sub_le_of_locallyCompactSpace`: every
  `Lᵖ` function, `p < ∞`, is approximated in `Lᵖ` by compactly supported continuous functions.
* `MeasureTheory.Lp.dense_setOf_continuous_hasCompactSupport` and
  `CompactlySupportedContinuousMap.denseRange_toLp`: the classes of compactly supported continuous
  functions are dense in `Lᵖ`, `p < ∞`.
* `MeasureTheory.Integrable.exists_sum_compactlySupported_tendsto`: on a weakly locally compact
  `R₁` Borel space with a measure finite on compact sets and compact inner regular on
  finite-measure sets, every integrable function is approximated in `L¹` and almost everywhere by
  partial sums of a sequence in `C_c(X, E)` with summable `L¹` norms.
* `CompactlySupportedContinuousMap.exists_hasSum_toLp`: every `Lᵖ` class (`p < ∞`) is the sum of
  an absolutely norm-summable series of compactly supported continuous functions.

## References

* W. Rudin, *Real and Complex Analysis*, 3rd ed., McGraw–Hill (1987), Theorem 3.14.
-/

public section

noncomputable section

open Filter MeasureTheory Topology
open scoped ENNReal CompactlySupported

namespace MeasureTheory

variable {X E : Type*} [TopologicalSpace X] [R1Space X] [WeaklyLocallyCompactSpace X]
  [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure X} {p : ℝ≥0∞}

section Dense

variable [BorelSpace X] [IsFiniteMeasureOnCompacts μ] [μ.InnerRegularCompactLTTop]

/-- In a weakly locally compact `R₁` space, the indicator function of a measurable set of finite
measure with constant value `c` is approximated in `Lᵖ`, `p < ∞`, by compactly supported continuous
functions. -/
theorem exists_hasCompactSupport_eLpNorm_sub_indicator_le (hp : p ≠ ∞) (c : E) {t : Set X}
    (ht : MeasurableSet t) (htμ : μ t < ∞) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ g : X → E, eLpNorm (g - t.indicator fun _ => c) p μ ≤ ε ∧
      (Continuous g ∧ HasCompactSupport g) := by
  obtain ⟨η, hη0, hη⟩ := exists_eLpNorm_indicator_le (μ := μ) hp c hε
  have hη2 : (η : ℝ≥0∞) / 2 ≠ 0 := (ENNReal.half_pos (by exact_mod_cast hη0.ne')).ne'
  obtain ⟨K, hKt, hKc, hKcl, hK⟩ := ht.exists_isCompact_isClosed_sdiff_lt htμ.ne hη2
  obtain ⟨U, hKU, hUo, hμU⟩ := hKc.exists_isOpen_lt_add (μ := μ) hη2
  have hUK : μ (U \ K) < η / 2 :=
    measure_sdiff_lt_of_lt_add hKcl.nullMeasurableSet hKU
      (ne_top_of_le_ne_top htμ.ne (measure_mono hKt)) hμU
  obtain ⟨f, hfK, hfU, hfs, hf01⟩ := exists_continuous_one_zero_of_isCompact hKc
    hUo.isClosed_compl (Set.disjoint_compl_right_iff_subset.2 hKU)
  refine ⟨fun x => f x • c,
    (eLpNorm_mono ((f.continuous.aestronglyMeasurable.smul_const c).sub
      (aestronglyMeasurable_const.indicator ht)) fun x => ?_).trans
      (hη ((U \ K) ∪ (t \ K)) ?_
        (((hUo.measurableSet.diff hKcl.measurableSet).union
          (ht.diff hKcl.measurableSet)).nullMeasurableSet)),
    f.continuous.smul continuous_const, hfs.smul_right⟩
  · -- `f • c` agrees with `c` on `K` and with `0` outside `U ∪ t`, and is bounded by `‖c‖`.
    simp only [Pi.sub_apply]
    have hf1 : |f x - 1| ≤ 1 :=
      abs_sub_le_iff.2 ⟨by linarith [(hf01 x).2], by linarith [(hf01 x).1]⟩
    by_cases hxK : x ∈ K
    · simp [hfK hxK, hKt hxK]
    by_cases hxUt : x ∈ U ∨ x ∈ t
    · rw [Set.indicator_of_mem
        (hxUt.elim (fun h => Set.mem_union_left _ (And.intro h hxK))
          (fun h => Set.mem_union_right _ (And.intro h hxK)))]
      by_cases hxt : x ∈ t
      · have hsub : f x • c - c = (f x - 1) • c := by rw [sub_smul, one_smul]
        rw [Set.indicator_of_mem hxt, hsub, norm_smul, Real.norm_eq_abs]
        exact mul_le_of_le_one_left (norm_nonneg c) hf1
      · rw [Set.indicator_of_notMem hxt, sub_zero, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (hf01 x).1]
        exact mul_le_of_le_one_left (norm_nonneg c) (hf01 x).2
    · simp [hfU (not_or.1 hxUt).1, Set.indicator_of_notMem (not_or.1 hxUt).2]
  · calc μ ((U \ K) ∪ (t \ K)) ≤ μ (U \ K) + μ (t \ K) := measure_union_le _ _
      _ ≤ η / 2 + η / 2 := add_le_add hUK.le hK.le
      _ = η := ENNReal.add_halves _

/-- **Density of compactly supported continuous functions in `Lᵖ`** for a measure on a weakly
locally compact `R₁` space that is finite on compact sets and inner regular on sets of finite
measure, `p < ∞`. Unlike `MeasureTheory.MemLp.exists_hasCompactSupport_eLpNorm_sub_le`, neither
normality of the space nor global outer regularity of the measure is assumed. -/
theorem MemLp.exists_hasCompactSupport_eLpNorm_sub_le_of_locallyCompactSpace (hp : p ≠ ∞)
    {f : X → E} (hf : MemLp f p μ) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ g : X → E, HasCompactSupport g ∧ eLpNorm (f - g) p μ ≤ ε ∧ Continuous g ∧ MemLp g p μ := by
  have hind (c : E) ⦃t : Set X⦄ (ht : MeasurableSet t) (htμ : μ t < ∞) {δ : ℝ≥0∞} (hδ : δ ≠ 0) :
      ∃ g : X → E, eLpNorm (g - t.indicator fun _ => c) p μ ≤ δ ∧
        (Continuous g ∧ HasCompactSupport g) :=
    exists_hasCompactSupport_eLpNorm_sub_indicator_le hp c ht htμ hδ
  obtain ⟨g, hfg, hgc, hgs⟩ := hf.induction_dense hp
    (fun g : X → E => Continuous g ∧ HasCompactSupport g) hind
    (fun _ _ hf hg => ⟨hf.1.add hg.1, hf.2.add hg.2⟩) hε
  exact ⟨g, hgs, hfg, hgc, hgc.memLp_of_hasCompactSupport hgs⟩

/-- **Density of compactly supported continuous functions in `Lᵖ`** for a measure on a weakly
locally compact `R₁` space that is finite on compact sets and inner regular on sets of finite
measure, `p < ∞`: the classes of compactly supported continuous functions are dense in
`Lp E p μ`. -/
theorem Lp.dense_setOf_continuous_hasCompactSupport [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    Dense {u : Lp E p μ | ∃ f : X → E, Continuous f ∧ HasCompactSupport f ∧ u =ᵐ[μ] f} := by
  refine Metric.dense_iff.2 fun u r hr => ?_
  obtain ⟨f, hfs, hf, hfc, hfp⟩ :=
    (Lp.memLp u).exists_hasCompactSupport_eLpNorm_sub_le_of_locallyCompactSpace hp
      (ENNReal.ofReal_pos.2 (half_pos hr)).ne'
  refine ⟨hfp.toLp f, ?_, f, hfc, hfs, hfp.coeFn_toLp⟩
  rw [Metric.mem_ball, dist_comm, Lp.dist_def,
    eLpNorm_congr_ae (EventuallyEq.rfl.sub hfp.coeFn_toLp)]
  exact (ENNReal.toReal_le_of_le_ofReal (half_pos hr).le hf).trans_lt (half_lt_self hr)

end Dense

end MeasureTheory

namespace CompactlySupportedContinuousMap

variable {X E : Type*} [TopologicalSpace X] [MeasurableSpace X] [NormedAddCommGroup E]

/-- Compactly supported continuous functions have dense range in `Lp E p μ` for `p < ∞`. -/
theorem denseRange_toLp [R1Space X] [WeaklyLocallyCompactSpace X] [BorelSpace X]
    [NormedSpace ℝ E] {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) (μ : Measure X)
    [IsFiniteMeasureOnCompacts μ] [μ.InnerRegularCompactLTTop]
    (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] :
    DenseRange (toLp (X := X) (E := E) p μ 𝕜) := by
  refine (Lp.dense_setOf_continuous_hasCompactSupport (X := X) (E := E) (μ := μ) hp).mono ?_
  rintro u ⟨f, hfc, hfs, hfu⟩
  let f' : C_c(X, E) := ⟨⟨f, hfc⟩, hfs⟩
  exact ⟨f', Lp.ext ((coeFn_toLp 𝕜 f').trans hfu.symm)⟩

/-- Every `Lᵖ` class (`p < ∞`) on a weakly locally compact `R₁` space is the sum of an
absolutely norm-summable series of compactly supported continuous functions. -/
theorem exists_hasSum_toLp [R1Space X] [WeaklyLocallyCompactSpace X] [BorelSpace X]
    [NormedSpace ℝ E] {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) (μ : Measure X)
    [IsFiniteMeasureOnCompacts μ] [μ.InnerRegularCompactLTTop]
    (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] (v : Lp E p μ) :
    ∃ ψ : ℕ → C_c(X, E),
      HasSum (fun n => toLp p μ 𝕜 (ψ n)) v ∧ Summable fun n => ‖toLp p μ 𝕜 (ψ n)‖ := by
  let S : AddSubgroup (Lp E p μ) := (toLp (X := X) (E := E) p μ 𝕜).toAddMonoidHom.range
  have hmem : v ∈ closure (S : Set (Lp E p μ)) := by
    simpa [S, AddMonoidHom.coe_range] using
      (denseRange_toLp (X := X) (E := E) hp μ 𝕜).closure_range ▸ Set.mem_univ v
  obtain ⟨w, hw_lim, hw_mem, -, hw⟩ :=
    controlled_sum_of_mem_closure hmem (b := fun n : ℕ => (1 / 2 : ℝ) ^ n) fun _ => by positivity
  choose ψ hψ using hw_mem
  have hψ' (n : ℕ) : toLp p μ 𝕜 (ψ n) = w n := hψ n
  have hnorm : Summable fun n => ‖toLp p μ 𝕜 (ψ n)‖ := by
    refine (summable_nat_add_iff 1).1 (.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
      (summable_geometric_two.comp_injective (add_left_injective 1)))
    simpa only [hψ', Function.comp_apply, add_comm] using (hw (n + 1) n.succ_pos).le
  refine ⟨ψ, (hasSum_iff_tendsto_nat_of_summable_norm hnorm).2 ?_, hnorm⟩
  simpa only [hψ'] using (tendsto_add_atTop_iff_nat 1).1 hw_lim

end CompactlySupportedContinuousMap

namespace MeasureTheory

/-- On a weakly locally compact `R₁` space `X` with its Borel σ-algebra and a measure `μ` finite on
compact sets and inner regular with respect to compact sets on sets of finite measure, every
integrable function `f : X → E` is approximated by a sequence `φ : ℕ → C_c(X, E)` that is the
partial-sum sequence of `u : ℕ → C_c(X, E)` with summable `L¹` norms, converging to `f` both in
`Lp E 1 μ` and `μ`-almost everywhere. -/
theorem Integrable.exists_sum_compactlySupported_tendsto {X E : Type*} [TopologicalSpace X]
    [R1Space X] [WeaklyLocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure X} [IsFiniteMeasureOnCompacts μ]
    [μ.InnerRegularCompactLTTop] {f : X → E} (hf : Integrable f μ) :
    ∃ (φ u : ℕ → C_c(X, E)),
      (∀ n, ∑ i ∈ Finset.range (n + 1), u i = φ n) ∧
      Tendsto (fun n => (φ n).integrable.toL1 (φ n)) atTop (𝓝 (hf.toL1 f)) ∧
      (∀ᵐ x ∂μ, Tendsto (fun n => φ n x) atTop (𝓝 (f x))) ∧
      (∑' k, ∫⁻ x, ‖u k x‖ₑ ∂μ) ≠ ∞ := by
  obtain ⟨u, hu_sum, hu_norm⟩ :=
    CompactlySupportedContinuousMap.exists_hasSum_toLp ENNReal.one_ne_top μ ℝ (hf.toL1 f)
  let φ : ℕ → C_c(X, E) := fun n => ∑ i ∈ Finset.range (n + 1), u i
  have hL1_eq (n : ℕ) :
      (φ n).integrable.toL1 (φ n) =
        ∑ i ∈ Finset.range (n + 1), CompactlySupportedContinuousMap.toLp 1 μ ℝ (u i) := by
    rw [← map_sum]
    exact Lp.ext
      ((φ n).integrable.coeFn_toL1.trans (CompactlySupportedContinuousMap.coeFn_toLp ℝ (φ n)).symm)
  have hL1 : Tendsto (fun n => (φ n).integrable.toL1 (φ n)) atTop (𝓝 (hf.toL1 f)) := by
    simp_rw [hL1_eq]
    exact hu_sum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hae : ∀ᵐ x ∂μ, Tendsto (fun n => φ n x) atTop (𝓝 (f x)) := by
    filter_upwards [CompactlySupportedContinuousMap.ae_hasSum_of_hasSum_toLp ℝ hu_sum hu_norm,
      hf.coeFn_toL1] with x ⟨hx, _⟩ hfx
    simp only [φ, CompactlySupportedContinuousMap.coe_sum, Finset.sum_apply]
    exact (hfx ▸ hx).tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hnorm_k (k : ℕ) :
      ∫⁻ x, ‖u k x‖ₑ ∂μ = ENNReal.ofReal ‖CompactlySupportedContinuousMap.toLp 1 μ ℝ (u k)‖ := by
    rw [CompactlySupportedContinuousMap.norm_toLp,
      eLpNorm_one_eq_lintegral_eNorm (u k).integrable.aestronglyMeasurable,
      ENNReal.ofReal_toReal (u k).integrable.2.ne]
  have hu_lt : (∑' k, ∫⁻ x, ‖u k x‖ₑ ∂μ) ≠ ∞ := by
    simp_rw [hnorm_k, ← ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) hu_norm]
    exact ENNReal.ofReal_ne_top
  exact ⟨φ, u, fun _ => rfl, hL1, hae, hu_lt⟩

end MeasureTheory
