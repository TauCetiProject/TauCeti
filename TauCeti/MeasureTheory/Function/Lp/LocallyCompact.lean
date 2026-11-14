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

/-!
# `Lᵖ` functions on a locally compact space

Let `μ` be a locally finite measure on a weakly locally compact `R₁` space `X` with its Borel
σ-algebra that is inner regular on sets of finite measure with respect to compact sets
(`[IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop]`), for instance either a regular or an
inner regular Haar measure on a locally compact group. This file proves that compactly supported
continuous functions are dense in `Lᵖ(X, μ)` for `p < ∞`, and that every integrable function is
the `L¹` and almost-everywhere sum of an `L¹`-absolutely convergent series of compactly supported
continuous functions.

Mathlib's `MeasureTheory.MemLp.exists_hasCompactSupport_eLpNorm_sub_le` assumes `NormalSpace X`
in addition to `R1Space X` and `WeaklyLocallyCompactSpace X`, and Mathlib provides no
`NormalSpace` instance for locally compact groups. Here normality and global outer regularity are
not needed: the indicator function of a measurable set `t` of finite measure is approximated
directly. Choose a compact closed `K ⊆ t` with `μ (t \ K)` small and an open `U ⊇ K` with
`μ (U \ K)` small, and apply Urysohn's lemma for the compact set `K` inside the open set `U`,
which holds in every locally compact regular space. Mathlib's
`MeasureTheory.MemLp.induction_dense` extends the approximation from indicator functions to all
of `Lᵖ`.

## Main results

* `MeasureTheory.exists_hasCompactSupport_eLpNorm_sub_indicator_le`: a constant multiple of the
  indicator function of a measurable set of finite measure is approximated in `Lᵖ` by compactly
  supported continuous functions.
* `MeasureTheory.MemLp.exists_hasCompactSupport_eLpNorm_sub_le_of_locallyCompactSpace`: every
  `Lᵖ` function, `p < ∞`, is approximated in `Lᵖ` by compactly supported continuous functions.
* `MeasureTheory.Lp.dense_setOf_continuous_hasCompactSupport`: the classes of compactly supported
  continuous functions are dense in `Lᵖ`, `p < ∞`.
* `MeasureTheory.Integrable.exists_sum_compactlySupported_tendsto`: every integrable function is
  approximated in `L¹` and almost everywhere by partial sums of a sequence in `C_c(X, E)` with
  summable `L¹` norms.

## References

* W. Rudin, *Real and Complex Analysis*, 3rd ed., McGraw–Hill (1987), Theorem 3.14.
-/

public section

noncomputable section

open Filter MeasureTheory Topology
open scoped CompactlySupported ENNReal

namespace MeasureTheory

variable {X E : Type*} [TopologicalSpace X] [R1Space X] [WeaklyLocallyCompactSpace X]
  [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure X} {p : ℝ≥0∞}

section Dense

variable [BorelSpace X] [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop]

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
  obtain ⟨U, hKU, hUo, hU⟩ := hKc.exists_isOpen_lt_add (μ := μ) hη2
  obtain ⟨f, hfK, hfU, hfs, hf01⟩ := exists_continuous_one_zero_of_isCompact hKc
    hUo.isClosed_compl (Set.disjoint_compl_right_iff_subset.2 hKU)
  refine ⟨fun x => f x • c,
    (eLpNorm_mono ((f.continuous.aestronglyMeasurable.smul_const c).sub
      (aestronglyMeasurable_const.indicator ht)) fun x => ?_).trans
      (hη (U \ K ∪ t \ K) ?_
        ((hUo.measurableSet.diff hKcl.measurableSet).union
          (ht.diff hKcl.measurableSet)).nullMeasurableSet),
    f.continuous.smul continuous_const, hfs.smul_right⟩
  · -- `f • c` agrees with `c` on `K` and with `0` outside `U ∪ t`, and is bounded by `‖c‖`.
    simp only [Pi.sub_apply]
    have hf1 : |f x - 1| ≤ 1 :=
      abs_sub_le_iff.2 ⟨by linarith [(hf01 x).2], by linarith [(hf01 x).1]⟩
    by_cases hxK : x ∈ K
    · simp [hfK hxK, hKt hxK]
    by_cases hxt : x ∈ t
    · have hfc : f x • c - c = (f x - 1) • c := by rw [sub_smul, one_smul]
      have hmem : x ∈ U \ K ∪ t \ K := Set.mem_union_right _ ⟨hxt, hxK⟩
      rw [Set.indicator_of_mem hxt, Set.indicator_of_mem hmem, hfc, norm_smul, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg c) hf1
    by_cases hxU : x ∈ U
    · have hmem : x ∈ U \ K ∪ t \ K := Set.mem_union_left _ ⟨hxU, hxK⟩
      rw [Set.indicator_of_notMem hxt, Set.indicator_of_mem hmem, sub_zero, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg (hf01 x).1]
      exact mul_le_of_le_one_left (norm_nonneg c) (hf01 x).2
    · simp [hfU hxU, Set.indicator_of_notMem hxt]
  · -- Both `U \ K` and `t \ K` have measure less than `η / 2`.
    have hUK : μ (U \ K) < η / 2 :=
      measure_sdiff_lt_of_lt_add hKcl.nullMeasurableSet hKU hKc.measure_lt_top.ne hU
    calc μ (U \ K ∪ t \ K) ≤ μ (U \ K) + μ (t \ K) := measure_union_le _ _
      _ ≤ η / 2 + η / 2 := add_le_add hUK.le hK.le
      _ = η := ENNReal.add_halves _

/-- **Density of compactly supported continuous functions in `Lᵖ`** for a locally finite measure
inner regular on finite-measure sets on a weakly locally compact `R₁` space, `p < ∞`. Unlike
`MeasureTheory.MemLp.exists_hasCompactSupport_eLpNorm_sub_le`, neither normality of the space nor
outer regularity on sets of infinite measure is assumed. -/
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

/-- **Density of compactly supported continuous functions in `Lᵖ`** for a locally finite measure
inner regular on finite-measure sets on a weakly locally compact `R₁` space, `p < ∞`: the classes
of compactly supported continuous functions are dense in `Lp E p μ`. -/
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

/-- Every integrable function `f : X → E` is approximated by a sequence `φ : ℕ → C_c(X, E)` that
is the partial-sum sequence of `u : ℕ → C_c(X, E)` with summable `L¹` norms, converging to `f`
both in `Lp E 1 μ` and `μ`-almost everywhere. -/
theorem Integrable.exists_sum_compactlySupported_tendsto {f : X → E} (hf : Integrable f μ) :
    ∃ (φ u : ℕ → C_c(X, E)),
      (∀ n, ∑ i ∈ Finset.range (n + 1), u i = φ n) ∧
      Tendsto (fun n => (φ n).integrable.toL1 (φ n)) atTop (𝓝 (hf.toL1 f)) ∧
      (∀ᵐ x ∂μ, Tendsto (fun n => φ n x) atTop (𝓝 (f x))) ∧
      (∑' k, ∫⁻ x, ‖u k x‖ₑ ∂μ) ≠ ∞ := by
  have hf_memLp : MemLp f 1 μ := memLp_one_iff_integrable.2 hf
  choose g hgs hfg hgc _ using fun n : ℕ =>
    hf_memLp.exists_hasCompactSupport_eLpNorm_sub_le_of_locallyCompactSpace ENNReal.one_ne_top
      (ENNReal.pow_pos (a := 2⁻¹) (by simp) n).ne'
  let φ : ℕ → C_c(X, E) := fun n => ⟨⟨g n, hgc n⟩, hgs n⟩
  have hdist (n : ℕ) : eLpNorm ((φ n : X → E) - f) 1 μ ≤ (2⁻¹ : ℝ≥0∞) ^ n := by
    rw [eLpNorm_sub_comm]; exact hfg n
  have hgeom : (∑' n : ℕ, (2⁻¹ : ℝ≥0∞) ^ n) ≠ ∞ := by simp
  -- Convergence in `Lp E 1 μ` and `μ`-almost everywhere from `∑' n, eLpNorm (φ n - f) 1 μ < ∞`.
  have hL1 : Tendsto (fun n => (φ n).integrable.toL1 (φ n)) atTop (𝓝 (hf.toL1 f)) := by
    rw [Lp.ext (hf.coeFn_toL1.trans hf_memLp.coeFn_toLp.symm)]
    refine Lp.tendsto_Lp_of_tendsto_eLpNorm f hf_memLp ?_
    simp_rw [eLpNorm_congr_ae ((φ _).integrable.coeFn_toL1.sub EventuallyEq.rfl)]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (ENNReal.tendsto_atTop_zero_of_tsum_ne_top hgeom) (fun _ => zero_le) hdist
  have hae : ∀ᵐ x ∂μ, Tendsto (fun n => φ n x) atTop (𝓝 (f x)) := by
    have hmeas (n : ℕ) : AEMeasurable (fun x => ‖φ n x - f x‖ₑ) μ :=
      ((φ n).integrable.sub hf).aestronglyMeasurable.eNorm
    have hsum_ae : ∫⁻ x, (∑' n, ‖φ n x - f x‖ₑ) ∂μ ≠ ∞ := by
      rw [lintegral_tsum hmeas]
      refine ne_top_of_le_ne_top hgeom (tsum_le_tsum fun n => ?_)
      simpa only [eLpNorm_one_eq_lintegral_eNorm ((φ n).integrable.sub hf).aestronglyMeasurable,
        Pi.sub_apply] using hdist n
    filter_upwards [ae_lt_top' (AEMeasurable.tsum hmeas) hsum_ae] with x hx
    simpa only [tendsto_iff_edist_tendsto_0, eDist_eq_eNorm_sub] using
      ENNReal.tendsto_atTop_zero_of_tsum_ne_top hx.ne
  -- Telescopic differences `u 0 = φ 0`, `u (n + 1) = φ (n + 1) - φ n`.
  let u : ℕ → C_c(X, E) := fun k => match k with | 0 => φ 0 | n + 1 => φ (n + 1) - φ n
  have hu_succ (n : ℕ) : u (n + 1) = φ (n + 1) - φ n := rfl
  have hsum_u (n : ℕ) : ∑ i ∈ Finset.range (n + 1), u i = φ n := by
    induction n with
    | zero => simp [u]
    | succ n ih => rw [Finset.sum_range_succ, ih, add_sub_cancel]
  have hu_lt : (∑' k, ∫⁻ x, ‖u k x‖ₑ ∂μ) ≠ ∞ := by
    rw [tsum_eq_zero_add' CompleteLattice.summable]
    refine (ENNReal.add_lt_top.2 ⟨(φ 0).integrable.2, ?_⟩).ne
    have hbound (n : ℕ) : ∫⁻ x, ‖u (n + 1) x‖ₑ ∂μ ≤ (2⁻¹ : ℝ≥0∞) ^ (n + 1) + (2⁻¹ : ℝ≥0∞) ^ n := by
      have hsub : ((φ (n + 1) : X → E) - (φ n : X → E)) =
          ((φ (n + 1) : X → E) - f) + (f - (φ n : X → E)) := by ext x; simp
      rw [← eLpNorm_one_eq_lintegral_eNorm (u (n + 1)).integrable.aestronglyMeasurable,
        hu_succ, CompactlySupportedContinuousMap.coe_sub, hsub]
      exact (eLpNorm_add_le le_rfl).trans (add_le_add (hdist (n + 1)) (hfg n))
    refine lt_of_le_of_lt (tsum_le_tsum hbound) ?_
    rw [tsum_add]
    exact ENNReal.add_lt_top.2 ⟨by
      simpa only [pow_succ, ENNReal.tsum_mul_right] using
        ENNReal.mul_lt_top hgeom.lt_top (by simp), hgeom.lt_top⟩
  exact ⟨φ, u, hsum_u, hL1, hae, hu_lt⟩

end Dense

end MeasureTheory
