/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.Topology.UrysohnsLemma

/-!
# `Lᵖ` functions on a locally compact space

Let `μ` be a regular measure on a locally compact regular space `X` with its Borel σ-algebra, for
instance a Haar measure on a locally compact group. This file proves that compactly supported
continuous functions are dense in `Lᵖ(X, μ)` for `p < ∞`, and that every neighbourhood of a point
supports a nonnegative `L¹` function of integral one.

Mathlib's `MeasureTheory.MemLp.exists_hasCompactSupport_eLpNorm_sub_le` assumes a normal space,
which a locally compact group need not be. Here the indicator function of a measurable set `t` of
finite measure is approximated directly: choose a compact closed `K ⊆ t` and an open `U ⊇ t` with
`μ (U \ K)` small, and apply Urysohn's lemma for the compact set `K` inside the open set `U`, which
holds in every locally compact regular space. Mathlib's `MeasureTheory.MemLp.induction_dense`
extends the approximation from indicator functions to all of `Lᵖ`.

The normalized indicator functions of neighbourhoods of the identity of a locally compact group are
the kernels of the approximate identities for convolution.

## Main results

* `MeasureTheory.exists_hasCompactSupport_eLpNorm_sub_indicator_le`: a constant multiple of the
  indicator function of a measurable set of finite measure is approximated in `Lᵖ` by compactly
  supported continuous functions.
* `MeasureTheory.MemLp.exists_hasCompactSupport_eLpNorm_sub_le_of_locallyCompactSpace`: every
  `Lᵖ` function, `p < ∞`, is approximated in `Lᵖ` by compactly supported continuous functions.
* `MeasureTheory.Lp.exists_nonneg_integral_eq_one_of_mem_nhds`: every neighbourhood of a point
  supports a nonnegative `L¹` function of integral one.

## References

* W. Rudin, *Real and Complex Analysis*, 3rd ed., McGraw–Hill (1987), Theorem 3.14.
-/

public section

noncomputable section

open Filter MeasureTheory Topology
open scoped ENNReal

namespace MeasureTheory

variable {X E : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure X} {p : ℝ≥0∞}

section Dense

variable [RegularSpace X] [BorelSpace X] [μ.Regular]

/-- In a locally compact regular space, the indicator function of a measurable set of finite
measure with constant value `c` is approximated in `Lᵖ`, `p < ∞`, by compactly supported continuous
functions. -/
theorem exists_hasCompactSupport_eLpNorm_sub_indicator_le (hp : p ≠ ∞) (c : E) {t : Set X}
    (ht : MeasurableSet t) (htμ : μ t < ∞) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ g : X → E, eLpNorm (g - t.indicator fun _ => c) p μ ≤ ε ∧
      (Continuous g ∧ HasCompactSupport g) := by
  obtain ⟨η, hη0, hη⟩ := exists_eLpNorm_indicator_le (μ := μ) hp c hε
  have hη2 : (η : ℝ≥0∞) / 2 ≠ 0 := (ENNReal.half_pos (by exact_mod_cast hη0.ne')).ne'
  obtain ⟨K, hKt, hKc, hKcl, hK⟩ := ht.exists_isCompact_isClosed_sdiff_lt htμ.ne hη2
  obtain ⟨U, htU, hUo, -, hU⟩ := ht.exists_isOpen_sdiff_lt htμ.ne hη2
  obtain ⟨f, hfK, hfU, hfs, hf01⟩ := exists_continuous_one_zero_of_isCompact hKc
    hUo.isClosed_compl (Set.disjoint_compl_right_iff_subset.2 (hKt.trans htU))
  refine ⟨fun x => f x • c,
    (eLpNorm_mono ((f.continuous.aestronglyMeasurable.smul_const c).sub
      (aestronglyMeasurable_const.indicator ht)) fun x => ?_).trans
      (hη (U \ K) ?_ (hUo.measurableSet.diff hKcl.measurableSet).nullMeasurableSet),
    f.continuous.smul continuous_const, hfs.smul_right⟩
  · -- `f • c` agrees with `c` on `K` and with `0` outside `U`, and is bounded by `‖c‖`.
    simp only [Pi.sub_apply]
    have hf1 : |f x - 1| ≤ 1 :=
      abs_sub_le_iff.2 ⟨by linarith [(hf01 x).2], by linarith [(hf01 x).1]⟩
    by_cases hxK : x ∈ K
    · simp [hfK hxK, hKt hxK]
    by_cases hxU : x ∈ U
    · rw [Set.indicator_of_mem (show x ∈ U \ K from ⟨hxU, hxK⟩)]
      by_cases hxt : x ∈ t
      · have hsub : f x • c - c = (f x - 1) • c := by rw [sub_smul, one_smul]
        rw [Set.indicator_of_mem hxt, hsub, norm_smul, Real.norm_eq_abs]
        exact mul_le_of_le_one_left (norm_nonneg c) hf1
      · rw [Set.indicator_of_notMem hxt, sub_zero, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (hf01 x).1]
        exact mul_le_of_le_one_left (norm_nonneg c) (hf01 x).2
    · simp [hfU hxU, Set.indicator_of_notMem fun hxt => hxU (htU hxt)]
  · -- `U \ K` lies in `(U \ t) ∪ (t \ K)`, of measure less than `η`.
    have hsub : U \ K ⊆ U \ t ∪ t \ K := fun x hx => by
      by_cases hxt : x ∈ t
      exacts [Or.inr ⟨hxt, hx.2⟩, Or.inl ⟨hx.1, hxt⟩]
    calc μ (U \ K) ≤ μ (U \ t) + μ (t \ K) := (measure_mono hsub).trans (measure_union_le _ _)
      _ ≤ η / 2 + η / 2 := add_le_add hU.le hK.le
      _ = η := ENNReal.add_halves _

/-- **Density of compactly supported continuous functions in `Lᵖ`** for a regular measure on a
locally compact regular space, `p < ∞`. Unlike
`MeasureTheory.MemLp.exists_hasCompactSupport_eLpNorm_sub_le`, no normality of the space is
assumed. -/
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

end Dense

namespace Lp

variable [OpensMeasurableSpace X] [μ.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts μ]

/-- Every neighbourhood `U` of a point `x` of a locally compact space supports a nonnegative `L¹`
kernel of integral one: the normalized indicator function of the interior of a compact
neighbourhood of `x` inside `U`. On a locally compact group, kernels for the neighbourhoods of `1`
feed `MeasureTheory.Lp.tendsto_convolutionL_left` and
`MeasureTheory.Lp.tendsto_convolutionL_right`. -/
theorem exists_nonneg_integral_eq_one_of_mem_nhds {x : X} {U : Set X} (hU : U ∈ 𝓝 x) :
    ∃ k : Lp ℝ 1 μ, 0 ≤ k ∧ ∫ y, k y ∂μ = 1 ∧ ∀ᵐ y ∂μ, y ∉ U → k y = 0 := by
  obtain ⟨V, hV1, hVU, hVc⟩ := local_compact_nhds hU
  have hW1 : interior V ∈ 𝓝 x := isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.2 hV1)
  have hWm : MeasurableSet (interior V) := isOpen_interior.measurableSet
  have hWfin : μ (interior V) ≠ ∞ :=
    ((measure_mono interior_subset).trans_lt hVc.measure_lt_top).ne
  have hWpos : μ.real (interior V) ≠ 0 :=
    (ENNReal.toReal_pos (Measure.measure_pos_of_mem_nhds μ hW1).ne' hWfin).ne'
  refine ⟨indicatorConstLp 1 hWm hWfin (μ.real (interior V))⁻¹, ?_, ?_, ?_⟩
  · rw [← coeFn_nonneg]
    filter_upwards [indicatorConstLp_coeFn (p := 1) (hs := hWm) (hμs := hWfin)
      (c := (μ.real (interior V))⁻¹)] with y hy
    rw [hy]
    exact Set.indicator_nonneg (fun _ _ => inv_nonneg.2 measureReal_nonneg) y
  · rw [integral_indicatorConstLp, smul_eq_mul, mul_inv_cancel₀ hWpos]
  · filter_upwards [indicatorConstLp_coeFn (p := 1) (hs := hWm) (hμs := hWfin)
      (c := (μ.real (interior V))⁻¹)] with y hy hyU
    rw [hy, Set.indicator_of_notMem fun hyV => hyU (hVU (interior_subset hyV))]

end Lp

end MeasureTheory
