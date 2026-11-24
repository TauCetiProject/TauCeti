/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Analysis.Normed.Group.Completion

/-!
# Limits at infinity and pointwise bounds for functions of bounded variation

If a function on a linearly ordered space approaches a limit `y` along a nontrivial filter
supported on a set `s`, the extended distance from `f x` (`x ∈ s`) to `y` is at most
`eVariationOn f s`. For a function taking values in a seminormed additive commutative group that
vanishes at both `±∞`, splitting the line at `x` via `eVariationOn.union` gives the sharp bound
`2 * ‖f x‖ₑ ≤ eVariationOn f univ`, and hence `‖f x‖ ≤ (eVariationOn f univ).toReal / 2` whenever
`f` has bounded variation on `univ`. The factor `1 / 2` is attained by `1_[0,1]`.

If `f` is also integrable along `atTop` (or `atBot`) with respect to a measure assigning infinite
measure to every element of the filter—in particular Lebesgue measure on `ℝ`—then bounded variation
forces `f` to tend to `0` at `+∞` (or `-∞`). Passing to `UniformSpace.Completion E` removes any
completeness or vector-space assumption on the codomain `E`.

## Main declarations

* `eVariationOn.edist_le_of_tendsto`: `edist (f x) y ≤ eVariationOn f s` when `f → y` along a
  nontrivial filter supported on `s`.
* `eVariationOn.two_mul_eNorm_le`: `2 * ‖f x‖ₑ ≤ eVariationOn f univ` when `f → 0` at both `±∞`.
* `BoundedVariationOn.tendsto_zero_atTop_of_measure_eq_top` and
  `BoundedVariationOn.tendsto_zero_atBot_of_measure_eq_top`: a function of bounded variation that is
  integrable along `atTop` (or `atBot`) for a measure with infinite tails tends to `0`.
* `BoundedVariationOn.tendsto_zero_atTop` and `BoundedVariationOn.tendsto_zero_atBot`: Lebesgue
  specializations for globally integrable functions `f : ℝ → E` of bounded variation.
* `BoundedVariationOn.norm_le_eVariationOn_toReal_div_two_of_integrable` and
  `BoundedVariationOn.norm_le_eVariationOn_toReal_of_integrable`: pointwise supremum bounds
  `‖f x‖ ≤ (eVariationOn f univ).toReal / 2` and `‖f x‖ ≤ (eVariationOn f univ).toReal` for
  integrable functions `f : ℝ → E` of bounded variation.

## References

* A. Kontorovich, T. Tao, *Prime Number Theorem And ...*, Lemma 3.1.4 (boundary limits of an
  integrable function of bounded variation).
-/

public section

open Filter MeasureTheory Set Topology UniformSpace
open scoped ENNReal

namespace eVariationOn

/-- If `f` tends to `y` along a nontrivial filter `l` supported on `s`, then the extended distance
from `f x` (`x ∈ s`) to `y` is bounded by `eVariationOn f s`. No finiteness of variation is
assumed. -/
theorem edist_le_of_tendsto {α E : Type*} [LinearOrder α] [PseudoEMetricSpace E]
    {f : α → E} {s : Set α} {l : Filter α} [l.NeBot] (hl : l ≤ 𝓟 s)
    {x : α} (hx : x ∈ s) {y : E} (hlim : Tendsto f l (𝓝 y)) :
    edist (f x) y ≤ eVariationOn f s := by
  refine le_of_tendsto (tendsto_const_nhds.edist hlim) ?_
  filter_upwards [hl (mem_principal_self s)] with z hz
  exact eVariationOn.edist_le f hx hz

/-- Seminormed-group specialization of `eVariationOn.edist_le_of_tendsto` for a zero limit. -/
theorem eNorm_le_of_tendsto_zero {α E : Type*} [LinearOrder α] [SeminormedAddCommGroup E]
    {f : α → E} {s : Set α} {l : Filter α} [l.NeBot] (hl : l ≤ 𝓟 s)
    {x : α} (hx : x ∈ s) (hlim : Tendsto f l (𝓝 0)) :
    ‖f x‖ₑ ≤ eVariationOn f s := by
  simpa only [edist_zero_right] using edist_le_of_tendsto hl hx hlim

/-- Sharp two-sided `ℝ≥0∞` bound: if `f` vanishes at both `-∞` and `+∞`, then `2 * ‖f x‖ₑ` is at
most the total variation of `f` on `univ`. -/
theorem two_mul_eNorm_le {α E : Type*} [LinearOrder α] [SeminormedAddCommGroup E]
    {f : α → E} (hbot : Tendsto f atBot (𝓝 0)) (htop : Tendsto f atTop (𝓝 0)) (x : α) :
    2 * ‖f x‖ₑ ≤ eVariationOn f univ := by
  have : Nonempty α := ⟨x⟩
  have hL : ‖f x‖ₑ ≤ eVariationOn f (Iic x) :=
    eNorm_le_of_tendsto_zero (le_principal_iff.mpr (Iic_mem_atBot x)) self_mem_Iic hbot
  have hR : ‖f x‖ₑ ≤ eVariationOn f (Ici x) :=
    eNorm_le_of_tendsto_zero (le_principal_iff.mpr (Ici_mem_atTop x)) self_mem_Ici htop
  calc
    2 * ‖f x‖ₑ = ‖f x‖ₑ + ‖f x‖ₑ := two_mul _
    _ ≤ eVariationOn f (Iic x) + eVariationOn f (Ici x) := add_le_add hL hR
    _ = eVariationOn f (Iic x ∪ Ici x) :=
      (eVariationOn.union f isGreatest_Iic isLeast_Ici).symm
    _ = eVariationOn f univ := by rw [Iic_union_Ici]

end eVariationOn

namespace BoundedVariationOn

section PseudoMetric

variable {α E : Type*} [LinearOrder α]

/-- Real-valued distance bound against a limit along a nontrivial filter supported on `s`. -/
theorem dist_le_of_tendsto [PseudoMetricSpace E] {f : α → E} {s : Set α}
    (hf : BoundedVariationOn f s) {l : Filter α} [l.NeBot] (hl : l ≤ 𝓟 s)
    {x : α} (hx : x ∈ s) {y : E} (hlim : Tendsto f l (𝓝 y)) :
    dist (f x) y ≤ (eVariationOn f s).toReal := by
  rw [← ENNReal.ofReal_le_iff_le_toReal hf, ← edist_dist]
  exact eVariationOn.edist_le_of_tendsto hl hx hlim

/-- Real-valued norm bound against a zero limit along a nontrivial filter supported on `s`. -/
theorem norm_le_of_tendsto_zero [SeminormedAddCommGroup E] {f : α → E} {s : Set α}
    (hf : BoundedVariationOn f s) {l : Filter α} [l.NeBot] (hl : l ≤ 𝓟 s)
    {x : α} (hx : x ∈ s) (hlim : Tendsto f l (𝓝 0)) :
    ‖f x‖ ≤ (eVariationOn f s).toReal := by
  simpa only [dist_zero_right] using hf.dist_le_of_tendsto hl hx hlim

/-- Sharp two-sided bound: if `f` has bounded variation on `univ` and tends to `0` at both `±∞`,
then `2 * ‖f x‖ ≤ (eVariationOn f univ).toReal`. -/
theorem two_mul_norm_le_eVariationOn_toReal [SeminormedAddCommGroup E] {f : α → E}
    (hf : BoundedVariationOn f univ) (hbot : Tendsto f atBot (𝓝 0))
    (htop : Tendsto f atTop (𝓝 0)) (x : α) :
    2 * ‖f x‖ ≤ (eVariationOn f univ).toReal := by
  have h := eVariationOn.two_mul_eNorm_le hbot htop x
  rw [← ENNReal.ofReal_le_iff_le_toReal hf]
  simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat,
    ofReal_norm] using h

/-- Sharp two-sided pointwise norm bound: if `f` has bounded variation on `univ` and tends to `0`
at both `±∞`, then `‖f x‖ ≤ (eVariationOn f univ).toReal / 2`. -/
theorem norm_le_eVariationOn_toReal_div_two [SeminormedAddCommGroup E] {f : α → E}
    (hf : BoundedVariationOn f univ) (hbot : Tendsto f atBot (𝓝 0))
    (htop : Tendsto f atTop (𝓝 0)) (x : α) :
    ‖f x‖ ≤ (eVariationOn f univ).toReal / 2 := by
  linarith [hf.two_mul_norm_le_eVariationOn_toReal hbot htop x]

end PseudoMetric

section MeasureLimits

variable {α E : Type*} [LinearOrder α] [MeasurableSpace α] [SeminormedAddCommGroup E]

/-- A function of bounded variation on a set `s ∈ atTop` that is integrable along `atTop` with
respect to a measure giving every tail infinite measure must tend to `0` at `+∞`. -/
theorem tendsto_zero_atTop_of_measure_eq_top {μ : Measure α} {f : α → E} {s : Set α}
    (hf : BoundedVariationOn f s) (hs : s ∈ atTop) (hint : IntegrableAtFilter f atTop μ)
    (hμ : ∀ t ∈ atTop, μ t = ∞) :
    Tendsto f atTop (𝓝 0) := by
  have hlip : LipschitzWith 1 ((↑) : E → Completion E) :=
    (Isometry.of_dist_eq Completion.dist_eq).lipschitzWith
  obtain ⟨c, hc⟩ := (hlip.comp_boundedVariationOn hf).exists_tendsto_atTop
  rw [inf_of_le_right (le_principal_iff.mpr hs)] at hc
  rcases hint with ⟨u, hu, hfu⟩
  have hc0 : c = 0 := IntegrableAtFilter.eq_zero_of_tendsto
    ⟨u, hu, (Completion.continuous_coe E).comp_aestronglyMeasurable hfu.1,
      by simpa only [HasFiniteIntegral, Function.comp_apply, Completion.eNorm_coe] using hfu.2⟩
    hμ hc
  rw [hc0] at hc
  exact tendsto_zero_iff_norm_tendsto_zero.mpr <| by
    simpa only [Function.comp_apply, Completion.norm_coe, norm_zero] using hc.norm

/-- A function of bounded variation on a set `s ∈ atBot` that is integrable along `atBot` with
respect to a measure giving every tail infinite measure must tend to `0` at `-∞`. -/
theorem tendsto_zero_atBot_of_measure_eq_top {μ : Measure α} {f : α → E} {s : Set α}
    (hf : BoundedVariationOn f s) (hs : s ∈ atBot) (hint : IntegrableAtFilter f atBot μ)
    (hμ : ∀ t ∈ atBot, μ t = ∞) :
    Tendsto f atBot (𝓝 0) :=
  hf.ofDual.tendsto_zero_atTop_of_measure_eq_top hs hint hμ

end MeasureLimits

section Real

variable {E : Type*} [SeminormedAddCommGroup E]

/-- A function `f : ℝ → E` of bounded variation on a set `s ∈ atTop` that is integrable along
`atTop` with respect to Lebesgue measure tends to `0` at `+∞`. -/
theorem tendsto_zero_atTop_of_integrableAtFilter {f : ℝ → E} {s : Set ℝ}
    (hf : BoundedVariationOn f s) (hs : s ∈ atTop) (hint : IntegrableAtFilter f atTop volume) :
    Tendsto f atTop (𝓝 0) :=
  hf.tendsto_zero_atTop_of_measure_eq_top hs hint fun _ ht ↦
    let ⟨b, hb⟩ := mem_atTop_sets.1 ht
    measure_mono_top (s₁ := Ici b) (fun _ hx ↦ hb _ hx) Real.volume_Ici

/-- A function `f : ℝ → E` of bounded variation on a set `s ∈ atBot` that is integrable along
`atBot` with respect to Lebesgue measure tends to `0` at `-∞`. -/
theorem tendsto_zero_atBot_of_integrableAtFilter {f : ℝ → E} {s : Set ℝ}
    (hf : BoundedVariationOn f s) (hs : s ∈ atBot) (hint : IntegrableAtFilter f atBot volume) :
    Tendsto f atBot (𝓝 0) :=
  hf.tendsto_zero_atBot_of_measure_eq_top hs hint fun _ ht ↦
    let ⟨b, hb⟩ := mem_atBot_sets.1 ht
    measure_mono_top (s₁ := Iic b) (fun _ hx ↦ hb _ hx) Real.volume_Iic

/-- An integrable function `f : ℝ → E` of bounded variation on `univ` tends to `0` at `+∞`. -/
theorem tendsto_zero_atTop {f : ℝ → E} (hf : BoundedVariationOn f univ) (hint : Integrable f) :
    Tendsto f atTop (𝓝 0) :=
  hf.tendsto_zero_atTop_of_integrableAtFilter univ_mem ⟨univ, univ_mem, hint.integrableOn⟩

/-- An integrable function `f : ℝ → E` of bounded variation on `univ` tends to `0` at `-∞`. -/
theorem tendsto_zero_atBot {f : ℝ → E} (hf : BoundedVariationOn f univ) (hint : Integrable f) :
    Tendsto f atBot (𝓝 0) :=
  hf.tendsto_zero_atBot_of_integrableAtFilter univ_mem ⟨univ, univ_mem, hint.integrableOn⟩

/-- Sharp pointwise bound for an integrable function of bounded variation on `ℝ`:
`‖f x‖ ≤ (eVariationOn f univ).toReal / 2` for every `x : ℝ`. -/
theorem norm_le_eVariationOn_toReal_div_two_of_integrable {f : ℝ → E}
    (hf : BoundedVariationOn f univ) (hint : Integrable f) (x : ℝ) :
    ‖f x‖ ≤ (eVariationOn f univ).toReal / 2 :=
  hf.norm_le_eVariationOn_toReal_div_two (hf.tendsto_zero_atBot hint)
    (hf.tendsto_zero_atTop hint) x

/-- Pointwise bound for an integrable function of bounded variation on `ℝ`:
`‖f x‖ ≤ (eVariationOn f univ).toReal` for every `x : ℝ`. -/
theorem norm_le_eVariationOn_toReal_of_integrable {f : ℝ → E}
    (hf : BoundedVariationOn f univ) (hint : Integrable f) (x : ℝ) :
    ‖f x‖ ≤ (eVariationOn f univ).toReal :=
  (hf.norm_le_eVariationOn_toReal_div_two_of_integrable hint x).trans
    (half_le_self ENNReal.toReal_nonneg)

end Real

end BoundedVariationOn

/-! ### Non-integrable counterexample -/

/-- The indicator of `[0, ∞)` has bounded variation `1` on `ℝ`, is not integrable, and tends to
`1` at `+∞`, showing that integrability is needed for `BoundedVariationOn.tendsto_zero_atTop`. -/
example :
    let f : ℝ → ℝ := (Ici (0 : ℝ)).indicator (fun _ ↦ 1)
    eVariationOn f univ = 1 ∧ BoundedVariationOn f univ ∧ ¬ Integrable f ∧
      Tendsto f atTop (𝓝 1) := by
  intro f
  have hmono : Monotone f := by
    intro x y hxy
    by_cases hx : x ∈ Ici (0 : ℝ)
    · have hy : y ∈ Ici (0 : ℝ) := mem_Ici.mpr ((mem_Ici.mp hx).trans hxy)
      simp [f, indicator_of_mem hx, indicator_of_mem hy]
    · by_cases hy : y ∈ Ici (0 : ℝ)
      · simp [f, indicator_of_notMem hx, indicator_of_mem hy]
      · simp [f, indicator_of_notMem hx, indicator_of_notMem hy]
  have hle : ∀ x, 0 ≤ f x ∧ f x ≤ 1 := by
    intro x
    by_cases hx : x ∈ Ici (0 : ℝ) <;> simp [f, hx]
  have hev : eVariationOn f univ = 1 := by
    refine le_antisymm ?_ ?_
    · rw [eVariationOn.eq_biSup_inter_Icc]
      simp only [mem_ofPred_eq, iSup_le_iff, and_imp, Prod.forall]
      intro a b _ _ _
      rw [(hmono.monotoneOn univ).eVariationOn_eq (mem_univ a) (mem_univ b)]
      have hsub : f b - f a ≤ 1 := by linarith [hle a, hle b]
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hsub
    · calc
        (1 : ℝ≥0∞) = edist (f 0) (f (-1)) := by
          simp [f, edist_dist]
        _ ≤ eVariationOn f univ := eVariationOn.edist_le f (mem_univ 0) (mem_univ (-1))
  have hbv : BoundedVariationOn f univ := by
    rw [BoundedVariationOn, hev]
    exact ENNReal.one_ne_top
  have hlim : Tendsto f atTop (𝓝 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ici_mem_atTop (0 : ℝ)] with x hx
    simp [f, indicator_of_mem hx]
  have hnot : ¬ Integrable f := by
    intro hint
    have h0 := hbv.tendsto_zero_atTop hint
    have : (1 : ℝ) = 0 := tendsto_nhds_unique hlim h0
    norm_num at this
  exact ⟨hev, hbv, hnot, hlim⟩
