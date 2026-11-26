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
import TauCeti.Topology.EMetricSpace.BoundedVariation

/-!
# Limits at infinity and pointwise bounds for integrable functions of bounded variation

If a function on a linearly ordered measurable space has bounded variation and is integrable along
`atTop` (or `atBot`) with respect to a measure assigning infinite measure to every element of the
filter—in particular Lebesgue measure on `ℝ`—then it must tend to `0` at `+∞` (or `-∞`). Passing to
`UniformSpace.Completion E` removes any completeness or vector-space assumption on the codomain `E`.

Combining vanishing at both `±∞` with `BoundedVariationOn.norm_le_eVariationOn_toReal_div_two` from
`TauCeti.Topology.EMetricSpace.BoundedVariation` yields the sharp global supremum bound
`‖f x‖ ≤ (eVariationOn f univ).toReal / 2` (and hence `‖f x‖ ≤ (eVariationOn f univ).toReal`) for
every integrable function `f : ℝ → E` of bounded variation. The factor `1 / 2` is attained by
`1_[0,1]`, and the indicator of `[0, ∞)` shows that integrability cannot be omitted.

## Main declarations

* `BoundedVariationOn.tendsto_zero_atTop_of_measure_eq_top` and
  `BoundedVariationOn.tendsto_zero_atBot_of_measure_eq_top`: a function of bounded variation that is
  integrable along `atTop` (or `atBot`) for a measure with infinite tails tends to `0`.
* `BoundedVariationOn.tendsto_zero_atTop_of_integrableAtFilter`,
  `BoundedVariationOn.tendsto_zero_atBot_of_integrableAtFilter`,
  `BoundedVariationOn.tendsto_zero_atTop`, and `BoundedVariationOn.tendsto_zero_atBot`: Lebesgue
  specializations on `ℝ`.
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

namespace BoundedVariationOn

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
