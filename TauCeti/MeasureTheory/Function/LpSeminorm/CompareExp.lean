/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# `Lᵖ` convergence gives `L¹` convergence on a finite measure space

On a finite measure space, Mathlib's exponent comparison
`eLpNorm_le_eLpNorm_mul_rpow_measure_univ` bounds the `L¹` seminorm by the `Lᵖ` seminorm (for
`1 ≤ p`) times a finite constant. This file packages that comparison as a convergence statement
both for the `L¹` seminorm and for the Bochner integral `∫ ‖f i‖ ∂μ`, the form in which `L¹`
convergence of a difference `f i = W i - a` is usually consumed.

## Main declarations

* `TauCeti.MeasureTheory.tendsto_eLpNorm_one_of_tendsto_eLpNorm`: convergence to zero in `Lᵖ`
  for `1 ≤ p` implies convergence to zero in `L¹`.
* `TauCeti.MeasureTheory.tendsto_integral_norm_of_tendsto_eLpNorm`: if `eLpNorm (f i) p μ → 0`
  for some `1 ≤ p`, then `∫ ‖f i‖ ∂μ → 0`.
* `TauCeti.MeasureTheory.not_tendsto_eLpNorm_sub_of_separated`: a sequence whose terms stay a
  definite `L¹` distance apart has no subsequence converging in `Lᵖ` for any `1 ≤ p`.
-/

public section

open Filter MeasureTheory
open scoped ENNReal Topology

namespace TauCeti

namespace MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The exponent `1 / 1 - 1 / p` comparing `L¹` with `Lᵖ` on a finite measure is nonnegative
when `1 ≤ p`. -/
theorem sub_one_div_toReal_nonneg {p : ℝ≥0∞} (hp : 1 ≤ p) :
    0 ≤ 1 / (1 : ℝ≥0∞).toReal - 1 / p.toReal := by
  rcases eq_or_ne p ⊤ with rfl | hp'
  · simp
  · have : 1 ≤ p.toReal := by
      simpa using ENNReal.toReal_mono hp' hp
    simpa using inv_le_one_of_one_le₀ this

/-- On a finite measure space, convergence to zero in `Lᵖ` for `1 ≤ p` implies convergence
to zero in `L¹`. No measurability hypothesis or finiteness assumption on `p` is needed. -/
theorem tendsto_eLpNorm_one_of_tendsto_eLpNorm {ι E : Type*} [NormedAddCommGroup E]
    {l : Filter ι} {μ : Measure Ω} [IsFiniteMeasure μ] {f : ι → Ω → E} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (h : Tendsto (fun i => eLpNorm (f i) p μ) l (𝓝 0)) :
    Tendsto (fun i => eLpNorm (f i) 1 μ) l (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ => zero_le)
    fun _ => eLpNorm_le_eLpNorm_mul_rpow_measure_univ_of_pos hp one_pos
  simpa using ENNReal.Tendsto.mul_const h
    (.inr (ENNReal.rpow_ne_top_of_nonneg (sub_one_div_toReal_nonneg hp)
      (measure_ne_top μ Set.univ)))

/-- **`Lᵖ` convergence implies `L¹` convergence on a finite measure space.** If `1 ≤ p` and a
family `f` tends to `0` in `Lᵖ` along a filter `l`, then `∫ ‖f i‖` tends to `0` along `l`.
No measurability hypothesis is needed: `eLpNorm (f i) p μ` is finite eventually along `l`, which
forces `f i` to be a.e. strongly measurable. -/
theorem tendsto_integral_norm_of_tendsto_eLpNorm {ι E : Type*} [NormedAddCommGroup E]
    {l : Filter ι} {μ : Measure Ω} [IsFiniteMeasure μ] {f : ι → Ω → E} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (h : Tendsto (fun i => eLpNorm (f i) p μ) l (𝓝 0)) :
    Tendsto (fun i => ∫ ω, ‖f i ω‖ ∂μ) l (𝓝 0) := by
  have hL1 := tendsto_eLpNorm_one_of_tendsto_eLpNorm hp h
  have hreal : Tendsto (fun i => (eLpNorm (f i) 1 μ).toReal) l (𝓝 0) := by
    simpa [Function.comp_def] using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hL1
  refine hreal.congr' ?_
  filter_upwards [h.eventually_lt_const ENNReal.zero_lt_top] with i hi
  have hf := aestronglyMeasurable_of_eLpNorm_ne_top hi.ne
  rw [eLpNorm_one_eq_lintegral_enorm hf, integral_norm_eq_lintegral_enorm hf]

/-- If, for all large `m`, the terms `f n` with `n` large stay at `L¹` distance at least `ε` from
`f m`, then no subsequence of `f` converges in `Lᵖ` for any `1 ≤ p`, on a finite measure. -/
theorem not_tendsto_eLpNorm_sub_of_separated {E : Type*} [NormedAddCommGroup E] {μ : Measure Ω}
    [IsFiniteMeasure μ] {f : ℕ → Ω → E} {ε : ℝ≥0∞} (hε : 0 < ε)
    (hsep : ∀ᶠ m in atTop, ∀ᶠ n in atTop, ε ≤ eLpNorm (f m - f n) 1 μ) {p : ℝ≥0∞}
    (hp : 1 ≤ p) {φ : ℕ → ℕ} (hφ : StrictMono φ) {g : Ω → E} :
    ¬ Tendsto (fun k => eLpNorm (f (φ k) - g) p μ) atTop (𝓝 0) := by
  intro h
  have h1 := tendsto_eLpNorm_one_of_tendsto_eLpNorm hp h
  have hsep' : ∀ᶠ k in atTop, ∀ᶠ k' in atTop, ε ≤ eLpNorm (f (φ k) - f (φ k')) 1 μ :=
    (hφ.tendsto_atTop.eventually hsep).mono fun _ hk => hφ.tendsto_atTop.eventually hk
  have hsmall : ∀ᶠ k in atTop, eLpNorm (f (φ k) - g) 1 μ < ε / 2 :=
    h1.eventually (gt_mem_nhds (ENNReal.half_pos hε.ne'))
  obtain ⟨k₀, hk₀, hk₀small⟩ := (hsep'.and hsmall).exists
  obtain ⟨k, hk, hksmall⟩ := (hk₀.and hsmall).exists
  have htri : eLpNorm (f (φ k₀) - f (φ k)) 1 μ ≤
      eLpNorm (f (φ k₀) - g) 1 μ + eLpNorm (f (φ k) - g) 1 μ := by
    have : f (φ k₀) - f (φ k) = (f (φ k₀) - g) - (f (φ k) - g) := by abel
    rw [this]
    exact eLpNorm_sub_le le_rfl
  have := (hk.trans htri).trans_lt (ENNReal.add_lt_add hk₀small hksmall)
  rw [ENNReal.add_halves] at this
  exact lt_irrefl _ this

end MeasureTheory

end TauCeti
