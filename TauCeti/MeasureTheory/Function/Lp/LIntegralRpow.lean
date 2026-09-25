/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# `Lᵖ` seminorm bounds out of bounds between the integrals `∫⁻ ‖·‖ₑ ^ p`

For `0 < p < ∞` the `Lᵖ` seminorm of `v` is by definition the `p`-th root of
`∫⁻ ‖v x‖ₑ ^ p ∂μ`, so a bound `∫⁻ ‖v‖ₑ ^ p ≤ c ^ p * ∫⁻ ‖w‖ₑ ^ p` between those integrals is the
same statement as `‖v‖_p ≤ c * ‖w‖_p` between the seminorms. This file records the passage from
the former to the latter, which is the direction an estimate proved by integration produces.

The two functions are allowed to take values in different spaces, and those spaces need carry
nothing beyond an extended norm, since that is all `eLpNorm` reads. In particular the statement
covers comparing a function with its derivative.

## Main declarations

* `TauCeti.eLpNorm_rpow_eq_lintegral`: for an `ℝ≥0∞`-valued function, the `p`-th power of the
  `Lᵖ` seminorm is the integral `∫⁻ f ^ p`.
* `TauCeti.eLpNorm_le_of_ae_tendsto_ennreal`: an `ℝ≥0∞`-valued Fatou lemma for the `Lᵖ`
  seminorm.
* `TauCeti.eLpNorm_le_eLpNorm_of_lintegral_rpow_le`: from
  `∫⁻ ‖v‖ₑ ^ p ≤ c ^ p * ∫⁻ ‖w‖ₑ ^ p` conclude `‖v‖_p ≤ c * ‖w‖_p`.
* `TauCeti.rpow_lintegral_le_measure_univ_rpow_mul`: Hölder's extended-valued integral inequality
  `(∫⁻ u) ^ r ≤ μ univ ^ (r - 1) * ∫⁻ u ^ r` for `u : α → ℝ≥0∞`.  On a finite measure space it
  expresses the nesting `L^r ⊆ L¹`; for a general `μ` it is only the inequality.
-/

public section

namespace TauCeti

open Filter
open MeasureTheory
open scoped ENNReal Topology

/-- For a finite nonzero exponent, the `p`-th power of the `Lᵖ` seminorm of an a.e. measurable
`ℝ≥0∞`-valued function is the integral of the `p`-th power of that function. This is
`MeasureTheory.lintegral_rpow_enorm_eq_rpow_eLpNorm'` read at an `ℝ≥0∞`-valued exponent and at a
function whose enorm is the identity, which is the shape the extended-valued estimates use. -/
theorem eLpNorm_rpow_eq_lintegral {α : Type*} [MeasurableSpace α]
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞) {f : α → ℝ≥0∞} {μ : Measure α}
    (hf : AEMeasurable f μ) :
    eLpNorm f p μ ^ p.toReal = ∫⁻ a, f a ^ p.toReal ∂μ := by
  rw [eLpNorm_eq_eLpNorm' hp0 hp hf.aestronglyMeasurable,
    ← lintegral_rpow_enorm_eq_rpow_eLpNorm' (ENNReal.toReal_pos hp0 hp)]
  simp

/-- **Fatou's lemma for the `Lᵖ` seminorm of `ℝ≥0∞`-valued functions.** For a finite nonzero
exponent, an almost everywhere pointwise limit of functions whose `Lᵖ` seminorms are bounded by
`c` also has `Lᵖ` seminorm at most `c`. -/
theorem eLpNorm_le_of_ae_tendsto_ennreal {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞) {f : ℕ → α → ℝ≥0∞} {g : α → ℝ≥0∞}
    {c : ℝ≥0∞} (hf : ∀ n, AEMeasurable (f n) μ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n ↦ f n x) atTop (𝓝 (g x)))
    (hle : ∀ n, eLpNorm (f n) p μ ≤ c) :
    eLpNorm g p μ ≤ c := by
  have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hg : AEMeasurable g μ := ENNReal.aemeasurable_of_tendsto hf hlim
  have key : eLpNorm g p μ ^ p.toReal ≤ c ^ p.toReal := by
    rw [eLpNorm_rpow_eq_lintegral hp0 hp hg]
    calc ∫⁻ x, g x ^ p.toReal ∂μ
        = ∫⁻ x, atTop.liminf (fun n ↦ f n x ^ p.toReal) ∂μ := by
          refine lintegral_congr_ae ?_
          filter_upwards [hlim] with x hx
          exact (Tendsto.liminf_eq
            (((ENNReal.continuous_rpow_const (y := p.toReal)).tendsto (g x)).comp hx)).symm
      _ ≤ atTop.liminf fun n ↦ ∫⁻ x, f n x ^ p.toReal ∂μ :=
          lintegral_liminf_le' fun n ↦ (hf n).pow_const _
      _ ≤ c ^ p.toReal := by
          refine liminf_le_of_frequently_le' (.of_forall fun n ↦ ?_)
          rw [← eLpNorm_rpow_eq_lintegral hp0 hp (hf n)]
          exact ENNReal.rpow_le_rpow (hle n) hr.le
  exact (ENNReal.rpow_le_rpow_iff hr).1 key

/-- Turn a bound between the `∫⁻ ‖·‖ₑ ^ p` integrals into a bound between the `Lᵖ` seminorms.
The two functions may have different codomains, which is what lets such a bound compare a
function with its derivative; only a topology and an extended norm on each is needed.

Only the function on the left has to be a.e. strongly measurable: without that its `Lᵖ` seminorm
is `∞` by definition, whatever the integral bound says, while a non-measurable `w` only makes the
right-hand side larger. -/
theorem eLpNorm_le_eLpNorm_of_lintegral_rpow_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {G H : Type*} [ENorm G] [TopologicalSpace G] [ENorm H] [TopologicalSpace H]
    {v : α → G} {w : α → H} {c : ℝ}
    (hc : 0 ≤ c) {p : ℝ≥0∞} (hp₀ : p ≠ 0) (hp : p ≠ ∞) (hv : AEStronglyMeasurable v μ)
    (h : ∫⁻ x, ‖v x‖ₑ ^ p.toReal ∂μ ≤
      ENNReal.ofReal (c ^ p.toReal) * ∫⁻ x, ‖w x‖ₑ ^ p.toReal ∂μ) :
    eLpNorm v p μ ≤ ENNReal.ofReal c * eLpNorm w p μ := by
  have hr0 : (0 : ℝ) < p.toReal := ENNReal.toReal_pos hp₀ hp
  have hwle : (∫⁻ x, ‖w x‖ₑ ^ p.toReal ∂μ) ^ (1 / p.toReal) ≤ eLpNorm w p μ := by
    by_cases hw : AEStronglyMeasurable w μ
    · exact (eLpNorm_eq_lintegral_rpow_enorm_toReal hp₀ hp hw).ge
    · simp [eLpNorm_of_not_aestronglyMeasurable hw]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp₀ hp hv]
  calc (∫⁻ x, ‖v x‖ₑ ^ p.toReal ∂μ) ^ (1 / p.toReal)
      ≤ (ENNReal.ofReal (c ^ p.toReal) * ∫⁻ x, ‖w x‖ₑ ^ p.toReal ∂μ) ^ (1 / p.toReal) :=
        ENNReal.rpow_le_rpow h (by positivity)
    _ = ENNReal.ofReal c * (∫⁻ x, ‖w x‖ₑ ^ p.toReal ∂μ) ^ (1 / p.toReal) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
          ← ENNReal.ofReal_rpow_of_nonneg hc hr0.le, ← ENNReal.rpow_mul,
          mul_one_div_cancel hr0.ne', ENNReal.rpow_one]
    _ ≤ ENNReal.ofReal c * eLpNorm w p μ := by gcongr

/-- **Hölder's inequality in extended-valued `∫⁻` form**, raised to the power `r`: the `L¹`
integral of `u : α → ℝ≥0∞` is controlled by its `L^r` integral at the cost of the factor
`μ univ ^ (r - 1)`.  Stated for an `ℝ≥0∞`-valued `u`, so a norm-valued application passes
`fun x => ‖f x‖ₑ` and needs only that this composite is measurable.

On a finite measure space this is the nesting `L^r ⊆ L¹`; for a general `μ` it is only the
displayed inequality, which does not by itself give that inclusion.  No finiteness is assumed, and
the bound is not vacuous when `μ univ = ∞`: arithmetic in `ℝ≥0∞` makes the right-hand side `0`
rather than `∞` whenever `∫⁻ ‖f‖ₑ ^ r = 0`, and the inequality still holds there because `f` then
vanishes almost everywhere. -/
theorem rpow_lintegral_le_measure_univ_rpow_mul {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {u : α → ℝ≥0∞} (hu : AEMeasurable u μ) {r : ℝ} (hr : 1 ≤ r) :
    (∫⁻ x, u x ∂μ) ^ r ≤ μ Set.univ ^ (r - 1) * ∫⁻ x, u x ^ r ∂μ := by
  have hf : AEStronglyMeasurable u μ := hu.aestronglyMeasurable
  have hr0 : (0 : ℝ) < r := one_pos.trans_le hr
  have hCr : eLpNorm u (ENNReal.ofReal r) μ = (∫⁻ x, u x ^ r ∂μ) ^ (1 / r) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hr0) ENNReal.ofReal_ne_top hf,
      ENNReal.toReal_ofReal hr0.le]
    simp only [enorm_eq_self]
  have holder : ∫⁻ x, u x ∂μ
      ≤ (∫⁻ x, u x ^ r ∂μ) ^ (1 / r) * μ Set.univ ^ (1 - 1 / r) := by
    have hle : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := by
      rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hr
    have := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (f := u) (μ := μ) hle hf
    rw [eLpNorm_one_eq_lintegral_enorm hf, hCr, ENNReal.toReal_one,
      ENNReal.toReal_ofReal hr0.le, div_one] at this
    simpa only [enorm_eq_self] using this
  have hinv : 1 / r * r = 1 := by field_simp
  have hexp : (1 - 1 / r) * r = r - 1 := by field_simp
  calc (∫⁻ x, u x ∂μ) ^ r
      ≤ ((∫⁻ x, u x ^ r ∂μ) ^ (1 / r) * μ Set.univ ^ (1 - 1 / r)) ^ r :=
        ENNReal.rpow_le_rpow holder hr0.le
    _ = ((∫⁻ x, u x ^ r ∂μ) ^ (1 / r)) ^ r * (μ Set.univ ^ (1 - 1 / r)) ^ r :=
        ENNReal.mul_rpow_of_nonneg _ _ hr0.le
    _ = (∫⁻ x, u x ^ r ∂μ) * μ Set.univ ^ (r - 1) := by
        rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul, hinv, hexp, ENNReal.rpow_one]
    _ = μ Set.univ ^ (r - 1) * ∫⁻ x, u x ^ r ∂μ := mul_comm _ _

end TauCeti
