/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Almost everywhere convergence along a subsequence

If the Lebesgue integrals of nonnegative functions `F n : α → ℝ≥0∞` tend to `0`, then along a
subsequence the functions themselves tend to `0` almost everywhere. Choose the subsequence with
integrals below `2⁻ʲ`: the sum `∑ⱼ F (φ j)` then has finite integral, so it is finite almost
everywhere, and its terms tend to `0` there.

Applied to the `p`-th powers of the errors of fields converging in `Lᵖ`, the same sum, plus the
`p`-th power of the limit, dominates the `p`-th powers of the fields along the subsequence, since
`‖x‖ᵖ ≤ 2ᵖ⁻¹ (‖a‖ᵖ + ‖x - a‖ᵖ)`.

## Main statements

* `TauCeti.exists_strictMono_lintegral_tsum_ne_top_of_tendsto_lintegral`: a subsequence of
  functions whose integrals tend to `0` has a sum with finite integral.
* `TauCeti.exists_strictMono_ae_tendsto_zero_of_tendsto_lintegral`: a subsequence of functions
  whose integrals tend to `0` tends to `0` almost everywhere.
* `TauCeti.exists_strictMono_enorm_pow_le_and_ae_tendsto_of_tendsto_lintegral`: fields
  converging in `Lᵖ` converge almost everywhere along a subsequence, along which their `p`-th
  powers have a common integrable majorant.
-/

public section

namespace TauCeti

open Filter MeasureTheory Set Topology
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Nonnegative functions with summable Lebesgue integrals tend to zero almost everywhere. -/
theorem ae_tendsto_zero_of_tsum_lintegral_ne_top {F : ℕ → α → ℝ≥0∞}
    (hF : ∀ n, AEMeasurable (F n) μ) (hsum : (∑' n, ∫⁻ a, F n a ∂μ) ≠ ∞) :
    ∀ᵐ a ∂μ, Tendsto (fun n ↦ F n a) atTop (𝓝 0) := by
  have hfinite : ∫⁻ a, ∑' n, F n a ∂μ ≠ ∞ := by
    rwa [lintegral_tsum hF]
  filter_upwards [ae_lt_top' (AEMeasurable.tsum hF) hfinite] with a ha
  exact ENNReal.tendsto_atTop_zero_of_tsum_ne_top ha.ne

/-- **A subsequence with summable integrals.** If `F n : α → ℝ≥0∞` are almost everywhere
measurable and `∫⁻ F n ∂μ → 0`, then along a subsequence the sum `∑ⱼ F (φ j)` has finite
integral. It dominates every `F (φ j)`, which makes it a common integrable bound for a dominated
convergence argument along the subsequence. -/
theorem exists_strictMono_lintegral_tsum_ne_top_of_tendsto_lintegral {F : ℕ → α → ℝ≥0∞}
    (hF : ∀ n, AEMeasurable (F n) μ) (h : Tendsto (fun n ↦ ∫⁻ a, F n a ∂μ) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∫⁻ a, ∑' j, F (φ j) a ∂μ ≠ ∞ := by
  -- Along a subsequence with `∫⁻ F (φ j) < 2⁻ʲ`, the sum `∑ⱼ F (φ j) a` has finite integral.
  obtain ⟨φ, hφ, hlt⟩ := extraction_forall_of_eventually fun j ↦
    h.eventually (gt_mem_nhds (ENNReal.pow_pos (a := 2⁻¹) (by simp) j))
  refine ⟨φ, hφ, ?_⟩
  rw [lintegral_tsum fun j ↦ hF (φ j)]
  exact ((_root_.tsum_le_tsum fun j ↦ (hlt j).le).trans_lt (by simp)).ne

/-- **A subsequence converging almost everywhere.** If `F n : α → ℝ≥0∞` are almost everywhere
measurable and `∫⁻ F n ∂μ → 0`, then along a subsequence `F (φ j) a → 0` for almost every `a`. -/
theorem exists_strictMono_ae_tendsto_zero_of_tendsto_lintegral {F : ℕ → α → ℝ≥0∞}
    (hF : ∀ n, AEMeasurable (F n) μ) (h : Tendsto (fun n ↦ ∫⁻ a, F n a ∂μ) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ a ∂μ, Tendsto (fun j ↦ F (φ j) a) atTop (𝓝 0) := by
  obtain ⟨φ, hφ, hsum⟩ := exists_strictMono_lintegral_tsum_ne_top_of_tendsto_lintegral hF h
  refine ⟨φ, hφ, ?_⟩
  -- The sum is finite almost everywhere, and its terms tend to `0` there.
  filter_upwards [ae_lt_top' (AEMeasurable.tsum fun j ↦ hF (φ j)) hsum] with a ha
  exact ENNReal.tendsto_atTop_zero_of_tsum_ne_top ha.ne

/-- **A common majorant along a subsequence.** Let `F k` be fields converging to `H` in `Lᵖ`
on measurable sets `U k ⊆ Ω`, `p ≠ 0` a natural number, with `‖H‖ ∈ Lᵖ(Ω)`, and let every point
of `Ω` lie in `U k` for all large `k`. Then along a subsequence the powers `‖F (φ j)‖ᵖ` on
`U (φ j)` have a common integrable majorant, and `F (φ j) → H` almost everywhere on `Ω`. -/
theorem exists_strictMono_enorm_pow_le_and_ae_tendsto_of_tendsto_lintegral
    {E : Type*} [SeminormedAddCommGroup E] {p : ℕ} (hp : p ≠ 0) {Ω : Set α}
    (hΩ : MeasurableSet Ω) {U : ℕ → Set α} (hU : ∀ k, MeasurableSet (U k)) (hUΩ : ∀ k, U k ⊆ Ω)
    (hΩU : ∀ y ∈ Ω, ∀ᶠ k in atTop, y ∈ U k) {F : ℕ → α → E}
    (hF : ∀ k, AEStronglyMeasurable (F k) (μ.restrict (U k))) {H : α → E}
    (hHm : AEStronglyMeasurable H (μ.restrict Ω)) (hH : ∫⁻ y in Ω, ‖H y‖ₑ ^ p ∂μ ≠ ∞)
    (hFH : Tendsto (fun k ↦ ∫⁻ y in U k, ‖F k y - H y‖ₑ ^ p ∂μ) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ (∃ G : α → ℝ≥0∞, ∫⁻ y, G y ∂μ ≠ ∞ ∧
      ∀ j, ∀ y ∈ U (φ j), ‖F (φ j) y‖ₑ ^ p ≤ G y) ∧
      ∀ᵐ y ∂μ, y ∈ Ω → Tendsto (fun j ↦ F (φ j) y) atTop (𝓝 (H y)) := by
  -- A subsequence along which the `Lᵖ` errors have a summable integral.
  set D : ℕ → α → ℝ≥0∞ := fun k ↦ (U k).indicator fun y ↦ ‖F k y - H y‖ₑ ^ p
  have hD (k : ℕ) : AEMeasurable (D k) μ :=
    (aemeasurable_indicator_iff (hU k)).2
      ((((hF k).sub (hHm.mono_measure (Measure.restrict_mono (hUΩ k) le_rfl))).eNorm).pow_const p)
  obtain ⟨φ, hφ, hS⟩ := exists_strictMono_lintegral_tsum_ne_top_of_tendsto_lintegral hD
    (by simpa only [D, lintegral_indicator (hU _)] using hFH)
  refine ⟨φ, hφ, ?_, ?_⟩
  -- The majorant `2ᵖ⁻¹ (‖H‖ᵖ + ∑ⱼ ‖F (φ j) - H‖ᵖ)`, from `‖x‖ᵖ ≤ 2ᵖ⁻¹ (‖a‖ᵖ + ‖x - a‖ᵖ)`.
  · have hC : (2 : ℝ≥0∞) ^ (p - 1) ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
    have hle (x a : E) : ‖x‖ₑ ^ p ≤ 2 ^ (p - 1) * (‖a‖ₑ ^ p + ‖x - a‖ₑ ^ p) := by
      have h : ‖x‖₊ ^ p ≤ 2 ^ (p - 1) * (‖a‖₊ ^ p + ‖x - a‖₊ ^ p) :=
        (pow_le_pow_left₀ zero_le (by simpa using nnNorm_add_le a (x - a)) p).trans
          (add_pow_le zero_le zero_le p)
      simpa only [eNorm, ENNReal.coe_pow, ENNReal.coe_mul, ENNReal.coe_add, ENNReal.coe_ofNat]
        using ENNReal.coe_le_coe.2 h
    refine ⟨fun y ↦ 2 ^ (p - 1) * (Ω.indicator (fun y ↦ ‖H y‖ₑ ^ p) y + ∑' j, D (φ j) y), ?_,
      fun j y hy ↦ (hle (F (φ j) y) (H y)).trans (mul_le_mul_right (add_le_add ?_ ?_) _)⟩
    · rw [lintegral_const_mul' _ _ hC, lintegral_add_left'
        ((aemeasurable_indicator_iff hΩ).2 (hHm.eNorm.pow_const p)), lintegral_indicator hΩ]
      exact ENNReal.mul_ne_top hC (ENNReal.add_ne_top.2 ⟨hH, hS⟩)
    · rw [indicator_of_mem (hUΩ _ hy)]
    · exact le_trans (le_of_eq (by simp only [D, indicator_of_mem hy]))
        (_root_.le_tsum (fun j ↦ D (φ j) y) j)
  -- The errors tend to `0` where the sum is finite, and `y` lies in `U (φ j)` eventually.
  · filter_upwards [ae_lt_top' (AEMeasurable.tsum fun j ↦ hD (φ j)) hS] with y hy hyΩ
    have h1 : Tendsto (fun j ↦ ‖F (φ j) y - H y‖ₑ ^ p) atTop (𝓝 0) :=
      (ENNReal.tendsto_atTop_zero_of_tsum_ne_top hy.ne).congr'
        ((hφ.tendsto_atTop.eventually (hΩU y hyΩ)).mono fun j hj ↦ by
          simp only [D, indicator_of_mem hj])
    have h2 := ((ENNReal.continuous_rpow_const (y := (p : ℝ)⁻¹)).tendsto 0).comp h1
    simp only [Function.comp_def, ENNReal.pow_rpow_inv_natCast hp,
      ENNReal.zero_rpow_of_pos (inv_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero hp)))] at h2
    rw [tendsto_iff_edist_tendsto_0]
    simpa only [eDist_eq_eNorm_sub] using h2

end TauCeti
