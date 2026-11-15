/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# Chebyshev's inequality for the second moment and `O((n + 1)⁻²)` tail convergence

For any measure `μ` and any function `Y` with values in a type with a norm, whose squared norm
is integrable, the set where `‖Y‖` is at least `c > 0` has measure at most `(∫ ‖Y‖²) / c²`. This is
Markov's inequality applied to `‖Y‖²`. Unlike `ProbabilityTheory.meas_ge_le_variance_div_sq`,
`Y` is not centered at its mean, so the bound applies directly to a deviation such as the error
of an estimator.

When a sequence of random variables satisfies a Chebyshev tail bound of order
`(C / (n + 1) ^ 2) / ε ^ 2`, squeezing gives convergence in measure to zero
(`TauCeti.tendsto_measure_ge_nhds_zero_of_le_div_sq`) and, on a single measure space, summability
of `∑ (n + 1)⁻²` together with the first Borel--Cantelli lemma gives almost-everywhere convergence
to zero (`TauCeti.ae_tendsto_nhds_zero_of_measure_ge_le_div_sq`).

## Main statements

* `TauCeti.meas_ge_le_integral_norm_sq_div_sq`: Chebyshev's inequality for the second moment,
  `μ {c ≤ ‖Y‖} ≤ (∫ ‖Y‖²) / c²`, for any measure and without centering.
* `TauCeti.meas_gt_le_div_sq_of_integral_sq_le`: the uncentered Chebyshev inequality
  `μ {η < Y} ≤ v / η²` for a real `Y` with `∫ Y² ≤ v`.
* `TauCeti.tendsto_measure_ge_nhds_zero_of_le_div_sq`: convergence of tail measures
  `μ n {ε ≤ ‖X n ω‖} → 0` under a `(C / (n + 1) ^ 2) / ε ^ 2` bound.
* `TauCeti.ae_tendsto_nhds_zero_of_measure_ge_le_div_sq`: almost-everywhere convergence `X n → 0`
  from a `(C / (n + 1) ^ 2) / ε ^ 2` tail bound via Borel--Cantelli.

## References

* R. Vershynin, *High-Dimensional Probability* (2018), §1.2: Chebyshev's inequality.
-/

public section

open Filter MeasureTheory
open scoped ENNReal Topology

namespace TauCeti

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Chebyshev's inequality for the second moment.** For any measure, if `‖Y‖²` is integrable
and `0 < c`, the set where `‖Y‖` is at least `c` has measure at most `(∫ ‖Y‖²) / c²`. Unlike
`ProbabilityTheory.meas_ge_le_variance_div_sq`, `Y` is not centered at its mean. -/
theorem meas_ge_le_integral_norm_sq_div_sq [Norm E] {Y : Ω → E}
    (hY : Integrable (fun ω ↦ ‖Y ω‖ ^ 2) μ) {c : ℝ} (hc : 0 < c) :
    μ {ω | c ≤ ‖Y ω‖} ≤ ENNReal.ofReal ((∫ ω, ‖Y ω‖ ^ 2 ∂μ) / c ^ 2) := by
  have hc2 : 0 < c ^ 2 := pow_pos hc 2
  calc μ {ω | c ≤ ‖Y ω‖}
      ≤ μ {ω | ENNReal.ofReal (c ^ 2) ≤ ENNReal.ofReal (‖Y ω‖ ^ 2)} :=
        measure_mono fun ω (hω : c ≤ ‖Y ω‖) ↦
          ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hc.le hω 2)
    _ ≤ (∫⁻ ω, ENNReal.ofReal (‖Y ω‖ ^ 2) ∂μ) / ENNReal.ofReal (c ^ 2) :=
        meas_ge_le_lintegral_div hY.aemeasurable.ennreal_ofReal
          (ENNReal.ofReal_pos.2 hc2).ne' ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal ((∫ ω, ‖Y ω‖ ^ 2 ∂μ) / c ^ 2) := by
        rw [← ofReal_integral_eq_lintegral_ofReal hY (.of_forall fun ω ↦ by positivity),
          ENNReal.ofReal_div_of_pos hc2]

/-- **The uncentered Chebyshev inequality.** If `Y²` is integrable with `∫ Y² ≤ v` and `0 < η`,
then the set where `Y` exceeds `η` has measure at most `v / η²`. -/
theorem meas_gt_le_div_sq_of_integral_sq_le {Y : Ω → ℝ} (hY : Integrable (fun ω ↦ Y ω ^ 2) μ)
    {v η : ℝ} (hv : ∫ ω, Y ω ^ 2 ∂μ ≤ v) (hη : 0 < η) :
    μ {ω | η < Y ω} ≤ ENNReal.ofReal (v / η ^ 2) := by
  have hY' : Integrable (fun ω ↦ ‖Y ω‖ ^ 2) μ := by simpa only [Real.norm_eq_abs, sq_abs] using hY
  calc μ {ω | η < Y ω}
      ≤ μ {ω | η ≤ ‖Y ω‖} :=
        measure_mono fun ω (hω : η < Y ω) ↦ hω.le.trans (Real.le_norm_self (Y ω))
    _ ≤ ENNReal.ofReal ((∫ ω, ‖Y ω‖ ^ 2 ∂μ) / η ^ 2) := meas_ge_le_integral_norm_sq_div_sq hY' hη
    _ ≤ ENNReal.ofReal (v / η ^ 2) := by
        simp only [Real.norm_eq_abs, sq_abs]
        gcongr

/-- If `ν n {ω | ε ≤ ‖X n ω‖} ≤ ENNReal.ofReal ((C / (n + 1) ^ 2) / ε ^ 2)` for every `n`, then
`ν n {ω | ε ≤ ‖X n ω‖}` tends to `0`. -/
theorem tendsto_measure_ge_nhds_zero_of_le_div_sq {α : ℕ → Type*} [∀ n, MeasurableSpace (α n)]
    {ν : (n : ℕ) → Measure (α n)} [Norm E] {X : (n : ℕ) → α n → E} {C ε : ℝ}
    (h : ∀ n, ν n {ω | ε ≤ ‖X n ω‖} ≤ ENNReal.ofReal ((C / (n + 1 : ℝ) ^ 2) / ε ^ 2)) :
    Tendsto (fun n ↦ ν n {ω | ε ≤ ‖X n ω‖}) atTop (𝓝 0) := by
  have hinv : Tendsto (fun n : ℕ ↦ (n + 1 : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa only [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hreal : Tendsto (fun n : ℕ ↦ (C / (n + 1 : ℝ) ^ 2) / ε ^ 2) atTop (𝓝 0) := by
    convert ((hinv.pow 2).const_mul C).div_const (ε ^ 2) using 1
    · ext n; simp [div_eq_mul_inv, inv_pow]
    · simp
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using ENNReal.tendsto_ofReal hreal) (fun _ ↦ bot_le) h

/-- **Borel--Cantelli convergence from an `O((n + 1)⁻² / ε²)` tail bound.** If
`μ {ω | ε ≤ ‖X n ω‖} ≤ ENNReal.ofReal ((C / (n + 1) ^ 2) / ε ^ 2)` for all `n` and `ε > 0`, then
`X n` tends to `0` almost everywhere under `μ`. -/
theorem ae_tendsto_nhds_zero_of_measure_ge_le_div_sq [SeminormedAddCommGroup E]
    {X : ℕ → Ω → E} {C : ℝ}
    (h : ∀ (n : ℕ) {ε : ℝ}, 0 < ε →
      μ {ω | ε ≤ ‖X n ω‖} ≤ ENNReal.ofReal ((C / (n + 1 : ℝ) ^ 2) / ε ^ 2)) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ X n ω) atTop (𝓝 0) := by
  have hs : Summable (fun n : ℕ ↦ (n + 1 : ℝ)⁻¹ ^ 2) := by
    simpa only [Nat.cast_add, Nat.cast_one, inv_pow] using
      (summable_nat_add_iff 1).2 ((Real.summable_nat_pow_inv (p := 2)).2 (by decide : 1 < 2))
  have hbc (j : ℕ) : ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, ‖X n ω‖ < (j + 1 : ℝ)⁻¹ := by
    have hbound (n : ℕ) : μ {ω | (j + 1 : ℝ)⁻¹ ≤ ‖X n ω‖} ≤
        ENNReal.ofReal ((C / (n + 1 : ℝ) ^ 2) / ((j + 1 : ℝ)⁻¹) ^ 2) :=
      h n (inv_pos.mpr (by positivity))
    have ht := Summable.mul_right ((((j + 1 : ℝ)⁻¹) ^ 2)⁻¹) (Summable.mul_left C hs)
    have hsum : Summable (fun n : ℕ ↦ (C / (n + 1 : ℝ) ^ 2) / ((j + 1 : ℝ)⁻¹) ^ 2) := by
      simpa only [div_eq_mul_inv, inv_pow, mul_assoc] using ht
    have hfinite : (∑' n, μ {ω | (j + 1 : ℝ)⁻¹ ≤ ‖X n ω‖}) ≠ ∞ :=
      ne_top_of_le_ne_top hsum.tsum_ofReal_ne_top (tsum_le_tsum hbound)
    simpa only [Set.mem_ofPred_eq, not_le] using ae_eventually_notMem hfinite
  filter_upwards [ae_all_iff.2 hbc] with ω hω
  refine tendsto_iff_norm_sub_tendsto_zero.2 <| Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt hε
  filter_upwards [hω j] with n hn
  simpa only [sub_zero, Real.dist_eq, abs_norm] using hn.trans (by simpa only [one_div] using hj)

end TauCeti
