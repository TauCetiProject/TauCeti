/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Moments.Basic
import Mathlib.Analysis.Convex.Integral
import TauCeti.Analysis.SpecialFunctions.Exp.Taylor

/-!
# Lower moment-generating-function bounds for bounded variables

These are lower counterparts of Bernstein's upper MGF bounds. The integrated Taylor
bound retains the mean and requires square integrability, an almost sure lower bound,
and integrability of the exponential at a nonnegative tilt. For an almost everywhere
measurable centred variable with an almost sure absolute bound, the exponential lower
bound applies at every real tilt. Independence lifts it to finite sums.

## Main results

* `MeasureTheory.MemLp.one_add_mul_le_mgf_of_neg_le`: the integrated Taylor lower bound.
* `AEMeasurable.exp_le_mgf_of_abs_le`: the exponential lower bound for a centred bounded variable.
* `ProbabilityTheory.iIndepFun.exp_le_mgf_sum_of_abs_le`: the bound for independent sums.
-/

public section

open MeasureTheory ProbabilityTheory Real

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

namespace ProbabilityTheory

/-- If `X` is square integrable, `-b ≤ X` almost surely and `exp (t X)` is
integrable for some `0 ≤ t`, then
`1 + t E X + E X² * (t ^ 2 / 2 * (1 - t * b / 3)) ≤ E exp (t X)`.
Only a lower bound on `X` is needed. Compare Bernstein's upper bound
`MeasureTheory.MemLp.mgf_le_exp_of_ae_le`. -/
theorem _root_.MeasureTheory.MemLp.one_add_mul_le_mgf_of_neg_le [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {b t : ℝ} (hX : MemLp X 2 μ) (hb : ∀ᵐ ω ∂μ, -b ≤ X ω)
    (ht : 0 ≤ t) (hexp : Integrable (fun ω ↦ exp (t * X ω)) μ) :
    1 + t * μ[X] + (∫ ω, X ω ^ 2 ∂μ) * (t ^ 2 / 2 * (1 - t * b / 3)) ≤ mgf X μ t := by
  have hXi : Integrable X μ := hX.integrable one_le_two
  have hX2 : Integrable (fun ω ↦ X ω ^ 2) μ := hX.integrable_sq
  set k := t ^ 2 / 2 * (1 - t * b / 3)
  -- Pointwise, `1 + t X + k X² ≤ exp (t X)` since `-t b ≤ t X`.
  have hpt : ∀ᵐ ω ∂μ, 1 + t * X ω + k * X ω ^ 2 ≤ exp (t * X ω) := by
    filter_upwards [hb] with ω hω
    have h := one_add_add_sq_div_two_mul_le_exp_of_neg_le (x := t * X ω) (c := t * b)
      (by nlinarith)
    simp only [k]
    nlinarith [h]
  have hint₁ : Integrable (fun ω ↦ 1 + t * X ω) μ := (integrable_const 1).add (hXi.const_mul t)
  have hint : Integrable (fun ω ↦ 1 + t * X ω + k * X ω ^ 2) μ := hint₁.add (hX2.const_mul k)
  calc 1 + t * μ[X] + (∫ ω, X ω ^ 2 ∂μ) * k = ∫ ω, (1 + t * X ω + k * X ω ^ 2) ∂μ := by
        rw [integral_add hint₁ (hX2.const_mul k),
          integral_add (integrable_const 1) (hXi.const_mul t), integral_const_mul,
          integral_const_mul]
        simp [mul_comm]
    _ ≤ mgf X μ t := integral_mono_ae hint hexp hpt

/-- **A lower bound for the moment-generating function.** If `X` is almost everywhere
measurable, has mean zero and `|X| ≤ b` almost surely, then for every real `t`,
`exp (E X² * t ^ 2 / 2 * (1 - |t| * b)) ≤ E exp (t X)`. Compare
Bernstein's upper bound `MeasureTheory.MemLp.mgf_le_exp_of_ae_le`. -/
theorem _root_.AEMeasurable.exp_le_mgf_of_abs_le [IsProbabilityMeasure μ] {X : Ω → ℝ} {b t : ℝ}
    (hX : AEMeasurable X μ) (hmean : μ[X] = 0) (hb : ∀ᵐ ω ∂μ, |X ω| ≤ b) :
    exp ((∫ ω, X ω ^ 2 ∂μ) * t ^ 2 / 2 * (1 - |t| * b)) ≤ mgf X μ t := by
  wlog ht : 0 ≤ t generalizing X t
  · have h := this hX.neg (by simpa only [Pi.neg_apply, integral_neg, neg_eq_zero] using hmean)
      (by simpa only [Pi.neg_apply, abs_neg] using hb) (neg_nonneg.mpr (le_of_not_ge ht))
    simpa only [Pi.neg_apply, neg_sq, abs_neg, mgf, neg_mul_neg] using h
  rw [abs_of_nonneg ht]
  have hb0 : 0 ≤ b := by
    obtain ⟨ω, hω⟩ := hb.exists
    exact (abs_nonneg _).trans hω
  have hL2 : MemLp X 2 μ := MemLp.of_bound hX.aestronglyMeasurable b (by simpa using hb)
  have hXi : Integrable X μ := hL2.integrable one_le_two
  have hexp : Integrable (fun ω ↦ exp (t * X ω)) μ := integrable_exp_mul_of_le t b ht hX (by
    filter_upwards [hb] with ω hω using (le_abs_self _).trans hω)
  set v := ∫ ω, X ω ^ 2 ∂μ
  have hv0 : 0 ≤ v := integral_nonneg fun ω ↦ sq_nonneg _
  rcases lt_or_ge 1 (t * b) with htb | htb
  · -- For `1 < t b` the exponent is negative, while `E exp (t X) ≥ 1 + t E X = 1`.
    refine (exp_le_one_iff.2 (by nlinarith [mul_nonneg hv0 (sq_nonneg t)])).trans ?_
    have hJ := convexOn_exp.map_integral_le continuous_exp.continuousOn isClosed_univ
      (Filter.Eventually.of_forall fun _ ↦ Set.mem_univ _) (hXi.const_mul t) hexp
    simpa only [mgf, integral_const_mul, hmean, mul_zero, exp_zero] using hJ
  have hmgf := hL2.one_add_mul_le_mgf_of_neg_le
    (by filter_upwards [hb] with ω hω using (abs_le.1 hω).1) ht hexp
  simp only [hmean, mul_zero, add_zero] at hmgf
  -- `1 + u ≥ exp (2 u / (u + 2))` for `u = v (t ^ 2 / 2) (1 - t b / 3) ≥ 0`, and
  -- `2 u / (u + 2)` is at least the exponent of the claim because `v t ^ 2 ≤ (t b) ^ 2 ≤ t b ≤ 1`.
  obtain ⟨w, hw⟩ : ∃ w, w = v * t ^ 2 := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, y = t * b := ⟨_, rfl⟩
  have hw0 : 0 ≤ w := hw ▸ mul_nonneg hv0 (sq_nonneg t)
  have hwy : w ≤ y := by
    have hvb : v ≤ b ^ 2 := by
      have := integral_mono_ae hL2.integrable_sq (integrable_const (b ^ 2)) (by
        filter_upwards [hb] with ω hω
        exact sq_le_sq' (abs_le.1 hω).1 (abs_le.1 hω).2)
      simpa using this
    have : v * t ^ 2 ≤ (t * b) ^ 2 := by nlinarith [sq_nonneg t]
    nlinarith [mul_nonneg ht hb0]
  have hu : v * (t ^ 2 / 2 * (1 - t * b / 3)) = w / 2 * (1 - y / 3) := by rw [hw, hy]; ring
  rw [hu] at hmgf
  have hu0 : 0 ≤ w / 2 * (1 - y / 3) := by
    have : y / 3 ≤ 1 := by linarith
    positivity
  have hlog := le_log_one_add_of_nonneg hu0
  rw [← exp_le_exp, exp_log (by positivity)] at hlog
  refine le_trans (exp_le_exp.2 ?_) (hlog.trans hmgf)
  have hexponent : v * t ^ 2 / 2 * (1 - t * b) = w / 2 * (1 - y) := by rw [hw, hy]
  rw [hexponent, le_div_iff₀ (by positivity)]
  have h1 : (1 - y) * (1 - y / 3) ≤ 1 := by nlinarith [mul_nonneg ht hb0]
  nlinarith [mul_le_mul_of_nonneg_left h1 hw0, mul_nonneg ht hb0]

/-- **A lower bound for the moment-generating function of an independent sum.** If the `Xᵢ`,
`i ∈ s`, are independent and almost everywhere measurable with mean zero and `|Xᵢ| ≤ b` almost
surely, then for every real `t` the moment-generating function of `∑ i ∈ s, Xᵢ` at `t` is at least
`exp (v * t ^ 2 / 2 * (1 - |t| * b))`, where `v = ∑ i ∈ s, E Xᵢ²`. Compare Bernstein's upper bound
`ProbabilityTheory.iIndepFun.mgf_sum_le_exp_of_ae_le`. -/
theorem iIndepFun.exp_le_mgf_sum_of_abs_le {ι : Type*} {X : ι → Ω → ℝ}
    (h_indep : iIndepFun X μ) {s : Finset ι} {b t : ℝ} (hX : ∀ i ∈ s, AEMeasurable (X i) μ)
    (hmean : ∀ i ∈ s, μ[X i] = 0) (hb : ∀ i ∈ s, ∀ᵐ ω ∂μ, |X i ω| ≤ b) :
    exp ((∑ i ∈ s, ∫ ω, X i ω ^ 2 ∂μ) * t ^ 2 / 2 * (1 - |t| * b)) ≤
      mgf (fun ω ↦ ∑ i ∈ s, X i ω) μ t := by
  have : IsProbabilityMeasure μ := h_indep.isProbabilityMeasure
  rw [h_indep.mgf_sum_of_aemeasurable hX, Finset.sum_mul, Finset.sum_div, Finset.sum_mul,
    exp_sum]
  exact Finset.prod_le_prod₀ (fun i _ ↦ (exp_pos _).le)
    fun i hi ↦ (hX i hi).exp_le_mgf_of_abs_le (hmean i hi) (hb i hi)

end ProbabilityTheory
