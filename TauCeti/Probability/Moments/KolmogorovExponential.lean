/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Moments.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import TauCeti.Analysis.SpecialFunctions.Exp.Taylor
import TauCeti.Probability.Moments.Basic
import TauCeti.Probability.Moments.Bernstein

/-!
# Kolmogorov's lower exponential bound

Let `X₁, …, Xₙ` be independent centred random variables with `|Xᵢ| ≤ M` almost surely, and let
`B = ∑ᵢ E Xᵢ²` be the variance of `S = ∑ᵢ Xᵢ`. Bernstein's inequality bounds `P(S > x)` above by
`exp (-(x² / 2B) (1 - o(1)))` when `x M / B` is small. Kolmogorov's lower exponential bound is the
matching lower bound: `P(S > x) > exp (-(x² / 2B) (1 + ε))`, with an explicit `ε` that is small
when `x M / B` is small and `x² / B` is large. Together the two bounds pin the tail of `S` at the
Gaussian rate in this range of `x`, which is what the lower half of the law of the iterated
logarithm needs.

The proof tilts the law of `S` by `exp (a S)` with `a = x / (B (1 - δ))`, `δ = ε / 8`. The
moment-generating function at `a` is at least `exp (B a² (1 - a M) / 2)`. Splitting `exp (a S)`
according as `S ≤ x`, `x < S ≤ a B (1 + δ)` or `S > a B (1 + δ)`, and comparing the two outer
pieces with the tilts at `a (1 - δ)` and `a (1 + δ)`, where Bernstein's bound on the
moment-generating function applies, shows that the middle piece carries at least half of it.
This replaces Kolmogorov's splitting of a layer-cake integral by a comparison of three tilts.

## Main results

* `MeasureTheory.MemLp.one_add_mul_le_mgf_of_neg_le`: if `E X = 0` and `-b ≤ X`, then
  `1 + E X² t² (1 - t b / 3) / 2 ≤ E exp (t X)` for `0 ≤ t`;
* `ProbabilityTheory.exp_le_mgf_of_abs_le`: if `E X = 0` and `|X| ≤ b`, then
  `exp (E X² t² (1 - t b) / 2) ≤ E exp (t X)` for `0 ≤ t`;
* `ProbabilityTheory.iIndepFun.exp_le_mgf_sum_of_abs_le`: the same lower bound for an independent
  sum, with `E X²` replaced by the sum of the second moments;
* `ProbabilityTheory.iIndepFun.exp_lt_measureReal_sum_gt_of_abs_le`: the lower bound
  `exp (-(x² / 2B) (1 + ε)) < P(S > x)` for every `0 ≤ ε ≤ 1` with `x M / B ≤ (ε / 64)²` and
  `512 ≤ (x² / B) ε²`;
* `TauCeti.kolmogorovEpsilon`: Kolmogorov's error term
  `max (32 √(log λ / λ)) (64 √ω)` as a function of `ω = x M / B` and `λ = x² / B`;
* `ProbabilityTheory.iIndepFun.kolmogorov_lower_exponential_bound`: **Kolmogorov's lower
  exponential bound**, the previous bound with `ε = kolmogorovEpsilon (x M / B) (x² / B) ≤ 1`.

## References

* A. Kolmogoroff, *Über das Gesetz des iterierten Logarithmus*, Math. Ann. 101 (1929), 126–135,
  Hilfssatz IV (p. 128).
-/

public section

open MeasureTheory ProbabilityTheory Real

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

namespace ProbabilityTheory

/-- If `X` is square integrable with mean zero, `-b ≤ X` almost surely and `exp (t X)` is
integrable for some `0 ≤ t`, then `1 + E X² * (t ^ 2 / 2 * (1 - t * b / 3)) ≤ E exp (t X)`. Only a
lower bound on `X` is needed. Compare the first step of Bernstein's upper bound
`MeasureTheory.MemLp.mgf_le_exp_of_ae_le`. -/
theorem _root_.MeasureTheory.MemLp.one_add_mul_le_mgf_of_neg_le [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {b t : ℝ} (hX : MemLp X 2 μ) (hmean : μ[X] = 0) (hb : ∀ᵐ ω ∂μ, -b ≤ X ω)
    (ht : 0 ≤ t) (hexp : Integrable (fun ω ↦ exp (t * X ω)) μ) :
    1 + (∫ ω, X ω ^ 2 ∂μ) * (t ^ 2 / 2 * (1 - t * b / 3)) ≤ mgf X μ t := by
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
  calc 1 + (∫ ω, X ω ^ 2 ∂μ) * k = ∫ ω, (1 + t * X ω + k * X ω ^ 2) ∂μ := by
        rw [integral_add hint₁ (hX2.const_mul k),
          integral_add (integrable_const 1) (hXi.const_mul t), integral_const_mul,
          integral_const_mul, hmean]
        simp [mul_comm]
    _ ≤ mgf X μ t := integral_mono_ae hint hexp hpt

/-- **A lower bound for the moment-generating function.** If `X` has mean zero and `|X| ≤ b`
almost surely, then for `0 ≤ t`, `exp (E X² * t ^ 2 / 2 * (1 - t * b)) ≤ E exp (t X)`. Compare
Bernstein's upper bound `MeasureTheory.MemLp.mgf_le_exp_of_ae_le`. -/
theorem exp_le_mgf_of_abs_le [IsProbabilityMeasure μ] {X : Ω → ℝ} {b t : ℝ}
    (hX : AEMeasurable X μ) (hmean : μ[X] = 0) (hb : ∀ᵐ ω ∂μ, |X ω| ≤ b) (ht : 0 ≤ t) :
    exp ((∫ ω, X ω ^ 2 ∂μ) * t ^ 2 / 2 * (1 - t * b)) ≤ mgf X μ t := by
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
    calc (1 : ℝ) = ∫ ω, (1 + t * X ω) ∂μ := by
          rw [integral_add (integrable_const 1) (hXi.const_mul t), integral_const_mul, hmean]
          simp
      _ ≤ mgf X μ t := integral_mono_ae ((integrable_const 1).add (hXi.const_mul t)) hexp
          (.of_forall fun ω ↦ by linarith [add_one_le_exp (t * X ω)])
  have hmgf := hL2.one_add_mul_le_mgf_of_neg_le hmean
    (by filter_upwards [hb] with ω hω using (abs_le.1 hω).1) ht hexp
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
  rw [show v * t ^ 2 / 2 * (1 - t * b) = w / 2 * (1 - y) by rw [hw, hy],
    le_div_iff₀ (by positivity)]
  have h1 : (1 - y) * (1 - y / 3) ≤ 1 := by nlinarith [mul_nonneg ht hb0]
  nlinarith [mul_le_mul_of_nonneg_left h1 hw0, mul_nonneg ht hb0]

/-- **A lower bound for the moment-generating function of an independent sum.** If the `Xᵢ`,
`i ∈ s`, are independent and almost everywhere measurable with mean zero and `|Xᵢ| ≤ b` almost
surely, then for `0 ≤ t` the moment-generating function of `∑ i ∈ s, Xᵢ` at `t` is at least
`exp (v * t ^ 2 / 2 * (1 - t * b))`, where `v = ∑ i ∈ s, E Xᵢ²`. Compare Bernstein's upper bound
`ProbabilityTheory.iIndepFun.mgf_sum_le_exp_of_ae_le`. -/
theorem iIndepFun.exp_le_mgf_sum_of_abs_le {ι : Type*} {X : ι → Ω → ℝ}
    (h_indep : iIndepFun X μ) {s : Finset ι} {b t : ℝ} (hX : ∀ i ∈ s, AEMeasurable (X i) μ)
    (hmean : ∀ i ∈ s, μ[X i] = 0) (hb : ∀ i ∈ s, ∀ᵐ ω ∂μ, |X i ω| ≤ b) (ht : 0 ≤ t) :
    exp ((∑ i ∈ s, ∫ ω, X i ω ^ 2 ∂μ) * t ^ 2 / 2 * (1 - t * b)) ≤
      mgf (fun ω ↦ ∑ i ∈ s, X i ω) μ t := by
  have : IsProbabilityMeasure μ := h_indep.isProbabilityMeasure
  rw [h_indep.mgf_sum_of_aemeasurable hX, Finset.sum_mul, Finset.sum_div, Finset.sum_mul,
    exp_sum]
  exact Finset.prod_le_prod₀ (fun i _ ↦ (exp_pos _).le)
    fun i hi ↦ exp_le_mgf_of_abs_le (hX i hi) (hmean i hi) (hb i hi) ht

/-- Comparison of three tilts: for `0 ≤ a` and `b ≤ a ≤ c`, splitting `exp (a S)` according as
`S ≤ x`, `x < S ≤ y` or `y < S` gives
`E exp (a S) ≤ exp ((a - b) x) E exp (b S) + exp (a y) P(x < S) + exp (-(c - a) y) E exp (c S)`. -/
private theorem mgf_le_tilt [IsFiniteMeasure μ] {S : Ω → ℝ} (hS : AEMeasurable S μ)
    {a b c x y : ℝ} (ha : 0 ≤ a) (hba : b ≤ a) (hac : a ≤ c)
    (hb : Integrable (fun ω ↦ exp (b * S ω)) μ) (hc : Integrable (fun ω ↦ exp (c * S ω)) μ) :
    mgf S μ a ≤ exp ((a - b) * x) * mgf S μ b + exp (a * y) * μ.real {ω | x < S ω} +
      exp (-((c - a) * y)) * mgf S μ c := by
  set E := {ω | x < S ω}
  have hE : NullMeasurableSet E μ := nullMeasurableSet_lt aemeasurable_const hS
  have hb' := hb.const_mul (exp ((a - b) * x))
  have hc' := hc.const_mul (exp (-((c - a) * y)))
  have hi : Integrable (E.indicator fun _ ↦ exp (a * y)) μ :=
    (integrable_const _).indicator₀ hE
  have hpt (ω : Ω) : exp (a * S ω) ≤ exp ((a - b) * x) * exp (b * S ω) +
      E.indicator (fun _ ↦ exp (a * y)) ω + exp (-((c - a) * y)) * exp (c * S ω) := by
    have h₁ := mul_nonneg (exp_pos ((a - b) * x)).le (exp_pos (b * S ω)).le
    have h₂ : 0 ≤ E.indicator (fun _ ↦ exp (a * y)) ω :=
      Set.indicator_nonneg (fun _ _ ↦ (exp_pos _).le) ω
    have h₃ := mul_nonneg (exp_pos (-((c - a) * y))).le (exp_pos (c * S ω)).le
    rcases le_or_gt (S ω) x with hx | hx
    · rw [← exp_add]
      have : a * S ω ≤ (a - b) * x + b * S ω := by nlinarith
      linarith [exp_le_exp.2 this]
    rcases le_or_gt (S ω) y with hy | hy
    · rw [Set.indicator_of_mem (show ω ∈ E from hx)]
      linarith [exp_le_exp.2 (mul_le_mul_of_nonneg_left hy ha)]
    · rw [← exp_add (-((c - a) * y))]
      have : a * S ω ≤ -((c - a) * y) + c * S ω := by nlinarith
      linarith [exp_le_exp.2 this]
  calc mgf S μ a ≤ ∫ ω, (exp ((a - b) * x) * exp (b * S ω) +
        E.indicator (fun _ ↦ exp (a * y)) ω + exp (-((c - a) * y)) * exp (c * S ω)) ∂μ :=
        integral_mono_of_nonneg (.of_forall fun ω ↦ (exp_pos _).le) ((hb'.add hi).add hc')
          (.of_forall hpt)
    _ = _ := by
        rw [integral_add (f := fun ω ↦ exp ((a - b) * x) * exp (b * S ω) +
          E.indicator (fun _ ↦ exp (a * y)) ω) (hb'.add hi) hc', integral_add hb' hi,
          integral_const_mul, integral_const_mul, integral_indicator₀ hE, setIntegral_const,
          smul_eq_mul, mgf, mgf]
        ring

/-- The exponent comparisons behind the lower bound, for the tilt `a`, the relative width `δ`,
`L = a² B` and `α = a M`: the outer tilts `a (1 ∓ δ)` fall short of the lower bound
`L (1 - α) / 2` for the tilt `a` by at least `2`, and the middle piece exceeds the target
exponent by more than `1`. -/
private theorem tilt_exponent_bounds {a B M δ : ℝ} (ha : 0 < a) (hM : 0 ≤ M) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1 / 8) (haM : a * M ≤ δ ^ 2 / 32) (hL : 8 ≤ a ^ 2 * B * δ ^ 2) :
    (a - a * (1 - δ)) * (a * B * (1 - δ)) +
        B * (a * (1 - δ)) ^ 2 / (2 * (1 - a * (1 - δ) * M / 3)) + 2 ≤
      B * a ^ 2 / 2 * (1 - a * M) ∧
    -((a * (1 + δ) - a) * (a * B * (1 + δ))) +
        B * (a * (1 + δ)) ^ 2 / (2 * (1 - a * (1 + δ) * M / 3)) + 2 ≤
      B * a ^ 2 / 2 * (1 - a * M) ∧
    -((a * B * (1 - δ)) ^ 2 / (2 * B) * (1 + 8 * δ)) + 1 <
      B * a ^ 2 / 2 * (1 - a * M) - a * (a * B * (1 + δ)) := by
  obtain ⟨L, hL'⟩ : ∃ L, L = a ^ 2 * B := ⟨_, rfl⟩
  obtain ⟨α, hα⟩ : ∃ α, α = a * M := ⟨_, rfl⟩
  have hα0 : 0 ≤ α := hα ▸ mul_nonneg ha.le hM
  have hαδ : α ≤ δ ^ 2 / 32 := hα ▸ haM
  have hL8 : 8 ≤ L * δ ^ 2 := hL' ▸ hL
  have hL0 : 0 < L := by nlinarith [sq_nonneg δ]
  have hB0 : 0 < B := by
    rw [hL'] at hL0
    exact pos_of_mul_pos_right hL0 (sq_nonneg a)
  have hδ2 : δ ^ 2 ≤ δ / 8 := by nlinarith
  have hE : B * a ^ 2 / 2 * (1 - a * M) = L / 2 * (1 - α) := by rw [hL', hα]; ring
  refine ⟨?_, ?_, ?_⟩
  · -- `B (a (1 - δ))² / (2 (1 - α (1 - δ) / 3)) ≤ L ((1 - δ)² + α) / 2`.
    have hq : B * (a * (1 - δ)) ^ 2 / (2 * (1 - a * (1 - δ) * M / 3)) ≤
        L / 2 * ((1 - δ) ^ 2 + α) := by
      have hden : 0 < 1 - α * (1 - δ) / 3 := by nlinarith
      rw [show a * (1 - δ) * M = α * (1 - δ) by rw [hα]; ring, div_le_iff₀ (by positivity)]
      have : (1 - δ) ^ 2 ≤ ((1 - δ) ^ 2 + α) * (1 - α * (1 - δ) / 3) := by
        nlinarith [mul_nonneg hα0 hδ.le, mul_nonneg (mul_nonneg hα0 hα0) hδ.le]
      calc B * (a * (1 - δ)) ^ 2 = L * (1 - δ) ^ 2 := by rw [hL']; ring
        _ ≤ L * (((1 - δ) ^ 2 + α) * (1 - α * (1 - δ) / 3)) :=
          mul_le_mul_of_nonneg_left this hL0.le
        _ = _ := by ring
    rw [show (a - a * (1 - δ)) * (a * B * (1 - δ)) = L * δ * (1 - δ) by rw [hL']; ring, hE]
    nlinarith [mul_le_mul_of_nonneg_left hαδ hL0.le]
  · -- `B (a (1 + δ))² / (2 (1 - α (1 + δ) / 3)) ≤ L ((1 + δ)² + 2 α) / 2`.
    have hq : B * (a * (1 + δ)) ^ 2 / (2 * (1 - a * (1 + δ) * M / 3)) ≤
        L / 2 * ((1 + δ) ^ 2 + 2 * α) := by
      have hden : 0 < 1 - α * (1 + δ) / 3 := by nlinarith
      rw [show a * (1 + δ) * M = α * (1 + δ) by rw [hα]; ring, div_le_iff₀ (by positivity)]
      have : (1 + δ) ^ 2 ≤ ((1 + δ) ^ 2 + 2 * α) * (1 - α * (1 + δ) / 3) := by
        nlinarith [mul_nonneg hα0 hδ.le, mul_nonneg (mul_nonneg hα0 hα0) hδ.le,
          mul_nonneg (mul_nonneg hα0 hδ.le) hδ.le,
          mul_nonneg (mul_nonneg (mul_nonneg hα0 hδ.le) hδ.le) hδ.le]
      calc B * (a * (1 + δ)) ^ 2 = L * (1 + δ) ^ 2 := by rw [hL']; ring
        _ ≤ L * (((1 + δ) ^ 2 + 2 * α) * (1 - α * (1 + δ) / 3)) :=
          mul_le_mul_of_nonneg_left this hL0.le
        _ = _ := by ring
    rw [show (a * (1 + δ) - a) * (a * B * (1 + δ)) = L * δ * (1 + δ) by rw [hL']; ring, hE]
    nlinarith [mul_le_mul_of_nonneg_left hαδ hL0.le]
  · rw [show (a * B * (1 - δ)) ^ 2 / (2 * B) = L / 2 * (1 - δ) ^ 2 by rw [hL']; field_simp,
      show B * a ^ 2 / 2 * (1 - a * M) - a * (a * B * (1 + δ)) = -(L / 2 * (1 + 2 * δ + α)) by
        rw [hL', hα]; ring]
    -- `(1 - δ)² (1 + 8 δ) - (1 + 2 δ + α) ≥ 2 δ` and `L δ ≥ 8 L δ² ≥ 64`.
    have hk : 2 * δ ≤ (1 - δ) ^ 2 * (1 + 8 * δ) - (1 + 2 * δ + α) := by
      nlinarith [pow_pos hδ 3]
    have hLδ : 64 ≤ L * δ := by nlinarith [mul_le_mul_of_nonneg_left hδ2 hL0.le]
    nlinarith [mul_le_mul_of_nonneg_left hk hL0.le]

/-- The lower bound in terms of the tilt `a` and the relative width `δ`, at the level
`x = a B (1 - δ)`. -/
private theorem exp_lt_measureReal_sum_gt_of_tilt {ι : Type*} {X : ι → Ω → ℝ}
    (h_indep : iIndepFun X μ) {s : Finset ι} {M B a δ : ℝ}
    (hX : ∀ i ∈ s, AEMeasurable (X i) μ) (hmean : ∀ i ∈ s, μ[X i] = 0)
    (hb : ∀ i ∈ s, ∀ᵐ ω ∂μ, |X i ω| ≤ M) (hB : ∑ i ∈ s, ∫ ω, X i ω ^ 2 ∂μ = B)
    (ha : 0 < a) (hM : 0 ≤ M) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 8)
    (haM : a * M ≤ δ ^ 2 / 32) (hL : 8 ≤ a ^ 2 * B * δ ^ 2) :
    exp (-((a * B * (1 - δ)) ^ 2 / (2 * B)) * (1 + 8 * δ)) <
      μ.real {ω | a * B * (1 - δ) < ∑ i ∈ s, X i ω} := by
  have : IsProbabilityMeasure μ := h_indep.isProbabilityMeasure
  obtain ⟨h₁, h₃, h₂⟩ := tilt_exponent_bounds ha hM hδ0 hδ1 haM hL
  have hS : AEMeasurable (fun ω ↦ ∑ i ∈ s, X i ω) μ := Finset.aemeasurable_fun_sum s hX
  have hL2 : ∀ i ∈ s, MemLp (X i) 2 μ := fun i hi ↦
    MemLp.of_bound (hX i hi).aestronglyMeasurable M (by simpa using hb i hi)
  have hup : ∀ i ∈ s, ∀ᵐ ω ∂μ, X i ω ≤ M := fun i hi ↦ by
    filter_upwards [hb i hi] with ω hω using (le_abs_self _).trans hω
  have hSle : ∀ᵐ ω ∂μ, ∑ i ∈ s, X i ω ≤ s.card * M := by
    filter_upwards [(Filter.eventually_all_finset s).2 hup] with ω hω
    simpa using Finset.sum_le_card_nsmul s (fun i ↦ X i ω) M hω
  have hδa : 0 ≤ a * δ := by positivity
  -- The moment-generating function at `a` from below, at `a (1 ∓ δ)` from above.
  have hlow := h_indep.exp_le_mgf_sum_of_abs_le hX hmean hb ha.le
  have hm₁ := h_indep.mgf_sum_le_exp_of_ae_le hL2 hmean hup (t := a * (1 - δ))
    (by nlinarith) (by nlinarith)
  have hm₃ := h_indep.mgf_sum_le_exp_of_ae_le hL2 hmean hup (t := a * (1 + δ))
    (by nlinarith) (by nlinarith)
  rw [hB] at hlow hm₁ hm₃
  have htilt := mgf_le_tilt hS (x := a * B * (1 - δ)) (y := a * B * (1 + δ)) ha.le
    (by nlinarith : a * (1 - δ) ≤ a) (by nlinarith : a ≤ a * (1 + δ))
    (integrable_exp_mul_of_le _ _ (by nlinarith) hS hSle)
    (integrable_exp_mul_of_le _ _ (by nlinarith) hS hSle)
  -- The two outer tilts carry at most a quarter of the lower bound `exp E` each.
  obtain ⟨E, hE⟩ : ∃ E, E = B * a ^ 2 / 2 * (1 - a * M) := ⟨_, rfl⟩
  rw [← hE] at hlow h₁ h₂ h₃
  have he2 : exp (E + -2) ≤ exp E / 4 := by
    have : exp (-2) ≤ 1 / 4 := by
      rw [exp_neg, inv_le_comm₀ (exp_pos _) (by norm_num)]
      linarith [quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    rw [exp_add]
    nlinarith [exp_pos E]
  have hout₁ := mul_le_mul_of_nonneg_left hm₁
    (exp_pos ((a - a * (1 - δ)) * (a * B * (1 - δ)))).le
  have hout₃ := mul_le_mul_of_nonneg_left hm₃
    (exp_pos (-((a * (1 + δ) - a) * (a * B * (1 + δ))))).le
  rw [← exp_add] at hout₁ hout₃
  have hc₁ : _ ≤ exp (E + -2) := hout₁.trans (exp_le_exp.2 (by linarith))
  have hc₃ : _ ≤ exp (E + -2) := hout₃.trans (exp_le_exp.2 (by linarith))
  have hmid : exp E / 2 ≤ exp (a * (a * B * (1 + δ))) *
      μ.real {ω | a * B * (1 - δ) < ∑ i ∈ s, X i ω} := by
    linarith
  have he1 : exp (-1) ≤ 1 / 2 := by
    rw [exp_neg, inv_le_comm₀ (exp_pos _) (by norm_num)]
    linarith [add_one_le_exp (1 : ℝ)]
  rw [← div_le_iff₀' (exp_pos _)] at hmid
  calc exp (-((a * B * (1 - δ)) ^ 2 / (2 * B)) * (1 + 8 * δ))
      < exp (E - a * (a * B * (1 + δ)) + -1) := exp_lt_exp.2 (by linarith)
    _ = exp E * exp (-1) / exp (a * (a * B * (1 + δ))) := by rw [exp_add, exp_sub]; ring
    _ ≤ exp E / 2 / exp (a * (a * B * (1 + δ))) := by gcongr; nlinarith [exp_pos E]
    _ ≤ _ := hmid

/-- **A lower exponential bound for the upper tail of an independent sum.** Let the `Xᵢ`,
`i ∈ s`, be independent and almost everywhere measurable with mean zero and `|Xᵢ| ≤ M` almost
surely, and let `B = ∑ i ∈ s, E Xᵢ²`. If `0 < x`, `0 ≤ ε ≤ 1`, `x M / B ≤ (ε / 64) ^ 2` and
`512 ≤ (x ^ 2 / B) ε ^ 2`, then `exp (-(x ^ 2 / (2 B)) (1 + ε)) < P(x < ∑ i ∈ s, Xᵢ)`. -/
theorem iIndepFun.exp_lt_measureReal_sum_gt_of_abs_le {ι : Type*} {X : ι → Ω → ℝ}
    (h_indep : iIndepFun X μ) {s : Finset ι} {M B x ε : ℝ}
    (hX : ∀ i ∈ s, AEMeasurable (X i) μ) (hmean : ∀ i ∈ s, μ[X i] = 0)
    (hb : ∀ i ∈ s, ∀ᵐ ω ∂μ, |X i ω| ≤ M) (hB : ∑ i ∈ s, ∫ ω, X i ω ^ 2 ∂μ = B) (hx : 0 < x)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hw : x * M / B ≤ (ε / 64) ^ 2)
    (hl : 512 ≤ x ^ 2 / B * ε ^ 2) :
    exp (-(x ^ 2 / (2 * B)) * (1 + ε)) < μ.real {ω | x < ∑ i ∈ s, X i ω} := by
  -- The hypotheses force `B > 0`, hence `s` nonempty and `M ≥ 0`.
  have hB0 : 0 < B := by
    refine (hB ▸ Finset.sum_nonneg fun i _ ↦ integral_nonneg fun ω ↦ sq_nonneg _).lt_of_ne
      fun h ↦ ?_
    simp [← h] at hl
    linarith
  obtain ⟨j, hj⟩ : s.Nonempty := Finset.nonempty_of_sum_ne_zero (hB ▸ hB0.ne')
  have hM : 0 ≤ M := by
    have : IsProbabilityMeasure μ := h_indep.isProbabilityMeasure
    obtain ⟨ω, hω⟩ := (hb j hj).exists
    exact (abs_nonneg _).trans hω
  -- Apply the tilted bound with `δ = ε / 8` and `a = x / (B (1 - δ))`.
  have hε0 : 0 < ε := hε.lt_of_ne fun h ↦ by simp [← h] at hl; linarith
  have hδ0 : 0 < ε / 8 := by positivity
  have h1δ : 0 < 1 - ε / 8 := by linarith
  have h8 : 8 - ε ≠ 0 := by linarith
  have ha : 0 < x / (B * (1 - ε / 8)) := by positivity
  have hxa : x / (B * (1 - ε / 8)) * B * (1 - ε / 8) = x := by field_simp
  have h := exp_lt_measureReal_sum_gt_of_tilt h_indep hX hmean hb hB ha hM hδ0 (by linarith)
    ?_ ?_
  · rwa [hxa, show 1 + 8 * (ε / 8) = 1 + ε by ring] at h
  · rw [show x / (B * (1 - ε / 8)) * M = x * M / B / (1 - ε / 8) by field_simp,
      div_le_iff₀ h1δ]
    nlinarith
  · rw [show (x / (B * (1 - ε / 8))) ^ 2 * B = x ^ 2 / B / (1 - ε / 8) ^ 2 by field_simp]
    have h0 : 0 ≤ x ^ 2 / B := by positivity
    have h2 : x ^ 2 / B ≤ x ^ 2 / B / (1 - ε / 8) ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left (by nlinarith : (1 - ε / 8) ^ 2 ≤ 1) h0]
    nlinarith [mul_le_mul_of_nonneg_right h2 (sq_nonneg (ε / 8))]

end ProbabilityTheory

namespace TauCeti

/-- **Kolmogorov's error term** in the lower exponential bound,
`max (32 √(log l / l)) (64 √w)`, as a function of `w = x M / B` and `l = x² / B`. -/
noncomputable def kolmogorovEpsilon (w l : ℝ) : ℝ :=
  max (32 * √(log l / l)) (64 * √w)

/-- The defining formula of `TauCeti.kolmogorovEpsilon`. -/
theorem kolmogorovEpsilon_def (w l : ℝ) :
    kolmogorovEpsilon w l = max (32 * √(log l / l)) (64 * √w) := (rfl)

/-- Kolmogorov's error term is nonnegative. -/
theorem kolmogorovEpsilon_nonneg (w l : ℝ) : 0 ≤ kolmogorovEpsilon w l :=
  (kolmogorovEpsilon_def w l).symm ▸ le_max_of_le_left (by positivity)

end TauCeti

namespace ProbabilityTheory

open TauCeti

/-- **Kolmogorov's lower exponential bound** (Kolmogorov 1929, Hilfssatz IV). Let the `Xᵢ`,
`i ∈ s`, be independent and almost everywhere measurable with mean zero and `|Xᵢ| ≤ M` almost
surely, and let `B = ∑ i ∈ s, E Xᵢ²`. Put `ω = x M / B`, `λ = x² / B` and
`ε = kolmogorovEpsilon ω λ = max (32 √(log λ / λ)) (64 √ω)`. If `0 < x`, `2 ≤ λ` and `ε ≤ 1`,
then `exp (-(x² / (2 B)) (1 + ε)) < P(x < ∑ i ∈ s, Xᵢ)`.

Kolmogorov assumes `ω < 1 / 256` and `λ > 512` instead of `ε ≤ 1` and `2 ≤ λ`; here `ε ≤ 1`
already forces `ω ≤ 1 / 4096`. -/
theorem iIndepFun.kolmogorov_lower_exponential_bound {ι : Type*} {X : ι → Ω → ℝ}
    (h_indep : iIndepFun X μ) {s : Finset ι} {M B x : ℝ}
    (hX : ∀ i ∈ s, AEMeasurable (X i) μ) (hmean : ∀ i ∈ s, μ[X i] = 0)
    (hb : ∀ i ∈ s, ∀ᵐ ω ∂μ, |X i ω| ≤ M) (hB : ∑ i ∈ s, ∫ ω, X i ω ^ 2 ∂μ = B) (hx : 0 < x)
    (hl : 2 ≤ x ^ 2 / B) (hε : kolmogorovEpsilon (x * M / B) (x ^ 2 / B) ≤ 1) :
    exp (-(x ^ 2 / (2 * B)) * (1 + kolmogorovEpsilon (x * M / B) (x ^ 2 / B))) <
      μ.real {ω | x < ∑ i ∈ s, X i ω} := by
  have h₁ : 32 * √(log (x ^ 2 / B) / (x ^ 2 / B)) ≤ kolmogorovEpsilon (x * M / B) (x ^ 2 / B) := by
    rw [kolmogorovEpsilon_def]
    exact le_max_left _ _
  have h₂ : 64 * √(x * M / B) ≤ kolmogorovEpsilon (x * M / B) (x ^ 2 / B) := by
    rw [kolmogorovEpsilon_def]
    exact le_max_right _ _
  set ε := kolmogorovEpsilon (x * M / B) (x ^ 2 / B)
  have hε0 : 0 ≤ ε := kolmogorovEpsilon_nonneg _ _
  refine h_indep.exp_lt_measureReal_sum_gt_of_abs_le hX hmean hb hB hx hε0 hε ?_ ?_
  · exact (sqrt_le_left (by positivity)).1 (by linarith)
  · -- `ε² ≥ 1024 log λ / λ` and `log λ ≥ 1 - 1 / λ ≥ 1 / 2`.
    have hl0 : 0 < x ^ 2 / B := by linarith
    have hq : log (x ^ 2 / B) / (x ^ 2 / B) ≤ (ε / 32) ^ 2 :=
      (sqrt_le_left (by positivity)).1 (by linarith)
    have hlog : 1 / 2 ≤ log (x ^ 2 / B) := by
      have := one_sub_inv_le_log_of_pos hl0
      have : (x ^ 2 / B)⁻¹ ≤ 1 / 2 := by
        rw [inv_le_comm₀ hl0 (by norm_num)]
        linarith
      linarith
    rw [div_le_iff₀ hl0] at hq
    nlinarith

end ProbabilityTheory
