/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Moments.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import TauCeti.Probability.Moments.Bernstein
import TauCeti.Probability.Moments.Bounded

/-!
# Kolmogorov's lower exponential bound

Let `X₁, …, Xₙ` be independent centred random variables with `|Xᵢ| ≤ M` almost surely, and let
`B = ∑ᵢ E Xᵢ²` be the variance of `S = ∑ᵢ Xᵢ`. Bernstein's inequality bounds `P(S > x)` above by
`exp (-(x² / 2B) (1 - o(1)))` when `x M / B` is small. Kolmogorov's lower exponential bound is the
matching lower bound: `P(S > x) > exp (-(x² / 2B) (1 + ε))`, with an explicit `ε` that is small
when `x M / B` is small and `x² / B` is large. Together the two bounds pin the tail of `S` at the
Gaussian rate in this range of `x`, which is what the lower half of the law of the iterated
logarithm needs.

Use `iIndepFun.exp_lt_measureReal_sum_gt_of_abs_le` when an application supplies its own
error `ε` and verifies the two numerical bounds. Use `iIndepFun.kolmogorov_lower_exponential_bound`
for the explicit error `kolmogorovEpsilon`; it requires `0 < x`, `2 ≤ x²/B` and an error at most
one. `TauCeti.kolmogorovEpsilon_le_iff` converts the error cutoff into two squared inequalities.
The proof compares three exponential tilts, using the lower MGF bounds in
`TauCeti.Probability.Moments.Bounded` and Bernstein's upper MGF bound.

## Main results

* `ProbabilityTheory.iIndepFun.exp_lt_measureReal_sum_gt_of_abs_le`: the lower bound
  `exp (-(x² / 2B) (1 + ε)) < P(S > x)` for `0 < x` and `0 ≤ ε ≤ 1` with `x M / B ≤ (ε / 64)²` and
  `512 ≤ (x² / B) ε²`;
* `TauCeti.kolmogorovEpsilon`: Kolmogorov's error term
  `max (32 √(log λ / λ)) (64 √ω)` as a function of `ω = x M / B` and `λ = x² / B`;
* `ProbabilityTheory.iIndepFun.kolmogorov_lower_exponential_bound`: **Kolmogorov's lower
  exponential bound**, for `0 < x`, `2 ≤ x²/B` and
  `ε = kolmogorovEpsilon (x M / B) (x² / B) ≤ 1`.

## References

* A. Kolmogoroff, *Über das Gesetz des iterierten Logarithmus*, Math. Ann. 101 (1929), 126–135,
  Hilfssatz IV (p. 128).
-/

public section

open MeasureTheory ProbabilityTheory Real

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

namespace ProbabilityTheory

/-- A common denominator estimate for the two outer tilts. -/
private theorem tilt_denominator_bound {α r : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1 / 32)
    (hr1 : r ≤ 9 / 8) :
    r ^ 2 / (1 - α * r / 3) ≤ r ^ 2 + 2 * α := by
  by_cases hr0 : 0 ≤ r
  · have hαr : α * r ≤ 9 / 256 :=
      (mul_le_mul_of_nonneg_right hα1 hr0).trans (by nlinarith)
    have hden : 0 < 1 - α * r / 3 := by linarith
    rw [div_le_iff₀ hden]
    have hr3 : r ^ 3 ≤ (9 / 8 : ℝ) ^ 3 := pow_le_pow_left₀ hr0 hr1 _
    have hrem : 0 ≤ 2 - r ^ 3 / 3 - 2 * α * r / 3 := by linarith
    nlinarith [mul_nonneg hα0 hrem]
  · have hden : 1 ≤ 1 - α * r / 3 := by nlinarith
    exact (div_le_self (sq_nonneg r) hden).trans (by linarith)

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
  have hq (r : ℝ) (hr1 : r ≤ 9 / 8) :
      B * (a * r) ^ 2 / (2 * (1 - a * r * M / 3)) ≤ L / 2 * (r ^ 2 + 2 * α) := by
    have hnorm : a * r * M = α * r := by rw [hα]; ring
    have hnum : B * (a * r) ^ 2 = L * r ^ 2 := by rw [hL']; ring
    rw [hnorm, hnum]
    calc _ = L / 2 * (r ^ 2 / (1 - α * r / 3)) := by
           rw [div_mul_eq_div_div]; ring
         _ ≤ _ := mul_le_mul_of_nonneg_left
           (tilt_denominator_bound hα0 (by nlinarith) hr1) (by positivity)
  refine ⟨?_, ?_, ?_⟩
  · have hq₁ := hq (1 - δ) (by linarith)
    have hnorm : (a - a * (1 - δ)) * (a * B * (1 - δ)) = L * δ * (1 - δ) := by
      rw [hL']; ring
    rw [hnorm, hE]
    nlinarith [mul_le_mul_of_nonneg_left hαδ hL0.le]
  · have hq₃ := hq (1 + δ) (by linarith)
    have hnorm : (a * (1 + δ) - a) * (a * B * (1 + δ)) = L * δ * (1 + δ) := by
      rw [hL']; ring
    rw [hnorm, hE]
    nlinarith [mul_le_mul_of_nonneg_left hαδ hL0.le]
  · have hx : (a * B * (1 - δ)) ^ 2 / (2 * B) = L / 2 * (1 - δ) ^ 2 := by
      rw [hL']; field_simp
    have hmid : B * a ^ 2 / 2 * (1 - a * M) - a * (a * B * (1 + δ)) =
        -(L / 2 * (1 + 2 * δ + α)) := by rw [hL', hα]; ring
    rw [hx, hmid]
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
  have hexp := h_indep.integrable_exp_mul_sum_of_aemeasurable hX (t := a * (1 + δ))
    fun i hi ↦ integrable_exp_mul_of_le _ M (by positivity) (hX i hi) (hup i hi)
  -- The moment-generating function at `a` from below, at `a (1 ∓ δ)` from above.
  have hlow := h_indep.exp_le_mgf_sum_of_abs_le hX hmean hb (t := a)
  have hm₁ := h_indep.mgf_sum_le_exp_of_ae_le hL2 hmean hup (t := a * (1 - δ))
    (by nlinarith) (by nlinarith)
  have hm₃ := h_indep.mgf_sum_le_exp_of_ae_le hL2 hmean hup (t := a * (1 + δ))
    (by nlinarith) (by nlinarith)
  rw [abs_of_pos ha] at hlow
  rw [hB] at hlow hm₁ hm₃
  have htilt := hS.mgf_le_tilt (x := a * B * (1 - δ)) (y := a * B * (1 + δ)) ha.le
    (by nlinarith : a * (1 - δ) ≤ a) (by nlinarith : a ≤ a * (1 + δ))
    (integrable_exp_mul_of_nonneg_of_le hexp (by nlinarith) (by nlinarith)) hexp
  -- The two outer tilts carry at most a quarter of the lower bound `exp E` each.
  obtain ⟨E, hE⟩ : ∃ E, E = B * a ^ 2 / 2 * (1 - a * M) := ⟨_, rfl⟩
  rw [← hE] at hlow h₁ h₂ h₃
  have he2 : exp (E + -2) ≤ exp E / 4 := by
    have : exp (-2) ≤ 1 / 4 := by
      rw [exp_neg, inv_le_comm₀ (exp_pos _) (by norm_num)]
      have he : exp (2 : ℝ) = exp 1 * exp 1 := by norm_num [← exp_add]
      rw [he]
      nlinarith [exp_one_gt_two]
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
    simpa using exp_one_gt_two.le
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
  · have haM : x / (B * (1 - ε / 8)) * M = x * M / B / (1 - ε / 8) := by
      field_simp
    rw [haM, div_le_iff₀ h1δ]
    nlinarith
  · have haB : (x / (B * (1 - ε / 8))) ^ 2 * B = x ^ 2 / B / (1 - ε / 8) ^ 2 := by
      field_simp
    rw [haB]
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

/-- A nonnegative cutoff on Kolmogorov's error term is equivalent to two squared bounds.
This avoids expanding the maximum and square roots when checking the tail theorem's hypotheses. -/
theorem kolmogorovEpsilon_le_iff {w l d : ℝ} (hd : 0 ≤ d) :
    kolmogorovEpsilon w l ≤ d ↔ log l / l ≤ (d / 32) ^ 2 ∧ w ≤ (d / 64) ^ 2 := by
  rw [kolmogorovEpsilon_def, max_le_iff]
  constructor
  · rintro ⟨hl, hw⟩
    exact ⟨(sqrt_le_left (by positivity)).1 (by linarith),
      (sqrt_le_left (by positivity)).1 (by linarith)⟩
  · rintro ⟨hl, hw⟩
    have hl' := (sqrt_le_left (by positivity : 0 ≤ d / 32)).2 hl
    have hw' := (sqrt_le_left (by positivity : 0 ≤ d / 64)).2 hw
    constructor <;> linarith

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
  set ε := kolmogorovEpsilon (x * M / B) (x ^ 2 / B)
  have hε0 : 0 ≤ ε := kolmogorovEpsilon_nonneg _ _
  obtain ⟨hq, hw⟩ := (kolmogorovEpsilon_le_iff hε0).1 (le_refl ε)
  refine h_indep.exp_lt_measureReal_sum_gt_of_abs_le hX hmean hb hB hx hε0 hε hw ?_
  -- `ε² ≥ 1024 log λ / λ` and `log λ ≥ log 2 > 1 / 2`.
  have hl0 : 0 < x ^ 2 / B := by linarith
  have hlog : 1 / 2 ≤ log (x ^ 2 / B) :=
    (by linarith [log_two_gt_d9] : (1 : ℝ) / 2 ≤ log 2).trans
      (log_le_log (by norm_num) hl)
  rw [div_le_iff₀ hl0] at hq
  nlinarith

end ProbabilityTheory
