/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Perimeter
public import TauCeti.MeasureTheory.Covering.EssentialBoundary
import TauCeti.Analysis.BoundedVariation.Poincare
import TauCeti.Analysis.SpecialFunctions.Pow.NNReal
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace

/-!
# The relative isoperimetric inequality in a ball

Let `E` be a finite-dimensional real inner product space of dimension `n ≥ 2` with an additive Haar
measure `μ`, and write `ω = μ(B(0, 1))`. This file proves the **relative isoperimetric
inequality**: for every ball `B = B(c, r)` and every set `s` null-measurable in `B`,

`min (μ(s ∩ B), μ(B \ s)) ^ (1 - 1/n) ≤ 2 ^ (n + 1) ω ^ (-1/n) P(s; B)`.

The constant does not depend on the radius, so the inequality is invariant under scaling, and the
perimeter may be taken in any open set containing the ball. Neither finite perimeter nor any
regularity of `s` is assumed. This is the estimate that turns perimeter bounds into the density
estimates of the boundary structure theory of sets of finite perimeter.

It is the indicator case of the localized Poincaré–Wirtinger inequality for functions of bounded
variation,

`∫_A |u - ⨍_S u| ≤ ω ^ (1 - 1/n) (diam Ω) ^ n / μ(S) μ(A) ^ (1/n) |Du|(Ω)`

(`TauCeti.setLIntegral_enorm_sub_setAverage_le_mul_measure_rpow_mul_totalVariationOn_of_convex`).
For an indicator, testing it on `A = s ∩ B` or `A = B \ s`, whichever the indicator deviates from
its mean on by at least `1/2`, and dividing by `μ(A) ^ (1/n)` gives the relative isoperimetric
inequality.

## Main results

* `TauCeti.min_measure_inter_measure_sdiff_rpow_le_perimeter`: the relative isoperimetric
  inequality in a ball.
* `TauCeti.min_div_closedBall_rpow_le_mul_perimeter_div`: the normalized closed-ball form in terms
  of `P(s; ball x r) / r ^ (n - 1)`.
* `TauCeti.notMem_essentialBoundary_of_tendsto_perimeter_ball_div`: vanishing `(n - 1)`-dimensional
  perimeter density at `x ∈ Ω` excludes `x` from the essential boundary `∂ᵉs`.

## References

* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, Remark 3.50.
* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §5.6.2.
* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Proposition 12.37.
-/

public section

namespace TauCeti

open Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped ENNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E}

/-- On the part `t ∩ B` of a ball `B ⊆ Ω` where the indicator of `s` takes a value `b` at distance
at least `1/2` from its mean over `B`, the localized Poincaré–Wirtinger inequality gives
`μ(t ∩ B) ^ (1 - 1/n) ≤ 2 ^ (n + 1) ω ^ (-1/n) P(s; Ω)`. -/
private theorem measure_inter_ball_rpow_le_perimeter (hn : 2 ≤ finrank ℝ E) {s t : Set E} {c : E}
    {r : ℝ} (hr : 0 < r) (hs : NullMeasurableSet s (μ.restrict (ball c r))) (hΩ : ball c r ⊆ Ω)
    {b : ℝ}
    (hb : 1 / 2 ≤ |b - ⨍ y in ball c r, s.indicator 1 y ∂μ|)
    (htb : ∀ x ∈ t ∩ ball c r, s.indicator 1 x = b) :
    μ (t ∩ ball c r) ^ (1 - (finrank ℝ E : ℝ)⁻¹) ≤
      ENNReal.ofReal (2 ^ (finrank ℝ E + 1) / μ.real (ball 0 1) ^ (finrank ℝ E : ℝ)⁻¹) *
        perimeter μ Ω s := by
  set B := ball c r
  set u := s.indicator (1 : E → ℝ)
  set a := ⨍ y in B, u y ∂μ
  have hu : IntegrableOn u B μ := (integrableOn_const measure_ball_lt_top.ne).indicator₀ hs
  -- `μ(t ∩ B) / 2 ≤ ∫_{t ∩ B} |u - a| ≤ C μ(t ∩ B) ^ (1/n) P(s; B)` with `C` the
  -- Poincaré–Wirtinger constant of `B`, and `2C ≤ 2 ^ (n + 1) ω ^ (-1/n)`.
  have hb' : 2⁻¹ ≤ ‖b - a‖ₑ := by
    rw [Real.eNorm_eq_ofReal_abs, ← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_inv_of_pos two_pos,
      ← one_div]
    exact ENNReal.ofReal_le_ofReal hb
  have hlow : 2⁻¹ * μ (t ∩ B) ≤ ∫⁻ x in t ∩ B, ‖u x - a‖ₑ ∂μ := by
    rw [← setLIntegral_const]
    refine setLIntegral_mono_ae
      ((hu.aestronglyMeasurable.sub aestronglyMeasurable_const).eNorm.mono_measure
        (Measure.restrict_mono inter_subset_right le_rfl)) ?_
    exact Filter.Eventually.of_forall fun x hx => by rw [htb x hx]; exact hb'
  have hup := setLIntegral_enorm_sub_setAverage_le_mul_measure_rpow_mul_totalVariationOn_of_convex
    (Ω := ⟨B, isOpen_ball⟩) (convex_ball c r) isBounded_ball hu.locallyIntegrableOn subset_rfl
    (measure_ball_pos μ c hr).ne' (inter_subset_right : t ∩ B ⊆ B)
  refine ENNReal.rpow_one_sub_le_of_le_mul_rpow (inv_lt_one_of_one_lt₀ (by exact_mod_cast hn))
    (measure_ne_top_of_subset inter_subset_right measure_ball_lt_top.ne) ?_
  refine ((ENNReal.inv_mul_le_iff two_ne_zero ENNReal.ofNat_ne_top).1 (hlow.trans hup)).trans ?_
  rw [← mul_assoc, ← mul_assoc, mul_right_comm (2 * _)]
  gcongr
  · rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul zero_le_two]
    refine ENNReal.ofReal_le_ofReal ((mul_le_mul_of_nonneg_left
      (μ.addHaar_real_ball_rpow_mul_diam_ball_pow_div_le c hr) zero_le_two).trans_eq ?_)
    ring
  · rw [← perimeter_def]
    exact perimeter_mono hΩ

/-- **The relative isoperimetric inequality in a ball.** Let `E` have dimension `n ≥ 2` and let
`ω = μ(B(0, 1))`. If the ball `B = B(c, r)` lies in the open set `Ω` and `s` is null-measurable in
`B`, then `min (μ(s ∩ B), μ(B \ s)) ^ (1 - 1/n) ≤ 2 ^ (n + 1) ω ^ (-1/n) P(s; Ω)`. The constant does
not depend on the radius, and the perimeter may be infinite. -/
theorem min_measure_inter_measure_sdiff_rpow_le_perimeter (hn : 2 ≤ finrank ℝ E) {s : Set E}
    {c : E} {r : ℝ} (hs : NullMeasurableSet s (μ.restrict (ball c r))) (hΩ : ball c r ⊆ Ω) :
    min (μ (s ∩ ball c r)) (μ (ball c r \ s)) ^ (1 - (finrank ℝ E : ℝ)⁻¹) ≤
      ENNReal.ofReal (2 ^ (finrank ℝ E + 1) / μ.real (ball 0 1) ^ (finrank ℝ E : ℝ)⁻¹) *
        perimeter μ Ω s := by
  have hexp : 0 < 1 - (finrank ℝ E : ℝ)⁻¹ :=
    sub_pos.2 (inv_lt_one_of_one_lt₀ (by exact_mod_cast hn))
  rcases le_or_gt r 0 with hr | hr
  · simp [ball_eq_empty.2 hr, ENNReal.zero_rpow_of_pos hexp]
  -- The indicator deviates from its mean `a` over the ball by at least `1/2` on `s ∩ B` or on
  -- `B \ s`.
  set a := ⨍ y in ball c r, s.indicator (1 : E → ℝ) y ∂μ
  rcases le_or_gt (1 / 2) |1 - a| with h1 | h1
  · exact (ENNReal.rpow_le_rpow (min_le_left _ _) hexp.le).trans
      (measure_inter_ball_rpow_le_perimeter hn hr hs hΩ h1 fun x hx => by simp [hx.1])
  · have h0 : 1 / 2 ≤ |0 - a| := by
      rw [zero_sub, abs_neg]
      exact le_abs.2 (Or.inl (by linarith [(abs_lt.1 h1).2]))
    refine (ENNReal.rpow_le_rpow (min_le_right _ _) hexp.le).trans ?_
    rw [sdiff_eq_compl_inter]
    exact measure_inter_ball_rpow_le_perimeter hn hr hs hΩ h0 fun x hx =>
      indicator_of_notMem hx.1 _

/-- Rescaled relative isoperimetric bound on closed balls: in dimension `n ≥ 2`, the `(1 - 1 / n)`
power of the smaller closed-ball volume proportion of `s` and `sᶜ` is controlled by
`P(s; ball x r) / r ^ (n - 1)`. -/
theorem min_div_closedBall_rpow_le_mul_perimeter_div (hn : 2 ≤ finrank ℝ E) {s : Set E} {x : E}
    {r : ℝ} (hr : 0 < r) (hs : NullMeasurableSet s (μ.restrict (ball x r))) :
    (min (μ (s ∩ closedBall x r)) (μ (closedBall x r \ s)) / μ (closedBall x r)) ^
        (1 - (finrank ℝ E : ℝ)⁻¹) ≤
      (ENNReal.ofReal (2 ^ (finrank ℝ E + 1) / μ.real (ball 0 1) ^ (finrank ℝ E : ℝ)⁻¹) /
          μ (ball (0 : E) 1) ^ (1 - (finrank ℝ E : ℝ)⁻¹)) *
        (perimeter μ ⟨ball x r, isOpen_ball⟩ s / ENNReal.ofReal r ^ (finrank ℝ E - 1)) := by
  set n := finrank ℝ E with hn_eq
  set q : ℝ := 1 - (n : ℝ)⁻¹
  have hq : 0 < q := sub_pos.2 (inv_lt_one_of_one_lt₀ (by exact_mod_cast hn))
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (zero_lt_two.trans_le hn)
  have hmin : min (μ (s ∩ closedBall x r)) (μ (closedBall x r \ s)) ^ q ≤
      ENNReal.ofReal (2 ^ (n + 1) / μ.real (ball 0 1) ^ (n : ℝ)⁻¹) *
        perimeter μ ⟨ball x r, isOpen_ball⟩ s := by
    rw [measure_congr (EventuallyEqSet.inter .rfl (μ.addHaar_closedBall_ae_eq_ball x r)),
      measure_congr (EventuallyEqSet.diff (μ.addHaar_closedBall_ae_eq_ball x r) .rfl)]
    exact min_measure_inter_measure_sdiff_rpow_le_perimeter hn hs
      (Ω := ⟨ball x r, isOpen_ball⟩) subset_rfl
  have hexp : (n : ℝ) * q = ((n - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (one_le_two.trans hn), Nat.cast_one, mul_sub, mul_one,
      mul_inv_cancel₀ (by positivity)]
  have hrpow : ENNReal.ofReal (r ^ n) ^ q = ENNReal.ofReal r ^ (n - 1) := by
    rw [ENNReal.ofReal_rpow_of_pos (pow_pos hr n), ← Real.rpow_natCast r n,
      ← Real.rpow_mul hr.le, hexp, Real.rpow_natCast, ENNReal.ofReal_pow hr.le]
  have hden : μ (closedBall x r) ^ q =
      ENNReal.ofReal r ^ (n - 1) * μ (ball (0 : E) 1) ^ q := by
    rw [Measure.addHaar_closedBall μ x hr.le, ← hn_eq, ENNReal.mul_rpow_of_nonneg _ _ hq.le, hrpow]
  have hωqt : μ (ball (0 : E) 1) ^ q ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg hq.le measure_ball_lt_top.ne
  rw [ENNReal.div_rpow_of_nonneg _ _ hq.le, hden]
  refine (ENNReal.div_le_div_right hmin _).trans_eq ?_
  simp only [div_eq_mul_inv,
    ENNReal.mul_inv (.inr hωqt) (.inl (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))]
  ring

/-- In dimension `n ≥ 2`, if `s` is null-measurable on `Ω`, `x ∈ Ω`, and
`P(s; ball x r) / r ^ (n - 1) → 0` as `r → 0⁺`, then `x ∉ ∂ᵉs`. -/
theorem notMem_essentialBoundary_of_tendsto_perimeter_ball_div (hn : 2 ≤ finrank ℝ E)
    {s : Set E} {x : E} (hs : NullMeasurableSet s (μ.restrict Ω)) (hx : x ∈ Ω)
    (hP : Tendsto (fun r => perimeter μ ⟨ball x r, isOpen_ball⟩ s /
        ENNReal.ofReal r ^ (finrank ℝ E - 1)) (𝓝[>] 0) (𝓝 0)) :
    x ∉ essentialBoundary μ s := by
  set n := finrank ℝ E
  set q : ℝ := 1 - (n : ℝ)⁻¹
  have hq : 0 < q := sub_pos.2 (inv_lt_one_of_one_lt₀ (by exact_mod_cast hn))
  set K := ENNReal.ofReal (2 ^ (n + 1) / μ.real (ball 0 1) ^ (n : ℝ)⁻¹) /
    μ (ball (0 : E) 1) ^ q
  have hKt : K ≠ ∞ := ENNReal.div_ne_top ENNReal.ofReal_ne_top
    (ENNReal.rpow_pos (measure_ball_pos μ 0 one_pos) measure_ball_lt_top.ne).ne'
  set f : ℝ → ℝ≥0∞ := fun r =>
    min (μ (s ∩ closedBall x r)) (μ (closedBall x r \ s)) / μ (closedBall x r)
  obtain ⟨ε, hε, hεΩ⟩ := Metric.mem_nhds_iff.1 (Ω.isOpen.mem_nhds hx)
  have hKP : Tendsto (fun r => K * (perimeter μ ⟨ball x r, isOpen_ball⟩ s /
      ENNReal.ofReal r ^ (n - 1))) (𝓝[>] 0) (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hP (.inr hKt)
  have hfq : Tendsto (fun r => f r ^ q) (𝓝[>] 0) (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hKP
      (.of_forall fun _ => zero_le) (eventually_of_mem (Ioo_mem_nhdsGT hε) fun r hr =>
        min_div_closedBall_rpow_le_mul_perimeter_div hn hr.1
          (hs.mono (Measure.restrict_mono ((ball_subset_ball hr.2.le).trans hεΩ) le_rfl)))
  refine notMem_essentialBoundary_of_tendsto_min_div ?_
  have hf := ((ENNReal.continuous_rpow_const (y := q⁻¹)).tendsto 0).comp hfq
  rw [ENNReal.zero_rpow_of_pos (inv_pos.2 hq)] at hf
  exact hf.congr fun r => by
    dsimp only [Function.comp_apply]
    rw [← ENNReal.rpow_mul, mul_inv_cancel₀ hq.ne', ENNReal.rpow_one]

end TauCeti
