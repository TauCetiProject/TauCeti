/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Average
public import TauCeti.Analysis.BoundedVariation.Perimeter
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

## References

* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, Remark 3.50.
* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §5.6.2.
* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Proposition 12.37.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Metric Module Set TopologicalSpace
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E}

/-- On the part `t ∩ B` of a ball `B ⊆ Ω` where the indicator of `s` takes a value `b` at distance
at least `1/2` from its mean over `B`, the localized Poincaré–Wirtinger inequality gives
`μ(t ∩ B) ^ (1 - 1/n) ≤ 2 ^ (n + 1) ω ^ (-1/n) P(s; Ω)`. -/
private theorem measure_inter_ball_rpow_le_perimeter (hn : 2 ≤ finrank ℝ E) {s t : Set E} {c : E}
    {r : ℝ} (hr : 0 < r) (hs : NullMeasurableSet s (μ.restrict (ball c r))) (hΩ : ball c r ⊆ Ω)
    (ht : NullMeasurableSet t (μ.restrict (ball c r))) {b : ℝ}
    (hb : 1 / 2 ≤ |b - ⨍ y in ball c r, s.indicator 1 y ∂μ|)
    (htb : ∀ x ∈ t, s.indicator 1 x = b) :
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
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_inv_of_pos two_pos,
      ← one_div]
    exact ENNReal.ofReal_le_ofReal hb
  have hlow : 2⁻¹ * μ (t ∩ B) ≤ ∫⁻ x in t ∩ B, ‖u x - a‖ₑ ∂μ := by
    rw [← Measure.restrict_restrict₀ ht, ← Measure.restrict_apply₀ ht, ← setLIntegral_const]
    exact lintegral_mono_ae ((ae_restrict_mem₀ ht).mono fun x hx => by rw [htb x hx]; exact hb')
  have hup := setLIntegral_enorm_sub_setAverage_le_mul_measure_rpow_mul_totalVariationOn_of_convex
    (Ω := ⟨B, isOpen_ball⟩) (convex_ball c r) isBounded_ball hu subset_rfl
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
      (measure_inter_ball_rpow_le_perimeter hn hr hs hΩ hs h1 fun x hx => by simp [hx])
  · have h0 : 1 / 2 ≤ |0 - a| := by
      rw [zero_sub, abs_neg]
      exact le_abs.2 (Or.inl (by linarith [(abs_lt.1 h1).2]))
    refine (ENNReal.rpow_le_rpow (min_le_right _ _) hexp.le).trans ?_
    rw [sdiff_eq_compl_inter]
    exact measure_inter_ball_rpow_le_perimeter hn hr hs hΩ hs.compl h0 fun x hx =>
      indicator_of_notMem hx _

end TauCeti
