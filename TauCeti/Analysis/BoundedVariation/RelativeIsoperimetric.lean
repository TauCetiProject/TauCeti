/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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
* `TauCeti.exists_min_div_closedBall_rpow_le_mul_perimeter_div`: the normalized closed-ball form
  in terms of `P(s; ball x r) / r ^ (n - 1)`.

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

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private lemma one_sub_inv_finrank_pos (hn : 2 ≤ finrank ℝ E) :
    0 < 1 - (finrank ℝ E : ℝ)⁻¹ :=
  sub_pos.2 (inv_lt_one_of_one_lt₀ (by exact_mod_cast hn))

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
  have hexp : 0 < 1 - (finrank ℝ E : ℝ)⁻¹ := one_sub_inv_finrank_pos hn
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

private noncomputable def normalizedRelativeIsoperimetricConst
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] (μ : Measure E) : ℝ≥0∞ :=
  ENNReal.ofReal (2 ^ (finrank ℝ E + 1) / μ.real (ball 0 1) ^ (finrank ℝ E : ℝ)⁻¹) /
    μ (ball (0 : E) 1) ^ (1 - (finrank ℝ E : ℝ)⁻¹)

omit [BorelSpace E] in
private theorem normalizedRelativeIsoperimetricConst_ne_top :
    normalizedRelativeIsoperimetricConst μ ≠ ∞ :=
  ENNReal.div_ne_top ENNReal.ofReal_ne_top
    (ENNReal.rpow_pos (measure_ball_pos μ 0 one_pos) measure_ball_lt_top.ne).ne'

/-- Rescaled relative isoperimetric bound on closed balls: in dimension `n ≥ 2`, there is a finite
constant `C` depending only on `μ` such that the `(1 - 1 / n)` power of the smaller closed-ball
volume proportion of `s` and `sᶜ` is at most `C * (P(s; ball x r) / r ^ (n - 1))`. -/
theorem exists_min_div_closedBall_rpow_le_mul_perimeter_div (hn : 2 ≤ finrank ℝ E)
    (μ : Measure E) [μ.IsAddHaarMeasure] :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ {s : Set E} {x : E} {r : ℝ}, 0 < r →
      NullMeasurableSet s (μ.restrict (ball x r)) →
      (min (μ (s ∩ closedBall x r)) (μ (closedBall x r \ s)) / μ (closedBall x r)) ^
          (1 - (finrank ℝ E : ℝ)⁻¹) ≤
        C * (perimeter μ ⟨ball x r, isOpen_ball⟩ s / ENNReal.ofReal r ^ (finrank ℝ E - 1)) := by
  refine ⟨normalizedRelativeIsoperimetricConst μ, normalizedRelativeIsoperimetricConst_ne_top,
    fun {s x r} hr hs => ?_⟩
  set n := finrank ℝ E with hn_eq
  set q : ℝ := 1 - (n : ℝ)⁻¹
  have hq : 0 < q := one_sub_inv_finrank_pos hn
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (zero_lt_two.trans_le hn)
  have hmin : min (μ (s ∩ closedBall x r)) (μ (closedBall x r \ s)) ^ q ≤
      ENNReal.ofReal (2 ^ (n + 1) / μ.real (ball 0 1) ^ (n : ℝ)⁻¹) *
        perimeter μ ⟨ball x r, isOpen_ball⟩ s := by
    rw [measure_congr (EventuallyEqSet.inter .rfl (μ.addHaar_closedBall_ae_eq_ball x r)),
      measure_congr (EventuallyEqSet.diff (μ.addHaar_closedBall_ae_eq_ball x r) .rfl)]
    exact min_measure_inter_measure_sdiff_rpow_le_perimeter hn hs
      (Ω := ⟨ball x r, isOpen_ball⟩) subset_rfl
  have hexp : (n : ℝ) * q = ((n - 1 : ℕ) : ℝ) := by
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (zero_lt_two.trans_le hn).ne'
    rw [Nat.cast_sub (one_le_two.trans hn), Nat.cast_one]
    dsimp only [q]
    field_simp
  have hrpow_real : (r ^ n) ^ q = r ^ (n - 1) := by
    calc (r ^ n) ^ q = (r ^ (n : ℝ)) ^ q := by rw [Real.rpow_natCast]
      _ = r ^ ((n : ℝ) * q) := (Real.rpow_mul hr.le _ _).symm
      _ = r ^ ((n - 1 : ℕ) : ℝ) := by rw [hexp]
      _ = r ^ (n - 1) := Real.rpow_natCast r (n - 1)
  have hrpow : ENNReal.ofReal (r ^ n) ^ q = ENNReal.ofReal r ^ (n - 1) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (pow_nonneg hr.le n) hq.le, hrpow_real,
      ENNReal.ofReal_pow hr.le]
  have hden : μ (closedBall x r) ^ q =
      ENNReal.ofReal r ^ (n - 1) * μ (ball (0 : E) 1) ^ q := by
    rw [Measure.addHaar_closedBall μ x hr.le, ← hn_eq, ENNReal.mul_rpow_of_nonneg _ _ hq.le, hrpow]
  have hωqt : μ (ball (0 : E) 1) ^ q ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg hq.le measure_ball_lt_top.ne
  rw [ENNReal.div_rpow_of_nonneg _ _ hq.le, hden]
  refine (ENNReal.div_le_div_right hmin _).trans_eq ?_
  simp only [normalizedRelativeIsoperimetricConst, div_eq_mul_inv,
    ENNReal.mul_inv (.inr hωqt) (.inl (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))]
  ring

end TauCeti
