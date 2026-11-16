/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Function.L2Space
import TauCeti.Analysis.SpecificLimits.Absorption
import TauCeti.MeasureTheory.Integral.Bochner.Basic

/-!
# Local bounds in `Lᵖ` from local bounds in `L²`

Let `w ≥ 0` be square integrable on a ball `B(x₀, R)` in a proper metric space, and suppose
that on every ball `B(y, s) ⊆ B(x₀, R)` the supremum of `w` on the half ball is controlled by its
`L²` norm:

`w ≤ D s^e ‖w‖_{L²(B(y, s))}` almost everywhere on `B(y, s/2)`.

This file shows that the `L²` norm on the right can then be replaced by any `Lᵖ` norm with
`0 < p ≤ 2`, at the cost of the exponent `e` becoming `2e/p`:

`w ≤ C R^{2e/p} ‖w‖_{Lᵖ(B(x₀, R))}` almost everywhere on `B(x₀, R/2)`.

This is how local boundedness of subsolutions, proved by De Giorgi's or Moser's iteration with
the `L²` norm on the right, is upgraded to the small exponents that Moser's proof of the Harnack
inequality needs.

Writing `F(r)` for the essential supremum of `w` on `B(x₀, r)`, the `L²` bound on concentric
balls `r < ρ` and the interpolation `‖w‖²_{L²} ≤ F(ρ)^{2-p} ‖w‖ᵖ_{Lᵖ}` give
`F(r) ≤ F(ρ)/2 + C (ρ - r)^{2e/p} ‖w‖_{Lᵖ}`, and the absorption lemma
`TauCeti.exists_le_mul_mul_rpow_add_of_le_mul_add` removes the term `F(ρ)/2`.

## Main declarations

* `TauCeti.exists_ae_le_mul_rpow_mul_setIntegral_rpow_of_forall_ball`: local `L²` bounds for
  the supremum on half balls imply the same bounds with any `Lᵖ` norm, `0 < p ≤ 2`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  the proof of Theorem 8.17.
* Q. Han, F. Lin, *Elliptic Partial Differential Equations*, Chapter 4.
-/

public section

noncomputable section

open Filter MeasureTheory Set TopologicalSpace
open scoped Topology

namespace TauCeti

variable {X : Type*} [PseudoMetricSpace X] [ProperSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] {mu : Measure X}

/-- **From half balls to concentric balls.** Suppose that on every ball `B(y, s) ⊆ B(x₀, R)`,
`w ≤ D s^e ‖w‖_{L²(B(y, s))}` almost everywhere on `B(y, s/2)`. Then for `r < ρ ≤ R`,
`w ≤ D (ρ - r)^e ‖w‖_{L²(B(x₀, ρ))}` almost everywhere on `B(x₀, r)`: the ball `B(x₀, r)` is
covered by the half balls `B(y, (ρ - r)/2)` with `y ∈ B(x₀, r)`. -/
private theorem ae_le_mul_sub_rpow_mul_sqrt_setIntegral {w : X → ℝ}
    {x₀ : X} {R D e : ℝ} (hD : 0 ≤ D)
    (hint : IntegrableOn (fun x => w x ^ 2) (Metric.ball x₀ R) mu)
    (H : ∀ y s, 0 < s → Metric.ball y s ⊆ Metric.ball x₀ R →
      ∀ᵐ x ∂mu.restrict (Metric.ball y (s / 2)),
        w x ≤ D * s ^ e * √(∫ x in Metric.ball y s, w x ^ 2 ∂mu))
    {r ρ : ℝ} (hrρ : r < ρ) (hρR : ρ ≤ R) :
    ∀ᵐ x ∂mu.restrict (Metric.ball x₀ r),
      w x ≤ D * (ρ - r) ^ e * √(∫ x in Metric.ball x₀ ρ, w x ^ 2 ∂mu) := by
  rw [ae_restrict_iff' measurableSet_ball, ae_iff]
  refine measure_null_of_locally_null _ fun y hy => ?_
  obtain ⟨hyr, -⟩ := not_imp.1 hy
  -- The ball of radius `ρ - r` about `y` lies in `B(x₀, ρ)`.
  have hsub : Metric.ball y (ρ - r) ⊆ Metric.ball x₀ ρ :=
    Metric.ball_subset_ball' (by linarith [Metric.mem_ball.1 hyr])
  have hy := H y (ρ - r) (sub_pos.2 hrρ) (hsub.trans (Metric.ball_subset_ball hρR))
  rw [ae_restrict_iff' measurableSet_ball, ae_iff] at hy
  refine ⟨_, inter_mem_nhdsWithin _ (Metric.ball_mem_nhds y (by linarith : 0 < (ρ - r) / 2)),
    measure_mono_null (fun x hx => ?_) hy⟩
  obtain ⟨_, hxw⟩ := not_imp.1 hx.1
  refine not_imp.2 ⟨hx.2, fun hle => hxw (hle.trans ?_)⟩
  -- The `L²` norm over the smaller ball is at most that over `B(x₀, ρ)`.
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (setIntegral_mono_set
    (hint.mono_set (Metric.ball_subset_ball hρR)) (Eventually.of_forall fun x => sq_nonneg (w x))
    hsub.eventuallySubset)) (mul_nonneg hD (Real.rpow_nonneg (sub_pos.2 hrρ).le e))

/-- In the setting of `ae_le_mul_sub_rpow_mul_sqrt_setIntegral`, for `w ≥ 0` and `r < ρ ≤ R`,
the essential supremum of `w` on `B(x₀, r)` is a real number at most
`D (ρ - r)^e ‖w‖_{L²(B(x₀, ρ))}`, and it bounds `w` almost everywhere on `B(x₀, r)`. -/
private theorem toReal_eLpNormEssSup_le_and_ae_le {w : X → ℝ}
    {x₀ : X} {R D e : ℝ} (hD : 0 ≤ D) (hw0 : ∀ x, 0 ≤ w x)
    (hint : IntegrableOn (fun x => w x ^ 2) (Metric.ball x₀ R) mu)
    (H : ∀ y s, 0 < s → Metric.ball y s ⊆ Metric.ball x₀ R →
      ∀ᵐ x ∂mu.restrict (Metric.ball y (s / 2)),
        w x ≤ D * s ^ e * √(∫ x in Metric.ball y s, w x ^ 2 ∂mu))
    {r ρ : ℝ} (hrρ : r < ρ) (hρR : ρ ≤ R) :
    (eLpNormEssSup w (mu.restrict (Metric.ball x₀ r))).toReal ≤
        D * (ρ - r) ^ e * √(∫ x in Metric.ball x₀ ρ, w x ^ 2 ∂mu) ∧
      ∀ᵐ x ∂mu.restrict (Metric.ball x₀ r),
        w x ≤ (eLpNormEssSup w (mu.restrict (Metric.ball x₀ r))).toReal := by
  have hb : 0 ≤ D * (ρ - r) ^ e * √(∫ x in Metric.ball x₀ ρ, w x ^ 2 ∂mu) :=
    mul_nonneg (mul_nonneg hD (Real.rpow_nonneg (sub_pos.2 hrρ).le e)) (Real.sqrt_nonneg _)
  have h1 : eLpNormEssSup w (mu.restrict (Metric.ball x₀ r)) ≤
      ENNReal.ofReal (D * (ρ - r) ^ e * √(∫ x in Metric.ball x₀ ρ, w x ^ 2 ∂mu)) :=
    eLpNormEssSup_le_of_ae_bound ((ae_le_mul_sub_rpow_mul_sqrt_setIntegral hD hint H hrρ
      hρR).mono fun x hx => by rwa [Real.norm_of_nonneg (hw0 x)])
  refine ⟨ENNReal.toReal_le_of_le_ofReal hb h1, ?_⟩
  filter_upwards [ae_le_eLpNormEssSup (f := w) (μ := mu.restrict (Metric.ball x₀ r))] with x hx
  calc w x = ‖w x‖ₑ.toReal := by rw [toReal_eNorm, Real.norm_of_nonneg (hw0 x)]
    _ ≤ _ := ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1) hx

/-- **The absorption step.** In the setting of `ae_le_mul_sub_rpow_mul_sqrt_setIntegral`, let
`F r` be the essential supremum of `w ≥ 0` on `B(x₀, r)` and `J = ∫_{B(x₀, R)} wᵖ` with
`0 < p ≤ 2`. Interpolating `‖w‖²_{L²} ≤ F^{2-p} J` and splitting the product with the weighted
arithmetic-geometric mean inequality gives, for `r < ρ < R`,

`F r ≤ F ρ / 2 + (2^{1-p/2} D √J)^{2/p} (ρ - r)^{2e/p}`. -/
private theorem toReal_eLpNormEssSup_le_half_add {w : X → ℝ}
    {x₀ : X} {R D e p : ℝ} (hD : 0 ≤ D) (hp : 0 < p) (hp2 : p ≤ 2)
    (hw0 : ∀ x, 0 ≤ w x) (hint : IntegrableOn (fun x => w x ^ 2) (Metric.ball x₀ R) mu)
    (hintp : IntegrableOn (fun x => w x ^ p) (Metric.ball x₀ R) mu)
    (H : ∀ y s, 0 < s → Metric.ball y s ⊆ Metric.ball x₀ R →
      ∀ᵐ x ∂mu.restrict (Metric.ball y (s / 2)),
        w x ≤ D * s ^ e * √(∫ x in Metric.ball y s, w x ^ 2 ∂mu))
    {r ρ : ℝ} (hrρ : r < ρ) (hρR : ρ < R) :
    (eLpNormEssSup w (mu.restrict (Metric.ball x₀ r))).toReal ≤
      1 / 2 * (eLpNormEssSup w (mu.restrict (Metric.ball x₀ ρ))).toReal +
        (2 ^ (1 - p / 2) * D * √(∫ x in Metric.ball x₀ R, w x ^ p ∂mu)) ^ (2 / p) *
          (ρ - r) ^ (2 * e / p) := by
  set F := (eLpNormEssSup w (mu.restrict (Metric.ball x₀ ρ))).toReal
  set J := ∫ x in Metric.ball x₀ R, w x ^ p ∂mu
  have hF : 0 ≤ F := ENNReal.toReal_nonneg
  have _hJ : 0 ≤ J := integral_nonneg fun x => Real.rpow_nonneg (hw0 x) p
  -- `w ≤ F` almost everywhere on `B(x₀, ρ)`, since `w` is bounded there.
  have hρr : 0 < ρ - r := sub_pos.2 hrρ
  have hwF : ∀ᵐ x ∂mu.restrict (Metric.ball x₀ ρ), w x ≤ F :=
    (toReal_eLpNormEssSup_le_and_ae_le hD hw0 hint H hρR le_rfl).2
  -- Interpolation: `∫_{B(x₀, ρ)} w² ≤ F^{2-p} J`.
  have hI : ∫ x in Metric.ball x₀ ρ, w x ^ 2 ∂mu ≤ F ^ (2 - p) * J :=
    by simpa only [Real.rpow_two] using
      MeasureTheory.setIntegral_rpow_le_rpow_mul_setIntegral_rpow hF
        (Metric.ball_subset_ball hρR.le) hp2 two_ne_zero (Eventually.of_forall hw0) hintp hwF
  have hsqrt : √(F ^ (2 - p) * J) = F ^ (1 - p / 2) * √J := by
    rw [Real.sqrt_mul (Real.rpow_nonneg hF _), Real.sqrt_eq_rpow (F ^ (2 - p)),
      ← Real.rpow_mul hF]
    ring_nf
  -- The bound on `B(x₀, r)` in terms of the `L²` norm on `B(x₀, ρ)`.
  set Y₀ := 2 ^ (1 - p / 2) * D * √J
  set Z := Y₀ * (ρ - r) ^ e
  have hZ : 0 ≤ Z := mul_nonneg (by positivity) (Real.rpow_nonneg hρr.le e)
  have _h2 : (0 : ℝ) < 2 ^ (1 - p / 2) := by positivity
  have hb : D * (ρ - r) ^ e * √(∫ x in Metric.ball x₀ ρ, w x ^ 2 ∂mu) ≤
      (F / 2) ^ (1 - p / 2) * (Z ^ (2 / p)) ^ (p / 2) := by
    rw [← Real.rpow_mul hZ, div_mul_div_cancel₀ hp.ne', div_self two_ne_zero, Real.rpow_one,
      Real.div_rpow hF zero_le_two]
    calc D * (ρ - r) ^ e * √(∫ x in Metric.ball x₀ ρ, w x ^ 2 ∂mu)
        ≤ D * (ρ - r) ^ e * (F ^ (1 - p / 2) * √J) := by
          rw [← hsqrt]
          gcongr
      _ = F ^ (1 - p / 2) / 2 ^ (1 - p / 2) * Z := by
          simp only [Z, Y₀]
          field_simp
  refine (toReal_eLpNormEssSup_le_and_ae_le hD hw0 hint H hrρ hρR.le).1.trans (hb.trans ?_)
  -- The weighted arithmetic-geometric mean inequality with weights `1 - p/2` and `p/2`.
  have hY : 0 ≤ Z ^ (2 / p) := Real.rpow_nonneg hZ _
  have hamgm := Real.geom_mean_le_arith_mean2_weighted (by linarith : 0 ≤ 1 - p / 2)
    (by positivity : 0 ≤ p / 2) (by positivity : 0 ≤ F / 2) hY (by ring)
  have hZY : Z ^ (2 / p) = Y₀ ^ (2 / p) * (ρ - r) ^ (2 * e / p) := by
    rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hρr.le _), ← Real.rpow_mul hρr.le]
    ring_nf
  rw [← hZY]
  nlinarith

omit [OpensMeasurableSpace X] in
/-- **A positive power of the radius forces vanishing.** If `w ≥ 0` is `L²` on `B(x₀, R)` and
`w ≤ D s^e ‖w‖_{L²(B(y, s))}` a.e. on `B(y, s/2)` for all `B(y, s) ⊆ B(x₀, R)`, `0 < e`, then
`w = 0` a.e. on `B(x₀, R/2)`. -/
private theorem ae_eq_zero_of_forall_ball_le_mul_rpow {e : ℝ} (he : 0 < e) (D : ℝ)
    {w : X → ℝ} {x₀ : X} {R : ℝ}
    (hw0 : ∀ x, 0 ≤ w x) (hint : IntegrableOn (fun x => w x ^ 2) (Metric.ball x₀ R) mu)
    (H : ∀ y s, 0 < s → Metric.ball y s ⊆ Metric.ball x₀ R →
      ∀ᵐ x ∂mu.restrict (Metric.ball y (s / 2)),
        w x ≤ D * s ^ e * √(∫ x in Metric.ball y s, w x ^ 2 ∂mu)) :
    ∀ᵐ x ∂mu.restrict (Metric.ball x₀ (R / 2)), w x = 0 := by
  rcases le_or_gt R 0 with hR | hR
  · simp [Metric.ball_eq_empty.2 (by linarith : R / 2 ≤ 0)]
  set L := √(∫ x in Metric.ball x₀ R, w x ^ 2 ∂mu)
  set s : ℕ → ℝ := fun k => R / (2 * ((k : ℝ) + 1))
  have hs0 : ∀ k, 0 < s k := fun k => by positivity
  have hsR : ∀ k, s k ≤ R / 2 := fun k =>
    div_le_div_of_nonneg_left hR.le two_pos (by linarith [Nat.cast_nonneg (α := ℝ) k])
  have hk (k : ℕ) : ∀ᵐ x ∂mu.restrict (Metric.ball x₀ (R / 2)), w x ≤ max D 0 * s k ^ e * L := by
    obtain ⟨t, hts, htc, hcov⟩ := countable_cover_nhdsWithin
      (s := Metric.ball x₀ (R / 2)) (f := fun y => Metric.ball y (s k / 2))
      fun y _ => nhdsWithin_le_nhds (Metric.ball_mem_nhds y (by linarith [hs0 k]))
    refine ae_restrict_of_ae_restrict_of_subset hcov
      ((ae_restrict_biUnion_iff _ htc _).2 fun y hy => ?_)
    have hsub : Metric.ball y (s k) ⊆ Metric.ball x₀ R := fun z hz => by
      rw [Metric.mem_ball] at hz ⊢
      have := Metric.mem_ball.1 (hts hy)
      linarith [dist_triangle z y x₀, hsR k]
    filter_upwards [H y (s k) (hs0 k) hsub] with x hx
    refine hx.trans ?_
    have hI := Real.sqrt_le_sqrt (setIntegral_mono_set hint
      (Eventually.of_forall fun x => by positivity) (Eventually.of_forall hsub))
    exact mul_le_mul (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg (hs0 k).le _)) hI (Real.sqrt_nonneg _)
      (mul_nonneg (le_max_right _ _) (Real.rpow_nonneg (hs0 k).le _))
  have hs : Tendsto s atTop (𝓝 0) := tendsto_const_nhds.div_atTop
    ((tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop).const_mul_atTop two_pos)
  have hpow : Tendsto (fun k => s k ^ e) atTop (𝓝 0) := by
    simpa [Function.comp_def, Real.zero_rpow he.ne'] using
      (Real.continuousAt_rpow_const 0 e (Or.inr he.le)).tendsto.comp hs
  have htend : Tendsto (fun k => max D 0 * s k ^ e * L) atTop (𝓝 0) := by
    simpa using (hpow.const_mul (max D 0)).mul_const L
  filter_upwards [ae_all_iff.2 hk] with x hx
  exact le_antisymm (ge_of_tendsto' htend hx) (hw0 x)

section L2ToLp

variable [IsFiniteMeasureOnCompacts mu]

/-- **`Lᵖ` local bounds from `L²` local bounds.** Fix `e`, `D` and `0 < p ≤ 2`. There is
`C > 0`, depending only on these, such that the following holds. Let `w ≥ 0` be square
integrable on `B(x₀, R)` and suppose that on every ball `B(y, s) ⊆ B(x₀, R)`,

`w ≤ D s^e ‖w‖_{L²(B(y, s))}` almost everywhere on `B(y, s/2)`.

Then `w ≤ C R^{2e/p} ‖w‖_{Lᵖ(B(x₀, R))}` almost everywhere on `B(x₀, R/2)`.

This is how local boundedness of subsolutions, proved by De Giorgi's or Moser's iteration with
the `L²` norm on the right, is upgraded to every `Lᵖ` norm with `0 < p < 2`: for Lebesgue
measure on `ℝⁿ`, the scaling exponent `e = -n/2` of the `L²` bound becomes `-n/p`. -/
theorem exists_ae_le_mul_rpow_mul_setIntegral_rpow_of_forall_ball (e : ℝ) (D : ℝ)
    {p : ℝ} (hp : 0 < p) (hp2 : p ≤ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ {w : X → ℝ} {x₀ : X} {R : ℝ},
      (∀ x, 0 ≤ w x) → MemLp w 2 (mu.restrict (Metric.ball x₀ R)) →
      (∀ y s, 0 < s → Metric.ball y s ⊆ Metric.ball x₀ R →
        ∀ᵐ x ∂mu.restrict (Metric.ball y (s / 2)),
          w x ≤ D * s ^ e * √(∫ x in Metric.ball y s, w x ^ 2 ∂mu)) →
      ∀ᵐ x ∂mu.restrict (Metric.ball x₀ (R / 2)),
        w x ≤ C * R ^ (2 * e / p) * (∫ x in Metric.ball x₀ R, w x ^ p ∂mu) ^ p⁻¹ := by
  refine (le_or_gt e 0).symm.elim (fun he => ⟨1, one_pos, fun {w x₀ R} hw0 hw2 H => ?_⟩)
    fun he => ?_
  · rcases le_or_gt R 0 with hR | hR
    · simp [Metric.ball_eq_empty.2 (by linarith : R / 2 ≤ 0)]
    filter_upwards [ae_eq_zero_of_forall_ball_le_mul_rpow he D hw0
      hw2.integrable_sq H] with x hx
    exact hx.le.trans (mul_nonneg (by positivity)
      (Real.rpow_nonneg (integral_nonneg fun x => Real.rpow_nonneg (hw0 x) p) _))
  obtain ⟨C₀, hC₀, habs⟩ := exists_le_mul_mul_rpow_add_of_le_mul_add (θ := 1 / 2) (by norm_num)
    (by norm_num) (-(2 * e / p))
  set D' := max D 1
  have hD' : 0 < D' := lt_max_of_lt_right one_pos
  refine ⟨C₀ * (2 ^ (1 - p / 2) * D') ^ (2 / p) / 4 ^ (2 * e / p), by positivity, ?_⟩
  intro w x₀ R hw0 hw2 H
  rcases le_or_gt R 0 with hR | hR
  · simp [Metric.ball_eq_empty.2 (by linarith : R / 2 ≤ 0)]
  have : IsFiniteMeasure (mu.restrict (Metric.ball x₀ R)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hint : IntegrableOn (fun x => w x ^ 2) (Metric.ball x₀ R) mu := hw2.integrable_sq
  have hintp : IntegrableOn (fun x => w x ^ p) (Metric.ball x₀ R) mu := by
    have := (hw2.mono_exponent (p := ENNReal.ofReal p)
      (ENNReal.ofReal_le_of_le_toReal (by simpa using hp2))).integrable_norm_rpow'
    rw [IntegrableOn]
    simpa [ENNReal.toReal_ofReal hp.le, Real.norm_of_nonneg (hw0 _)] using this
  -- Weaken the constant to `D' = max D 1 > 0`.
  have H' : ∀ y s, 0 < s → Metric.ball y s ⊆ Metric.ball x₀ R →
      ∀ᵐ x ∂mu.restrict (Metric.ball y (s / 2)),
        w x ≤ D' * s ^ e * √(∫ x in Metric.ball y s, w x ^ 2 ∂mu) := fun y s hs hsub =>
    (H y s hs hsub).mono fun x hx => hx.trans (by gcongr; exact le_max_left _ _)
  set F : ℝ → ℝ := fun r => (eLpNormEssSup w (mu.restrict (Metric.ball x₀ r))).toReal
  set J := ∫ x in Metric.ball x₀ R, w x ^ p ∂mu
  have hJ : 0 ≤ J := integral_nonneg fun x => Real.rpow_nonneg (hw0 x) p
  -- `F` is bounded on `[R/2, 3R/4]` by the `L²` bound against `B(x₀, R)`.
  have hbdd : BddAbove (F '' Icc (R / 2) (3 * R / 4)) := by
    refine ⟨D' * (R / 4) ^ e * √(∫ x in Metric.ball x₀ R, w x ^ 2 ∂mu), ?_⟩
    rintro _ ⟨ρ, hρ, rfl⟩
    refine (toReal_eLpNormEssSup_le_and_ae_le hD'.le hw0 hint H' (by linarith [hρ.2])
      le_rfl).1.trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith [hρ.2]) he) hD'.le)
      (Real.sqrt_nonneg _)
  have hstep : ∀ s t, R / 2 ≤ s → s < t → t ≤ 3 * R / 4 →
      F s ≤ 1 / 2 * F t + (2 ^ (1 - p / 2) * D' * √J) ^ (2 / p) * (t - s) ^ (-(-(2 * e / p)))
        + 0 := fun s t _ hst ht => by
    rw [neg_neg, add_zero]
    exact toReal_eLpNormEssSup_le_half_add hD'.le hp hp2 hw0 hint hintp H' hst (by linarith)
  have hmain := habs (by linarith) (by positivity) le_rfl hbdd hstep
  -- `w ≤ F (R/2)` almost everywhere on `B(x₀, R/2)`.
  filter_upwards [(toReal_eLpNormEssSup_le_and_ae_le hD'.le hw0 hint H'
    (by linarith : R / 2 < R) le_rfl).2] with x hx
  refine hx.trans (hmain.trans (le_of_eq ?_))
  rw [neg_neg, add_zero, show 3 * R / 4 - R / 2 = R / 4 by ring,
    Real.div_rpow hR.le (by norm_num), Real.mul_rpow (by positivity) (Real.sqrt_nonneg _),
    Real.sqrt_eq_rpow, ← Real.rpow_mul hJ]
  field_simp

end L2ToLp

end TauCeti
