/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.ResolventTransform.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import TauCeti.Analysis.SpecialFunctions.Integrals.Basic
import TauCeti.Basic.Real.Sign
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Arctan
import TauCeti.MeasureTheory.Measure.Interval
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Stieltjes inversion for the resolvent transform

For a finite measure `μ` on the real line, integrating the imaginary part of its resolvent
transform along a horizontal segment and letting the segment approach the real axis recovers the
mass of the corresponding interval, with half weight at the two endpoints:

`π⁻¹ ∫_a^b Im m_μ(x + iη) dx → μ (a, b) + (μ {a} + μ {b}) / 2` as `η → 0⁺`, for `a < b`.

The proof integrates the Poisson kernel in `x` first, which gives a difference of arctangents
(`Real.integral_div_sub_sq_add_sq`), and then applies dominated convergence in the measure
variable, using the limits `Real.tendsto_arctan_div_nhdsGT_zero`. As a consequence a finite measure
on `ℝ` is determined by the imaginary part of its resolvent transform on the upper half-plane.
This uniqueness is what lets limits of resolvent transforms identify limiting spectral laws.

We use Mathlib's `MeasureTheory.resolventTransform`, with sign `(x - z)⁻¹`, not
`(z - x)⁻¹`. No moment assumptions are needed.

## Main declarations

* `MeasureTheory.intervalIntegral_im_resolventTransform`: the integral of the imaginary part of
  the transform along a horizontal segment, as an integral of arctangent differences.
* `MeasureTheory.tendsto_intervalIntegral_im_resolventTransform`: Stieltjes inversion.
* `MeasureTheory.Measure.ext_of_im_resolventTransform` and
  `MeasureTheory.Measure.ext_of_resolventTransform`: a finite measure on `ℝ` is determined by its
  transform on the upper half-plane.

## References

* Anderson, Guionnet and Zeitouni, *An Introduction to Random Matrices*, §2.4.1,
  Theorem 2.4.3.
-/

public section

noncomputable section

open MeasureTheory Filter Complex Set
open scoped Topology Real

namespace MeasureTheory

variable {μ : Measure ℝ} [IsFiniteMeasure μ]

/-- Integrating the imaginary part of the resolvent transform along the horizontal segment from
`a + iη` to `b + iη` gives the integral of a difference of arctangents. For `η = 0` both sides
vanish. -/
theorem intervalIntegral_im_resolventTransform (a b η : ℝ) :
    ∫ x in a..b, (resolventTransform μ (x + η * I)).im =
      ∫ t, (Real.arctan ((b - t) / η) - Real.arctan ((a - t) / η)) ∂μ := by
  rcases eq_or_ne η 0 with rfl | hη
  · simp [im_resolventTransform]
  have hpos (x t : ℝ) : 0 < (t - x) ^ 2 + η ^ 2 := by positivity
  have hz (x : ℝ) : ((x : ℂ) + η * I).re = x ∧ ((x : ℂ) + η * I).im = η := by simp
  simp only [im_resolventTransform, (hz _).1, (hz _).2]
  rw [intervalIntegral_integral_swap]
  · simp_rw [Real.integral_div_sub_sq_add_sq]
  -- The kernel is continuous and bounded by `|η|⁻¹` on a finite product measure.
  have : IsFiniteMeasure (volume.restrict (uIoc a b)) := isFiniteMeasure_restrict.2
    (ne_top_of_le_ne_top isCompact_uIcc.measure_lt_top.ne (measure_mono uIoc_subset_uIcc))
  refine Integrable.of_bound (Continuous.aestronglyMeasurable ?_) |η|⁻¹ (ae_of_all _ ?_)
  · exact continuous_const.div (by fun_prop) fun p => (hpos p.1 p.2).ne'
  · rintro ⟨x, t⟩
    rw [Function.uncurry_apply_pair, Real.norm_eq_abs, abs_div, abs_of_pos (hpos x t)]
    calc |η| / ((t - x) ^ 2 + η ^ 2) ≤ |η| / η ^ 2 :=
          div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) (by nlinarith)
      _ = |η|⁻¹ := by rw [← sq_abs]; field_simp

/-- **Stieltjes inversion.** For a finite measure `μ` on `ℝ` and `a < b`,
`π⁻¹ ∫_a^b Im m_μ(x + iη) dx` tends to `μ (a, b) + (μ {a} + μ {b}) / 2` as `η → 0⁺`. -/
theorem tendsto_intervalIntegral_im_resolventTransform {a b : ℝ} (hab : a < b) :
    Tendsto (fun η : ℝ => π⁻¹ * ∫ x in a..b, (resolventTransform μ (x + η * I)).im) (𝓝[>] 0)
      (𝓝 (μ.real (Ioo a b) + (μ.real {a} + μ.real {b}) / 2)) := by
  have hlim : ∫ t, (Real.sign (b - t) - Real.sign (a - t)) / 2 ∂μ =
      μ.real (Ioo a b) + (μ.real {a} + μ.real {b}) / 2 := by
    simp_rw [Real.sign_sub_sub_sign_sub_div_two hab]
    have hi (s : Set ℝ) (hs : MeasurableSet s) : Integrable (s.indicator (1 : ℝ → ℝ)) μ :=
      (integrable_const 1).indicator hs
    have ha := hi _ (measurableSet_singleton a)
    have hb := hi _ (measurableSet_singleton b)
    rw [integral_add (hi _ measurableSet_Ioo) ?_, integral_div, integral_add ha hb,
      integral_indicator_one measurableSet_Ioo, integral_indicator_one (measurableSet_singleton a),
      integral_indicator_one (measurableSet_singleton b)]
    exact (ha.add hb).div_const 2
  rw [← hlim]
  have heq : (fun η : ℝ => ∫ t, π⁻¹ * (Real.arctan ((b - t) / η) - Real.arctan ((a - t) / η)) ∂μ)
      =ᶠ[𝓝[>] 0] fun η => π⁻¹ * ∫ x in a..b, (resolventTransform μ (x + η * I)).im := by
    filter_upwards [self_mem_nhdsWithin] with η hη
    rw [intervalIntegral_im_resolventTransform a b η, integral_const_mul]
  refine Tendsto.congr' heq
    (tendsto_integral_filter_of_dominated_convergence (fun _ => 1) ?_ ?_ (integrable_const 1) ?_)
  · exact Eventually.of_forall fun η => (Continuous.aestronglyMeasurable (by fun_prop))
  · -- Each kernel lies in `[0, 1]` up to sign, since arctangents lie in `(-π / 2, π / 2)`.
    refine Eventually.of_forall fun η => ae_of_all _ fun t => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos Real.pi_pos, inv_mul_le_iff₀ Real.pi_pos,
      mul_one, abs_le]
    constructor <;> linarith [Real.arctan_lt_pi_div_two ((b - t) / η),
      Real.neg_pi_div_two_lt_arctan ((b - t) / η), Real.arctan_lt_pi_div_two ((a - t) / η),
      Real.neg_pi_div_two_lt_arctan ((a - t) / η)]
  · refine ae_of_all _ fun t => ?_
    convert ((Real.tendsto_arctan_div_nhdsGT_zero (b - t)).sub
      (Real.tendsto_arctan_div_nhdsGT_zero (a - t))).const_mul π⁻¹ using 2
    field_simp

namespace Measure

/-- A finite measure on `ℝ` is determined by the imaginary part of its resolvent transform on
the upper half-plane. -/
theorem ext_of_im_resolventTransform {ν : Measure ℝ} [IsFiniteMeasure ν]
    (h : ∀ z : ℂ, 0 < z.im → (resolventTransform μ z).im = (resolventTransform ν z).im) :
    μ = ν := by
  -- By Stieltjes inversion, `μ (a, b) + μ [a, b]` and `ν (a, b) + ν [a, b]` agree for `a < b`.
  have hIcc (ρ : Measure ℝ) [IsFiniteMeasure ρ] {a b : ℝ} (hab : a < b) :
      ρ.real (Icc a b) = ρ.real (Ioo a b) + ρ.real {a} + ρ.real {b} := by
    rw [← Ico_union_right hab.le, ← Ioo_union_left hab,
      measureReal_union (by simp [hab.ne']) (measurableSet_singleton b),
      measureReal_union (by simp) (measurableSet_singleton a)]
  have hint {a b : ℝ} (hab : a < b) :
      μ.real (Ioo a b) + μ.real (Icc a b) = ν.real (Ioo a b) + ν.real (Icc a b) := by
    have heq : (fun η : ℝ => π⁻¹ * ∫ x in a..b, (resolventTransform ν (x + η * I)).im)
        =ᶠ[𝓝[>] 0] fun η => π⁻¹ * ∫ x in a..b, (resolventTransform μ (x + η * I)).im := by
      filter_upwards [self_mem_nhdsWithin] with η hη
      congr 1
      exact intervalIntegral.integral_congr fun x _ => (h _ (by simpa using hη)).symm
    have := tendsto_nhds_unique (tendsto_intervalIntegral_im_resolventTransform (μ := μ) hab)
      ((tendsto_intervalIntegral_im_resolventTransform (μ := ν) hab).congr' heq)
    rw [hIcc μ hab, hIcc ν hab]
    linarith
  -- Letting `a → -∞` and then `b → y⁺` identifies the distribution functions.
  have hreal (ρ : Measure ℝ) [IsFiniteMeasure ρ] {l : Filter ℝ} {s : ℝ → Set ℝ} {t : Set ℝ}
      (hs : Tendsto (fun x => ρ (s x)) l (𝓝 (ρ t))) :
      Tendsto (fun x => ρ.real (s x)) l (𝓝 (ρ.real t)) :=
    (ENNReal.tendsto_toReal (measure_ne_top ρ _)).comp hs
  have hbot (ρ : Measure ℝ) [IsFiniteMeasure ρ] (b : ℝ) :
      Tendsto (fun a => ρ.real (Ioo a b) + ρ.real (Icc a b)) atBot
        (𝓝 (ρ.real (Iio b) + ρ.real (Iic b))) :=
    (hreal ρ (tendsto_measure_Ioo_atBot ρ b)).add (hreal ρ (tendsto_measure_Icc_atBot ρ b))
  have hhalf (b : ℝ) : μ.real (Iio b) + μ.real (Iic b) = ν.real (Iio b) + ν.real (Iic b) :=
    tendsto_nhds_unique (hbot μ b)
      ((hbot ν b).congr' ((eventually_lt_atBot b).mono fun _ hab => (hint hab).symm))
  have hright (ρ : Measure ℝ) [IsFiniteMeasure ρ] (y : ℝ) :
      Tendsto (fun b => ρ.real (Iio b) + ρ.real (Iic b)) (𝓝[>] y)
        (𝓝 (ρ.real (Iic y) + ρ.real (Iic y))) :=
    (hreal ρ (tendsto_measure_Iio_nhdsGT ⟨y + 1, by linarith, measure_ne_top ρ _⟩)).add
      (hreal ρ (tendsto_measure_Iic_nhdsGT ⟨y + 1, by linarith, measure_ne_top ρ _⟩))
  refine ext_of_Iic μ ν fun y => ?_
  have := tendsto_nhds_unique (hright μ y) ((hright ν y).congr fun b => (hhalf b).symm)
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ _) (measure_ne_top ν _)).1
    (by simp only [← measureReal_def]; linarith)

/-- A finite measure on `ℝ` is determined by its resolvent transform on the upper half-plane. -/
theorem ext_of_resolventTransform {ν : Measure ℝ} [IsFiniteMeasure ν]
    (h : ∀ z : ℂ, 0 < z.im → resolventTransform μ z = resolventTransform ν z) : μ = ν :=
  ext_of_im_resolventTransform fun z hz => congrArg Complex.im (h z hz)

end Measure

end MeasureTheory
