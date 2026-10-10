/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import TauCeti.Analysis.Fourier.ExponentialAbs

/-!
# Laplace transforms of the absolute sine

This file develops the Laplace transform of `|sin|` against an exponential
weight, by periodic decomposition and the geometric series, together with the
elementary periodicity and two-sided integrability facts it needs.

This is a topic split of `ForTauCeti/Analysis/Fourier/HaagerupZsidoKernel.lean`.
The generic absolute-sine trigonometric lemmas `Real.abs_sin_add_nat_mul_pi` and
`Real.abs_sin_abs` live in the `Real` namespace; the generic even-function
integrability lemma `MeasureTheory.integrable_iff_integrableOn_Ioi_of_even`
lives in `ForTauCeti.Analysis.Fourier.ExponentialAbs`.  The remaining
declarations are moved verbatim and remain in the `TauCeti.HaagerupZsido`
namespace.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: authored directly in `ForTauCeti` at Davis--Kahan
  commit `f35ffc0`; it has had no prior home.
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Original authors / copyright: Jon Crall, GPT 5.6 High; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
* Spectra influence: **none** — this module imports only Mathlib and sibling
  `ForTauCeti` staging modules.
-/

public section

namespace Real

/-- Shifting by an integer multiple of `π` preserves the absolute sine. -/
theorem abs_sin_add_nat_mul_pi (s : ℝ) (n : ℕ) :
    |Real.sin (s + n * Real.pi)| = |Real.sin s| := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep : s + ((n + 1 : ℕ) : ℝ) * Real.pi =
          (s + (n : ℝ) * Real.pi) + Real.pi := by
        push_cast
        ring
      rw [hstep, Real.sin_add_pi, abs_neg, ih]

/-- The absolute sine is invariant under absolute value of the argument. -/
theorem abs_sin_abs (t : ℝ) : |Real.sin (|t|)| = |Real.sin t| := by
  rcases abs_cases t with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]
  · rw [h, Real.sin_neg, abs_neg]

end Real

namespace TauCeti
namespace HaagerupZsido

open MeasureTheory Set Filter Asymptotics
open scoped BigOperators FourierTransform

noncomputable section

/-- One-period Laplace--sine integral, from the elementary antiderivative
`-(exp (-y*t) * (y * sin t + cos t)) / (1 + y ^ 2)`. -/
private theorem integral_zero_pi_sin_mul_exp_neg (y : ℝ) :
    (∫ t in (0 : ℝ)..Real.pi, Real.sin t * Real.exp (-y * t)) =
      (1 + Real.exp (-Real.pi * y)) / (1 + y ^ 2) := by
  have hden : (1 : ℝ) + y ^ 2 ≠ 0 := by positivity
  let F : ℝ → ℝ := fun t =>
    -(Real.exp (-y * t) * (y * Real.sin t + Real.cos t)) / (1 + y ^ 2)
  have hFd (t : ℝ) : HasDerivAt F (Real.sin t * Real.exp (-y * t)) t := by
    have hlin : HasDerivAt (fun t : ℝ => -y * t) (-y) t := by
      simpa using (hasDerivAt_id t).const_mul (-y)
    have hexp := hlin.exp
    have htrig : HasDerivAt (fun t : ℝ => y * Real.sin t + Real.cos t)
        (y * Real.cos t + -Real.sin t) t :=
      ((Real.hasDerivAt_sin t).const_mul y).add (Real.hasDerivAt_cos t)
    have hprod := hexp.mul htrig
    have hval : Real.sin t * Real.exp (-y * t) =
        -(Real.exp (-y * t) * -y * (y * Real.sin t + Real.cos t) +
          Real.exp (-y * t) * (y * Real.cos t + -Real.sin t)) / (1 + y ^ 2) := by
      rw [eq_div_iff hden]
      ring
    rw [hval]
    exact (hprod.neg).div_const (1 + y ^ 2)
  have hint : IntervalIntegrable (fun t => Real.sin t * Real.exp (-y * t))
      MeasureTheory.volume 0 Real.pi :=
    (by fun_prop : Continuous fun t : ℝ =>
      Real.sin t * Real.exp (-y * t)).intervalIntegrable 0 Real.pi
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hFd t) hint]
  simp only [F, Real.sin_pi, Real.cos_pi, Real.sin_zero, Real.cos_zero,
    mul_zero, mul_one, zero_add, mul_neg]
  rw [show -y * Real.pi = -Real.pi * y by ring, Real.exp_zero]
  ring

/-- Partial Laplace transform of the absolute sine over `N` periods.  Each
period contributes one geometric factor. -/
private theorem integral_abs_sin_mul_exp_neg_upto (y : ℝ) (N : ℕ) :
    (∫ t in (0 : ℝ)..((N : ℝ) * Real.pi),
        |Real.sin t| * Real.exp (-y * t)) =
      (∑ n ∈ Finset.range N, Real.exp (-Real.pi * y) ^ n) *
        ((1 + Real.exp (-Real.pi * y)) / (1 + y ^ 2)) := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hcast : ((N + 1 : ℕ) : ℝ) * Real.pi =
          (N : ℝ) * Real.pi + Real.pi := by
        push_cast
        ring
      have hcont : Continuous fun t : ℝ => |Real.sin t| * Real.exp (-y * t) := by
        fun_prop
      have hi1 : IntervalIntegrable (fun t => |Real.sin t| * Real.exp (-y * t))
          MeasureTheory.volume 0 ((N : ℝ) * Real.pi) :=
        hcont.intervalIntegrable _ _
      have hi2 : IntervalIntegrable (fun t => |Real.sin t| * Real.exp (-y * t))
          MeasureTheory.volume ((N : ℝ) * Real.pi)
          ((N : ℝ) * Real.pi + Real.pi) :=
        hcont.intervalIntegrable _ _
      have hshift :
          (∫ t in ((N : ℝ) * Real.pi)..((N : ℝ) * Real.pi + Real.pi),
              |Real.sin t| * Real.exp (-y * t)) =
            Real.exp (-Real.pi * y) ^ N *
              ((1 + Real.exp (-Real.pi * y)) / (1 + y ^ 2)) := by
        have hcomp := intervalIntegral.integral_comp_add_right
          (a := 0) (b := Real.pi)
          (fun t => |Real.sin t| * Real.exp (-y * t)) ((N : ℝ) * Real.pi)
        rw [zero_add] at hcomp
        rw [show (N : ℝ) * Real.pi + Real.pi =
          Real.pi + (N : ℝ) * Real.pi by ring, ← hcomp]
        calc
          (∫ s in (0 : ℝ)..Real.pi,
              |Real.sin (s + (N : ℝ) * Real.pi)| *
                Real.exp (-y * (s + (N : ℝ) * Real.pi))) =
              ∫ s in (0 : ℝ)..Real.pi,
                Real.exp (-y * ((N : ℝ) * Real.pi)) *
                  (Real.sin s * Real.exp (-y * s)) := by
            apply intervalIntegral.integral_congr
            intro s hs
            rw [Set.uIcc_of_le Real.pi_nonneg] at hs
            dsimp only
            have hsin : |Real.sin (s + (N : ℝ) * Real.pi)| = Real.sin s := by
              rw [Real.abs_sin_add_nat_mul_pi]
              exact abs_of_nonneg
                (Real.sin_nonneg_of_nonneg_of_le_pi hs.1 hs.2)
            rw [hsin, show -y * (s + (N : ℝ) * Real.pi) =
              -y * s + -y * ((N : ℝ) * Real.pi) by ring, Real.exp_add]
            ring
          _ = Real.exp (-y * ((N : ℝ) * Real.pi)) *
              ((1 + Real.exp (-Real.pi * y)) / (1 + y ^ 2)) := by
            rw [intervalIntegral.integral_const_mul,
              integral_zero_pi_sin_mul_exp_neg]
          _ = Real.exp (-Real.pi * y) ^ N *
              ((1 + Real.exp (-Real.pi * y)) / (1 + y ^ 2)) := by
            congr 1
            rw [← Real.exp_nat_mul]
            congr 1
            ring
      rw [hcast, ← intervalIntegral.integral_add_adjacent_intervals hi1 hi2,
        ih, hshift, Finset.sum_range_succ]
      ring

/-- Integrability of the absolute sine against an exponential weight. -/
private theorem integrableOn_abs_sin_mul_exp_neg {y : ℝ} (hy : 0 < y) :
    IntegrableOn (fun t : ℝ => |Real.sin t| * Real.exp (-y * t))
      (Set.Ioi 0) := by
  apply (exp_neg_integrableOn_Ioi 0 hy).mono'
  · exact (by fun_prop : Measurable fun t : ℝ =>
      |Real.sin t| * Real.exp (-y * t)).aestronglyMeasurable
  · filter_upwards [] with t
    rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_pos (Real.exp_pos _)]
    have hsin : |Real.sin t| ≤ 1 :=
      abs_le.mpr ⟨Real.neg_one_le_sin t, Real.sin_le_one t⟩
    calc
      |Real.sin t| * Real.exp (-y * t) ≤ 1 * Real.exp (-y * t) :=
        mul_le_mul_of_nonneg_right hsin (Real.exp_pos _).le
      _ = Real.exp (-y * t) := one_mul _

/-- The Laplace transform of the absolute sine, by periodic decomposition and
the geometric series. -/
private theorem integral_Ioi_abs_sin_mul_exp_neg {y : ℝ} (hy : 0 < y) :
    (∫ t in Set.Ioi (0 : ℝ), |Real.sin t| * Real.exp (-y * t)) =
      (1 + Real.exp (-Real.pi * y)) /
        ((1 - Real.exp (-Real.pi * y)) * (1 + y ^ 2)) := by
  let q : ℝ := Real.exp (-Real.pi * y)
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 :=
    Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  have hqne : 1 - q ≠ 0 := by linarith
  have hden : (1 : ℝ) + y ^ 2 ≠ 0 := by positivity
  have hb : Filter.Tendsto (fun N : ℕ => (N : ℝ) * Real.pi)
      Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const Real.pi_pos
  have hlim1 := intervalIntegral_tendsto_integral_Ioi 0
    (integrableOn_abs_sin_mul_exp_neg hy) hb
  have hgeo : Filter.Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N, q ^ n)
      Filter.atTop (nhds (1 - q)⁻¹) :=
    (hasSum_geometric_of_lt_one hq0 hq1).tendsto_sum_nat
  have hlim2 : Filter.Tendsto
      (fun N : ℕ => ∫ t in (0 : ℝ)..((N : ℝ) * Real.pi),
        |Real.sin t| * Real.exp (-y * t))
      Filter.atTop (nhds ((1 - q)⁻¹ * ((1 + q) / (1 + y ^ 2)))) := by
    apply (hgeo.mul_const ((1 + q) / (1 + y ^ 2))).congr
    intro N
    exact (integral_abs_sin_mul_exp_neg_upto y N).symm
  rw [tendsto_nhds_unique hlim1 hlim2]
  -- states the goal with the definition unfolded, in the shape the next step needs;
  -- there is no `_apply` lemma to rewrite with here.
  change (1 - q)⁻¹ * ((1 + q) / (1 + y ^ 2)) = (1 + q) / ((1 - q) * (1 + y ^ 2))
  field_simp

/-- Two-sided integrability of the absolute sine against a symmetric
exponential. -/
theorem integrable_abs_sin_mul_exp_neg_abs {y : ℝ} (hy : 0 < y) :
    Integrable (fun t : ℝ => |Real.sin t| * Real.exp (-y * |t|)) := by
  refine (integrable_iff_integrableOn_Ioi_of_even (fun t => by simp [Real.sin_neg])).mpr ?_
  apply (integrableOn_abs_sin_mul_exp_neg hy).congr_fun _ measurableSet_Ioi
  intro t ht
  dsimp only
  rw [abs_of_pos (show (0 : ℝ) < t from ht)]

/-- The two-sided Laplace transform of the absolute sine. -/
theorem integral_abs_sin_mul_exp_neg_abs {y : ℝ} (hy : 0 < y) :
    (∫ t : ℝ, |Real.sin t| * Real.exp (-y * |t|)) =
      2 * ((1 + Real.exp (-Real.pi * y)) /
        ((1 - Real.exp (-Real.pi * y)) * (1 + y ^ 2))) := by
  have h := integral_comp_abs
    (f := fun s : ℝ => |Real.sin s| * Real.exp (-y * s))
  calc
    (∫ t : ℝ, |Real.sin t| * Real.exp (-y * |t|)) =
        ∫ t : ℝ, |Real.sin (|t|)| * Real.exp (-y * |t|) := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [Real.abs_sin_abs]
    _ = 2 * ∫ t in Set.Ioi (0 : ℝ), |Real.sin t| * Real.exp (-y * t) := h
    _ = 2 * ((1 + Real.exp (-Real.pi * y)) /
        ((1 - Real.exp (-Real.pi * y)) * (1 + y ^ 2))) := by
      rw [integral_Ioi_abs_sin_mul_exp_neg hy]

end

end HaagerupZsido
end TauCeti
