/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.SpecialFunctions.Pow.NNReal
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Integrals of a weakly singular norm power

Let `E` be a finite-dimensional real normed space of dimension `d`.  This file
computes the integral of the kernel `x ↦ ‖x‖ ^ s` on a ball centred at the origin, for every
exponent `s > -d`.  The singularity is locally integrable because the radial Jacobian is
`r ^ (d - 1)`.  For an additive Haar measure `μ` and `R ≥ 0`,

`\int x in ball 0 R, ‖x‖ ^ s ∂μ = d * μ.real (ball 0 1) * (R ^ (d + s) / (d + s))`.

The weakly singular exponent `s = 1 - d` gives the value `d * μ.real (ball 0 1) * R`; this is
the kernel bound used when the straight-segment estimate is averaged over a ball in the proof of
the Poincaré--Wirtinger inequality.  When `d > 1`, the exponents `s = (1 - d) q` with
`q < d / (d - 1)` are the ones met in Hölder's inequality against the Riesz potential in Morrey's
inequality.  When `d = 1`, the kernel is constant and imposes no upper bound on `q`.

On the real line, a pole may also sit off the line: for `e ∈ ℂ` and `s > -1`, the kernel
`x ↦ |x - e| ^ s` has finite lower integral over every closed interval, since for `s ≤ 0` it is
at most `|x - Re e| ^ s`.

## Main declarations

* `TauCeti.integrableOn_norm_rpow_ball`: integrability on a centred ball.
* `TauCeti.integral_norm_rpow_ball`: the exact radial integral.
* `TauCeti.integrableOn_norm_sub_rpow_ball`: integrability after translation.
* `TauCeti.integral_norm_sub_rpow_ball`: the exact integral with any centre.
* `TauCeti.locallyIntegrable_norm_sub_rpow`: local integrability after translation.
* `TauCeti.setLIntegral_closedBall_enorm_sub_rpow`: the lower integral with any centre, over a
  closed ball.
* `TauCeti.integral_norm_sub_rpow_one_sub_finrank_le`: the translated-ball bound, for `s = 1 - d`.
* `Complex.setLIntegral_closedBall_enorm_ofReal_sub_rpow_lt_top`: for `e ∈ ℂ` and `s > -1`,
  `∫⁻ x in closedBall c R, ‖(x : ℂ) - e‖ₑ ^ s < ∞` over the real line.

## References

The statements and radial proof are adapted from Scott Armstrong and Julia Kempe's Apache-2.0
`scottnarmstrong/DeGiorgi/DeGiorgi/Poincare.lean`, commit
`4c1b3077d3782b24065184df4ba59501b2e56fc7`, lines 750--870.  The formulation here uses an
arbitrary additive Haar measure and Mathlib's `MeasureTheory.integral_fun_norm_addHaar`.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Metric Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {mu : Measure E} [mu.IsAddHaarMeasure]

/-- The kernel `x ↦ ‖x‖ ^ s` is integrable on every ball centred at the origin when
`-dim E < s`. -/
theorem integrableOn_norm_rpow_ball {s : ℝ} (hs : -(Module.finrank ℝ E : ℝ) < s) {R : ℝ} :
    IntegrableOn (fun x : E => ‖x‖ ^ s) (ball 0 R) mu := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · have hs0 : 0 < s := by simpa [Module.finrank_zero_of_subsingleton] using hs
    simp only [norm_of_subsingleton, Real.zero_rpow hs0.ne']
    exact integrableOn_zero
  refine integrableOn_ball_of_norm_le_rpow (μ := mu) Module.finrank_pos
    (C := 1) (α := -s) (by linarith) ?_ ?_
  · filter_upwards with x
    rw [neg_neg, one_mul, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg x) _)]
  · exact (by fun_prop : Measurable fun x : E => ‖x‖ ^ s).aestronglyMeasurable

/-- The exact integral of the kernel `x ↦ ‖x‖ ^ s` on a ball centred at the origin, for
`-dim E < s`. The coefficient is stated using the chosen additive Haar measure, so the result
applies to both Lebesgue volume and its scalar multiples. -/
theorem integral_norm_rpow_ball {s : ℝ} (hs : -(Module.finrank ℝ E : ℝ) < s) {R : ℝ}
    (hR : 0 ≤ R) :
    ∫ x in ball (0 : E) R, ‖x‖ ^ s ∂mu =
      (Module.finrank ℝ E : ℝ) * mu.real (ball (0 : E) 1) *
        (R ^ ((Module.finrank ℝ E : ℝ) + s) / ((Module.finrank ℝ E : ℝ) + s)) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · have hs0 : 0 < s := by simpa [Module.finrank_zero_of_subsingleton] using hs
    simp [norm_of_subsingleton, Real.zero_rpow hs0.ne', Module.finrank_zero_of_subsingleton]
  let d := Module.finrank ℝ E
  let f : ℝ → ℝ := fun r => if 0 < r ∧ r < R then r ^ s else 0
  have hconv : ∫ x in ball (0 : E) R, ‖x‖ ^ s ∂mu = ∫ x : E, f ‖x‖ ∂mu := by
    rw [← integral_indicator measurableSet_ball]
    refine integral_congr_ae ?_
    have hzero : mu ({0} : Set E) = 0 := measure_singleton 0
    filter_upwards [compl_mem_ae_iff.mpr hzero] with x hx
    simp only [f, indicator, mem_ball, dist_zero_right]
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    simp only [and_iff_right hxpos]
  have hradial : ∫ x : E, f ‖x‖ ∂mu =
      d • mu.real (ball (0 : E) 1) • ∫ r in Ioi (0 : ℝ), r ^ (d - 1) • f r :=
    integral_fun_norm_addHaar mu f
  have hd : 1 ≤ d := Module.finrank_pos
  have hds : -1 < (d : ℝ) - 1 + s := by linarith
  have hradialIntegral : ∫ r in Ioi (0 : ℝ), r ^ (d - 1) • f r =
      R ^ ((d : ℝ) + s) / ((d : ℝ) + s) := by
    have heq : Set.EqOn (fun r : ℝ => r ^ (d - 1) • f r)
        ((Ioo (0 : ℝ) R).indicator fun r => r ^ ((d : ℝ) - 1 + s)) (Ioi 0) := by
      intro r hr
      simp only [mem_Ioi] at hr
      simp only [f, smul_eq_mul, indicator, mem_Ioo]
      split_ifs with h
      · rw [← Real.rpow_natCast r (d - 1), Nat.cast_sub hd, Nat.cast_one, ← Real.rpow_add hr]
      · simp
    have hsupport : ∫ r in Ioi (0 : ℝ), r ^ (d - 1) • f r =
        ∫ r in Ioo (0 : ℝ) R, r ^ ((d : ℝ) - 1 + s) := by
      rw [setIntegral_congr_fun measurableSet_Ioi heq, setIntegral_indicator measurableSet_Ioo,
        inter_eq_right.mpr Ioo_subset_Ioi_self]
    have hpower : ∫ r in Ioo (0 : ℝ) R, r ^ ((d : ℝ) - 1 + s) =
        R ^ ((d : ℝ) + s) / ((d : ℝ) + s) := by
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hR,
        integral_rpow (Or.inl hds), Real.zero_rpow (by linarith), sub_zero]
      congr 1 <;> ring_nf
    exact hsupport.trans hpower
  rw [hconv, hradial, hradialIntegral]
  simp only [nsmul_eq_mul, smul_eq_mul]
  simp [d, mul_assoc]

/-- The kernel with pole `x` and exponent `s > -dim E` is integrable on every ball centred
at `x`. -/
theorem integrableOn_norm_sub_rpow_ball {s : ℝ} (hs : -(Module.finrank ℝ E : ℝ) < s) (x : E)
    {R : ℝ} : IntegrableOn (fun y : E => ‖x - y‖ ^ s) (ball x R) mu := by
  have hpres := measurePreserving_add_right mu x
  have hemb := (MeasurableEquiv.addRight x : E ≃ᵐ E).measurableEmbedding
  have hpre : (fun z : E => z + x) ⁻¹' ball x R = ball (0 : E) R := by
    ext z
    simp [mem_ball]
  rw [← hpres.integrableOn_comp_preimage hemb, hpre]
  exact (integrableOn_norm_rpow_ball (mu := mu) hs (R := R)).congr
    (ae_of_all _ fun z => by simp [norm_neg])

/-- The kernel with pole `x` and exponent `s > -dim E` is locally integrable. -/
theorem locallyIntegrable_norm_sub_rpow {s : ℝ} (hs : -(Module.finrank ℝ E : ℝ) < s) (x : E) :
    LocallyIntegrable (fun y : E => ‖x - y‖ ^ s) mu := by
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨R, hKR⟩ := hK.isBounded.subset_ball x
  exact (integrableOn_norm_sub_rpow_ball (mu := mu) hs x).mono_set hKR

/-- The integral of the kernel with pole `x` and exponent `s > -dim E` over a ball centred at `x`
does not depend on the centre and has the same exact value as the radial integral at the
origin. -/
theorem integral_norm_sub_rpow_ball {s : ℝ} (hs : -(Module.finrank ℝ E : ℝ) < s) {R : ℝ}
    (hR : 0 ≤ R) (x : E) :
    ∫ y in ball x R, ‖x - y‖ ^ s ∂mu =
      (Module.finrank ℝ E : ℝ) * mu.real (ball (0 : E) 1) *
        (R ^ ((Module.finrank ℝ E : ℝ) + s) / ((Module.finrank ℝ E : ℝ) + s)) := by
  have hpres := measurePreserving_add_right mu x
  have hemb := (MeasurableEquiv.addRight x : E ≃ᵐ E).measurableEmbedding
  have hpre : (fun z : E => z + x) ⁻¹' ball x R = ball (0 : E) R := by
    ext z
    simp [mem_ball]
  rw [← hpres.setIntegral_preimage_emb hemb, hpre]
  have hfun : (fun z : E => ‖x - (z + x)‖ ^ s) = fun z => ‖z‖ ^ s := by
    funext z
    simp [norm_neg]
  rw [hfun, integral_norm_rpow_ball hs hR]

/-- If `x` lies in `closedBall z R`, then the integral over `ball z R` of the kernel with pole
`x` is bounded by the exact integral on `ball 0 (2R)`. -/
theorem integral_norm_sub_rpow_one_sub_finrank_le {R : ℝ} (x : E) {z : E}
    (hx : x ∈ closedBall z R) :
    ∫ y in ball z R, ‖x - y‖ ^ (1 - (Module.finrank ℝ E : ℝ)) ∂mu ≤
      (Module.finrank ℝ E : ℝ) * mu.real (ball (0 : E) 1) * (2 * R) := by
  have hxR : dist x z ≤ R := mem_closedBall.mp hx
  have hR : 0 ≤ R := dist_nonneg.trans hxR
  have hsub : ball z R ⊆ ball x (2 * R) := by
    intro y hy
    rw [mem_ball] at hy ⊢
    calc
      dist y x ≤ dist y z + dist z x := dist_triangle y z x
      _ < R + R := by rw [dist_comm] at hxR; exact add_lt_add_of_lt_of_le hy hxR
      _ = 2 * R := by ring
  have htwoR : 0 ≤ 2 * R := by positivity
  have hintegrable :
      IntegrableOn (fun y : E => ‖x - y‖ ^ (1 - (Module.finrank ℝ E : ℝ)))
        (ball x (2 * R)) mu :=
    integrableOn_norm_sub_rpow_ball (by linarith) x
  calc
    ∫ y in ball z R, ‖x - y‖ ^ (1 - (Module.finrank ℝ E : ℝ)) ∂mu ≤
        ∫ y in ball x (2 * R), ‖x - y‖ ^ (1 - (Module.finrank ℝ E : ℝ)) ∂mu := by
      apply setIntegral_mono_set hintegrable
      · exact ae_of_all _ fun y => Real.rpow_nonneg (norm_nonneg _) _
      · exact hsub.eventuallyLE
    _ = (Module.finrank ℝ E : ℝ) * mu.real (ball (0 : E) 1) * (2 * R) :=
      by rw [integral_norm_sub_rpow_ball (by linarith) htwoR, add_sub_cancel, Real.rpow_one,
        div_one]

/-- The lower integral of the kernel with pole `x` and exponent `s > -dim E` over the closed
ball of radius `R` about `x`. Unlike its Bochner counterpart `TauCeti.integral_norm_sub_rpow_ball`,
the kernel takes the value `∞` at the pole when `s < 0`; this does not change the integral, since
the pole is a null set. -/
theorem setLIntegral_closedBall_enorm_sub_rpow {s : ℝ} (hs : -(Module.finrank ℝ E : ℝ) < s)
    {R : ℝ} (hR : 0 ≤ R) (x : E) :
    ∫⁻ y in closedBall x R, ‖x - y‖ₑ ^ s ∂mu =
      ENNReal.ofReal ((Module.finrank ℝ E : ℝ) * mu.real (ball (0 : E) 1) *
        (R ^ ((Module.finrank ℝ E : ℝ) + s) / ((Module.finrank ℝ E : ℝ) + s))) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · -- In dimension zero the exponent is positive, so the kernel vanishes identically.
    have hs0 : 0 < s := by simpa [Module.finrank_zero_of_subsingleton] using hs
    have h0 : (fun y : E => ‖x - y‖ₑ ^ s) = 0 := funext fun y => by
      rw [Subsingleton.elim (x - y) 0, enorm_zero, ENNReal.zero_rpow_of_pos hs0, Pi.zero_apply]
    simp [h0, lintegral_zero_fun, Module.finrank_zero_of_subsingleton]
  have hball := mu.addHaar_closedBall_ae_eq_ball x R
  rw [Measure.restrict_congr_set hball, ← integral_norm_sub_rpow_ball hs hR x,
    ofReal_integral_eq_lintegral_ofReal (integrableOn_norm_sub_rpow_ball hs x)
      (ae_of_all _ fun y => Real.rpow_nonneg (norm_nonneg _) _)]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_restrict_of_ae (compl_mem_ae_iff.mpr (measure_singleton (μ := mu) x))]
    with y hy
  have hxy : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr fun h => hy (h ▸ rfl))
  rw [← ENNReal.ofReal_rpow_of_pos hxy, ofReal_norm]

end TauCeti

namespace Complex

open MeasureTheory

/-- For a complex point `e` and an exponent `s > -1`, the kernel `x ↦ |x - e| ^ s` on the real line
has finite lower integral over every closed interval. For `s ≤ 0` it is at most `|x - Re e| ^ s`,
whose pole is integrable; for `s ≥ 0` it is bounded on the interval. -/
theorem setLIntegral_closedBall_enorm_ofReal_sub_rpow_lt_top (e : ℂ) {s : ℝ} (hs : -1 < s)
    (c R : ℝ) : ∫⁻ x in Metric.closedBall c R, ‖(x : ℂ) - e‖ₑ ^ s < ⊤ := by
  rcases lt_or_ge R 0 with hR | hR
  · simp [Metric.closedBall_eq_empty.mpr hR]
  rcases le_total s 0 with hs0 | hs0
  · calc ∫⁻ x in Metric.closedBall c R, ‖(x : ℂ) - e‖ₑ ^ s
        ≤ ∫⁻ x in Metric.closedBall e.re (R + |c - e.re|), ‖e.re - x‖ₑ ^ s := by
          refine (lintegral_mono fun x ↦ ENNReal.rpow_le_rpow_of_nonpos ?_ hs0).trans
            (lintegral_mono_set fun x hx ↦ ?_)
          · rw [← ofReal_norm, ← ofReal_norm, Real.norm_eq_abs, abs_sub_comm]
            exact ENNReal.ofReal_le_ofReal (by simpa using abs_re_le_norm ((x : ℂ) - e))
          · rw [Metric.mem_closedBall, Real.dist_eq] at hx ⊢
            linarith [abs_sub_le x c e.re]
      _ < ⊤ := by
          rw [TauCeti.setLIntegral_closedBall_enorm_sub_rpow (by simpa using hs) (by positivity)]
          exact ENNReal.ofReal_lt_top
  · calc ∫⁻ x in Metric.closedBall c R, ‖(x : ℂ) - e‖ₑ ^ s
        ≤ ∫⁻ _ in Metric.closedBall c R, ENNReal.ofReal (|c| + R + ‖e‖) ^ s := by
          refine setLIntegral_mono_ae (by fun_prop) (ae_of_all _ fun x hx ↦ ?_)
          refine ENNReal.rpow_le_rpow ?_ hs0
          rw [← ofReal_norm]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [Metric.mem_closedBall, Real.dist_eq] at hx
          calc ‖(x : ℂ) - e‖ ≤ ‖(x : ℂ)‖ + ‖e‖ := norm_sub_le _ _
            _ ≤ |c| + R + ‖e‖ := by
              rw [norm_real, Real.norm_eq_abs]
              linarith [abs_sub_abs_le_abs_sub x c]
      _ < ⊤ := by
          rw [setLIntegral_const]
          exact ENNReal.mul_lt_top (ENNReal.rpow_ne_top_of_nonneg hs0 ENNReal.ofReal_ne_top).lt_top
            measure_closedBall_lt_top

end Complex
