/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.MeasureTheory.Function.L1Space.Integrable
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

* `TauCeti.integrableOn_norm_rpow_ball`: integrability on a centred ball, and
  `TauCeti.integrableOn_norm_rpow_ball_iff`: its converse on a nontrivial space.
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

/-- On a nontrivial space, the kernel `x ↦ ‖x‖ ^ s` is integrable on a ball of positive radius
centred at the origin exactly when `-dim E < s`. -/
theorem integrableOn_norm_rpow_ball_iff [Nontrivial E] {s R : ℝ} (hR : 0 < R) :
    IntegrableOn (fun x : E => ‖x‖ ^ s) (ball 0 R) mu ↔ -(Module.finrank ℝ E : ℝ) < s := by
  have hd : 1 ≤ Module.finrank ℝ E := Module.finrank_pos
  have hcongr : IntegrableOn (fun y : ℝ => y ^ (Module.finrank ℝ E - 1) • y ^ s) (Ioo 0 R) ↔
      IntegrableOn (fun y : ℝ => y ^ ((Module.finrank ℝ E : ℝ) - 1 + s)) (Ioo 0 R) :=
    integrableOn_congr_fun (fun y hy => by
      rw [smul_eq_mul, Real.rpow_add hy.1, ← Real.rpow_natCast, Nat.cast_sub hd, Nat.cast_one])
      measurableSet_Ioo
  rw [integrableOn_fun_norm_addHaar mu (f := fun r : ℝ => r ^ s), hcongr,
    intervalIntegral.integrableOn_Ioo_rpow_iff hR]
  constructor <;> intro h <;> linarith

/-- A norm power is integrable outside a positive-radius closed ball exactly below the
negative dimension. This includes divergence at the logarithmic borderline. -/
theorem integrableOn_norm_rpow_compl_closedBall_iff [Nontrivial E] {s R : ℝ} (hR : 0 < R) :
    IntegrableOn (fun x : E => ‖x‖ ^ s) (closedBall 0 R)ᶜ mu ↔
      s < -(Module.finrank ℝ E : ℝ) := by
  let d := Module.finrank ℝ E
  have hd : 1 ≤ d := Module.finrank_pos
  let f : ℝ → ℝ := (Ioi R).indicator (fun r => r ^ s)
  have hnorm : (fun x : E => f ‖x‖) =
      (closedBall (0 : E) R)ᶜ.indicator (fun x => ‖x‖ ^ s) := by
    funext x
    simp [f, Set.indicator, mem_closedBall, not_le]
  have hrad := integrable_fun_norm_addHaar mu (f := f)
  rw [hnorm, integrable_indicator_iff isClosed_closedBall.measurableSet.compl] at hrad
  have heq : EqOn (fun r : ℝ => r ^ (d-1) • f r)
      ((Ioi R).indicator (fun r => r ^ ((d : ℝ)-1+s))) (Ioi 0) := by
    intro r hr
    have hr0 : 0 < r := hr
    by_cases h : R < r
    · have hrmem : r ∈ Ioi R := h
      simp only [f, indicator_of_mem hrmem, smul_eq_mul]
      rw [← Real.rpow_natCast, Nat.cast_sub hd, Nat.cast_one, ← Real.rpow_add hr0]
    · simp [f, h]
  have hsupp : Function.support ((Ioi R).indicator (fun r : ℝ => r ^ ((d : ℝ)-1+s))) ⊆ Ioi 0 :=
    (support_indicator_subset).trans (Ioi_subset_Ioi hR.le)
  rw [integrableOn_congr_fun heq measurableSet_Ioi,
    integrableOn_iff_integrable_of_support_subset hsupp,
    integrable_indicator_iff measurableSet_Ioi, integrableOn_Ioi_rpow_iff hR] at hrad
  exact hrad.trans (by dsimp [d]; constructor <;> intro h <;> linarith)

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

/-- The integral of `‖x - x₀‖ ^ 2` over the ball of radius `R` about `x₀` in dimension `n` is
`n / (n + 2) * R ^ 2` times the measure of the ball. -/
theorem integral_norm_sub_sq_ball {R : ℝ} (x₀ : E) :
    ∫ x in ball x₀ R, ‖x - x₀‖ ^ 2 ∂mu =
      Module.finrank ℝ E / (Module.finrank ℝ E + 2) * R ^ 2 * mu.real (ball x₀ R) := by
  rcases le_or_gt R 0 with hR | hR
  · simp [Metric.ball_eq_empty.2 hR]
  have h := integral_norm_sub_rpow_ball (mu := mu) (s := 2) (by linarith) hR.le x₀
  simp_rw [norm_sub_rev x₀, Real.rpow_two] at h
  have hball : mu.real (ball x₀ R) = R ^ Module.finrank ℝ E * mu.real (ball (0 : E) 1) := by
    rw [measureReal_def, Measure.addHaar_ball_of_pos mu _ hR, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity), measureReal_def]
  rw [h, hball, Real.rpow_add hR, Real.rpow_two, Real.rpow_natCast]
  field_simp

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

namespace TauCeti

open MeasureTheory Metric Set
open scoped ENNReal

/-- A nonzero multiple of an inverse power has a finite positive `Lp` tail precisely when
its decay order times the exponent exceeds the real dimension two. -/
theorem memLp_div_pow_compl_closedBall_iff {a : ℂ} (ha : a ≠ 0) {R : ℝ} (hR : 0 < R)
    (m : ℕ) {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp_top : p ≠ ∞) :
    MemLp (fun z : ℂ => a/z^m) p (volume.restrict (closedBall 0 R)ᶜ) ↔
      2 < (m : ℝ)*p.toReal := by
  have hscale : MemLp (fun z : ℂ => a/z^m) p (volume.restrict (closedBall 0 R)ᶜ) ↔
      MemLp (fun z : ℂ => (z^m)⁻¹) p (volume.restrict (closedBall 0 R)ᶜ) := by
    constructor
    · intro h
      have hi := h.const_mul a⁻¹
      simpa only [div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ ha, one_mul] using hi
    · intro h
      simpa only [div_eq_mul_inv] using h.const_mul a
  rw [hscale, ← integrable_norm_rpow_iff (by fun_prop) hp0 hp_top]
  have heq : (fun z : ℂ => ‖(z^m)⁻¹‖ ^ p.toReal) =
      (fun z => ‖z‖ ^ (-((m : ℝ)*p.toReal))) := by
    funext z
    rw [norm_inv, norm_pow, Real.inv_rpow (by positivity),
      ← Real.rpow_natCast_mul (norm_nonneg z), Real.rpow_neg (norm_nonneg z)]
  rw [heq]
  simpa only [IntegrableOn, Complex.finrank_real_complex, Nat.cast_ofNat, neg_lt_neg_iff] using
    (TauCeti.integrableOn_norm_rpow_compl_closedBall_iff (E := ℂ) (mu := volume)
      (s := -((m : ℝ)*p.toReal)) hR)

end TauCeti
