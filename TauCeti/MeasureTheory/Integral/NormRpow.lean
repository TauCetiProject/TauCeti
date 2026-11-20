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
* `MeasureTheory.Measure.not_integrable_norm_sub_rpow`: a power of the distance to a point is
  never integrable over the whole space, for an additive Haar measure on a nontrivial space.
* `TauCeti.integrableOn_norm_sub_rpow_ball_iff_integrableOn_norm_rpow_ball`,
  `TauCeti.integrableOn_norm_sub_rpow_ball`: translation equivalence and integrability after
  translation.
* `TauCeti.integral_norm_sub_rpow_ball`: the exact integral with any centre.
* `TauCeti.locallyIntegrable_norm_sub_rpow`: local integrability after translation.
* `TauCeti.setLIntegral_closedBall_enorm_sub_rpow`: the lower integral with any centre, over a
  closed ball.
* `TauCeti.ae_enorm_le_ofReal_mul_enorm_sub_rpow_of_norm_le`: off-diagonal real-norm domination
  `‖f y‖ ≤ C * ‖x - y‖ ^ s` on a measurable set implies `∀ᵐ y, ‖f y‖ₑ ≤ ofReal C * ‖x - y‖ₑ ^ s`
  under any null-singleton measure.
* `TauCeti.setLIntegral_enorm_sub_rpow_le_of_mem_closure`,
  `TauCeti.setIntegral_norm_sub_rpow_le_of_mem_closure`: diameter bounds on any bounded set for
  poles in its closure and exponents `s > -d`, together with divergence `= ∞` at interior poles for
  `s ≤ -d` (`TauCeti.setLIntegral_enorm_sub_rpow_eq_top_of_mem_interior`).
* `TauCeti.integral_norm_sub_rpow_one_sub_finrank_le`: the translated-ball bound, for `s = 1 - d`.
* `TauCeti.memLp_div_pow_compl_closedBall_iff` and
  `TauCeti.memLp_div_sub_pow_compl_closedBall_iff`: `a / (z - c) ^ m` is in `Lᵖ` off a disc
  centred at `c` exactly when `2 < m p`.
* `Bornology.IsBounded.memLp_norm_inv_restrict`, `TauCeti.not_memLp_norm_inv_closedBall`:
  `‖x‖⁻¹` is `Lʳ` on bounded sets for `r < dim E`, and not near the origin for `r ≥ dim E`.
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
open scoped ENNReal

/-- Off-diagonal real-norm domination `‖f y‖ ≤ C * ‖x - y‖ ^ s` on a measurable set `Ω` implies
almost-everywhere extended-norm domination `‖f y‖ₑ ≤ ENNReal.ofReal C * ‖x - y‖ₑ ^ s` under
`μ.restrict Ω` whenever singletons have `μ`-measure zero. -/
theorem ae_enorm_le_ofReal_mul_enorm_sub_rpow_of_norm_le {E F : Type*} [SeminormedAddGroup E]
    [MeasurableSpace E] {μ : Measure E} [NullSingletonClass μ] [SeminormedAddGroup F]
    {Ω : Set E} (hΩ : MeasurableSet Ω) {f : E → F} {x : E} {s C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ y ∈ Ω, x ≠ y → ‖f y‖ ≤ C * ‖x - y‖ ^ s) :
    ∀ᵐ y ∂μ.restrict Ω, ‖f y‖ₑ ≤ ENNReal.ofReal C * ‖x - y‖ₑ ^ s := by
  filter_upwards [ae_restrict_mem hΩ,
    ae_restrict_of_ae (compl_mem_ae_iff.2 (measure_singleton (μ := μ) x))] with y hy hyx
  calc ‖f y‖ₑ = ENNReal.ofReal ‖f y‖ := (ofReal_norm _).symm
    _ ≤ ENNReal.ofReal (C * ‖x - y‖ ^ s) := ENNReal.ofReal_le_ofReal (hf y hy (Ne.symm hyx))
    _ = ENNReal.ofReal C * ENNReal.ofReal (‖x - y‖ ^ s) := ENNReal.ofReal_mul hC
    _ ≤ ENNReal.ofReal C * ENNReal.ofReal ‖x - y‖ ^ s :=
        mul_le_mul_right (ENNReal.ofReal_rpow_le (norm_nonneg _)) _
    _ = ENNReal.ofReal C * ‖x - y‖ₑ ^ s := by rw [ofReal_norm]

/-- Translation invariance reducing integrability of `y ↦ ‖x - y‖ ^ s` on `ball x R` to
integrability of `z ↦ ‖z‖ ^ s` on `ball 0 R`. -/
theorem integrableOn_norm_sub_rpow_ball_iff_integrableOn_norm_rpow_ball {E : Type*}
    [SeminormedAddCommGroup E] [MeasurableSpace E] [MeasurableAdd E] {μ : Measure E}
    [μ.IsAddLeftInvariant] {s R : ℝ} (x : E) :
    IntegrableOn (fun y : E => ‖x - y‖ ^ s) (ball x R) μ ↔
      IntegrableOn (fun z : E => ‖z‖ ^ s) (ball 0 R) μ := by
  have hpre : (fun z : E => x + z) ⁻¹' ball x R = ball (0 : E) R := by ext z; simp [mem_ball]
  rw [← (measurePreserving_add_left μ x).integrableOn_comp_preimage
    (measurableEmbedding_addLeft x), hpre]
  simp only [Function.comp_def, sub_add_cancel_left, norm_neg]

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
    {R : ℝ} : IntegrableOn (fun y : E => ‖x - y‖ ^ s) (ball x R) mu :=
  (integrableOn_norm_sub_rpow_ball_iff_integrableOn_norm_rpow_ball x).2
    (integrableOn_norm_rpow_ball hs)

/-- The kernel with pole `x` and exponent `s > -dim E` is locally integrable. -/
theorem locallyIntegrable_norm_sub_rpow {s : ℝ} (hs : -(Module.finrank ℝ E : ℝ) < s) (x : E) :
    LocallyIntegrable (fun y : E => ‖x - y‖ ^ s) mu := by
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨R, hKR⟩ := hK.isBounded.subset_ball x
  exact (integrableOn_norm_sub_rpow_ball (mu := mu) hs x).mono_set hKR

/-- The kernel with pole `x` and exponent `s > -dim E` is integrable on every bounded set. -/
theorem integrableOn_norm_sub_rpow_of_isBounded {s : ℝ} (hs : -(Module.finrank ℝ E : ℝ) < s)
    {Ω : Set E} (hb : Bornology.IsBounded Ω) (x : E) :
    IntegrableOn (fun y : E => ‖x - y‖ ^ s) Ω mu := by
  obtain ⟨R, hΩR⟩ := hb.subset_ball x
  exact (integrableOn_norm_sub_rpow_ball (mu := mu) hs x).mono_set hΩR

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
    exact mu.addHaar_real_ball_of_pos x₀ hR
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
      · exact hsub.eventuallySubset
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
      rw [Subsingleton.elim (x - y) 0, eNorm_zero, ENNReal.zero_rpow_of_pos hs0, Pi.zero_apply]
    simp [h0, lintegral_zero_fun, Module.finrank_zero_of_subsingleton]
  rw [mu.restrict_closedBall_eq_restrict_ball x R, ← integral_norm_sub_rpow_ball hs hR x,
    ofReal_integral_eq_lintegral_ofReal (integrableOn_norm_sub_rpow_ball hs x)
      (ae_of_all _ fun y => Real.rpow_nonneg (norm_nonneg _) _)]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_restrict_of_ae (compl_mem_ae_iff.mpr (measure_singleton (μ := mu) x))]
    with y hy
  have hxy : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr fun h => hy (h ▸ rfl))
  rw [← ENNReal.ofReal_rpow_of_pos hxy, ofReal_norm]

/-- On a bounded set `Ω` with `x ∈ closure Ω`, the lower integral over `Ω` of `y ↦ ‖x - y‖ₑ ^ s`
with `s > -dim E` is at most its exact integral over `closedBall x (diam Ω)`, namely
`n μ(B(0, 1)) (diam Ω) ^ (n + s) / (n + s)`. -/
theorem setLIntegral_enorm_sub_rpow_le_of_mem_closure {s : ℝ}
    (hs : -(Module.finrank ℝ E : ℝ) < s) {Ω : Set E} {x : E}
    (hb : Bornology.IsBounded Ω) (hx : x ∈ closure Ω) :
    ∫⁻ y in Ω, ‖x - y‖ₑ ^ s ∂mu ≤
      ENNReal.ofReal ((Module.finrank ℝ E : ℝ) * mu.real (ball 0 1) *
        (diam Ω ^ ((Module.finrank ℝ E : ℝ) + s) / ((Module.finrank ℝ E : ℝ) + s))) := by
  calc
    _ ≤ ∫⁻ y in closedBall x (diam Ω), ‖x - y‖ₑ ^ s ∂mu :=
      lintegral_mono_set fun _ hy => mem_closedBall.2
        ((dist_le_diam_of_mem hb.closure (subset_closure hy) hx).trans_eq (diam_closure Ω))
    _ = _ := setLIntegral_closedBall_enorm_sub_rpow hs diam_nonneg x

/-- Bochner integral form of `TauCeti.setLIntegral_enorm_sub_rpow_le_of_mem_closure`. -/
theorem setIntegral_norm_sub_rpow_le_of_mem_closure {s : ℝ}
    (hs : -(Module.finrank ℝ E : ℝ) < s) {Ω : Set E} {x : E}
    (hb : Bornology.IsBounded Ω) (hx : x ∈ closure Ω) :
    ∫ y in Ω, ‖x - y‖ ^ s ∂mu ≤
      (Module.finrank ℝ E : ℝ) * mu.real (ball 0 1) *
        (diam Ω ^ ((Module.finrank ℝ E : ℝ) + s) / ((Module.finrank ℝ E : ℝ) + s)) := by
  have hpos : 0 < (Module.finrank ℝ E : ℝ) + s := by linarith
  have hrhs : 0 ≤ (Module.finrank ℝ E : ℝ) * mu.real (ball (0 : E) 1) *
      (diam Ω ^ ((Module.finrank ℝ E : ℝ) + s) / ((Module.finrank ℝ E : ℝ) + s)) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) measureReal_nonneg)
      (div_nonneg (Real.rpow_nonneg diam_nonneg _) hpos.le)
  rw [← ENNReal.ofReal_le_ofReal_iff hrhs,
    ofReal_integral_eq_lintegral_ofReal (integrableOn_norm_sub_rpow_of_isBounded hs hb x)
      (ae_of_all _ fun _ => Real.rpow_nonneg (norm_nonneg _) _)]
  exact (lintegral_mono fun y => by
    rw [← ofReal_norm]; exact ENNReal.ofReal_rpow_le (norm_nonneg _)).trans
    (setLIntegral_enorm_sub_rpow_le_of_mem_closure hs hb hx)

/-- On a nontrivial space, if `s ≤ -dim E` and `x ∈ interior Ω`, the lower integral of
`y ↦ ‖x - y‖ₑ ^ s` over `Ω` is infinite. -/
theorem setLIntegral_enorm_sub_rpow_eq_top_of_mem_interior [Nontrivial E] {s : ℝ}
    (hs : s ≤ -(Module.finrank ℝ E : ℝ)) {Ω : Set E} {x : E} (hx : x ∈ interior Ω) :
    ∫⁻ y in Ω, ‖x - y‖ₑ ^ s ∂mu = ⊤ := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hx)
  by_contra hne
  have hball_ne : ∫⁻ y in ball x r, ENNReal.ofReal (‖x - y‖ ^ s) ∂mu ≠ ⊤ :=
    ne_top_of_le_ne_top hne
      ((lintegral_mono fun y => by
        rw [← ofReal_norm]; exact ENNReal.ofReal_rpow_le (norm_nonneg _)).trans
        (lintegral_mono_set hball))
  have hint : IntegrableOn (fun y : E => ‖x - y‖ ^ s) (ball x r) mu :=
    (lintegral_ofReal_ne_top_iff_integrable
      (by fun_prop : Measurable fun y : E => ‖x - y‖ ^ s).aestronglyMeasurable
      (ae_of_all _ fun _ => Real.rpow_nonneg (norm_nonneg _) _)).1 hball_ne
  exact (((integrableOn_norm_sub_rpow_ball_iff_integrableOn_norm_rpow_ball x).trans
    (integrableOn_norm_rpow_ball_iff hr)).1 hint).not_ge hs

/-- On a bounded set `Ω` containing `x`, the Riesz kernel `‖x - y‖ ^ (1 - n)` has integral over
`Ω` at most `n μ(B(0, 1)) diam Ω`, since `Ω` lies in the closed ball of radius `diam Ω` about
`x`. -/
theorem lintegral_enorm_sub_rpow_le_of_mem {Ω : Set E} {x : E}
    (hb : Bornology.IsBounded Ω) (hx : x ∈ Ω) :
    ∫⁻ y in Ω, ‖x - y‖ₑ ^ (1 - (Module.finrank ℝ E : ℝ)) ∂mu ≤
      ENNReal.ofReal (Module.finrank ℝ E * mu.real (ball 0 1) * diam Ω) := by
  simpa only [add_sub_cancel, Real.rpow_one, div_one] using
    setLIntegral_enorm_sub_rpow_le_of_mem_closure
      (s := 1 - (Module.finrank ℝ E : ℝ)) (by linarith) hb (subset_closure hx)

section Inverse

open scoped ENNReal

/-- On a bounded set, `‖x‖ ^ s` is `Lʳ` for every finite exponent `r` with `-dim E < s r`. -/
theorem _root_.Bornology.IsBounded.memLp_norm_rpow_restrict {K : Set E}
    (hK : Bornology.IsBounded K) {s : ℝ} {r : ℝ≥0∞} (hr : r ≠ ∞)
    (hs : -(Module.finrank ℝ E : ℝ) < s * r.toReal) :
    MemLp (fun x : E => ‖x‖ ^ s) r (mu.restrict K) := by
  have hm : Measurable fun x : E => ‖x‖ ^ s := by fun_prop
  rcases eq_or_ne r 0 with rfl | hr0
  · exact memLp_zero_iff_aestronglyMeasurable.2 hm.aestronglyMeasurable
  obtain ⟨R, hR⟩ := hK.subset_ball 0
  refine MemLp.mono_measure (Measure.restrict_mono hR le_rfl) ?_
  rw [← integrable_norm_rpow_iff hm.aestronglyMeasurable hr0 hr]
  have heq : (fun x : E => ‖‖x‖ ^ s‖ ^ r.toReal) = fun x => ‖x‖ ^ (s * r.toReal) := by
    funext x
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg x) _), ← Real.rpow_mul (norm_nonneg x)]
  rw [heq]
  exact integrableOn_norm_rpow_ball hs

/-- On a bounded set, a function dominated by `C ‖x‖ ^ s` is `Lʳ` for every finite exponent `r`
with `-dim E < s r`. -/
theorem _root_.Bornology.IsBounded.memLp_of_norm_le_mul_norm_rpow {F : Type*}
    [NormedAddCommGroup F] {K : Set E} (hK : Bornology.IsBounded K) {f : E → F} {s C : ℝ}
    {r : ℝ≥0∞} (hr : r ≠ ∞) (hs : -(Module.finrank ℝ E : ℝ) < s * r.toReal)
    (hf : AEStronglyMeasurable f (mu.restrict K)) (hle : ∀ x, ‖f x‖ ≤ C * ‖x‖ ^ s) :
    MemLp f r (mu.restrict K) :=
  ((hK.memLp_norm_rpow_restrict hr hs).const_mul C).of_le hf <|
    Filter.Eventually.of_forall fun x => (hle x).trans (Real.le_norm_self _)

/-- On a bounded set, `‖x‖⁻¹` is `Lʳ` for every exponent `r < dim E`. -/
theorem _root_.Bornology.IsBounded.memLp_norm_inv_restrict {K : Set E}
    (hK : Bornology.IsBounded K) {r : ℝ≥0∞}
    (hr : r < Module.finrank ℝ E) : MemLp (fun x : E => ‖x‖⁻¹) r (mu.restrict K) := by
  have hrtop : r ≠ ∞ := (hr.trans_le le_top).ne
  have hlt : r.toReal < Module.finrank ℝ E := by
    simpa using (ENNReal.toReal_lt_toReal hrtop (by simp)).2 hr
  simpa only [Real.rpow_neg_one] using
    hK.memLp_norm_rpow_restrict (mu := mu) (s := -1) hrtop (by linarith)

/-- On a nontrivial space, `‖x‖⁻¹` is not `Lʳ` on a closed ball of positive radius about the
origin when `dim E ≤ r`. -/
theorem not_memLp_norm_inv_closedBall [Nontrivial E] {ε : ℝ} (hε : 0 < ε) {r : ℝ≥0∞}
    (hr : Module.finrank ℝ E ≤ r) :
    ¬ MemLp (fun x : E => ‖x‖⁻¹) r (mu.restrict (closedBall 0 ε)) := by
  intro h
  have : IsFiniteMeasure (mu.restrict (closedBall (0 : E) ε)) :=
    isFiniteMeasure_restrict.2 measure_closedBall_lt_top.ne
  have h2 := h.mono_exponent hr
  rw [← integrable_norm_rpow_iff (by fun_prop) (by simp [Module.finrank_pos.ne'])
    (by simp)] at h2
  have heq : (fun x : E => ‖‖x‖⁻¹‖ ^ (Module.finrank ℝ E : ℝ≥0∞).toReal) =
      fun x => ‖x‖ ^ (-(Module.finrank ℝ E : ℝ)) := by
    funext x
    rw [Real.norm_of_nonneg (inv_nonneg.2 (norm_nonneg x)), Real.inv_rpow (norm_nonneg x),
      Real.rpow_neg (norm_nonneg x), ENNReal.toReal_natCast]
  rw [heq] at h2
  have h3 : IntegrableOn (fun x : E => ‖x‖ ^ (-(Module.finrank ℝ E : ℝ))) (ball 0 ε) mu :=
    IntegrableOn.mono_set h2 ball_subset_closedBall
  exact lt_irrefl _ ((integrableOn_norm_rpow_ball_iff hε).1 h3)

end Inverse

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

/-- The translate of `memLp_div_pow_compl_closedBall_iff` to an arbitrary centre `c`. -/
theorem memLp_div_sub_pow_compl_closedBall_iff {a : ℂ} (ha : a ≠ 0) (c : ℂ) {R : ℝ}
    (hR : 0 < R) (m : ℕ) {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp_top : p ≠ ∞) :
    MemLp (fun z : ℂ => a/(z - c)^m) p (volume.restrict (closedBall c R)ᶜ) ↔
      2 < (m : ℝ)*p.toReal := by
  have hpres := (measurePreserving_add_right (volume : Measure ℂ) c).restrict_preimage
    (measurableSet_closedBall (x := c) (ε := R)).compl
  have hpre : (fun z : ℂ => z + c) ⁻¹' (closedBall c R)ᶜ = (closedBall 0 R)ᶜ := by
    ext z
    simp [mem_closedBall, dist_eq_norm]
  rw [hpre] at hpres
  rw [← hpres.map_eq, (measurableEmbedding_addRight c).memLp_map_measure_iff]
  simpa [Function.comp_def] using memLp_div_pow_compl_closedBall_iff ha hR m hp0 hp_top

end TauCeti

namespace MeasureTheory.Measure

open Metric Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A power of the distance to a point is not integrable for an additive Haar measure on a
nontrivial finite-dimensional space, for every real exponent: integrability near the point needs
`-finrank < p` and integrability away from it needs `p < -finrank`. -/
theorem not_integrable_norm_sub_rpow [Nontrivial E] (μ : Measure E) [μ.IsAddHaarMeasure]
    (p : ℝ) (b : E) : ¬ Integrable (fun x ↦ ‖x - b‖ ^ p) μ := fun hint ↦ by
  have h0 : Integrable (fun x : E ↦ ‖x‖ ^ p) μ :=
    ((measurePreserving_sub_right μ b).integrable_comp_emb
      (MeasurableEquiv.subRight b).measurableEmbedding).1 hint
  have h1 := (TauCeti.integrableOn_norm_rpow_ball_iff (E := E) (mu := μ) (s := p)
    (R := 1) one_pos).1 h0.integrableOn
  have h2 := (TauCeti.integrableOn_norm_rpow_compl_closedBall_iff (E := E) (mu := μ) (s := p)
    (R := 1) one_pos).1 h0.integrableOn
  linarith

end MeasureTheory.Measure
