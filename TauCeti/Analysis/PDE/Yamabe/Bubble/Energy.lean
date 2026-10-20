/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Yamabe.Bubble.Moments
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Function.L2Space
import TauCeti.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Gradient, integrability and energy of the Yamabe bubbles

Let `E` be a real inner product space of dimension `n > 2`, and let
`U = U_{t,b}`, `U(x) = (2 t / (t² + ‖x - b‖²)) ^ ((n - 2) / 2)`, be the bubble of scale `t > 0`
centred at `b` (`TauCeti.Yamabe.bubble`). With `aₙ = 4 (n - 1) / (n - 2)` and
`pₙ = 2 n / (n - 2)`, this file proves:

* `U ∈ L^{pₙ}` and `dU ∈ L²` for every additive Haar measure, with
  `U ^ pₙ = (2 t / (t² + ‖x - b‖²)) ^ n`;
* the **energy identity** `aₙ ∫ ‖dU‖² = n (n - 1) ∫ U ^ pₙ`, again for every additive Haar
  measure;
* the value `∫ U ^ pₙ = 2 π ^ ((n + 1) / 2) / Γ((n + 1) / 2)` for Lebesgue measure.

The integrability of `U ^ pₙ` and its value hold more generally in every positive dimension
`n ≠ 2`, including `n = 1`.

The value is the classical surface area `|Sⁿ|` of the unit sphere `Sⁿ ⊆ ℝⁿ⁺¹`, as it must be,
since `U ^ (4 / (n - 2))` times the Euclidean metric is the pullback of the round metric of `Sⁿ`;
neither the sphere nor the stereographic projection is formalized here. Classically, the two
identities together say that `aₙ ∫ ‖dU‖² = n (n - 1) |Sⁿ|`, so that the Sobolev quotient of `U`
is `n (n - 1) |Sⁿ| ^ (2 / n)`, the Yamabe invariant of the round sphere; this is the equality case
of the sharp Euclidean Sobolev inequality, which is not proved here.

The energy identity is proved in polar coordinates. Both integrands are radial about `b`, and
the radial integrals are related by integrating the derivative of
`r ↦ r ^ n (t² + r²) (2 t / (t² + r²)) ^ n`, which vanishes at `0` and at infinity exactly
because `n > 2`. This gives the energy identity directly, without a whole-space integration by
parts. The integrability of `U ^ pₙ` and `‖dU‖²` and the value of `∫ U ^ pₙ` are the moments of
order `0` of `TauCeti.Analysis.PDE.Yamabe.Bubble.Moments`; the value then follows from Legendre's
duplication formula.

## Main declarations

* `TauCeti.Yamabe.memLp_bubble`, `TauCeti.Yamabe.memLp_fderiv_bubble`: `U ∈ L^{pₙ}`, `dU ∈ L²`.
* `TauCeti.Yamabe.conformalCoefficient_mul_integral_norm_fderiv_bubble_sq`: the energy identity.
* `TauCeti.Yamabe.integral_bubble_rpow_criticalExponent`: the value of `∫ U ^ pₙ`.

## References

* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), §3.
* T. Aubin, *Problèmes isopérimétriques et espaces de Sobolev*, J. Differential Geom. 11 (1976).
-/

public section

noncomputable section

namespace TauCeti.Yamabe

open Filter InnerProductSpace MeasureTheory Metric Module Real Set Topology
open scoped Gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

/-- In every positive dimension `n ≠ 2`, the critical power `U_{t,b} ^ pₙ` of a bubble is
integrable for every additive Haar measure. -/
theorem integrable_bubble_rpow_criticalExponent (hn₀ : 0 < finrank ℝ E) (hn : finrank ℝ E ≠ 2)
    {t : ℝ} (ht : 0 < t) (b : E) :
    Integrable (fun x ↦ bubble t b x ^ criticalExponent (finrank ℝ E)) μ := by
  simpa using integrable_norm_sub_rpow_mul_bubble_rpow_criticalExponent μ hn le_rfl
    (by exact_mod_cast hn₀) ht b

/-- In dimension `n > 2`, the squared norm of the differential of a bubble is integrable for
every additive Haar measure. -/
theorem integrable_norm_fderiv_bubble_sq (hn : 2 < finrank ℝ E) {t : ℝ} (ht : 0 < t) (b : E) :
    Integrable (fun x ↦ ‖fderiv ℝ (bubble t b) x‖ ^ 2) μ := by
  have hn' : (2 : ℝ) < finrank ℝ E := by exact_mod_cast hn
  simpa using integrable_norm_sub_rpow_mul_norm_fderiv_bubble_sq μ le_rfl
    (by linarith) ht b

/-- In dimension `n > 2`, a bubble lies in `L^{pₙ}` for every additive Haar measure. -/
theorem memLp_bubble (hn : 2 < finrank ℝ E) {t : ℝ} (ht : 0 < t) (b : E) :
    MemLp (bubble t b) (ENNReal.ofReal (criticalExponent (finrank ℝ E))) μ := by
  have hp : 0 < criticalExponent (finrank ℝ E) := by
    have : (2 : ℝ) < finrank ℝ E := by exact_mod_cast hn
    rw [criticalExponent_def]
    exact div_pos (by linarith) (by linarith)
  refine (integrable_norm_rpow_iff
    (contDiff_bubble (m := 0) ht.ne' b).continuous.aestronglyMeasurable
    (by simpa using hp) ENNReal.ofReal_ne_top).mp ?_
  rw [ENNReal.toReal_ofReal hp.le]
  refine (integrable_bubble_rpow_criticalExponent μ (by omega) hn.ne' ht b).congr
    (.of_forall fun x ↦ ?_)
  simp only [Real.norm_of_nonneg (bubble_pos ht b x).le]

/-- In dimension `n > 2`, the differential of a bubble lies in `L²` for every additive Haar
measure. -/
theorem memLp_fderiv_bubble (hn : 2 < finrank ℝ E) {t : ℝ} (ht : 0 < t) (b : E) :
    MemLp (fderiv ℝ (bubble t b)) 2 μ :=
  (memLp_two_iff_integrable_sq_norm ((contDiff_bubble (m := 1) ht.ne' b).continuous_fderiv
    one_ne_zero).aestronglyMeasurable).mpr (integrable_norm_fderiv_bubble_sq μ hn ht b)

/-- **The energy identity of a bubble**: in dimension `n > 2`,
`aₙ ∫ ‖dU_{t,b}‖² = n (n - 1) ∫ U_{t,b} ^ pₙ` for every additive Haar measure. -/
theorem conformalCoefficient_mul_integral_norm_fderiv_bubble_sq (hn : 2 < finrank ℝ E) {t : ℝ}
    (ht : 0 < t) (b : E) :
    conformalCoefficient (finrank ℝ E) * ∫ x, ‖fderiv ℝ (bubble t b) x‖ ^ 2 ∂μ =
      (finrank ℝ E : ℝ) * (finrank ℝ E - 1) *
        ∫ x, bubble t b x ^ criticalExponent (finrank ℝ E) ∂μ := by
  -- Translate `b` to the origin, pass to polar coordinates, and compare the two radial integrals
  -- with `sub_two_mul_integral_radial`.
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  set n := finrank ℝ E with hn_def
  -- Both integrands are radial about `b`, with profiles `φ` and `ψ`.
  set ψ : ℝ → ℝ := fun r ↦ (2 * t / (t ^ 2 + r ^ 2)) ^ n
  set C : ℝ := (((n : ℝ) - 2) / (2 * t)) ^ 2 with hC
  set φ : ℝ → ℝ := fun r ↦ C * (r ^ 2 * ψ r) with hφ
  have hgrad (b : E) : (fun x ↦ ‖fderiv ℝ (bubble t b) x‖ ^ 2) = fun x ↦ φ ‖x - b‖ := by
    funext x
    rw [norm_fderiv_bubble_sq ht, ← hn_def]
    ring
  have hpow (b : E) : (fun x ↦ bubble t b x ^ criticalExponent n) = fun x ↦ ψ ‖x - b‖ := by
    funext x
    exact bubble_rpow_criticalExponent hn.ne' ht b x
  -- The radial profiles are integrable, by integrability on `E` of the bubble centred at `0`.
  have hC0 : C ≠ 0 := by
    have : (n : ℝ) - 2 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hn.ne')
    positivity
  have h₁ : IntegrableOn (fun r : ℝ ↦ r ^ (n - 1) * ψ r) (Ioi 0) := by
    have h := integrable_bubble_rpow_criticalExponent μ (by omega) hn.ne' ht 0
    rw [hpow 0] at h
    simp only [sub_zero] at h
    simpa using (integrable_fun_norm_addHaar μ (f := ψ)).mp h
  have h₂ : IntegrableOn (fun r : ℝ ↦ r ^ (n - 1) * (r ^ 2 * ψ r)) (Ioi 0) := by
    have h := integrable_norm_fderiv_bubble_sq μ hn ht 0
    rw [hgrad 0] at h
    simp only [sub_zero] at h
    refine IntegrableOn.congr_fun (((integrable_fun_norm_addHaar μ (f := φ)).mp h).const_mul C⁻¹)
      (fun r _ ↦ ?_) measurableSet_Ioi
    simp only [hφ, smul_eq_mul, ← hn_def]
    field_simp
  have hrad : ((n : ℝ) - 2) * ∫ r in Ioi 0, r ^ (n - 1) * (r ^ 2 * ψ r) =
      n * t ^ 2 * ∫ r in Ioi 0, r ^ (n - 1) * ψ r :=
    sub_two_mul_integral_radial hn ht h₁ h₂
  have hI₂ : ∫ r in Ioi (0 : ℝ), r ^ (n - 1) • φ r =
      C * ∫ r in Ioi (0 : ℝ), r ^ (n - 1) * (r ^ 2 * ψ r) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun r _ ↦ ?_
    simp only [hφ, smul_eq_mul]
    ring
  have hφb := integral_sub_right_eq_self (μ := μ) (fun y ↦ φ ‖y‖) b
  have hψb := integral_sub_right_eq_self (μ := μ) (fun y ↦ ψ ‖y‖) b
  rw [hgrad b, hpow b, hφb, hψb, integral_fun_norm_addHaar μ φ, integral_fun_norm_addHaar μ ψ,
    ← hn_def, hI₂]
  have haC : conformalCoefficient n * C = ((n : ℝ) - 1) * ((n : ℝ) - 2) / t ^ 2 := by
    have : (n : ℝ) - 2 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hn.ne')
    rw [conformalCoefficient_def, hC]
    field_simp
    ring
  simp only [nsmul_eq_mul, smul_eq_mul]
  calc conformalCoefficient n * (n * (μ.real (ball 0 1) *
        (C * ∫ r in Ioi (0 : ℝ), r ^ (n - 1) * (r ^ 2 * ψ r)))) =
      ((n : ℝ) - 1) / t ^ 2 * n * μ.real (ball 0 1) *
        (((n : ℝ) - 2) * ∫ r in Ioi (0 : ℝ), r ^ (n - 1) * (r ^ 2 * ψ r)) := by
        linear_combination (n * μ.real (ball 0 1) *
          ∫ r in Ioi (0 : ℝ), r ^ (n - 1) * (r ^ 2 * ψ r)) * haC
    _ = _ := by
      rw [hrad]
      field_simp

/-- **The critical norm of a bubble**: in every positive dimension `n ≠ 2`, for Lebesgue measure,
`∫ U_{t,b} ^ pₙ = 2 π ^ ((n + 1) / 2) / Γ((n + 1) / 2)`, independently of the scale and the
centre. The right-hand side is the classical surface area of the unit sphere `Sⁿ ⊆ ℝⁿ⁺¹`. -/
theorem integral_bubble_rpow_criticalExponent (hn₀ : 0 < finrank ℝ E) (hn : finrank ℝ E ≠ 2)
    {t : ℝ} (ht : 0 < t) (b : E) :
    ∫ x, bubble t b x ^ criticalExponent (finrank ℝ E) =
      2 * π ^ (((finrank ℝ E : ℝ) + 1) / 2) / Gamma (((finrank ℝ E : ℝ) + 1) / 2) := by
  set n := finrank ℝ E with hn_def
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn₀
  -- This is the moment of order `0`, a beta integral.
  have hmoment := integral_norm_sub_rpow_mul_bubble_rpow_criticalExponent volume hn le_rfl hn0 ht b
  simp only [Real.rpow_zero, one_mul, add_zero, sub_zero, mul_one] at hmoment
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) hn₀
  have hΓhalf := Gamma_pos_of_pos (half_pos hn0)
  rw [hmoment, volume_real_unitBall, ProbabilityTheory.beta, ← hn_def, add_halves,
    Gamma_add_one (half_pos hn0).ne']
  -- Legendre's duplication formula at `n / 2`.
  have hdup := Real.Gamma_mul_Gamma_add_half ((n : ℝ) / 2)
  rw [show 2 * ((n : ℝ) / 2) = n by ring, show (n : ℝ) / 2 + 1 / 2 = (n + 1) / 2 by ring] at hdup
  have h2 : (2 : ℝ) ^ n * 2 ^ (1 - (n : ℝ)) = 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add two_pos]
    ring_nf
    exact Real.rpow_one 2
  have hπ : π ^ ((n : ℝ) / 2) * √π = π ^ (((n : ℝ) + 1) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add pi_pos]
    ring_nf
  have hΓn := Gamma_pos_of_pos hn0
  have hΓ := Gamma_pos_of_pos (show 0 < ((n : ℝ) + 1) / 2 by positivity)
  have htwo_pow : (2 : ℝ) ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hn₀]
  calc (n : ℝ) * (π ^ ((n : ℝ) / 2) / ((n : ℝ) / 2 * Gamma (n / 2))) *
        (2 ^ (n - 1) * (Gamma (n / 2) * Gamma (n / 2) / Gamma n)) =
      2 ^ n * π ^ ((n : ℝ) / 2) * Gamma (n / 2) / Gamma n := by
        rw [htwo_pow]
        field_simp
    _ = _ := by
      rw [div_eq_div_iff hΓn.ne' hΓ.ne']
      linear_combination (2 ^ n * π ^ ((n : ℝ) / 2)) * hdup +
        (Gamma n * π ^ ((n : ℝ) / 2) * √π) * h2 + (2 * Gamma n) * hπ

end TauCeti.Yamabe
