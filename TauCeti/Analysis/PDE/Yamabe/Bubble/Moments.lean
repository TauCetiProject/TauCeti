/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Yamabe.Bubble.Energy
public import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Moment

/-!
# Moments of the Euclidean Yamabe bubbles

Let `U = U_{t,b}` be a Yamabe bubble on an `n`-dimensional real inner product space.  This file
computes the even moments of its critical density `U ^ pₙ` and of its Dirichlet-energy density
`|dU|²`.  For `t > 0`,

* the `2m`-th moment of `U ^ pₙ` is finite in the subcritical range `2m < n` and scales as
  `t ^ (2m)`;
* the `2m`-th moment of `|dU|²` is finite when `2m < n - 2`, and also scales as
  `t ^ (2m)`.

The displayed formulas retain the beta integral and the unit-ball volume.  This form makes both
the scale and the loss of integrability at the critical moment transparent.  In particular, the
fourth energy moment is covered in dimensions at least seven; its dimension-six endpoint is the
logarithmically divergent truncated moment and requires a separate estimate.

## Main declarations

* `TauCeti.Yamabe.integrable_norm_sub_sq_pow_mul_bubble_rpow_criticalExponent` and
  `TauCeti.Yamabe.integral_norm_sub_sq_pow_mul_bubble_rpow_criticalExponent`: even moments of the
  critical density.
* `TauCeti.Yamabe.integrable_norm_sub_sq_pow_mul_norm_fderiv_bubble_sq` and
  `TauCeti.Yamabe.integral_norm_sub_sq_pow_mul_norm_fderiv_bubble_sq`: even moments of the energy
  density.

## References

* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), §3 and
  §6.
* T. Aubin, *Problèmes isopérimétriques et espaces de Sobolev*, J. Differential Geom. 11
  (1976).
-/

public section

noncomputable section

namespace TauCeti.Yamabe

open InnerProductSpace MeasureTheory Metric Module ProbabilityTheory Real Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private lemma criticalMoment_profile (hn : finrank ℝ E ≠ 2) (m : ℕ) {t : ℝ} (ht : 0 < t)
    (b x : E) :
    (‖x - b‖ ^ 2) ^ m * bubble t b x ^ criticalExponent (finrank ℝ E) =
      ((2 * t) ^ finrank ℝ E * t ^ (2 * m) / t ^ (2 * finrank ℝ E)) *
        ((‖t⁻¹ • (x - b)‖ ^ 2) ^ m *
          (1 + ‖t⁻¹ • (x - b)‖ ^ 2) ^ (-(2 * (finrank ℝ E : ℝ)) / 2)) := by
  rw [bubble_rpow_criticalExponent hn ht]
  have hS : 0 < 1 + ‖t⁻¹ • (x - b)‖ ^ 2 := by positivity
  have hexponent : -(2 * (finrank ℝ E : ℝ)) / 2 = -(finrank ℝ E : ℝ) := by ring
  rw [hexponent, Real.rpow_neg hS.le, Real.rpow_natCast, norm_smul, norm_inv,
    Real.norm_of_nonneg ht.le]
  have hnorm : 1 + (t⁻¹ * ‖x - b‖) ^ 2 =
      (t ^ 2 + ‖x - b‖ ^ 2) / t ^ 2 := by
    field_simp
  have hscale : (t⁻¹ * ‖x - b‖) ^ 2 = ‖x - b‖ ^ 2 / t ^ 2 := by
    field_simp
  rw [hnorm, hscale, div_pow]
  field_simp
  rw [div_pow, div_pow]
  field_simp
  ring

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- In positive dimension `n ≠ 2`, the `2m`-th moment about the centre of the critical bubble
density is integrable when `2m < n`. -/
theorem integrable_norm_sub_sq_pow_mul_bubble_rpow_criticalExponent
    (μ : Measure E) [μ.IsAddHaarMeasure] (hn : finrank ℝ E ≠ 2) (m : ℕ)
    (hm : 2 * m < finrank ℝ E) {t : ℝ} (ht : 0 < t) (b : E) :
    Integrable (fun x ↦ (‖x - b‖ ^ 2) ^ m *
      bubble t b x ^ criticalExponent (finrank ℝ E)) μ := by
  have hmR : (2 * m : ℝ) < finrank ℝ E := by exact_mod_cast hm
  have hJ := integrable_norm_sq_pow_mul_rpow_neg_one_add_norm_sq μ m
    (r := 2 * (finrank ℝ E : ℝ)) (by linarith)
  have hscaled := (hJ.comp_smul (inv_ne_zero ht.ne')).const_mul
    ((2 * t) ^ finrank ℝ E * t ^ (2 * m) / t ^ (2 * finrank ℝ E))
  have htranslated := hscaled.comp_sub_right b
  exact htranslated.congr (.of_forall fun x ↦ (criticalMoment_profile hn m ht b x).symm)

/-- The `2m`-th moment about the centre of the critical bubble density.  Its dependence on the
scale is exactly `t ^ (2m)`. -/
theorem integral_norm_sub_sq_pow_mul_bubble_rpow_criticalExponent
    (hn : finrank ℝ E ≠ 2) (m : ℕ) (hm : 2 * m < finrank ℝ E) {t : ℝ} (ht : 0 < t)
    (b : E) :
    ∫ x, (‖x - b‖ ^ 2) ^ m * bubble t b x ^ criticalExponent (finrank ℝ E) =
      (finrank ℝ E : ℝ) * volume.real (ball (0 : E) 1) *
        (2 ^ (finrank ℝ E - 1) * t ^ (2 * m) *
          beta (((finrank ℝ E : ℝ) + 2 * m) / 2)
            (((finrank ℝ E : ℝ) - 2 * m) / 2)) := by
  let J : E → ℝ := fun z ↦ (‖z‖ ^ 2) ^ m *
    (1 + ‖z‖ ^ 2) ^ (-(2 * (finrank ℝ E : ℝ)) / 2)
  let C : ℝ := (2 * t) ^ finrank ℝ E * t ^ (2 * m) / t ^ (2 * finrank ℝ E)
  have hpoint (x : E) :
      (‖x - b‖ ^ 2) ^ m * bubble t b x ^ criticalExponent (finrank ℝ E) =
        C * J (t⁻¹ • (x - b)) := criticalMoment_profile hn m ht b x
  let _ : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  have hmR : (2 * m : ℝ) < finrank ℝ E := by exact_mod_cast hm
  rw [integral_congr_ae (.of_forall hpoint), integral_const_mul,
    integral_sub_right_eq_self (fun y ↦ J (t⁻¹ • y)) b,
    Measure.integral_comp_inv_smul_of_nonneg volume J ht.le,
    integral_norm_sq_pow_mul_rpow_neg_one_add_norm_sq m (r := 2 * (finrank ℝ E : ℝ))
      (by linarith), smul_eq_mul]
  dsimp only [C]
  have ht0 : t ≠ 0 := ht.ne'
  have hn0 : 0 < finrank ℝ E := by omega
  have hbeta_arg : 2 * (finrank ℝ E : ℝ) - finrank ℝ E - 2 * m =
      (finrank ℝ E : ℝ) - 2 * m := by ring
  rw [hbeta_arg]
  rw [mul_pow]
  field_simp
  have htwo_pow : (2 : ℝ) ^ finrank ℝ E = 2 * 2 ^ (finrank ℝ E - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ finrank ℝ E)]
  rw [htwo_pow]
  ring

/-- In dimension `n > 2`, the `2m`-th moment about the centre of the Dirichlet-energy density of
a bubble is integrable when `2m < n - 2`. -/
theorem integrable_norm_sub_sq_pow_mul_norm_fderiv_bubble_sq
    (μ : Measure E) [μ.IsAddHaarMeasure] (m : ℕ)
    (hm : 2 * m < finrank ℝ E - 2) {t : ℝ} (ht : 0 < t) (b : E) :
    Integrable (fun x ↦ (‖x - b‖ ^ 2) ^ m * ‖fderiv ℝ (bubble t b) x‖ ^ 2) μ := by
  have hn : 2 < finrank ℝ E := by omega
  have hm' : 2 * (m + 1) < finrank ℝ E := by omega
  have h :=
    (integrable_norm_sub_sq_pow_mul_bubble_rpow_criticalExponent
      μ hn.ne' (m + 1) hm' ht b).const_mul
      ((((finrank ℝ E : ℝ) - 2) / (2 * t)) ^ 2)
  refine h.congr (.of_forall fun x ↦ ?_)
  dsimp only
  rw [norm_fderiv_bubble_sq ht, ← bubble_rpow_criticalExponent hn.ne' ht b x]
  ring

/-- The `2m`-th moment about the centre of the Dirichlet-energy density of a bubble.  It scales as
`t ^ (2m)`; the excluded endpoint `2m = n - 2` is the logarithmic case. -/
theorem integral_norm_sub_sq_pow_mul_norm_fderiv_bubble_sq
    (m : ℕ) (hm : 2 * m < finrank ℝ E - 2) {t : ℝ}
    (ht : 0 < t) (b : E) :
    ∫ x, (‖x - b‖ ^ 2) ^ m * ‖fderiv ℝ (bubble t b) x‖ ^ 2 =
      ((finrank ℝ E : ℝ) - 2) ^ 2 * (finrank ℝ E : ℝ) *
        volume.real (ball (0 : E) 1) *
          (2 ^ (finrank ℝ E - 3) * t ^ (2 * m) *
            beta (((finrank ℝ E : ℝ) + 2 * m + 2) / 2)
              (((finrank ℝ E : ℝ) - 2 * m - 2) / 2)) := by
  have hn : 2 < finrank ℝ E := by omega
  have hm' : 2 * (m + 1) < finrank ℝ E := by omega
  have henergy : (∫ x, (‖x - b‖ ^ 2) ^ m * ‖fderiv ℝ (bubble t b) x‖ ^ 2) =
      (((finrank ℝ E : ℝ) - 2) / (2 * t)) ^ 2 *
      ∫ x, (‖x - b‖ ^ 2) ^ (m + 1) *
        bubble t b x ^ criticalExponent (finrank ℝ E) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (.of_forall fun x ↦ ?_)
    dsimp only
    rw [norm_fderiv_bubble_sq ht, ← bubble_rpow_criticalExponent hn.ne' ht b x]
    ring
  rw [henergy,
    integral_norm_sub_sq_pow_mul_bubble_rpow_criticalExponent hn.ne' (m + 1) hm' ht b]
  have ht0 : t ≠ 0 := ht.ne'
  have hbeta₁ : ((finrank ℝ E : ℝ) + 2 * (m + 1)) / 2 =
      ((finrank ℝ E : ℝ) + 2 * m + 2) / 2 := by
    ring
  have hbeta₂ : ((finrank ℝ E : ℝ) - 2 * (m + 1)) / 2 =
      ((finrank ℝ E : ℝ) - 2 * m - 2) / 2 := by
    ring
  have hm_succ : 2 * (m + 1) = 2 * m + 2 := by ring
  rw [hm_succ]
  simp only [Nat.cast_add, Nat.cast_one]
  have hpow_index : finrank ℝ E - 1 = (finrank ℝ E - 3) + 2 := by omega
  rw [hbeta₁, hbeta₂, hpow_index, pow_add]
  field_simp
  ring

end TauCeti.Yamabe
