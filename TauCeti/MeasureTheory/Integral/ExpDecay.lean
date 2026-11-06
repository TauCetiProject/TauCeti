/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Prod
import TauCeti.MeasureTheory.Integral.Bochner.Basic

/-!
# Exponential integrals on the real line and radial exponentials

This file records integrability and evaluation of exponential integrands: on a half-line or the
whole real line, natural powers multiplied by an exponentially decaying factor, the exact rate at
which a bare exponential is integrable on a right half-line, and integrability of the two-sided
exponential; and, on a finite-dimensional real normed space, integrability of the radial
exponential `exp (-a ‖x‖)` for every additive Haar measure, by integrating in polar coordinates.

Mathlib supplies the *sufficient* direction of the right-half-line integrability criterion,
`integrableOn_exp_mul_Ioi`, for a negative rate.  `integrableOn_exp_mul_Ioi_iff` adds the converse,
which is what lets a caller describe an exponential-moment domain as an exact set rather than an
inclusion.

## Main results

* `TauCeti.integrableOn_pow_mul_exp_neg_mul_Ioi`: integrability on `(0, ∞)`.
* `TauCeti.integral_pow_mul_exp_neg_mul_Ioi`: evaluation in terms of a factorial.
* `TauCeti.lintegral_ofReal_exp_neg_mul_mul_lintegral`: an iterated exponential integral is a
  Stieltjes-kernel integral.
* `TauCeti.integrableOn_exp_mul_Ioi_iff`: `exp (a * ·)` is integrable on `(c, ∞)` exactly when
  `a < 0`.
* `TauCeti.integrableOn_exp_mul_Iic_iff`: `exp (a * ·)` is integrable on `(-∞, c]` exactly when
  `0 < a`.
* `TauCeti.integrable_exp_neg_mul_abs`: `exp (-(a * |·|))` is integrable when `0 < a`.
* `TauCeti.memLp_exp_neg_mul_abs`: `exp (-(a * |·|))` lies in every `Lᵖ` when `0 < a`.
* `TauCeti.integrable_exp_mul_I_mul_exp_neg_mul_abs`: the same times the oscillation
  `exp (b * x * I)`.
* `TauCeti.integrable_exp_neg_mul_norm`: `exp (-(a * ‖·‖))` is integrable on a finite-dimensional
  space when `0 < a`.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace TauCeti

/-- Natural powers times an exponentially decaying factor are integrable on `(0, ∞)`. -/
theorem integrableOn_pow_mul_exp_neg_mul_Ioi (n : ℕ) {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => t ^ n * Real.exp (-(b * t))) (Set.Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := (1 : ℝ)) (s := (n : ℝ)) (b := b)
    (lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg n)) one_pos hb
  simpa only [Real.rpow_one, Real.rpow_natCast, neg_mul] using h

/-- The integral of a natural power times an exponentially decaying factor on `(0, ∞)`. -/
theorem integral_pow_mul_exp_neg_mul_Ioi (n : ℕ) {a : ℝ} (ha : 0 < a) :
    ∫ t : ℝ in Set.Ioi 0, t ^ n * Real.exp (-(a * t)) = n.factorial / a ^ (n + 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := ((n + 1 : ℕ) : ℝ)) (r := a) (by positivity) ha
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right,
    Real.Gamma_nat_eq_factorial] at h
  have hcast : (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) := by norm_num
  rw [hcast, Real.rpow_natCast] at h
  have h' : ∫ t : ℝ in Set.Ioi 0, t ^ n * Real.exp (-(a * t)) =
      (1 / a) ^ (n + 1) * n.factorial := by
    rw [← h]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t _
    dsimp
    rw [Real.rpow_natCast t n]
  rw [h', one_div, div_eq_mul_inv, inv_pow]
  ring

/-- **The Stieltjes kernel is an iterated exponential integral.** Swapping the two integrations
turns the outer Laplace integral of the inner one into the Stieltjes integral of `ν`. -/
theorem lintegral_ofReal_exp_neg_mul_mul_lintegral (ν : Measure ℝ≥0) [SFinite ν] {t : ℝ}
    (ht : 0 < t) :
    ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(t * s))) *
        ∫⁻ x : ℝ≥0, ENNReal.ofReal (Real.exp (-(s * (x : ℝ)))) ∂ν
      = ∫⁻ x : ℝ≥0, ENNReal.ofReal (t + (x : ℝ))⁻¹ ∂ν := by
  have hmeas : AEMeasurable (Function.uncurry fun (s : ℝ) (x : ℝ≥0) =>
      ENNReal.ofReal (Real.exp (-((t + (x : ℝ)) * s))))
      ((volume.restrict (Ioi (0 : ℝ))).prod ν) := by
    refine Measurable.aemeasurable ?_
    simp only [Function.uncurry_def]
    fun_prop
  calc
    ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(t * s))) *
          ∫⁻ x : ℝ≥0, ENNReal.ofReal (Real.exp (-(s * (x : ℝ)))) ∂ν
        = ∫⁻ s in Ioi (0 : ℝ), ∫⁻ x : ℝ≥0,
            ENNReal.ofReal (Real.exp (-((t + (x : ℝ)) * s))) ∂ν := by
          refine lintegral_congr fun s => ?_
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          refine lintegral_congr fun x => ?_
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
          congr 2
          ring
    _ = ∫⁻ x : ℝ≥0, (∫⁻ s in Ioi (0 : ℝ),
          ENNReal.ofReal (Real.exp (-((t + (x : ℝ)) * s)))) ∂ν := lintegral_lintegral_swap hmeas
    _ = ∫⁻ x : ℝ≥0, ENNReal.ofReal (t + (x : ℝ))⁻¹ ∂ν := by
          refine lintegral_congr fun x => ?_
          have htx : 0 < t + (x : ℝ) := add_pos_of_pos_of_nonneg ht x.coe_nonneg
          have hint : IntegrableOn
              (fun s : ℝ => Real.exp (-((t + (x : ℝ)) * s))) (Ioi 0) := by
            simpa only [pow_zero, one_mul] using
              integrableOn_pow_mul_exp_neg_mul_Ioi 0 htx
          rw [← ofReal_integral_eq_lintegral_ofReal hint
            (.of_forall fun s => (Real.exp_pos _).le)]
          simpa using congrArg ENNReal.ofReal
            (integral_pow_mul_exp_neg_mul_Ioi 0 htx)

/-- The radial exponential `exp (-(a * ‖x‖))` is integrable for every additive Haar measure on a
finite-dimensional real normed space, when `0 < a`. -/
theorem integrable_exp_neg_mul_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : E ↦ Real.exp (-(a * ‖x‖))) μ := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · have : CompactSpace E := Finite.compactSpace
    exact (integrable_const (1 : ℝ)).congr (.of_forall fun x ↦ by simp [Subsingleton.elim x 0])
  · refine (integrable_fun_norm_addHaar μ (f := fun t ↦ Real.exp (-(a * t)))).mpr ?_
    simpa only [smul_eq_mul] using integrableOn_pow_mul_exp_neg_mul_Ioi _ ha

/-- The two-sided exponential is integrable on the line. -/
theorem integrable_exp_neg_mul_abs {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : ℝ ↦ Real.exp (-(a * |x|))) := by
  simpa only [neg_mul] using MeasureTheory.integrable_comp_abs
    (integrableOn_exp_mul_Ioi (a := -a) (by linarith) 0)

/-- The two-sided exponential lies in every `Lᵖ` space on the line. -/
theorem memLp_exp_neg_mul_abs {a : ℝ} (ha : 0 < a) (p : ℝ≥0∞) :
    MemLp (fun x : ℝ ↦ Real.exp (-(a * |x|))) p := by
  have hmeas : AEStronglyMeasurable (fun x : ℝ ↦ Real.exp (-(a * |x|))) :=
    (by fun_prop : Continuous fun x : ℝ ↦ Real.exp (-(a * |x|))).aestronglyMeasurable
  rcases eq_or_ne p 0 with rfl | hp₀
  · exact memLp_zero_iff_aestronglyMeasurable.2 hmeas
  rcases eq_or_ne p ∞ with rfl | hp
  · refine memLp_top_of_bound hmeas 1 (.of_forall fun x ↦ ?_)
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff, neg_nonpos]
    positivity
  refine (memLp_norm_rpow_iff hmeas hp₀ hp).1 ?_
  rw [ENNReal.div_self hp₀ hp, memLp_one_iff_integrable]
  refine (integrable_exp_neg_mul_abs (mul_pos ha (ENNReal.toReal_pos hp₀ hp))).congr
    (.of_forall fun x ↦ ?_)
  dsimp only
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, ← Real.exp_mul]
  ring_nf

/-- The two-sided exponential times a unimodular oscillation `exp (b * x * I)` is integrable on
the line. -/
theorem integrable_exp_mul_I_mul_exp_neg_mul_abs {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Integrable
      (fun x : ℝ ↦ Complex.exp ((b : ℂ) * x * Complex.I) * (Real.exp (-(a * |x|)) : ℂ)) :=
  ((integrable_exp_neg_mul_abs ha).ofReal).bdd_mul (c := 1) (by fun_prop)
    (.of_forall fun x ↦ by simp [Complex.norm_exp])


/-- At a nonnegative rate the integrand is bounded below by a positive constant on `(c, ∞)`, a set
of infinite measure, so it is not integrable there. -/
private theorem not_integrableOn_exp_mul_Ioi {a c : ℝ} (ha : 0 ≤ a) :
    ¬ IntegrableOn (fun x : ℝ => Real.exp (a * x)) (Set.Ioi c) := by
  intro h
  have hsub : Set.Ioi c ⊆ {x : ℝ | Real.exp (a * c) ≤ Real.exp (a * x)} := by
    intro x hx
    exact Real.exp_le_exp.2 (by nlinarith [le_of_lt (Set.mem_Ioi.mp hx)])
  have h1 : (volume.restrict (Set.Ioi c)) (Set.Ioi c) < ⊤ :=
    lt_of_le_of_lt (measure_mono hsub) (h.measure_ge_lt_top (Real.exp_pos (a * c)))
  rw [Measure.restrict_apply_self, Real.volume_Ioi] at h1
  exact absurd h1 (by simp)

/-- **The exact integrability rate.**  `fun x => exp (a * x)` is integrable on `(c, ∞)` precisely
when the rate is negative.  Mathlib's `integrableOn_exp_mul_Ioi` is the `←` direction. -/
@[simp]
theorem integrableOn_exp_mul_Ioi_iff {a c : ℝ} :
    IntegrableOn (fun x : ℝ => Real.exp (a * x)) (Set.Ioi c) ↔ a < 0 := by
  refine ⟨fun h => ?_, fun ha => integrableOn_exp_mul_Ioi ha c⟩
  by_contra hne
  exact not_integrableOn_exp_mul_Ioi (not_lt.mp hne) h

/-- **The exact integrability rate on a left half-line.** `fun x => exp (a * x)` is integrable
on `(-∞, c]` precisely when the rate is positive. -/
@[simp]
theorem integrableOn_exp_mul_Iic_iff {a c : ℝ} :
    IntegrableOn (fun x : ℝ => Real.exp (a * x)) (Set.Iic c) ↔ 0 < a := by
  rw [integrableOn_Iic_iff_integrableOn_Iio,
    ← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding]
  simpa only [Function.comp_def, neg_preimage, neg_Iio, neg_neg, mul_neg, neg_mul,
    neg_lt_zero] using (integrableOn_exp_mul_Ioi_iff (a := -a) (c := -c))

end TauCeti
