/-
Copyright (c) 2026 Tau Ceti Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.HalfStudentT.Basic
import TauCeti.Probability.Distributions.BetaPrime.Moments
import TauCeti.Probability.Distributions.StudentT.Moments
import TauCeti.Probability.Moments.IntegrableExpMul

/-!
# Moments of half-Student t laws

A half-Student t variable with degree `ν` and scale `s` has a finite real-power moment
exactly for `-1 < q < ν`. The lower bound comes from the positive density near zero,
and the upper bound from its polynomial tail. This file computes these moments, the mean
and variance on their finite ranges, and the exact exponential-integrability domain `Iic 0`.
Degree one specializes to the half-Cauchy law, which has no finite mean.

The square of a Student t variable has an F law. Rescaling this identity identifies the
half-Student t law as a square-root image of a beta-prime law, so its sharp real-power
moment theory follows from the existing beta-prime moments.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  second edition, Wiley, 1995, chapter 28.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set

namespace TauCeti.Probability

variable {ν s q t : ℝ}

private theorem sqrt_rpow_ae_betaPrimeMeasure (hν : 0 < ν) (hs : 0 < s) (q : ℝ) :
    (fun x : ℝ ↦ (s * √(ν * x)) ^ q) =ᵐ[betaPrimeMeasure (1 / 2) (ν / 2)]
      fun x ↦ (s ^ q * ν ^ (q / 2)) * x ^ (q / 2) := by
  filter_upwards [ae_mem_Ioi_betaPrimeMeasure (1 / 2) (ν / 2)] with x hx
  rw [mul_rpow hs.le (sqrt_nonneg _), ← rpow_div_two_eq_sqrt q (mul_pos hν hx).le,
    mul_rpow hν.le hx.le, mul_assoc]

/-- Real powers of a half-Student t variable are integrable exactly between the zero and
tail thresholds. Both endpoints are excluded. -/
@[simp]
theorem integrable_rpow_halfStudentTMeasure_iff (hν : 0 < ν) (hs : 0 < s) (q : ℝ) :
    Integrable (fun x : ℝ ↦ x ^ q) (halfStudentTMeasure ν s) ↔ -1 < q ∧ q < ν := by
  rw [halfStudentTMeasure_eq_map_betaPrimeMeasure hν hs,
    integrable_map_measure (by fun_prop) (by fun_prop)]
  simp only [Function.comp_def]
  rw [integrable_congr (sqrt_rpow_ae_betaPrimeMeasure hν hs q),
    integrable_const_mul_iff (isUnit_iff_ne_zero.2
      (mul_pos (rpow_pos_of_pos hs q) (rpow_pos_of_pos hν (q / 2))).ne'),
    integrable_rpow_betaPrimeMeasure_iff one_half_pos (half_pos hν)]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

/-- The real-power moments of a half-Student t law on their exact integrability range. -/
@[simp]
theorem integral_rpow_halfStudentTMeasure (hν : 0 < ν) (hs : 0 < s)
    (hq₀ : -1 < q) (hqν : q < ν) :
    ∫ x, x ^ q ∂halfStudentTMeasure ν s =
      s ^ q * ν ^ (q / 2) * Real.Gamma ((q + 1) / 2) * Real.Gamma ((ν - q) / 2) /
        (√π * Real.Gamma (ν / 2)) := by
  rw [halfStudentTMeasure_eq_map_betaPrimeMeasure hν hs,
    integral_map (by fun_prop) (by fun_prop),
    integral_congr_ae (sqrt_rpow_ae_betaPrimeMeasure hν hs q), integral_const_mul,
    integral_rpow_betaPrimeMeasure one_half_pos (half_pos hν) (by linarith) (by linarith)]
  have hsum : 1 / 2 + q / 2 + (ν / 2 - q / 2) = (ν + 1) / 2 := by ring
  have hsum' : 1 / 2 + ν / 2 = (ν + 1) / 2 := by ring
  have hG : Real.Gamma ((ν + 1) / 2) ≠ 0 :=
    (Gamma_pos_of_pos (by positivity)).ne'
  have hshape : 1 / 2 + q / 2 = (q + 1) / 2 := by ring
  have htail : ν / 2 - q / 2 = (ν - q) / 2 := by ring
  simp only [beta, hsum, hsum', Gamma_one_half_eq]
  rw [hshape, htail]
  field_simp

/-- A natural moment of a half-Student t law exists exactly below its degree. -/
@[simp]
theorem integrable_pow_halfStudentTMeasure_iff (hν : 0 < ν) (hs : 0 < s) (n : ℕ) :
    Integrable (fun x : ℝ ↦ x ^ n) (halfStudentTMeasure ν s) ↔ (n : ℝ) < ν := by
  have hn : -1 < (n : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) n]
  simpa only [rpow_natCast, and_iff_right hn] using
    integrable_rpow_halfStudentTMeasure_iff hν hs (n : ℝ)

/-- Natural moments, including order zero, on their finite range. -/
theorem integral_pow_halfStudentTMeasure (hν : 0 < ν) (hs : 0 < s) (n : ℕ)
    (hn : (n : ℝ) < ν) :
    ∫ x, x ^ n ∂halfStudentTMeasure ν s =
      s ^ n * ν ^ ((n : ℝ) / 2) * Real.Gamma (((n : ℝ) + 1) / 2) *
        Real.Gamma ((ν - n) / 2) / (√π * Real.Gamma (ν / 2)) := by
  simpa only [rpow_natCast] using integral_rpow_halfStudentTMeasure hν hs
    (q := (n : ℝ)) (by linarith [Nat.cast_nonneg (α := ℝ) n]) hn

/-- The mean of a half-Student t law exists exactly above degree one. -/
@[simp]
theorem integrable_id_halfStudentTMeasure_iff (hν : 0 < ν) (hs : 0 < s) :
    Integrable id (halfStudentTMeasure ν s) ↔ 1 < ν := by
  simpa only [pow_one, Nat.cast_one, Function.id_def] using
    integrable_pow_halfStudentTMeasure_iff hν hs 1

/-- The half-Cauchy law at positive scale has no finite mean. -/
theorem not_integrable_id_halfCauchyMeasure (hs : 0 < s) :
    ¬ Integrable id (halfCauchyMeasure s) := by
  simp [halfCauchyMeasure, integrable_id_halfStudentTMeasure_iff one_pos hs]

/-- The mean of a half-Student t law when its degree exceeds one. -/
@[simp]
theorem integral_id_halfStudentTMeasure (hν : 1 < ν) (hs : 0 < s) :
    ∫ x, x ∂halfStudentTMeasure ν s =
      s * √ν * Real.Gamma ((ν - 1) / 2) / (√π * Real.Gamma (ν / 2)) := by
  have hshape : ((1 : ℝ) + 1) / 2 = 1 := by norm_num
  simpa only [rpow_one, hshape, Gamma_one, mul_one, ← sqrt_eq_rpow] using
    integral_rpow_halfStudentTMeasure (zero_lt_one.trans hν) hs (q := 1) (by norm_num) hν

/-- The second raw moment of a half-Student t law when its degree exceeds two. -/
@[simp]
theorem integral_sq_halfStudentTMeasure (hν : 2 < ν) (hs : 0 < s) :
    ∫ x, x ^ 2 ∂halfStudentTMeasure ν s = s ^ 2 * ν / (ν - 2) := by
  rw [halfStudentTMeasure_of_pos (zero_lt_two.trans hν) hs,
    integral_map (by fun_prop) (by fun_prop)]
  simp only [mul_pow, sq_abs]
  rw [integral_const_mul, integral_sq_studentTMeasure hν, mul_div_assoc]

/-- The variance of a half-Student t law when its second moment exists. -/
@[simp]
theorem variance_id_halfStudentTMeasure (hν : 2 < ν) (hs : 0 < s) :
    variance id (halfStudentTMeasure ν s) = s ^ 2 *
      (ν / (ν - 2) - ν / π *
        (Real.Gamma ((ν - 1) / 2) / Real.Gamma (ν / 2)) ^ 2) := by
  have hν₀ : 0 < ν := zero_lt_two.trans hν
  let _ := isProbabilityMeasure_halfStudentTMeasure hν₀ hs
  have hLp : MemLp id 2 (halfStudentTMeasure ν s) :=
    (memLp_two_iff_integrable_sq aestronglyMeasurable_id).2
      ((integrable_pow_halfStudentTMeasure_iff hν₀ hs 2).2 (by exact_mod_cast hν))
  rw [variance_eq_sub hLp]
  simp only [Pi.pow_apply, id_eq, integral_sq_halfStudentTMeasure hν hs,
    integral_id_halfStudentTMeasure (by linarith : 1 < ν) hs,
    div_pow, mul_pow, sq_sqrt hν₀.le, sq_sqrt pi_pos.le]
  ring

/-- Half-Student t exponential moments exist exactly at nonpositive rates. -/
@[simp]
theorem integrable_exp_mul_id_halfStudentTMeasure_iff (hν : 0 < ν) (hs : 0 < s) (t : ℝ) :
    Integrable (fun x : ℝ ↦ exp (t * x)) (halfStudentTMeasure ν s) ↔ t ≤ 0 := by
  let _ := isProbabilityMeasure_halfStudentTMeasure hν hs
  constructor
  · intro hint
    by_contra ht
    have ht₀ : 0 < t := lt_of_not_ge ht
    have hmom : ¬ Integrable (fun x : ℝ ↦ x ^ ν) (halfStudentTMeasure ν s) := by
      simp [integrable_rpow_halfStudentTMeasure_iff hν hs]
    exact not_integrable_exp_mul_of_not_integrable_rpow ν measurable_id.aemeasurable
      ((ae_pos_halfStudentTMeasure ν s).mono fun _ hx ↦ hx.le) hν.le hmom ht₀ hint
  · intro ht
    exact integrable_exp_mul_of_ge t 0 ht measurable_id.aemeasurable
      ((ae_pos_halfStudentTMeasure ν s).mono fun _ hx ↦ hx.le)

/-- The exact exponential-integrability domain is the nonpositive half-line. -/
@[simp]
theorem integrableExpSet_id_halfStudentTMeasure (hν : 0 < ν) (hs : 0 < s) :
    integrableExpSet id (halfStudentTMeasure ν s) = Iic 0 := by
  ext t
  simpa only [integrableExpSet, id_eq, mem_ofPred_eq, mem_Iic] using
    integrable_exp_mul_id_halfStudentTMeasure_iff hν hs t

end TauCeti.Probability

namespace ProbabilityTheory.HasLaw

open TauCeti.Probability

variable {ν s q : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}

/-- A half-Student t random variable has the same sharp real-power integrability range. -/
theorem integrable_rpow_halfStudentTMeasure_iff
    (hX : HasLaw X (halfStudentTMeasure ν s) P) (hν : 0 < ν) (hs : 0 < s) (q : ℝ) :
    Integrable (fun ω ↦ X ω ^ q) P ↔ -1 < q ∧ q < ν := by
  rw [← TauCeti.Probability.integrable_rpow_halfStudentTMeasure_iff hν hs, ← hX.map_eq,
    integrable_map_measure (by fun_prop) hX.aemeasurable]
  rfl

/-- Real-power moments of a random variable with half-Student t law. -/
theorem integral_rpow_halfStudentTMeasure
    (hX : HasLaw X (halfStudentTMeasure ν s) P) (hν : 0 < ν) (hs : 0 < s)
    (hq₀ : -1 < q) (hqν : q < ν) :
    ∫ ω, X ω ^ q ∂P =
      s ^ q * ν ^ (q / 2) * Real.Gamma ((q + 1) / 2) * Real.Gamma ((ν - q) / 2) /
        (√π * Real.Gamma (ν / 2)) := by
  rw [← TauCeti.Probability.integral_rpow_halfStudentTMeasure hν hs hq₀ hqν, ← hX.map_eq,
    integral_map hX.aemeasurable (by fun_prop)]

/-- The expectation of a half-Student t random variable with finite first moment. -/
theorem integral_halfStudentTMeasure
    (hX : HasLaw X (halfStudentTMeasure ν s) P) (hν : 1 < ν) (hs : 0 < s) :
    ∫ ω, X ω ∂P =
      s * √ν * Real.Gamma ((ν - 1) / 2) / (√π * Real.Gamma (ν / 2)) := by
  rw [hX.integral_eq, integral_id_halfStudentTMeasure hν hs]

/-- The variance of a half-Student t random variable with finite second moment. -/
theorem variance_halfStudentTMeasure
    (hX : HasLaw X (halfStudentTMeasure ν s) P) (hν : 2 < ν) (hs : 0 < s) :
    variance X P = s ^ 2 *
      (ν / (ν - 2) - ν / π *
        (Real.Gamma ((ν - 1) / 2) / Real.Gamma (ν / 2)) ^ 2) := by
  rw [hX.variance_eq, variance_id_halfStudentTMeasure hν hs]

end ProbabilityTheory.HasLaw
