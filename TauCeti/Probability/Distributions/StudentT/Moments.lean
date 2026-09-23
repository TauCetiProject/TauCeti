/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude, Codex
-/
module

public import TauCeti.Probability.Distributions.StudentT.Basic
public import Mathlib.Probability.Moments.IntegrableExpMul
public import Mathlib.Probability.Moments.Variance
import TauCeti.Analysis.Calculus.RealCharts
import TauCeti.MeasureTheory.Integral.Bochner.Basic
import TauCeti.Probability.Distributions.StudentT.WeightedIntegral
import TauCeti.Analysis.SpecialFunctions.Beta
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# Moments of Student's t law

This file proves the mean, variance, polynomial moment thresholds and exponential moment domain of
the Student t distribution defined in `TauCeti/Probability/Distributions/StudentT/Basic.lean`. The
cumulative distribution function is computed in
`TauCeti/Probability/Distributions/StudentT/Cdf.lean`. The density is even, and on the positive
half-line the substitution `w = x ^ 2 / ν` turns every weighted integral into Euler's second beta
integral
`∫ w ^ (a - 1) * (1 + w) ^ (-(a + b)) = Β(a, b)`, so the weighted density is integrable there
exactly for `-1 < q < ν`; the exponential-moment statements read off that sharp threshold.

## Main results

* `integrable_pow_studentTMeasure_iff` — within the nondegenerate family, a natural power is
  integrable exactly when its degree is less than the degrees of freedom;
* `integrable_id_studentTMeasure_iff` and `integral_id_studentTMeasure` — within the nondegenerate
  family the mean exists exactly when `1 < ν`, while its Bochner integral is zero for every
  parameter;
* `integrable_sq_studentTMeasure_iff`, `integral_sq_studentTMeasure` and
  `variance_id_studentTMeasure` — the second moment exists exactly when `2 < ν`, and then both it
  and the variance equal `ν / (ν - 2)`;
* `integrable_exp_mul_id_studentTMeasure_iff` — `exp (t · x)` is integrable exactly at `t = 0`;
* `integrableExpSet_id_studentTMeasure` — the exponential-moment domain is the singleton `{0}`,
  together with the matching non-integrability statement for every nonzero rate.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2, 2nd ed.,
  Wiley (1995), ch. 28.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set

open scoped ENNReal Real

namespace TauCeti

namespace Probability

variable {ν q x t : ℝ}

/-! ### Polynomial moments -/

/-- The beta kernel is integrable on the positive half-line precisely for `-1 < q < ν`: the
exponent at `0` is `(q - 1) / 2` and the tail exponent is `(q - ν - 2) / 2`. -/
private lemma integrableOn_studentTBetaKernel_Ioi_iff (hq : -1 < q) :
    IntegrableOn (studentTBetaKernel ν q) (Ioi (0 : ℝ)) ↔ q < ν := by
  have h := integrableOn_rpow_mul_one_add_rpow_iff
    (a := (q + 1) / 2) (b := (ν - q) / 2) (by linarith)
  have hleft : (q + 1) / 2 - 1 = (q - 1) / 2 := by ring
  have hsum : (q + 1) / 2 + (ν - q) / 2 = (ν + 1) / 2 := by ring
  have htail : 0 < (ν - q) / 2 ↔ q < ν := by
    constructor <;> intro hh <;> linarith
  simpa only [studentTBetaKernel, hleft, hsum, htail] using h

/-- The weighted Student t density `studentTPDFReal ν x * x ^ q` is integrable on the positive
half-line exactly for `-1 < q < ν`. -/
private theorem integrableOn_pow_mul_studentTPDFReal_Ioi_iff (hν : 0 < ν) (hq : -1 < q) :
    IntegrableOn (fun x : ℝ => studentTPDFReal ν x * x ^ q) (Ioi (0 : ℝ)) ↔ q < ν := by
  set C := Real.Gamma ((ν + 1) / 2) / (Real.sqrt (ν * Real.pi) * Real.Gamma (ν / 2))
  let g : ℝ → ℝ := fun w => C * ν ^ ((q + 1) / 2) / 2 * studentTBetaKernel ν q w
  have hderiv : ∀ z ∈ Ioi (0 : ℝ),
      HasDerivWithinAt (fun z : ℝ => z ^ 2 / ν) (2 * z / ν) (Ioi (0 : ℝ)) z :=
    fun z _ => (hasDerivAt_sq_div_const ν z).hasDerivWithinAt
  have hiff : IntegrableOn g (Ioi (0 : ℝ)) ↔
      IntegrableOn (fun x : ℝ => studentTPDFReal ν x * x ^ q) (Ioi (0 : ℝ)) := by
    have himg0 : (fun z : ℝ => z ^ 2 / ν) '' Ioi (0 : ℝ) = Ioi (0 ^ 2 / ν) :=
      image_sq_div_const_Ioi hν (y := 0) le_rfl
    have himg : (fun z : ℝ => z ^ 2 / ν) '' Ioi (0 : ℝ) = Ioi (0 : ℝ) := by
      rw [himg0]
      simp
    have h_g_eq : ∀ z : ℝ, 0 < z → |2 * z / ν| • g (z ^ 2 / ν) =
        studentTPDFReal ν z * z ^ q := by
      intro z hz
      simpa [g] using abs_deriv_smul_studentTPDFReal hν q hz
    have h_g_eq' : EqOn (fun z : ℝ => |2 * z / ν| • g (z ^ 2 / ν))
        (fun x : ℝ => studentTPDFReal ν x * x ^ q) (Ioi (0 : ℝ)) := by
      intro z hz
      exact h_g_eq z hz
    have himg1 : IntegrableOn (fun z : ℝ => |2 * z / ν| • g (z ^ 2 / ν)) (Ioi (0 : ℝ)) ↔
        IntegrableOn (fun x : ℝ => studentTPDFReal ν x * x ^ q) (Ioi (0 : ℝ)) := by
      refine ⟨fun h => h.congr_fun h_g_eq' measurableSet_Ioi,
        fun h => h.congr_fun (fun z hz => (h_g_eq' hz).symm) measurableSet_Ioi⟩
    have hpre : IntegrableOn g ((fun z : ℝ => z ^ 2 / ν) '' Ioi (0 : ℝ)) ↔
        IntegrableOn (fun z : ℝ => |2 * z / ν| • g (z ^ 2 / ν)) (Ioi (0 : ℝ)) :=
      integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hderiv
        (injOn_sq_div_const_Ioi hν.ne') g
    rw [himg] at hpre
    exact hpre.trans himg1
  have hC_ne : C ≠ 0 := (studentT_const_pos hν).ne'
  have hc : IsUnit (C * ν ^ ((q + 1) / 2) / 2) := isUnit_iff_ne_zero.mpr <|
    div_ne_zero (mul_ne_zero hC_ne (Real.rpow_pos_of_pos hν _).ne') (by norm_num)
  rw [← hiff]
  simpa [g, IntegrableOn, integrable_const_mul_iff hc] using
    integrableOn_studentTBetaKernel_Ioi_iff hq

private lemma studentTPDFReal_abs (ν x : ℝ) : studentTPDFReal ν |x| = studentTPDFReal ν x := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
  · rw [abs_of_nonpos hx, studentTPDFReal_neg]

/-- A natural power is integrable under a nondegenerate Student t law exactly when its degree is
less than the degrees of freedom. -/
@[simp]
theorem integrable_pow_studentTMeasure_iff (hν : 0 < ν) (q : ℕ) :
    Integrable (fun x : ℝ => x ^ q) (studentTMeasure ν) ↔ (q : ℝ) < ν := by
  constructor
  · intro hint
    have hden := (integrable_studentTMeasure_iff (ν := ν)
      (f := fun x : ℝ => x ^ q)).mp hint
    have hIoi : IntegrableOn (fun x : ℝ => studentTPDFReal ν x * x ^ (q : ℝ))
        (Ioi (0 : ℝ)) := by
      simpa only [Real.rpow_natCast, smul_eq_mul] using hden.integrableOn (s := Ioi (0 : ℝ))
    exact (integrableOn_pow_mul_studentTPDFReal_Ioi_iff hν
      (lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (Nat.cast_nonneg q))).mp hIoi
  · intro hq
    rw [integrable_studentTMeasure_iff]
    simp_rw [smul_eq_mul]
    have hIoi := (integrableOn_pow_mul_studentTPDFReal_Ioi_iff hν
      (lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (Nat.cast_nonneg q))).2 hq
    have habs := TauCeti.MeasureTheory.integrable_comp_abs hIoi
    rw [← integrable_norm_iff (by fun_prop)]
    simpa only [studentTPDFReal_abs, Real.rpow_natCast, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (studentTPDFReal_nonneg ν _), abs_pow] using habs

/-- The identity is integrable under a nondegenerate Student t law exactly when the number of
degrees of freedom exceeds one. -/
@[simp]
theorem integrable_id_studentTMeasure_iff (hν : 0 < ν) :
    Integrable id (studentTMeasure ν) ↔ 1 < ν := by
  delta id
  simpa only [pow_one, Nat.cast_one] using integrable_pow_studentTMeasure_iff hν 1

/-- The Bochner integral of the identity under a Student t measure is zero for every parameter,
including by convention when the identity is not integrable. -/
@[simp]
theorem integral_id_studentTMeasure (ν : ℝ) :
    ∫ x, x ∂studentTMeasure ν = 0 := by
  have hpres : MeasurePreserving (fun x : ℝ => -x) (studentTMeasure ν) (studentTMeasure ν) :=
    ⟨measurable_neg, studentTMeasure_map_neg ν⟩
  have h : (∫ x, -x ∂studentTMeasure ν) = ∫ x, x ∂studentTMeasure ν := by
    simpa only [Function.comp_apply, id_eq] using
      hpres.integral_comp (Homeomorph.neg ℝ).measurableEmbedding id
  rw [integral_neg] at h
  linarith

private lemma studentTKernel_sq (hν : 0 < ν) (x : ℝ) :
    x ^ 2 * (1 + x ^ 2 / ν) ^ (-((ν + 1) / 2)) =
      ν * ((1 + x ^ 2 / ν) ^ (-((ν - 1) / 2)) -
        (1 + x ^ 2 / ν) ^ (-((ν + 1) / 2))) := by
  have hbase : 0 < 1 + x ^ 2 / ν := by positivity
  have hshift :
      (1 + x ^ 2 / ν) ^ (-((ν - 1) / 2)) =
        (1 + x ^ 2 / ν) * (1 + x ^ 2 / ν) ^ (-((ν + 1) / 2)) := by
    calc
      (1 + x ^ 2 / ν) ^ (-((ν - 1) / 2)) =
          (1 + x ^ 2 / ν) ^ (1 + -((ν + 1) / 2)) := by
        apply congrArg (fun t : ℝ => (1 + x ^ 2 / ν) ^ t)
        ring
      _ = (1 + x ^ 2 / ν) ^ 1 *
          (1 + x ^ 2 / ν) ^ (-((ν + 1) / 2)) := Real.rpow_add hbase _ _
      _ = (1 + x ^ 2 / ν) *
          (1 + x ^ 2 / ν) ^ (-((ν + 1) / 2)) := by rw [Real.rpow_one]
  rw [hshift]
  field_simp
  ring

private theorem integrable_sq_studentTMeasure_of_two_lt (hν : 2 < ν) :
    Integrable (fun x : ℝ => x ^ 2) (studentTMeasure ν) :=
  (integrable_pow_studentTMeasure_iff (lt_trans zero_lt_two hν) 2).2 (by simpa using hν)

private lemma beta_sub_beta_add_one (hν : 2 < ν) :
    beta (1 / 2) ((ν - 2) / 2) - beta (1 / 2) (ν / 2) =
      beta (3 / 2) ((ν - 2) / 2) := by
  let b := (ν - 2) / 2
  have hb : b ≠ 0 := by
    dsimp [b]
    linarith
  have hsum : b + 1 / 2 ≠ 0 := by
    dsimp [b]
    linarith
  have hright : beta (1 / 2) (b + 1) =
      b / (b + 1 / 2) * beta (1 / 2) b := by
    rw [beta_comm (1 / 2) (b + 1), beta_add_one_left hb hsum,
      beta_comm b (1 / 2)]
  have hleft : beta (1 / 2 + 1) b =
      (1 / 2) / (1 / 2 + b) * beta (1 / 2) b :=
    beta_add_one_left (by norm_num) (by simpa [add_comm] using hsum)
  have hνdiv : ν / 2 = b + 1 := by
    dsimp [b]
    ring
  have hthree : (3 : ℝ) / 2 = 1 / 2 + 1 := by ring
  rw [hνdiv, hthree, hright, hleft]
  have hcoeff : 1 - b / (b + 1 / 2) = (1 / 2) / (1 / 2 + b) := by
    have hsum' : 1 / 2 + b ≠ 0 := by simpa [add_comm] using hsum
    have hbhalf : b + 1 / 2 = 1 / 2 + b := by ring
    rw [hbhalf]
    apply (eq_div_iff hsum').2
    rw [sub_mul, one_mul, div_mul_cancel₀ b hsum']
    ring
  calc
    beta (1 / 2) b - b / (b + 1 / 2) * beta (1 / 2) b =
        (1 - b / (b + 1 / 2)) * beta (1 / 2) b := by ring
    _ = (1 / 2) / (1 / 2 + b) * beta (1 / 2) b := by rw [hcoeff]

private lemma integral_sq_mul_studentTKernel (hν : 2 < ν) :
    ∫ x : ℝ, x ^ 2 * (1 + x ^ 2 / ν) ^ (-((ν + 1) / 2)) =
      ν * √ν * beta (3 / 2) ((ν - 2) / 2) := by
  have hνpos : 0 < ν := lt_trans zero_lt_two hν
  have hshift : Integrable (fun x : ℝ =>
      (1 + x ^ 2 / ν) ^ (-((ν - 1) / 2))) :=
    integrable_one_add_sq_div_rpow hνpos (by linarith)
  have hbase : Integrable (fun x : ℝ =>
      (1 + x ^ 2 / ν) ^ (-((ν + 1) / 2))) :=
    integrable_one_add_sq_div_rpow hνpos (by linarith)
  have hminus : (ν - 1) / 2 - 1 / 2 = (ν - 2) / 2 := by ring
  have hplus : (ν + 1) / 2 - 1 / 2 = ν / 2 := by ring
  calc
    ∫ x : ℝ, x ^ 2 * (1 + x ^ 2 / ν) ^ (-((ν + 1) / 2)) =
        ∫ x : ℝ, ν * ((1 + x ^ 2 / ν) ^ (-((ν - 1) / 2)) -
          (1 + x ^ 2 / ν) ^ (-((ν + 1) / 2))) := by
      exact integral_congr_ae (ae_of_all _ fun x => studentTKernel_sq hνpos x)
    _ = ν * ((∫ x : ℝ, (1 + x ^ 2 / ν) ^ (-((ν - 1) / 2))) -
          ∫ x : ℝ, (1 + x ^ 2 / ν) ^ (-((ν + 1) / 2))) := by
      rw [integral_const_mul, integral_sub hshift hbase]
    _ = ν * (√ν * beta (1 / 2) ((ν - 1) / 2 - 1 / 2) -
          √ν * beta (1 / 2) ((ν + 1) / 2 - 1 / 2)) := by
      rw [integral_one_add_sq_div_rpow hνpos (by linarith),
        integral_one_add_sq_div_rpow hνpos (by linarith)]
    _ = ν * √ν * beta (3 / 2) ((ν - 2) / 2) := by
      rw [hminus, hplus, ← mul_sub, beta_sub_beta_add_one hν]
      ring

/-- The second raw moment of a Student t law is `ν / (ν - 2)` when `2 < ν`. -/
@[simp]
theorem integral_sq_studentTMeasure (hν : 2 < ν) :
    ∫ x, x ^ 2 ∂studentTMeasure ν = ν / (ν - 2) := by
  have hνpos : 0 < ν := lt_trans zero_lt_two hν
  have hbpos : 0 < (ν - 2) / 2 := by linarith
  have hGν : Real.Gamma (ν / 2) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hGb : Real.Gamma ((ν - 2) / 2) ≠ 0 := (Real.Gamma_pos_of_pos hbpos).ne'
  have hGs : Real.Gamma ((ν + 1) / 2) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hsqrtν : √ν ≠ 0 := (Real.sqrt_pos.mpr hνpos).ne'
  have hsqrtπ : √π ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hsub : ν - 2 ≠ 0 := by linarith
  have hthree : (3 : ℝ) / 2 = 1 / 2 + 1 := by ring
  have hgammaSum : (1 : ℝ) / 2 + 1 + (ν - 2) / 2 = (ν + 1) / 2 := by ring
  have hνhalf : ν / 2 = (ν - 2) / 2 + 1 := by ring
  rw [integral_studentTMeasure_eq]
  simp_rw [smul_eq_mul, studentTPDFReal_of_pos hνpos]
  calc
    ∫ x : ℝ, (Real.Gamma ((ν + 1) / 2) /
          (√(ν * π) * Real.Gamma (ν / 2)) *
          (1 + x ^ 2 / ν) ^ (-((ν + 1) / 2))) * x ^ 2 =
        Real.Gamma ((ν + 1) / 2) /
          (√(ν * π) * Real.Gamma (ν / 2)) *
          ∫ x : ℝ, x ^ 2 * (1 + x ^ 2 / ν) ^ (-((ν + 1) / 2)) := by
      rw [← integral_const_mul]
      congr 1
      funext x
      ring
    _ = Real.Gamma ((ν + 1) / 2) /
          (√(ν * π) * Real.Gamma (ν / 2)) *
          (ν * √ν * beta (3 / 2) ((ν - 2) / 2)) := by
      rw [integral_sq_mul_studentTKernel hν]
    _ = ν / (ν - 2) := by
      rw [ProbabilityTheory.beta, hthree,
        Real.Gamma_add_one (by norm_num : (1 : ℝ) / 2 ≠ 0),
        Real.Gamma_one_half_eq, hgammaSum, hνhalf,
        Real.Gamma_add_one (ne_of_gt hbpos), Real.sqrt_mul hνpos.le]
      field_simp

/-- Squaring is integrable under a nondegenerate Student t law exactly when the number of degrees
of freedom exceeds two. -/
theorem integrable_sq_studentTMeasure_iff (hν : 0 < ν) :
    Integrable (fun x : ℝ => x ^ 2) (studentTMeasure ν) ↔ 2 < ν := by
  simpa only [Nat.cast_ofNat] using integrable_pow_studentTMeasure_iff hν 2

/-- At or below two degrees of freedom, the second raw moment of a nondegenerate Student t law
diverges. -/
theorem not_integrable_sq_studentTMeasure (hν : 0 < ν) (hν2 : ν ≤ 2) :
    ¬ Integrable (fun x : ℝ => x ^ 2) (studentTMeasure ν) := by
  rw [integrable_sq_studentTMeasure_iff hν]
  exact not_lt.mpr hν2

/-- The variance of a Student t law is `ν / (ν - 2)` when `2 < ν`. -/
@[simp]
theorem variance_id_studentTMeasure (hν : 2 < ν) :
    variance id (studentTMeasure ν) = ν / (ν - 2) := by
  have _ : IsProbabilityMeasure (studentTMeasure ν) :=
    isProbabilityMeasure_studentTMeasure (lt_trans zero_lt_two hν)
  have hmem : MemLp id 2 (studentTMeasure ν) :=
    (memLp_two_iff_integrable_sq measurable_id'.aestronglyMeasurable).2
      (by simpa using integrable_sq_studentTMeasure_of_two_lt hν)
  rw [variance_eq_sub hmem]
  simp only [Pi.pow_apply, id_eq]
  rw [integral_sq_studentTMeasure hν, integral_id_studentTMeasure]
  ring

/-! ### Exponential moments -/

/-- The exponential of a nonzero multiple of the identity is not integrable under a Student t
law: if `exp (t * x)` and `exp (-t * x)` were both integrable, then every moment would be
finite, contradicting the sharp moment threshold `q < ν`. -/
theorem not_integrable_exp_mul_id_studentTMeasure (hν : 0 < ν) {t : ℝ} (ht : t ≠ 0) :
    ¬ Integrable (fun x : ℝ => Real.exp (t * x)) (studentTMeasure ν) := by
  intro hint
  -- reflection in the origin turns the rate `t` into `-t`
  have hmap : (studentTMeasure ν).map (fun x : ℝ => -x) = studentTMeasure ν :=
    studentTMeasure_map_neg ν
  have hkey : Integrable (fun y : ℝ => Real.exp (t * y))
      ((studentTMeasure ν).map (fun x : ℝ => -x)) := by
    rw [hmap]
    exact hint
  have hcomp : Integrable (fun x : ℝ => Real.exp (t * (-x))) (studentTMeasure ν) :=
    (integrable_map_measure hkey.aestronglyMeasurable measurable_neg.aemeasurable).mp hkey
  have hneg : Integrable (fun x : ℝ => Real.exp (-t * x)) (studentTMeasure ν) := by
    simpa [mul_neg] using hcomp
  -- both one-sided exponential moments would force every polynomial moment to be finite
  have hmom : Integrable (fun x : ℝ => |x| ^ ν) (studentTMeasure ν) :=
    integrable_rpow_abs_of_integrable_exp_mul ht hint hneg hν.le
  have hden : Integrable (fun x : ℝ => studentTPDFReal ν x * |x| ^ ν) :=
    (integrable_studentTMeasure_iff (ν := ν) (f := fun x : ℝ => |x| ^ ν)).mp hmom
  have hIoi : IntegrableOn (fun x : ℝ => studentTPDFReal ν x * x ^ ν) (Ioi (0 : ℝ)) := by
    have h1 : IntegrableOn (fun x : ℝ => studentTPDFReal ν x * |x| ^ ν) (Ioi (0 : ℝ)) :=
      hden.integrableOn
    have h2 : ∀ x ∈ Ioi (0 : ℝ), studentTPDFReal ν x * |x| ^ ν = studentTPDFReal ν x * x ^ ν := by
      intro x hx
      have hx0 : 0 < x := hx
      have habs : |x| = x := abs_of_pos hx0
      rw [habs]
    exact h1.congr_fun h2 measurableSet_Ioi
  have hq : -1 < ν := by linarith
  have : ν < ν := (integrableOn_pow_mul_studentTPDFReal_Ioi_iff hν hq).mp hIoi
  linarith

/-- The exponential integrand of a Student t law is integrable exactly at rate zero. -/
@[simp]
theorem integrable_exp_mul_id_studentTMeasure_iff (hν : 0 < ν) (t : ℝ) :
    Integrable (fun x : ℝ => Real.exp (t * x)) (studentTMeasure ν) ↔ t = 0 := by
  have : IsProbabilityMeasure (studentTMeasure ν) :=
    isProbabilityMeasure_studentTMeasure hν
  refine ⟨fun h => not_ne_iff.mp fun ht => not_integrable_exp_mul_id_studentTMeasure hν ht h,
    fun ht => ?_⟩
  subst t
  have h : (fun x : ℝ => Real.exp (0 * x)) = fun _ : ℝ => (1 : ℝ) := by
    funext x
    simp
  rw [h]
  exact integrable_const (1 : ℝ)

/-- The exponential-integrability domain of the identity under a Student t law is the singleton
`{0}`: every nonzero exponential moment diverges in the polynomial tails. -/
@[simp]
theorem integrableExpSet_id_studentTMeasure (hν : 0 < ν) :
    integrableExpSet id (studentTMeasure ν) = {0} := by
  ext t
  simpa [integrableExpSet, id_eq] using integrable_exp_mul_id_studentTMeasure_iff hν t


end Probability

end TauCeti
