/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import TauCeti.MeasureTheory.Integral.NormRpow
public import TauCeti.Probability.Distributions.Uniform.Ball.Basic

/-!
# The circular law

The circular law is the uniform probability measure on the open unit disc of `ℂ`, with density
`π⁻¹ 1_{|z| < 1}` with respect to the area measure. It is the uniform ball law
`TauCeti.Probability.uniformBallMeasure` of the plane `ℂ`, of center `0` and radius `1`.

## Main definitions

* `TauCeti.Probability.circularLaw`: the uniform probability measure on the unit disc,
  `uniformBallMeasure 0 1`.

## Main results

* `TauCeti.Probability.circularLaw_eq_smul_restrict`: the law is `π⁻¹` times the area measure
  restricted to the disc.
* `TauCeti.Probability.isProbabilityMeasure_circularLaw`: total mass one.
* `TauCeti.Probability.ae_mem_ball_circularLaw`: the law is carried by the open unit disc.
* `TauCeti.Probability.map_rotation_circularLaw`: invariance under rotations.
* `TauCeti.Probability.integral_norm_pow_circularLaw`: `∫ ‖z‖ ^ n = 2 / (n + 2)`.
* `TauCeti.Probability.integral_pow_circularLaw`: `∫ z ^ k = 0` for `k ≠ 0`.
* `TauCeti.Probability.integral_pow_mul_conj_pow_circularLaw`: `∫ z ^ p * conj z ^ q = 0` for
  `p ≠ q`, and `1 / (p + 1)` for `p = q`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Metric Set
open scoped ComplexConjugate ENNReal

namespace TauCeti.Probability

/-- The circular law: the uniform probability measure on the open unit disc of `ℂ`. -/
def circularLaw : Measure ℂ := uniformBallMeasure 0 1

theorem circularLaw_def : circularLaw = uniformBallMeasure (0 : ℂ) 1 := (rfl)

/-- The circular law is `π⁻¹` times the area measure restricted to the unit disc. -/
theorem circularLaw_eq_smul_restrict :
    circularLaw = ENNReal.ofReal Real.pi⁻¹ • volume.restrict (ball (0 : ℂ) 1) := by
  have hvol : volume (ball (0 : ℂ) 1) = ENNReal.ofReal Real.pi := by
    simp [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]
  rw [circularLaw_def, uniformBallMeasure_of_ne_zero one_ne_zero, ProbabilityTheory.cond, hvol,
    ENNReal.ofReal_inv_of_pos Real.pi_pos]

/-- The circular law is a probability measure. -/
instance isProbabilityMeasure_circularLaw : IsProbabilityMeasure circularLaw :=
  isProbabilityMeasure_uniformBallMeasure zero_le_one

/-- The circular law is carried by the open unit disc. -/
theorem ae_mem_ball_circularLaw : ∀ᵐ z ∂circularLaw, z ∈ ball (0 : ℂ) 1 :=
  ae_mem_ball_uniformBallMeasure one_pos

/-- The circular law is invariant under rotations of the plane. -/
theorem map_rotation_circularLaw (u : Circle) :
    circularLaw.map (fun z : ℂ ↦ (u : ℂ) * z) = circularLaw := by
  have hfun : ⇑(rotation u) = fun z : ℂ ↦ (u : ℂ) * z := funext (rotation_apply u)
  have h := (rotation u).map_uniformBallMeasure (0 : ℂ) 1
  rw [map_zero, hfun] at h
  exact h

/-- The radial moments of the circular law: `∫ ‖z‖ ^ n = 2 / (n + 2)`. -/
@[simp]
theorem integral_norm_pow_circularLaw (n : ℕ) :
    ∫ z : ℂ, ‖z‖ ^ n ∂circularLaw = 2 / (n + 2) := by
  rw [circularLaw_eq_smul_restrict, integral_smul_measure]
  have hscale : (ENNReal.ofReal Real.pi⁻¹).toReal = Real.pi⁻¹ :=
    ENNReal.toReal_ofReal (by positivity)
  rw [hscale, smul_eq_mul]
  have h := TauCeti.integral_norm_rpow_ball (E := ℂ) (mu := volume)
    (s := (n : ℝ)) (by
      rw [Complex.finrank_real_complex]
      exact lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg n)) (R := 1) (by norm_num)
  rw [Complex.finrank_real_complex] at h
  have hvolENN : volume (ball (0 : ℂ) 1) = ENNReal.ofReal Real.pi := by
    simp [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]
  have hvol : volume.real (ball (0 : ℂ) 1) = Real.pi := by
    rw [measureReal_def, hvolENN]
    exact ENNReal.toReal_ofReal Real.pi_pos.le
  rw [hvol] at h
  have h' : ∫ z, ‖z‖ ^ n ∂volume.restrict (ball (0 : ℂ) 1) =
      2 * Real.pi * (1 ^ (2 + (n : ℝ)) / (2 + (n : ℝ))) := by
    simpa [Real.rpow_natCast] using h
  rw [h']
  norm_num
  field_simp
  ring

/-- Every nonzero natural power of `z` integrates to zero against the circular law. -/
@[simp]
theorem integral_pow_circularLaw {k : ℕ} (hk : k ≠ 0) : ∫ z, z ^ k ∂circularLaw = 0 := by
  set u : Circle := Circle.exp (Real.pi / k) with hu
  have huk : (u : ℂ) ^ k = -1 := by
    rw [hu, Circle.coe_exp, ← Complex.exp_nat_mul]
    have : (k : ℂ) * (↑(Real.pi / k) * Complex.I) = Real.pi * Complex.I := by
      push_cast
      field_simp
    rw [this, Complex.exp_pi_mul_I]
  have h := integral_map (μ := circularLaw) (measurable_const_mul (u : ℂ)).aemeasurable
    (f := fun z : ℂ ↦ z ^ k) (by fun_prop)
  rw [map_rotation_circularLaw] at h
  simp only [mul_pow, huk, neg_one_mul, integral_neg] at h
  linear_combination (1 / 2 : ℂ) * h

/-- The mixed moments of the circular law: unequal powers integrate to zero, while the
diagonal moment of order `p` is `1 / (p + 1)`. -/
@[simp]
theorem integral_pow_mul_conj_pow_circularLaw (p q : ℕ) :
    ∫ z : ℂ, z ^ p * conj z ^ q ∂circularLaw =
      if p = q then ((1 / (p + 1) : ℝ) : ℂ) else 0 := by
  by_cases hpq : p = q
  · subst q
    have hfun : ∀ z : ℂ, z ^ p * conj z ^ p = ‖z‖ ^ (2 * p) := by
      intro z
      rw [← mul_pow]
      rw [Complex.mul_conj', ← pow_mul]
    rw [integral_congr_ae (Filter.Eventually.of_forall hfun)]
    have hcast : ∀ z : ℂ, (‖z‖ : ℂ) ^ (2 * p) =
        ((‖z‖ ^ (2 * p) : ℝ) : ℂ) := by
      intro z
      exact (Complex.ofReal_pow _ _).symm
    have hfrac : (2 : ℝ) / ((2 * p : ℕ) + 2) = 1 / (p + 1) := by
      push_cast
      field_simp
    rw [integral_congr_ae (Filter.Eventually.of_forall hcast)]
    calc
      ∫ z : ℂ, ((‖z‖ ^ (2 * p) : ℝ) : ℂ) ∂circularLaw =
          (∫ z : ℂ, ‖z‖ ^ (2 * p) ∂circularLaw : ℝ) := integral_ofReal
      _ = _ := by
        rw [integral_norm_pow_circularLaw]
        simp only [ite_true]
        simpa using congrArg Complex.ofReal hfrac
  · let d := if p < q then q - p else p - q
    have hd : d ≠ 0 := by
      dsimp [d]
      split_ifs with h
      · exact Nat.sub_ne_zero_of_lt h
      · exact Nat.sub_ne_zero_of_lt (lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hpq))
    have hcases : p < q ∨ q < p := lt_or_gt_of_ne hpq
    set u : Circle := Circle.exp (Real.pi / d) with hu
    have huk : (u : ℂ) ^ d = -1 := by
      rw [hu, Circle.coe_exp, ← Complex.exp_nat_mul]
      have hmul : (d : ℂ) * (↑(Real.pi / d) * Complex.I) = Real.pi * Complex.I := by
        push_cast
        field_simp
      rw [hmul, Complex.exp_pi_mul_I]
    have hconj : conj (u : ℂ) = (u : ℂ)⁻¹ :=
      (Circle.coe_inv_eq_conj u).symm
    have hfactor : (u : ℂ) ^ p * conj (u : ℂ) ^ q = -1 := by
      rcases hcases with hpq' | hqp'
      · have hq : q = p + d := by
          simpa [d, hpq', Nat.add_comm] using
            (Nat.sub_add_cancel (Nat.le_of_lt hpq')).symm
        rw [hconj, hq, pow_add, inv_pow, inv_pow]
        calc
          (u : ℂ) ^ p * (((u : ℂ) ^ p)⁻¹ * ((u : ℂ) ^ d)⁻¹) =
              ((u : ℂ) ^ p * ((u : ℂ) ^ p)⁻¹) * ((u : ℂ) ^ d)⁻¹ := by
            rw [← mul_assoc]
          _ = ((u : ℂ) ^ d)⁻¹ := by field_simp
          _ = -1 := by rw [huk]; norm_num
      · have hp : p = q + d := by
          simpa [d, not_lt_of_ge (le_of_lt hqp'), Nat.add_comm] using
            (Nat.sub_add_cancel (Nat.le_of_lt hqp')).symm
        rw [hconj, hp, pow_add, inv_pow]
        calc
          ((u : ℂ) ^ q * (u : ℂ) ^ d) * ((u : ℂ) ^ q)⁻¹ =
              (u : ℂ) ^ d := by field_simp
          _ = -1 := huk
    let f : ℂ → ℂ := fun z ↦ z ^ p * conj z ^ q
    have hchange : ∀ z : ℂ, f ((u : ℂ) * z) = -f z := by
      intro z
      calc
        f ((u : ℂ) * z) =
            ((u : ℂ) ^ p * conj (u : ℂ) ^ q) * (z ^ p * conj z ^ q) := by
          simp only [f, mul_pow, map_mul]
          ring
        _ = -f z := by rw [hfactor]; simp [f]
    have h := integral_map (μ := circularLaw) (measurable_const_mul (u : ℂ)).aemeasurable
      (f := f) (by fun_prop)
    rw [map_rotation_circularLaw] at h
    have hchange' := integral_congr_ae (μ := circularLaw)
      (Filter.Eventually.of_forall hchange)
    rw [hchange', integral_neg] at h
    have hzero : (∫ z, f z ∂circularLaw) = 0 := by
      linear_combination (1 / 2 : ℂ) * h
    simpa [f, hpq] using hzero

end TauCeti.Probability
