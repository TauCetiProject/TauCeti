/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Skellam.Basic
public import TauCeti.Probability.Distributions.Poisson.Basic

/-!
# Skellam transforms and convolution

Real casting preserves the signed difference in the Skellam construction. All exponential
moments exist, and the cumulant-generating function is the sum of the Poisson cumulants at
opposite arguments. Convolution adds the respective rates on the native integer carrier.

## References

* J. G. Skellam, *The frequency distribution of the difference between two Poisson variates
  belonging to different populations*, Journal of the Royal Statistical Society 109 (1946), 296.

The transform computations reuse Mathlib's Poisson characteristic function and Tau Ceti's
Poisson moment-generating function.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace TauCeti.Probability

/-- Real casting of the native Skellam law is the difference of real-cast Poisson laws. -/
theorem map_intCast_skellamMeasure (r₁ r₂ : ℝ≥0) :
    (skellamMeasure r₁ r₂).map (Int.cast : ℤ → ℝ) =
      (Po(ℝ, r₁).prod Po(ℝ, r₂)).map (fun z : ℝ × ℝ => z.1 - z.2) := by
  rw [skellamMeasure_def, Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext z
  simp

/-- Every real exponential of a Skellam count is integrable. -/
theorem integrable_exp_mul_intCast_skellamMeasure (r₁ r₂ : ℝ≥0) (t : ℝ) :
    Integrable (fun k : ℤ => exp (t * k)) (skellamMeasure r₁ r₂) := by
  suffices h : Integrable (fun x : ℝ => exp (t * x))
      ((skellamMeasure r₁ r₂).map (Int.cast : ℤ → ℝ)) by
    exact (integrable_map_measure (f := (Int.cast : ℤ → ℝ))
      (g := fun x : ℝ => exp (t * x)) (by fun_prop) (by fun_prop)).1 h
  rw [map_intCast_skellamMeasure, integrable_map_measure (by fun_prop) (by fun_prop)]
  have h := (integrable_exp_mul_id_map_cast_poissonMeasure r₁ t).mul_prod
    (integrable_exp_mul_id_map_cast_poissonMeasure r₂ (-t))
  convert h using 1
  funext z
  simp only [Function.comp_apply]
  rw [← exp_add]
  congr 1
  ring

/-- The exact exponential-integrability domain of the real cast of a Skellam count. -/
@[simp]
theorem integrableExpSet_intCast_skellamMeasure (r₁ r₂ : ℝ≥0) :
    integrableExpSet (Int.cast : ℤ → ℝ) (skellamMeasure r₁ r₂) = Set.univ := by
  ext t
  simp only [integrableExpSet, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  exact integrable_exp_mul_intCast_skellamMeasure r₁ r₂ t

/-- The moment-generating function of the signed Skellam count. -/
@[simp]
theorem mgf_intCast_skellamMeasure (r₁ r₂ : ℝ≥0) (t : ℝ) :
    mgf (Int.cast : ℤ → ℝ) (skellamMeasure r₁ r₂) t =
      exp ((r₁ : ℝ) * (exp t - 1) + (r₂ : ℝ) * (exp (-t) - 1)) := by
  rw [← mgf_id_map (by fun_prop), map_intCast_skellamMeasure, mgf_id_map (by fun_prop), mgf]
  have hfun : (fun z : ℝ × ℝ => exp (t * (z.1 - z.2))) =
      fun z => exp (t * z.1) * exp ((-t) * z.2) := by
    funext z
    rw [← exp_add]
    congr 1
    ring
  rw [hfun, integral_prod_mul (fun x : ℝ => exp (t * x))
    (fun x : ℝ => exp ((-t) * x))]
  rw [← mgf, ← mgf, mgf_id_map_cast_poissonMeasure, mgf_id_map_cast_poissonMeasure, ← exp_add]

/-- The Skellam cumulant-generating function, valid on all of `ℝ`. -/
@[simp]
theorem cgf_intCast_skellamMeasure (r₁ r₂ : ℝ≥0) (t : ℝ) :
    cgf (Int.cast : ℤ → ℝ) (skellamMeasure r₁ r₂) t =
      (r₁ : ℝ) * (exp t - 1) + (r₂ : ℝ) * (exp (-t) - 1) := by
  rw [cgf, mgf_intCast_skellamMeasure, log_exp]

/-- Every natural moment of the signed Skellam count is absolutely integrable. -/
theorem integrable_pow_intCast_skellamMeasure (r₁ r₂ : ℝ≥0) (n : ℕ) :
    Integrable (fun k : ℤ => (k : ℝ) ^ n) (skellamMeasure r₁ r₂) :=
  integrable_pow_of_integrable_exp_mul (by norm_num : (1 : ℝ) ≠ 0)
    (integrable_exp_mul_intCast_skellamMeasure r₁ r₂ 1)
    (integrable_exp_mul_intCast_skellamMeasure r₁ r₂ (-1)) n

private theorem hasDerivAt_cgf_intCast_skellamMeasure (r₁ r₂ : ℝ≥0) (t : ℝ) :
    HasDerivAt (cgf (Int.cast : ℤ → ℝ) (skellamMeasure r₁ r₂))
      ((r₁ : ℝ) * exp t - (r₂ : ℝ) * exp (-t)) t := by
  rw [funext (cgf_intCast_skellamMeasure r₁ r₂)]
  convert (((hasDerivAt_exp t).sub_const 1).const_mul (r₁ : ℝ)).add
    ((((hasDerivAt_id t).neg.exp).sub_const 1).const_mul (r₂ : ℝ)) using 1
  · rfl
  · simp only [Pi.neg_apply, id_eq]
    ring

/-- The Skellam mean is the difference of its rates. -/
@[simp]
theorem integral_intCast_skellamMeasure (r₁ r₂ : ℝ≥0) :
    ∫ k : ℤ, (k : ℝ) ∂skellamMeasure r₁ r₂ = (r₁ : ℝ) - r₂ := by
  have h := deriv_cgf_zero (by simp :
    0 ∈ interior (integrableExpSet (Int.cast : ℤ → ℝ) (skellamMeasure r₁ r₂)))
  simpa [(hasDerivAt_cgf_intCast_skellamMeasure r₁ r₂ 0).deriv] using h.symm

/-- The Skellam variance is the sum of its rates, including zero-rate boundaries. -/
@[simp]
theorem variance_intCast_skellamMeasure (r₁ r₂ : ℝ≥0) :
    variance (Int.cast : ℤ → ℝ) (skellamMeasure r₁ r₂) = (r₁ : ℝ) + r₂ := by
  have hmem : MemLp (Int.cast : ℤ → ℝ) 2 (skellamMeasure r₁ r₂) :=
    (memLp_two_iff_integrable_sq (by fun_prop)).2
      (integrable_pow_intCast_skellamMeasure r₁ r₂ 2)
  have hfirst : deriv (cgf (Int.cast : ℤ → ℝ) (skellamMeasure r₁ r₂)) =
      fun t => (r₁ : ℝ) * exp t - (r₂ : ℝ) * exp (-t) :=
    funext fun t => (hasDerivAt_cgf_intCast_skellamMeasure r₁ r₂ t).deriv
  have hsecond : iteratedDeriv 2 (cgf (Int.cast : ℤ → ℝ) (skellamMeasure r₁ r₂)) 0 =
      (r₁ : ℝ) + r₂ := by
    rw [iteratedDeriv_succ, iteratedDeriv_one, hfirst]
    simpa [Pi.sub_def, Pi.neg_def] using (((hasDerivAt_exp 0).const_mul (r₁ : ℝ)).sub
      (((hasDerivAt_id (0 : ℝ)).neg.exp).const_mul (r₂ : ℝ))).deriv
  rw [variance_eq_sub hmem]
  have h := iteratedDeriv_two_cgf (by simp :
    0 ∈ interior (integrableExpSet (Int.cast : ℤ → ℝ) (skellamMeasure r₁ r₂)))
  simpa [hsecond, hfirst, integral_intCast_skellamMeasure] using h.symm

/-- The characteristic function of the real-cast Skellam law. -/
@[simp]
theorem charFun_map_intCast_skellamMeasure (r₁ r₂ : ℝ≥0) (t : ℝ) :
    charFun ((skellamMeasure r₁ r₂).map (Int.cast : ℤ → ℝ)) t =
      Complex.exp ((r₁ : ℂ) * (Complex.exp (t * Complex.I) - 1) +
        (r₂ : ℂ) * (Complex.exp (-t * Complex.I) - 1)) := by
  rw [map_intCast_skellamMeasure, charFun_apply_real,
    integral_map (by fun_prop) (by fun_prop)]
  have hfun : (fun z : ℝ × ℝ => Complex.exp ((t : ℂ) * ((z.1 - z.2 : ℝ) : ℂ) * Complex.I)) =
      fun z => Complex.exp ((t : ℂ) * z.1 * Complex.I) *
        Complex.exp ((-t : ℂ) * z.2 * Complex.I) := by
    funext z
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hfun, integral_prod_mul (fun x : ℝ => Complex.exp ((t : ℂ) * x * Complex.I))
    (fun x : ℝ => Complex.exp ((-t : ℂ) * x * Complex.I))]
  rw [← charFun_apply_real, ← Complex.ofReal_neg, ← charFun_apply_real,
    charFun_map_cast_poissonMeasure,
    charFun_map_cast_poissonMeasure, ← Complex.exp_add]

/-- Convolution adds both rates of the Skellam law. -/
theorem skellamMeasure_conv_skellamMeasure (r₁ r₂ s₁ s₂ : ℝ≥0) :
    skellamMeasure r₁ r₂ ∗ skellamMeasure s₁ s₂ = skellamMeasure (r₁ + s₁) (r₂ + s₂) := by
  have hcast : MeasurableEmbedding (Int.cast : ℤ → ℝ) :=
    ⟨Int.cast_injective, by fun_prop, fun s _ => (Set.to_countable s).image _ |>.measurableSet⟩
  apply hcast.map_injective
  have hconv := Measure.map_conv_addMonoidHom (μ := skellamMeasure r₁ r₂)
    (ν := skellamMeasure s₁ s₂) (Int.castAddHom ℝ) (by fun_prop)
  simp only [Int.coe_castAddHom] at hconv
  rw [hconv]
  apply Measure.ext_of_charFun
  ext t
  simp only [charFun_conv, charFun_map_intCast_skellamMeasure, ← Complex.exp_add]
  congr 1
  push_cast
  ring

end TauCeti.Probability

namespace ProbabilityTheory.IndepFun

/-- Independent Skellam counts add by adding their respective Poisson rates. -/
theorem hasLaw_add_skellamMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X Y : Ω → ℤ} {r₁ r₂ s₁ s₂ : ℝ≥0} (hXY : IndepFun X Y P)
    (hX : HasLaw X (TauCeti.Probability.skellamMeasure r₁ r₂) P)
    (hY : HasLaw Y (TauCeti.Probability.skellamMeasure s₁ s₂) P) :
    HasLaw (X + Y) (TauCeti.Probability.skellamMeasure (r₁ + s₁) (r₂ + s₂)) P := by
  rw [← TauCeti.Probability.skellamMeasure_conv_skellamMeasure]
  exact hXY.hasLaw_add hX hY

end ProbabilityTheory.IndepFun
