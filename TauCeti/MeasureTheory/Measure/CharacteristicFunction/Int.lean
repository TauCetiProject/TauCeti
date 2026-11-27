/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The characteristic function of a measure on the integers

A finite measure `μ` on `ℤ` is read on the line through its image `μ.map (Int.cast : ℤ → ℝ)`.
The characteristic function `φ(t) = ∫ exp(i t k) dμ(k)` of that image is a Fourier series in `t`:
it has period `2π`, and the masses of `μ` are its Fourier coefficients,

`μ {k} = (2π)⁻¹ ∫_{-π}^{π} exp(-i t k) φ(t) dt`.

This inversion formula on the integers expresses the local probabilities `P(S = k)` of an
integer-valued random variable `S` through its characteristic function. Its forms for sums of
independent integer random variables are in `TauCeti.Probability.Independence.IntInversion`.

## Main results

* `MeasureTheory.periodic_charFun_map_intCast`: the characteristic function of an integer law has
  period `2π`.
* `MeasureTheory.integral_exp_mul_intCast_mul_I`: orthogonality of the characters on `[-π, π]`,
  `∫_{-π}^{π} exp(i t n) dt` is `2π` for `n = 0` and `0` for every other integer `n`.
* `MeasureTheory.measureReal_singleton_eq_integral_charFun_map_intCast`: inversion on the
  integers.

## References

* R. Durrett, *Probability: Theory and Examples*, fifth edition, Exercise 3.3.2 (ii).
-/

public section

open Complex Real

namespace MeasureTheory

/-- The characters `t ↦ exp(i t n)`, `n ∈ ℤ`, are orthogonal on `[-π, π]`: the integral of
`exp(i t n)` over `[-π, π]` is `2π` for `n = 0` and `0` otherwise. -/
theorem integral_exp_mul_intCast_mul_I (n : ℤ) :
    ∫ t in -π..π, cexp (t * n * I) = if n = 0 then (2 * π : ℂ) else 0 := by
  split_ifs with hn
  · subst hn
    simp only [Int.cast_zero, mul_zero, zero_mul, Complex.exp_zero,
      intervalIntegral.integral_const, sub_neg_eq_add, real_smul]
    push_cast
    ring
  have hc : (n : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast hn) I_ne_zero
  have h2 : cexp ((n : ℂ) * I * π) = cexp ((n : ℂ) * I * ↑(-π)) := by
    rw [exp_eq_exp_iff_exists_int]
    exact ⟨n, by push_cast; ring⟩
  have hfun : (fun t : ℝ ↦ cexp (t * n * I)) = fun t : ℝ ↦ cexp (n * I * t) :=
    funext fun t ↦ by congr 1; ring
  rw [hfun, integral_exp_mul_complex hc, h2, sub_self, zero_div]

variable (μ : Measure ℤ)

/-- The characteristic function of the image on the line of a measure `μ` on `ℤ`, as an integral
over `ℤ`. -/
theorem charFun_map_intCast_apply (t : ℝ) :
    charFun (μ.map (Int.cast : ℤ → ℝ)) t = ∫ k, cexp (t * k * I) ∂μ := by
  rw [charFun_apply_real, integral_map (measurable_of_countable _).aemeasurable
    (Continuous.aestronglyMeasurable (by fun_prop))]
  simp only [ofReal_intCast]

/-- The characteristic function of a measure on `ℤ`, read on the line, has period `2π`. -/
theorem periodic_charFun_map_intCast :
    Function.Periodic (charFun (μ.map (Int.cast : ℤ → ℝ))) (2 * π) := by
  intro t
  rw [charFun_map_intCast_apply, charFun_map_intCast_apply]
  congr 1 with k
  rw [exp_eq_exp_iff_exists_int]
  exact ⟨k, by push_cast; ring⟩

/-- **Inversion on the integers.** The mass of a finite measure `μ` on `ℤ` at `k` is the `k`-th
Fourier coefficient of the characteristic function `φ` of its image on the line:
`μ {k} = (2π)⁻¹ ∫_{-π}^{π} exp(-i t k) φ(t) dt`. -/
theorem measureReal_singleton_eq_integral_charFun_map_intCast [IsFiniteMeasure μ] (k : ℤ) :
    (μ.real {k} : ℂ) = (2 * π : ℂ)⁻¹ *
      ∫ t in -π..π, cexp (-(t * k * I)) * charFun (μ.map (Int.cast : ℤ → ℝ)) t := by
  have hint : Integrable (Function.uncurry fun (t : ℝ) (l : ℤ) ↦ cexp (t * (l - k : ℤ) * I))
      ((volume.restrict (Set.uIoc (-π) π)).prod μ) := by
    rw [Set.uIoc_of_le (by linarith [pi_pos])]
    refine (integrable_const (1 : ℝ)).mono' (Continuous.aestronglyMeasurable ?_)
      (ae_of_all _ fun ⟨t, l⟩ ↦ ?_)
    · have hl : Continuous fun p : ℝ × ℤ ↦ ((p.2 - k : ℤ) : ℂ) :=
        (continuous_of_discreteTopology (f := fun l : ℤ ↦ ((l - k : ℤ) : ℂ))).comp continuous_snd
      exact ((continuous_ofReal.comp continuous_fst).mul hl |>.mul continuous_const).cexp
    · simp only [Function.uncurry_apply_pair]
      norm_cast
      rw [norm_exp_ofReal_mul_I]
  calc (μ.real {k} : ℂ)
      = (2 * π : ℂ)⁻¹ * ∫ l, (if l - k = 0 then (2 * π : ℂ) else 0) ∂μ := by
        have hind : (fun l : ℤ ↦ if l - k = 0 then (2 * π : ℂ) else 0) =
            Set.indicator {k} fun _ ↦ (2 * π : ℂ) := by
          ext l
          simp [Set.indicator_apply, sub_eq_zero]
        rw [hind, integral_indicator_const _ (measurableSet_singleton k), real_smul]
        field_simp
    _ = (2 * π : ℂ)⁻¹ * ∫ l, (∫ t in -π..π, cexp (t * (l - k : ℤ) * I)) ∂μ := by
        simp_rw [integral_exp_mul_intCast_mul_I]
    _ = (2 * π : ℂ)⁻¹ *
        ∫ t in -π..π, cexp (-(t * k * I)) * charFun (μ.map (Int.cast : ℤ → ℝ)) t := by
        rw [← intervalIntegral_integral_swap hint]
        congr 1
        refine intervalIntegral.integral_congr fun t _ ↦ ?_
        simp only [charFun_map_intCast_apply, ← integral_const_mul, ← Complex.exp_add]
        congr 1 with l
        congr 1
        push_cast
        ring

end MeasureTheory
