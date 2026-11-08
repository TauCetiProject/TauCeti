/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TemperateGrowth
public import Mathlib.Analysis.PSeries
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Algebra.Order.ToIntervalMod
import TauCeti.Analysis.PSeries
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds

/-!
# Temperate growth from uniformly bounded interval masses

A measure on the real line with uniformly bounded mass on the integer unit intervals
integrates every weight `(1 + ‖x‖) ^ p` with `p < -1`. In particular it has temperate
growth in Mathlib's sense, and hence defines a tempered distribution. No absolute
continuity or absence of atoms is required.

This applies to uniformly locally bounded convolution-harmonic measures, permitting
the use of Fourier transforms of tempered distributions in their rigidity theory.
Only bounds on the integer intervals are needed; bounds on all translated unit
intervals imply this hypothesis directly.

## References

* William Feller, *An Introduction to Probability Theory and Its Applications*, vol. II,
  2nd edition, Wiley, 1971, Chapter XI, for uniformly locally bounded measures in renewal
  theory.
-/

public section

open MeasureTheory Set
open scoped NNReal

namespace MeasureTheory.Measure

/-- Uniformly bounded masses on the integer unit intervals imply integrability of every
inverse power of `1 + ‖x‖` of order greater than one. The measure may have atoms. -/
theorem integrable_one_add_norm_rpow_of_measure_Icc_int_le (μ : Measure ℝ)
    {C : ℝ≥0} (hμ : ∀ n : ℤ, μ (Icc (n : ℝ) (n + 1)) ≤ C)
    {p : ℝ} (hp : p < -1) :
    Integrable (fun x : ℝ => (1 + ‖x‖) ^ p) μ := by
  let f : ℝ → ℝ := fun x => (1 + ‖x‖) ^ p
  let b : ℤ → ℝ := fun n => (2 : ℝ) ^ (-p) * (1 + ‖(n : ℝ)‖) ^ p
  have hf : Continuous f := by
    exact Continuous.rpow_const (by fun_prop) (fun x => Or.inl (by positivity))
  -- On each unit interval, the weight is bounded by a constant times its value at the left end.
  have hb (n : ℤ) {x : ℝ} (hx : x ∈ Icc (n : ℝ) (n + 1)) : ‖f x‖ ≤ b n := by
    rw [Real.norm_of_nonneg (by positivity)]
    refine TauCeti.one_add_norm_rpow_le_two_rpow_mul_of_norm_sub_le_one (by linarith) ?_
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hx.1, hx.2]
  have hi (n : ℤ) : IntegrableOn f (Icc (n : ℝ) (n + 1)) μ := by
    have hm : μ (Icc (n : ℝ) (n + 1)) < ⊤ :=
      (hμ n).trans_lt (by simp)
    let : IsFiniteMeasure (μ.restrict (Icc (n : ℝ) (n + 1))) :=
      ⟨by simpa using hm⟩
    exact ⟨hf.aestronglyMeasurable, .of_bounded
      (ae_restrict_of_forall_mem measurableSet_Icc fun x hx => hb n hx)⟩
  have hs : Summable (fun n : ℤ => (1 + ‖(n : ℝ)‖) ^ p) := by
    simpa only [Real.norm_eq_abs] using TauCeti.summable_one_add_abs_int_rpow hp
  -- Sum the interval integrals using the uniform mass bound; overlaps at atoms cause no problem.
  have hsum : Summable fun n : ℤ => ∫ x in Icc (n : ℝ) (n + 1), ‖f x‖ ∂μ := by
    refine (hs.mul_left ((2 : ℝ) ^ (-p) * C)).of_nonneg_of_le
      (fun n => integral_nonneg fun x => norm_nonneg _) fun n => ?_
    have hm : μ (Icc (n : ℝ) (n + 1)) < ⊤ := (hμ n).trans_lt (by simp)
    have hmass : μ.real (Icc (n : ℝ) (n + 1)) ≤ C := by
      exact ENNReal.toReal_mono (by simp) (hμ n)
    calc
      (∫ x in Icc (n : ℝ) (n + 1), ‖f x‖ ∂μ) ≤
          b n * μ.real (Icc (n : ℝ) (n + 1)) := by
        simpa only [norm_norm, Real.norm_of_nonneg (integral_nonneg
          (fun x : ℝ => norm_nonneg (f x)))] using
          norm_setIntegral_le_of_norm_le_const (f := fun x => ‖f x‖) hm
            (fun x hx => by simpa only [norm_norm] using hb n hx)
      _ ≤ b n * C := mul_le_mul_of_nonneg_left hmass (by positivity)
      _ = ((2 : ℝ) ^ (-p) * C) * (1 + ‖(n : ℝ)‖) ^ p := by dsimp [b]; ring
  simpa only [iUnion_Icc_intCast, integrableOn_univ] using
    integrableOn_iUnion_of_summable_integral_norm hi hsum

/-- A real-line measure with uniformly bounded mass on integer unit intervals has temperate
growth, so Mathlib's measure-to-tempered-distribution construction applies. -/
theorem hasTemperateGrowth_of_measure_Icc_int_le (μ : Measure ℝ)
    {C : ℝ≥0} (hμ : ∀ n : ℤ, μ (Icc (n : ℝ) (n + 1)) ≤ C) :
    μ.HasTemperateGrowth := by
  refine ⟨2, ?_⟩
  exact μ.integrable_one_add_norm_rpow_of_measure_Icc_int_le hμ (by norm_num)

end MeasureTheory.Measure
