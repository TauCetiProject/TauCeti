/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
import TauCeti.Analysis.Fourier.SineSeries
import TauCeti.MeasureTheory.Function.LpSeminorm.ContinuousOn

/-!
# Fourier coefficients on an interval

Mathlib's `fourierCoeffOn hab f n` is the `n`-th Fourier coefficient of `f` on `[a, b]`, that is,
of the `(b - a)`-periodic function agreeing with `f` on `(a, b]`. This file records that the
integrand of such a coefficient stays interval-integrable
(`IntervalIntegrable.fourier_smul`), the additivity of `fourierCoeffOn`
on interval-integrable functions (`TauCeti.fourierCoeffOn_add`, `TauCeti.fourierCoeffOn_sub`),
the interval counterparts of Mathlib's `fourierCoeff.add`, and computes the coefficients of the
Fourier monomials themselves (`TauCeti.fourierCoeffOn_fourier`), the interval counterpart of
Mathlib's `fourierCoeff_fourier`, in particular for a circle `c + w e^{2πimt/(b-a)}`
(`TauCeti.fourierCoeffOn_const_add_mul_fourier`). Conversely, a function continuous on `[a, b]` is
determined there by its Fourier coefficients (`TauCeti.eqOn_Icc_of_fourierCoeffOn_eq`); the
endpoint `a`, which the coefficients do not see, is recovered by continuity.
-/

public section

open MeasureTheory Set
open scoped Interval

variable {a b : ℝ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Multiplying an interval-integrable function by a Fourier monomial `t ↦ fourier n t` of any
period `T` keeps it interval-integrable; with `T = b - a` and frequency `-n` this is the integrand
of `fourierCoeffOn_eq_integral`. -/
theorem IntervalIntegrable.fourier_smul {f : ℝ → E}
    (hf : IntervalIntegrable f volume a b) (T : ℝ) (n : ℤ) :
    IntervalIntegrable (fun t : ℝ ↦ fourier n (t : AddCircle T) • f t) volume a b :=
  hf.continuousOn_smul ((fourier n).continuous.comp (AddCircle.continuous_mk' T)).continuousOn

namespace TauCeti

/-- Fourier coefficients on an interval are additive on interval-integrable functions. -/
theorem fourierCoeffOn_add (hab : a < b) {f g : ℝ → E} (hf : IntervalIntegrable f volume a b)
    (hg : IntervalIntegrable g volume a b) (n : ℤ) :
    fourierCoeffOn hab (fun t ↦ f t + g t) n = fourierCoeffOn hab f n + fourierCoeffOn hab g n := by
  simp only [fourierCoeffOn_eq_integral, smul_add]
  rw [intervalIntegral.integral_add (hf.fourier_smul (b - a) (-n))
    (hg.fourier_smul (b - a) (-n)), smul_add]

/-- Fourier coefficients on an interval are subtractive on interval-integrable functions. -/
theorem fourierCoeffOn_sub (hab : a < b) {f g : ℝ → E} (hf : IntervalIntegrable f volume a b)
    (hg : IntervalIntegrable g volume a b) (n : ℤ) :
    fourierCoeffOn hab (fun t ↦ f t - g t) n = fourierCoeffOn hab f n - fourierCoeffOn hab g n := by
  simp only [fourierCoeffOn_eq_integral, smul_sub]
  rw [intervalIntegral.integral_sub (hf.fourier_smul (b - a) (-n))
    (hg.fourier_smul (b - a) (-n)), smul_sub]

/-- On `[a, b]`, the `m`-th Fourier monomial of period `b - a` has Fourier coefficient one at
frequency `m` and zero at every other frequency. -/
theorem fourierCoeffOn_fourier (hab : a < b) (m n : ℤ) :
    fourierCoeffOn hab (fun t : ℝ ↦ fourier m (t : AddCircle (b - a))) n =
      (Pi.single m 1 : ℤ → ℂ) n := by
  have : Fact (0 < b - a) := ⟨sub_pos.2 hab⟩
  rw [← fourierCoeff_fourier (T := b - a) m, fourierCoeffOn_eq_integral,
    fourierCoeff_eq_intervalIntegral _ _ a, add_sub_cancel]

/-- The Fourier coefficients on `[a, b]` of the circle `c + w e^{2πimt/(b-a)}` are `c` at
frequency `0` and `w` at frequency `m`, added together when `m = 0`. -/
theorem fourierCoeffOn_const_add_mul_fourier (hab : a < b) (c w : ℂ) (m n : ℤ) :
    fourierCoeffOn hab (fun t : ℝ ↦ c + w * fourier m (t : AddCircle (b - a))) n =
      (Pi.single 0 c : ℤ → ℂ) n + (Pi.single m w : ℤ → ℂ) n := by
  have hcont (k : ℤ) :
      IntervalIntegrable (fun t : ℝ ↦ fourier k (t : AddCircle (b - a))) volume a b :=
    ((fourier k).continuous.comp (AddCircle.continuous_mk' (b - a))).intervalIntegrable a b
  have hc : (fun t : ℝ ↦ c + w * fourier m (t : AddCircle (b - a))) =
      fun t : ℝ ↦ c * fourier 0 (t : AddCircle (b - a)) +
        w * fourier m (t : AddCircle (b - a)) := by
    simp
  rw [hc, fourierCoeffOn_add hab ((hcont 0).const_mul c) ((hcont m).const_mul w),
    fourierCoeffOn.const_mul, fourierCoeffOn.const_mul, fourierCoeffOn_fourier,
    fourierCoeffOn_fourier]
  simp only [Pi.single_apply]
  split_ifs <;> ring

/-- **Uniqueness of Fourier coefficients on an interval.** Two complex functions continuous on
`[a, b]` with the same Fourier coefficients on `[a, b]` agree on `[a, b]`. -/
theorem eqOn_Icc_of_fourierCoeffOn_eq (hab : a < b) {f g : ℝ → ℂ} (hf : ContinuousOn f [[a, b]])
    (hg : ContinuousOn g [[a, b]]) (h : ∀ n, fourierCoeffOn hab f n = fourierCoeffOn hab g n) :
    EqOn f g (Icc a b) := by
  have hfg : ContinuousOn (fun t ↦ f t - g t) [[a, b]] := hf.sub hg
  have hL2 : MemLp (fun t ↦ f t - g t) 2 (volume.restrict (Ioc a b)) :=
    (hfg.memLp_top_restrict_of_subset_isCompact isCompact_uIcc measurableSet_Ioc
      (Ioc_subset_Icc_self.trans Icc_subset_uIcc)).mono_exponent le_top
  have hae := ae_eq_zero_of_forall_fourierCoeffOn_eq_zero hab hL2 fun n ↦ by
    rw [fourierCoeffOn_sub hab hf.intervalIntegrable hg.intervalIntegrable, h, sub_self]
  rw [uIcc_of_le hab.le] at hfg
  intro t ht
  exact sub_eq_zero.1 (Measure.eqOn_Icc_of_ae_eq volume hab.ne
    (by rwa [Measure.restrict_congr_set Ioc_ae_eq_Icc] at hae) hfg continuousOn_const ht)

end TauCeti
