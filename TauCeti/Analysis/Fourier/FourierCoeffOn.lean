/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Fourier.AddCircle
import TauCeti.Analysis.Calculus.PeriodicDeriv
import TauCeti.Analysis.Fourier.SineSeries
import TauCeti.MeasureTheory.Function.LpSeminorm.ContinuousOn

/-!
# Fourier coefficients on an interval

Mathlib's `fourierCoeffOn hab f n` is the `n`-th Fourier coefficient of `f` on `[a, b]`, that is,
of the `(b - a)`-periodic function agreeing with `f` on `(a, b]`. This file records that the
integrand of such a coefficient stays interval-integrable
(`IntervalIntegrable.fourier_smul`), the additivity of `fourierCoeffOn`
on interval-integrable functions (`TauCeti.fourierCoeffOn_add`, `TauCeti.fourierCoeffOn_sub`),
the interval counterparts of Mathlib's `fourierCoeff.add`, bounds the coefficients by a sup bound
on `(a, b]` (`TauCeti.norm_fourierCoeffOn_le`), and computes the coefficients of the
Fourier monomials themselves (`TauCeti.fourierCoeffOn_fourier`), the interval counterpart of
Mathlib's `fourierCoeff_fourier`, in particular for a circle `c + w e^{2πimt/(b-a)}`
(`TauCeti.fourierCoeffOn_const_add_mul_fourier`). Conversely, a function continuous on `[a, b]` is
determined there by its Fourier coefficients (`TauCeti.eqOn_Icc_of_fourierCoeffOn_eq`); the
endpoint `a`, which the coefficients do not see, is recovered by continuity.

For a function on `AddCircle T`, the Fourier coefficients are those of its lift on any period
interval (`TauCeti.fourierCoeff_eq_fourierCoeffOn`). On such an interval, each derivative of a
`C^k` periodic function multiplies its coefficients by `2πin / T`
(`TauCeti.fourierCoeffOn_iteratedDeriv`), since periodicity kills the boundary term of the
integration by parts.
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

/-- A pointwise bound on a function over the interval `(a, b]` bounds its Fourier coefficients
on `[a, b]`. -/
theorem norm_fourierCoeffOn_le (hab : a < b) {g : ℝ → E} {M : ℝ}
    (hM : ∀ x ∈ Ioc a b, ‖g x‖ ≤ M) (n : ℤ) : ‖fourierCoeffOn hab g n‖ ≤ M := by
  rw [fourierCoeffOn_eq_integral, norm_smul]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
    (f := fun x : ℝ ↦ fourier (-n) (x : AddCircle (b - a)) • g x) (C := M) fun x hx ↦ by
      simp only [norm_smul, fourier_apply, Circle.norm_coe, one_mul]
      rw [uIoc_of_le hab.le] at hx
      exact hM x hx
  have hba := sub_pos.2 hab
  rw [abs_of_pos hba] at h
  rw [norm_div, norm_one, Real.norm_of_nonneg hba.le]
  calc 1 / (b - a) * _ ≤ 1 / (b - a) * (M * (b - a)) := by gcongr
    _ = M := by field_simp

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


section Circle

open Complex
open scoped Real

variable {T : ℝ} [hT : Fact (0 < T)]

/-- The Fourier coefficients of a function on `AddCircle T` are those of its lift to `ℝ` on any
period interval `(a, a + T]`. -/
theorem fourierCoeff_eq_fourierCoeffOn (a : ℝ) (f : AddCircle T → ℂ) (n : ℤ) :
    fourierCoeff f n = fourierCoeffOn (lt_add_of_pos_right a hT.out) (fun x : ℝ ↦ f x) n := by
  rw [← fourierCoeff_liftIoc_eq]
  congr 1
  funext x
  simp [AddCircle.liftIoc, AddCircle.coe_equivIoc]

/-- Each derivative of a `C^k` function of period `T` multiplies its Fourier coefficients on a
period interval by `2πin / T`. At frequency `0` this says that the derivatives have mean zero. -/
theorem fourierCoeffOn_iteratedDeriv {f : ℝ → ℂ} {k : ℕ} (hf : ContDiff ℝ k f)
    (hper : Function.Periodic f T) (a : ℝ) (n : ℤ) {j : ℕ} (hj : j ≤ k) :
    fourierCoeffOn (lt_add_of_pos_right a hT.out) (iteratedDeriv j f) n =
      (2 * π * I * n / T) ^ j * fourierCoeffOn (lt_add_of_pos_right a hT.out) f n := by
  rcases eq_or_ne n 0 with rfl | hn
  · cases j with
    | zero => simp
    | succ j =>
      have hd := hf.differentiable_iteratedDeriv j (by exact_mod_cast hj)
      simp only [fourierCoeffOn_eq_integral, neg_zero, fourier_zero, one_smul, iteratedDeriv_succ]
      rw [intervalIntegral.integral_deriv_eq_sub (fun x _ ↦ (hd x))]
      · simp [hper.iteratedDeriv j a]
      · simpa [iteratedDeriv_succ] using
          (hf.continuous_iteratedDeriv (j + 1) (by exact_mod_cast hj)).intervalIntegrable a (a + T)
  induction j with
  | zero => simp
  | succ j ih =>
    have hd := hf.differentiable_iteratedDeriv j (by exact_mod_cast hj)
    have h := fourierCoeffOn_of_hasDerivAt (lt_add_of_pos_right a hT.out) hn
      (f := iteratedDeriv j f) (f' := iteratedDeriv (j + 1) f)
      (fun x _ ↦ by simpa [iteratedDeriv_succ] using (hd x).hasDerivAt)
      ((hf.continuous_iteratedDeriv (j + 1) (by exact_mod_cast hj)).intervalIntegrable _ _)
    rw [hper.iteratedDeriv j a, sub_self, mul_zero, zero_sub, ih (by omega)] at h
    have hT0 : (T : ℂ) ≠ 0 := ofReal_ne_zero.2 hT.out.ne'
    have hc : (2 * π * I * n : ℂ) ≠ 0 := by simp [hn, Real.pi_ne_zero, I_ne_zero]
    rw [pow_succ, mul_comm _ (2 * π * I * n / T), mul_assoc, h]
    push_cast
    field_simp
    ring

end Circle

end TauCeti
