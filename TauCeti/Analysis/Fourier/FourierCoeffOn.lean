/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import TauCeti.Analysis.Calculus.PeriodicDeriv
import TauCeti.Analysis.Fourier.Uniqueness
import TauCeti.Analysis.Fourier.AddCircle
import TauCeti.Analysis.Fourier.SineSeries
import TauCeti.MeasureTheory.Function.LpSeminorm.ContinuousOn
import TauCeti.MeasureTheory.Integral.Circle.Haar

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
(`TauCeti.fourierCoeffOn_const_add_mul_fourier`). Conversely, a function continuous on `[a, b]`
with values in a complete normed complex space is determined there by its Fourier coefficients
(`TauCeti.eqOn_Icc_of_fourierCoeffOn_eq`); the endpoint `a`, which the coefficients do not see,
is recovered by continuity. In particular, a complex function is a circle `c + w e^{2πist/(b-a)}`
on `[a, b]` exactly when its coefficients vanish outside the frequencies `0` and `s`
(`TauCeti.exists_eqOn_const_add_mul_fourier_iff`).

For a function on `AddCircle T`, the Fourier coefficients are those of its lift on any period
interval (`TauCeti.fourierCoeff_eq_fourierCoeffOn`). On such an interval, each derivative of a
`C^k` periodic function multiplies its coefficients by `2πin / T`
(`TauCeti.fourierCoeffOn_iteratedDeriv`), since periodicity kills the boundary term of the
integration by parts. The same holds for a function on the circle with values in any complete
normed complex space and a continuous derivative (`TauCeti.fourierCoeff_of_hasDerivAt`).

On the unit circle of `ℂ`, a function `φ : ℂ → ℂ` restricted to the circle and read on
`AddCircle (2 * π)` has the Fourier coefficients of `θ ↦ φ(e^{iθ})` on `[0, 2π]`
(`TauCeti.fourierCoeff_comp_toCircle`), and is continuous when `θ ↦ φ(e^{iθ})` is
(`TauCeti.continuous_comp_toCircle`). If these coefficients `c n` are summable, the Fourier series
`∑ c n w ^ n` sums to `φ w` at every point `w` of the unit circle
(`TauCeti.hasSum_fourierCoeffOn_circleMap_mul_zpow`).
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

/-- **Uniqueness of Fourier coefficients on an interval.** Two functions continuous on `[a, b]`
with values in a complete normed complex space and with the same Fourier coefficients on
`[a, b]` agree on `[a, b]`. -/
theorem eqOn_Icc_of_fourierCoeffOn_eq [CompleteSpace E] (hab : a < b) {f g : ℝ → E}
    (hf : ContinuousOn f [[a, b]]) (hg : ContinuousOn g [[a, b]])
    (h : ∀ n, fourierCoeffOn hab f n = fourierCoeffOn hab g n) :
    EqOn f g (Icc a b) := by
  have hfg : ContinuousOn (fun t ↦ f t - g t) [[a, b]] := hf.sub hg
  have hae := hfg.intervalIntegrable.1.ae_eq_zero_of_forall_fourierCoeffOn_eq_zero hab fun n ↦ by
    rw [fourierCoeffOn_sub hab hf.intervalIntegrable hg.intervalIntegrable, h, sub_self]
  rw [uIcc_of_le hab.le] at hfg
  intro t ht
  exact sub_eq_zero.1 (Measure.eqOn_Icc_of_ae_eq volume hab.ne
    (by rwa [Measure.restrict_congr_set Ioc_ae_eq_Icc] at hae) hfg continuousOn_const ht)

/-- A complex function continuous on `[a, b]` agrees there with the circle
`c + w e^{2πist/(b-a)}` for some `c` and `w` exactly when its Fourier coefficients on `[a, b]`
vanish outside the frequencies `0` and `s`; `c` and `w` are then its coefficients at `0` and
`s` when `s ≠ 0`. -/
theorem exists_eqOn_const_add_mul_fourier_iff (hab : a < b) {f : ℝ → ℂ}
    (hf : ContinuousOn f [[a, b]]) {s : ℤ} :
    (∃ c w : ℂ, ∀ t ∈ Icc a b, f t = c + w * fourier s (t : AddCircle (b - a))) ↔
      ∀ n, n ≠ 0 → n ≠ s → fourierCoeffOn hab f n = 0 := by
  constructor
  · rintro ⟨c, w, hcw⟩ n h0 hs'
    rw [fourierCoeffOn_congr_ae hab ((ae_restrict_mem measurableSet_Ioc).mono
      fun t ht ↦ hcw t (Ioc_subset_Icc_self ht)), fourierCoeffOn_const_add_mul_fourier]
    simp [h0, hs']
  · intro h
    by_cases hs : s = 0
    · subst s
      refine ⟨fourierCoeffOn hab f 0, 0,
        eqOn_Icc_of_fourierCoeffOn_eq hab hf
          (continuous_const.add (continuous_const.mul
            ((fourier 0).continuous.comp (AddCircle.continuous_mk' _)))).continuousOn fun n ↦ ?_⟩
      rw [fourierCoeffOn_const_add_mul_fourier]
      by_cases h0 : n = 0
      · simp [h0]
      · simp [h n h0 h0, h0]
    refine ⟨fourierCoeffOn hab f 0, fourierCoeffOn hab f s,
      eqOn_Icc_of_fourierCoeffOn_eq hab hf (continuous_const.add (continuous_const.mul
        ((fourier s).continuous.comp (AddCircle.continuous_mk' _)))).continuousOn fun n ↦ ?_⟩
    rw [fourierCoeffOn_const_add_mul_fourier]
    by_cases h0 : n = 0
    · simp [h0, hs]
    by_cases hs' : n = s
    · simp [hs', hs]
    · simp [h n h0 hs', h0, hs']


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

/-- A square-integrable function on `(a, b]` is the restriction of an `L²` class on the circle of
length `b - a` with the same Fourier coefficients. -/
theorem exists_Lp_fourierCoeff_eq_fourierCoeffOn [Fact (0 < b - a)] (hab : a < b) {g : ℝ → ℂ}
    (hgL2 : MemLp g 2 (volume.restrict (Ioc a b))) :
    ∃ G : Lp ℂ 2 (AddCircle.haarAddCircle (T := b - a)),
      ∀ n : ℤ, fourierCoeff G n = fourierCoeffOn hab g n := by
  have hG₀ : MemLp (AddCircle.liftIoc (b - a) a g) 2 AddCircle.haarAddCircle := by
    have hgL2' : MemLp g 2 (volume.restrict (Ioc a (a + (b - a)))) := by
      rwa [add_sub_cancel]
    exact hgL2'.memLp_liftIoc.haarAddCircle
  exact ⟨hG₀.toLp, fun n => by
    simp [fourierCoeff_congr_ae hG₀.coeFn_toLp, fourierCoeff_liftIoc_eq]⟩

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
    rw [pow_succ, mul_comm _ (2 * π * I * n / T), mul_assoc, h]
    push_cast
    field_simp
    ring

/-- Differentiating a function on `AddCircle T` multiplies its Fourier coefficients by
`2πin / T`, for functions with values in any complete normed complex space: if the lift of `f` to
`ℝ` has the continuous derivative `g`, then `ĝ(n) = 2πin / T • f̂(n)`. -/
theorem fourierCoeff_of_hasDerivAt [CompleteSpace E] {f g : AddCircle T → E}
    (hf : ∀ x : ℝ, HasDerivAt (fun y : ℝ ↦ f y) (g x) x) (hg : Continuous g) (n : ℤ) :
    fourierCoeff g n = (2 * π * I * n / T : ℂ) • fourierCoeff f n := by
  have hu (x : ℝ) := hasDerivAt_fourier_neg T n x
  have hgc : Continuous fun y : ℝ ↦ g y := hg.comp (AddCircle.continuous_mk' T)
  have hibp := intervalIntegral.integral_smul_deriv_eq_deriv_smul (a := 0) (b := T)
    (u := fun y : ℝ ↦ fourier (-n) (y : AddCircle T)) (v := fun y : ℝ ↦ f y)
    (fun x _ ↦ hu x) (fun x _ ↦ hf x)
    (Continuous.intervalIntegrable (by fun_prop) _ _) (hgc.intervalIntegrable _ _)
  -- The boundary term vanishes because `T = 0` on the circle.
  have hT0 : ((T : ℝ) : AddCircle T) = ((0 : ℝ) : AddCircle T) := by simp
  simp only [hT0, sub_self, zero_sub, mul_smul, intervalIntegral.integral_smul] at hibp
  rw [fourierCoeff_eq_intervalIntegral g n 0, fourierCoeff_eq_intervalIntegral f n 0, zero_add,
    hibp, smul_comm, ← neg_smul]
  congr 2
  ring

end Circle

section UnitCircle

open AddCircle Complex Metric
open scoped Real

local instance fourierCoeffOnTwoPiPos : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩

/-- The Fourier coefficients of `φ` restricted to the unit circle, as a function on
`AddCircle (2 * π)`, are those of `θ ↦ φ(e^{iθ})` on `[0, 2π]`. -/
theorem fourierCoeff_comp_toCircle (φ : ℂ → ℂ) (n : ℤ) :
    fourierCoeff (fun x : AddCircle (2 * π) ↦ φ (toCircle x)) n =
      fourierCoeffOn Real.two_pi_pos (fun θ ↦ φ (circleMap 0 1 θ)) n := by
  rw [fourierCoeff_eq_fourierCoeffOn 0]
  simp only [coe_toCircle_coe_eq_circleMap, zero_add]

/-- The restriction of `φ` to the unit circle is continuous as a function on `AddCircle (2 * π)`
when `θ ↦ φ(e^{iθ})` is continuous. -/
theorem continuous_comp_toCircle {X : Type*} [TopologicalSpace X] {φ : ℂ → X}
    (hφ : Continuous fun θ ↦ φ (circleMap 0 1 θ)) :
    Continuous fun x : AddCircle (2 * π) ↦ φ (toCircle x) := by
  refine (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.mpr ?_
  simpa [Function.comp_def, coe_toCircle_coe_eq_circleMap] using hφ

/-- **Fourier series on the unit circle.** If `θ ↦ φ(e^{iθ})` is continuous with summable Fourier
coefficients `c n` on `[0, 2π]`, then `∑ c n w ^ n = φ w` at every point `w` of the unit circle. -/
theorem hasSum_fourierCoeffOn_circleMap_mul_zpow {φ : ℂ → ℂ}
    (hφ : Continuous fun θ ↦ φ (circleMap 0 1 θ))
    (hs : Summable fun n : ℤ ↦ fourierCoeffOn Real.two_pi_pos (fun θ ↦ φ (circleMap 0 1 θ)) n)
    {w : ℂ} (hw : w ∈ sphere (0 : ℂ) 1) :
    HasSum (fun n : ℤ ↦ fourierCoeffOn Real.two_pi_pos (fun θ ↦ φ (circleMap 0 1 θ)) n * w ^ n)
      (φ w) := by
  have hs' : Summable (fourierCoeff fun x : AddCircle (2 * π) ↦ φ (toCircle x)) := by
    convert hs using 1
    exact funext (fourierCoeff_comp_toCircle φ)
  have := has_pointwise_sum_fourier_series_of_summable
    (f := ⟨fun x ↦ φ (toCircle x), continuous_comp_toCircle hφ⟩) hs'
    ((arg w : ℝ) : AddCircle (2 * π))
  simpa only [ContinuousMap.coe_mk, fourierCoeff_comp_toCircle,
    fourier_apply_eq_coe_toCircle_zpow, toCircle_arg_of_mem_sphere hw, smul_eq_mul] using this

end UnitCircle

end TauCeti
