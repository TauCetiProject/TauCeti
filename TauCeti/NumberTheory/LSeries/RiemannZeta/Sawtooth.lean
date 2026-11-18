/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.PSeriesComplex
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.Floor
import TauCeti.Analysis.Asymptotics.Sum.EulerMaclaurin
import TauCeti.Analysis.MellinTransform.UpperTail
import TauCeti.NumberTheory.LSeries.RiemannZeta

/-!
# First-order Euler–Maclaurin continuation of the Riemann zeta function

Applying first-order Euler–Maclaurin summation (`TauCeti.sum_Ioc_floor_eq_eulerMaclaurin_one`) to
`t ↦ (t : ℂ) ^ (-s)` on `[a, N]` with `0 < a` and letting `N → ∞` expresses `riemannZeta s` on
`1 < re s` as a finite Dirichlet sum up to `⌊a⌋₊`, a polar main term `a ^ (1 - s) / (s - 1)`, a
boundary term `B₁(fract a) * a ^ (-s)`, and the sawtooth remainder integral
`-s * ∫ t in Ioi a, B₁(fract t) * t ^ (-(s + 1))`, where `B₁(x) = bernoulliFun 1 x = x - 1 / 2`.

Because the periodic sawtooth kernel `t ↦ B₁(fract t)` is bounded by `1 / 2`, the upper-tail Mellin
interface in `TauCeti.Analysis.MellinTransform.UpperTail` makes the remainder integral converge
absolutely and define a holomorphic function on the entire open right half-plane `0 < re s`, with
explicit norm at most `a ^ (-re s) / (2 * re s)`. Multiplying by `s - 1` matches Mathlib's entire
completion `riemannZeta₁ s = (s - 1) * ζ(s)` on `1 < re s` and therefore across the connected
half-plane `0 < re s` by the identity theorem.

Specializing the cutoff `a` recovers several classical representations:
* `a = N` (`1 ≤ N : ℕ`) gives the integer-cutoff trapezoidal Euler–Maclaurin formula;
* `a = N + 1 / 2` (`N : ℕ`) makes the boundary term `B₁(1 / 2) = 0` vanish identically;
* `a = 1` gives the sawtooth and fractional-part representations of both `riemannZeta₀ s` on all of
  `0 < re s` (including `s = 1`) and `riemannZeta s` on `0 < re s`, `s ≠ 1`;
* differentiating the `riemannZeta₁` identity at `s = 1` via `deriv_riemannZeta₁_one` yields the
  general first-order Euler–Maclaurin formula for `Real.eulerMascheroniConstant` at any `0 < a`, as
  well as the improper integrals `∫ t in Ioi 1, B₁(fract t) / t ^ 2 = 1 / 2 - γ` and
  `∫ t in Ioi 1, fract t / t ^ 2 = 1 - γ`.

## Main results

* `TauCeti.abs_bernoulliFun_one_fract_le`: `|bernoulliFun 1 (Int.fract x)| ≤ 1 / 2`.
* `TauCeti.integrableOn_Ioi_bernoulliFun_one_fract_mul_cpow`,
  `TauCeti.differentiableOn_integral_Ioi_bernoulliFun_one_fract_mul_cpow`,
  `TauCeti.norm_integral_Ioi_bernoulliFun_one_fract_mul_cpow_le`: absolute convergence, holomorphy,
  and explicit `a ^ (-re s) / (2 * re s)` norm bound for the sawtooth remainder on `0 < re s`.
* `TauCeti.riemannZeta₁_eq_add_mul_sum_sawtooth`: regularized Euler–Maclaurin identity for
  `riemannZeta₁ s` across all `0 < re s` (including `s = 1`) for any `0 < a`.
* `TauCeti.riemannZeta_eq_sum_add_integral_sawtooth`: continuation of `riemannZeta s` to `0 < re s`,
  `s ≠ 1` with arbitrary positive real cutoff `0 < a`.
* `TauCeti.riemannZeta_eq_sum_nat_add_integral_sawtooth`,
  `TauCeti.riemannZeta_eq_sum_half_add_integral_sawtooth`: specializations to integer (`1 ≤ N`) and
  half-integer (`N + 1 / 2`) cutoffs.
* `TauCeti.riemannZeta₀_eq_one_half_sub_integral_sawtooth`,
  `TauCeti.riemannZeta₀_eq_one_sub_integral_fract`,
  `TauCeti.riemannZeta_eq_one_div_add_one_half_sub_integral_sawtooth`,
  `TauCeti.riemannZeta_eq_div_sub_integral_fract`: unit-cutoff sawtooth and fractional-part
  representations.
* `TauCeti.eulerMascheroniConstant_eq_sum_sub_log_add_sawtooth`,
  `TauCeti.integral_Ioi_bernoulliFun_one_fract_div_sq`, `TauCeti.integral_Ioi_fract_div_sq`:
  Euler–Maclaurin identities for the Euler–Mascheroni constant `γ`.

## References

* E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function* (2nd ed., rev. D. R. Heath-Brown),
  §2.1.
* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I. Classical Theory*, §1.3.
* H. Davenport, *Multiplicative Number Theory* (3rd ed.), Chapter 12.
-/

public section

open Complex Filter Finset MeasureTheory Set Asymptotics
open scoped Topology

namespace TauCeti

/-! ### Boundedness, integrability, and holomorphy of the sawtooth and fractional-part kernels -/

/-- The periodic first Bernoulli function `B₁(fract x) = fract x - 1 / 2` has absolute value at
most `1 / 2` everywhere on `ℝ`. -/
theorem abs_bernoulliFun_one_fract_le (x : ℝ) :
    |bernoulliFun 1 (Int.fract x)| ≤ 1 / 2 := by
  rw [bernoulliFun_one, abs_le]
  exact ⟨by linarith [Int.fract_nonneg x], by linarith [Int.fract_lt_one x]⟩

private lemma measurable_ofReal_bernoulliFun_one_fract :
    Measurable fun t : ℝ ↦ (bernoulliFun 1 (Int.fract t) : ℂ) :=
  continuous_ofReal.measurable.comp ((continuous_bernoulliFun 1).measurable.comp measurable_fract)

private lemma norm_ofReal_bernoulliFun_one_fract_le (t : ℝ) :
    ‖(bernoulliFun 1 (Int.fract t) : ℂ)‖ ≤ 1 / 2 := by
  simpa only [Complex.norm_real, Real.norm_eq_abs] using abs_bernoulliFun_one_fract_le t

private lemma locallyIntegrable_ofReal_bernoulliFun_one_fract :
    LocallyIntegrable (fun t : ℝ ↦ (bernoulliFun 1 (Int.fract t) : ℂ)) :=
  (locallyIntegrable_const (1 : ℝ)).mono
    measurable_ofReal_bernoulliFun_one_fract.aestronglyMeasurable
    (Eventually.of_forall fun t ↦
      (norm_ofReal_bernoulliFun_one_fract_le t).trans (by norm_num))

private lemma isBigO_ofReal_bernoulliFun_one_fract :
    (fun t : ℝ ↦ (bernoulliFun 1 (Int.fract t) : ℂ)) =O[atTop] fun t ↦ t ^ (0 : ℝ) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨1 / 2, ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t _
  simpa only [Real.rpow_zero, Real.norm_eq_abs, abs_one, mul_one] using
    norm_ofReal_bernoulliFun_one_fract_le t

private lemma measurable_ofReal_fract : Measurable fun t : ℝ ↦ ((Int.fract t : ℝ) : ℂ) :=
  continuous_ofReal.measurable.comp measurable_fract

private lemma norm_ofReal_fract_le (t : ℝ) : ‖((Int.fract t : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg t)]
  exact (Int.fract_lt_one t).le

private lemma locallyIntegrable_ofReal_fract :
    LocallyIntegrable (fun t : ℝ ↦ ((Int.fract t : ℝ) : ℂ)) :=
  (locallyIntegrable_const (1 : ℝ)).mono measurable_ofReal_fract.aestronglyMeasurable
    (Eventually.of_forall fun t ↦ by simpa using norm_ofReal_fract_le t)

private lemma isBigO_ofReal_fract :
    (fun t : ℝ ↦ ((Int.fract t : ℝ) : ℂ)) =O[atTop] fun t ↦ t ^ (0 : ℝ) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨1, ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t _
  simpa only [Real.rpow_zero, Real.norm_eq_abs, abs_one, mul_one] using norm_ofReal_fract_le t

/-- For `0 < a` and `0 < re s`, the sawtooth remainder integrand
`t ↦ B₁(fract t) * t ^ (-(s + 1))` is integrable on `(a, ∞)`. -/
theorem integrableOn_Ioi_bernoulliFun_one_fract_mul_cpow {a : ℝ} (ha : 0 < a) {s : ℂ}
    (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ ↦ (bernoulliFun 1 (Int.fract t) : ℂ) * (t : ℂ) ^ (-(s + 1)))
      (Set.Ioi a) :=
  integrableOn_Ioi_mul_cpow_of_isBigO ha
    (locallyIntegrable_ofReal_bernoulliFun_one_fract.locallyIntegrableOn _)
    isBigO_ofReal_bernoulliFun_one_fract hs

/-- For `0 < a`, the sawtooth remainder integral `s ↦ ∫ t in Ioi a, B₁(fract t) * t ^ (-(s + 1))`
is complex-differentiable on `{s | 0 < s.re}`. -/
theorem differentiableOn_integral_Ioi_bernoulliFun_one_fract_mul_cpow {a : ℝ} (ha : 0 < a) :
    DifferentiableOn ℂ
      (fun s : ℂ ↦ ∫ t in Set.Ioi a, (bernoulliFun 1 (Int.fract t) : ℂ) * (t : ℂ) ^ (-(s + 1)))
      {s | 0 < s.re} :=
  differentiableOn_integral_Ioi_mul_cpow_of_isBigO ha isBigO_ofReal_bernoulliFun_one_fract

/-- For `0 < a` and `0 < re s`, the sawtooth remainder integral on `(a, ∞)` has norm at most
`a ^ (-re s) / (2 * re s)`. -/
theorem norm_integral_Ioi_bernoulliFun_one_fract_mul_cpow_le {a : ℝ} (ha : 0 < a) {s : ℂ}
    (hs : 0 < s.re) :
    ‖∫ t in Set.Ioi a, (bernoulliFun 1 (Int.fract t) : ℂ) * (t : ℂ) ^ (-(s + 1))‖ ≤
      a ^ (-s.re) / (2 * s.re) := by
  calc
    _ ≤ (1 / 2) * a ^ (-s.re) / s.re :=
      norm_integral_Ioi_mul_cpow_le_of_bound ha
        (fun t _ ↦ norm_ofReal_bernoulliFun_one_fract_le t) hs
    _ = a ^ (-s.re) / (2 * s.re) := by ring

/-- For `0 < a` and `0 < re s`, the fractional-part remainder integrand
`t ↦ fract t * t ^ (-(s + 1))` is integrable on `(a, ∞)`. -/
theorem integrableOn_Ioi_fract_mul_cpow {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ ↦ ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))) (Set.Ioi a) :=
  integrableOn_Ioi_mul_cpow_of_isBigO ha
    (locallyIntegrable_ofReal_fract.locallyIntegrableOn _) isBigO_ofReal_fract hs

/-- For `0 < a`, the fractional-part integral `s ↦ ∫ t in Ioi a, fract t * t ^ (-(s + 1))` is
complex-differentiable on `{s | 0 < s.re}`. -/
theorem differentiableOn_integral_Ioi_fract_mul_cpow {a : ℝ} (ha : 0 < a) :
    DifferentiableOn ℂ
      (fun s : ℂ ↦ ∫ t in Set.Ioi a, ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)))
      {s | 0 < s.re} :=
  differentiableOn_integral_Ioi_mul_cpow_of_isBigO ha isBigO_ofReal_fract

/-- For `0 < a` and `0 < re s`, the fractional-part remainder integral on `(a, ∞)` has norm at most
`a ^ (-re s) / re s`. -/
theorem norm_integral_Ioi_fract_mul_cpow_le {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : 0 < s.re) :
    ‖∫ t in Set.Ioi a, ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))‖ ≤ a ^ (-s.re) / s.re := by
  simpa only [one_mul] using
    norm_integral_Ioi_mul_cpow_le_of_bound ha (fun t _ ↦ norm_ofReal_fract_le t) hs

/-- Relating the sawtooth upper-tail integral to the fractional-part upper-tail integral on
`(a, ∞)` via `B₁(fract t) = fract t - 1 / 2`. -/
private lemma integral_Ioi_bernoulliFun_one_fract_eq_sub {a : ℝ} (ha : 0 < a) {s : ℂ}
    (hs : 0 < s.re) :
    (∫ t in Set.Ioi a, (bernoulliFun 1 (Int.fract t) : ℂ) * (t : ℂ) ^ (-(s + 1))) =
      (∫ t in Set.Ioi a, ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))) -
        (a : ℂ) ^ (-s) / (2 * s) := by
  have hs0 : s ≠ 0 := fun h ↦ by simp [h] at hs
  have hre : (-(s + 1)).re < -1 := by simp only [neg_re, add_re, one_re]; linarith
  have hc : IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ (-(s + 1))) (Set.Ioi a) :=
    integrableOn_Ioi_cpow_of_lt hre ha
  have hcongr : (∫ t in Set.Ioi a, (bernoulliFun 1 (Int.fract t) : ℂ) * (t : ℂ) ^ (-(s + 1))) =
      ∫ t in Set.Ioi a,
        (((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) - (1 / 2 : ℂ) * (t : ℂ) ^ (-(s + 1))) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
    simp only [bernoulliFun_one, ofReal_sub, ofReal_div, ofReal_one, ofReal_ofNat]
    ring
  rw [hcongr, integral_sub (integrableOn_Ioi_fract_mul_cpow ha hs) (hc.const_mul _),
    integral_const_mul, integral_Ioi_cpow_of_lt hre ha]
  have hexp : -(s + 1) + 1 = -s := by ring
  rw [hexp]
  field_simp [hs0]

/-! ### Finite Euler–Maclaurin step and passage to `N → ∞` on `1 < re s` -/

private lemma sum_Icc_split_Ioc {m N : ℕ} (hm : m ≤ N) (f : ℕ → ℂ) :
    ∑ k ∈ Finset.Icc 1 N, f k =
      (∑ k ∈ Finset.Icc 1 m, f k) + ∑ k ∈ Finset.Ioc m N, f k := by
  have hunion : Finset.Icc 1 m ∪ Finset.Ioc m N = Finset.Icc 1 N := by
    ext k
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hdisj : Disjoint (Finset.Icc 1 m) (Finset.Ioc m N) :=
    Finset.disjoint_left.mpr fun k hk₁ hk₂ ↦ by
      simp only [Finset.mem_Icc, Finset.mem_Ioc] at hk₁ hk₂
      omega
  rw [← hunion, Finset.sum_union hdisj]

private lemma sum_Ioc_cpow_neg_eq {a : ℝ} (ha : 0 < a) {N : ℕ} (haN : a ≤ N) (s : ℂ) :
    ∑ k ∈ Finset.Ioc ⌊a⌋₊ N, (k : ℂ) ^ (-s) =
      (bernoulliFun 1 (Int.fract a) : ℂ) * (a : ℂ) ^ (-s) + (N : ℂ) ^ (-s) / 2 +
        (∫ t in a..(N : ℝ), (t : ℂ) ^ (-s)) -
        s * ∫ t in a..(N : ℝ), (bernoulliFun 1 (Int.fract t) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
  let f : ℝ → ℂ := fun t ↦ (t : ℂ) ^ (-s)
  have hpos {t : ℝ} (ht : t ∈ Set.Icc a (N : ℝ)) : 0 < t := ha.trans_le ht.1
  have hdiff (t : ℝ) (ht : t ∈ Set.Icc a (N : ℝ)) : DifferentiableAt ℝ f t :=
    differentiableAt_id.ofReal_cpow_const (-s) (hpos ht).ne'
  have hderiv_eq : Set.EqOn (deriv f) (fun t : ℝ ↦ -s * (t : ℂ) ^ (-s - 1)) (Set.Icc a N) := by
    intro t ht
    exact Complex.deriv_ofReal_cpow_const (-s) (hpos ht).ne'
  have hcont : ContinuousOn (fun t : ℝ ↦ -s * (t : ℂ) ^ (-s - 1)) (Set.Icc a N) :=
    continuousOn_const.mul <| Complex.continuous_ofReal.continuousOn.cpow_const fun t ht ↦
      Or.inl (by simpa using hpos ht)
  have hint : IntervalIntegrable (deriv f) volume a N :=
    (hcont.congr hderiv_eq).intervalIntegrable_of_Icc haN
  have hEM := sum_Ioc_floor_eq_eulerMaclaurin_one ha.le haN hdiff hint
  rw [Nat.floor_natCast] at hEM
  have hrem : (∫ t in a..(N : ℝ), bernoulliFun 1 (Int.fract t) • deriv f t) =
      -s * ∫ t in a..(N : ℝ), (bernoulliFun 1 (Int.fract t) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    have ht' : t ∈ Set.Icc a N := (Set.uIcc_of_le haN) ▸ ht
    rw [hderiv_eq ht', Complex.real_smul, show -s - 1 = -(s + 1) by ring]
    ring
  have hB0 : (bernoulliFun 1 0 : ℂ) = -1 / 2 := by
    rw [bernoulliFun_one]
    norm_num
  rw [hrem] at hEM
  simp only [f, Complex.real_smul, ofReal_natCast] at hEM
  rw [Int.fract_natCast, hB0] at hEM
  linear_combination hEM

private lemma tendsto_sum_Icc_cpow_neg {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun N : ℕ ↦ ∑ k ∈ Finset.Icc 1 N, (k : ℂ) ^ (-s)) atTop (𝓝 (riemannZeta s)) := by
  have hsumm : Summable (fun n : ℕ ↦ 1 / ((n : ℂ) + 1) ^ s) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr (Complex.summable_one_div_nat_cpow.2 hs)
  have hsum : HasSum (fun n : ℕ ↦ ((n + 1 : ℕ) : ℂ) ^ (-s)) (riemannZeta s) := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
    refine hsumm.hasSum.congr_fun fun n ↦ ?_
    rw [Nat.cast_add, Nat.cast_one, one_div, cpow_neg]
  refine hsum.tendsto_sum_nat.congr fun N ↦ ?_
  have hrange := (Finset.sum_Ico_eq_sum_range (fun k : ℕ ↦ (k : ℂ) ^ (-s)) 1 (N + 1)).symm
  rw [Nat.add_sub_cancel, Finset.Ico_add_one_right_eq_Icc] at hrange
  refine (Finset.sum_congr rfl fun k _ ↦ ?_).trans hrange
  rw [Nat.add_comm]

private lemma tendsto_natCast_cpow_neg_zero {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun N : ℕ ↦ (N : ℂ) ^ (-s)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine ((tendsto_rpow_neg_atTop hs).comp tendsto_natCast_atTop_atTop).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  dsimp only [Function.comp_def]
  rw [← ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hN', neg_re]

/-- First-order Euler–Maclaurin representation of `riemannZeta s` in the half-plane of absolute
convergence `1 < re s`. -/
private lemma riemannZeta_eq_sum_add_integral_sawtooth_of_one_lt_re {s : ℂ} (hs : 1 < s.re)
    {a : ℝ} (ha : 0 < a) :
    riemannZeta s =
      (∑ n ∈ Finset.Icc 1 ⌊a⌋₊, (n : ℂ) ^ (-s)) +
        (a : ℂ) ^ (1 - s) / (s - 1) +
        (bernoulliFun 1 (Int.fract a) : ℂ) * (a : ℂ) ^ (-s) -
        s * ∫ t in Set.Ioi a, (bernoulliFun 1 (Int.fract t) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
  have hs0 : 0 < s.re := zero_lt_one.trans hs
  have hs1 : s - 1 ≠ 0 := fun h ↦ by
    have := congrArg Complex.re h
    simp at this
    linarith
  have hre : (-s).re < -1 := by simp only [neg_re]; linarith
  have hI₁ : Tendsto (fun N : ℕ ↦ ∫ t in a..(N : ℝ), (t : ℂ) ^ (-s)) atTop
      (𝓝 ((a : ℂ) ^ (1 - s) / (s - 1))) := by
    have hlim := intervalIntegral_tendsto_integral_Ioi a
      (integrableOn_Ioi_cpow_of_lt hre ha) tendsto_natCast_atTop_atTop
    rw [integral_Ioi_cpow_of_lt hre ha] at hlim
    have hval : -(a : ℂ) ^ (-s + 1) / (-s + 1) = (a : ℂ) ^ (1 - s) / (s - 1) := by
      rw [show -s + 1 = -(s - 1) by ring, show (1 - s : ℂ) = -(s - 1) by ring]
      field_simp [hs1, neg_ne_zero.mpr hs1]
    rwa [hval] at hlim
  have hI₂ : Tendsto (fun N : ℕ ↦
      ∫ t in a..(N : ℝ), (bernoulliFun 1 (Int.fract t) : ℂ) * (t : ℂ) ^ (-(s + 1))) atTop
      (𝓝 (∫ t in Set.Ioi a, (bernoulliFun 1 (Int.fract t) : ℂ) * (t : ℂ) ^ (-(s + 1)))) :=
    intervalIntegral_tendsto_integral_Ioi a
      (integrableOn_Ioi_bernoulliFun_one_fract_mul_cpow ha hs0) tendsto_natCast_atTop_atTop
  have hN0 : Tendsto (fun N : ℕ ↦ (N : ℂ) ^ (-s) / 2) atTop (𝓝 0) := by
    simpa using (tendsto_natCast_cpow_neg_zero hs0).div_const (2 : ℂ)
  have hrhs := ((tendsto_const_nhds (x := (∑ n ∈ Finset.Icc 1 ⌊a⌋₊, (n : ℂ) ^ (-s)) +
      (bernoulliFun 1 (Int.fract a) : ℂ) * (a : ℂ) ^ (-s))).add hN0 |>.add hI₁).sub
    (hI₂.const_mul s)
  have hlim : Tendsto (fun N : ℕ ↦ ∑ k ∈ Finset.Icc 1 N, (k : ℂ) ^ (-s)) atTop
      (𝓝 (((∑ n ∈ Finset.Icc 1 ⌊a⌋₊, (n : ℂ) ^ (-s)) +
        (bernoulliFun 1 (Int.fract a) : ℂ) * (a : ℂ) ^ (-s) + 0 +
        (a : ℂ) ^ (1 - s) / (s - 1)) -
        s * ∫ t in Set.Ioi a, (bernoulliFun 1 (Int.fract t) : ℂ) * (t : ℂ) ^ (-(s + 1)))) := by
    refine hrhs.congr' ?_
    filter_upwards [eventually_ge_atTop (⌈a⌉₊ : ℕ)] with N hN
    have haN : a ≤ (N : ℝ) := (Nat.le_ceil a).trans (Nat.cast_le.mpr hN)
    have hfl : ⌊a⌋₊ ≤ N := Nat.floor_le_of_le haN
    rw [sum_Icc_split_Ioc hfl, sum_Ioc_cpow_neg_eq ha haN]
    ring
  linear_combination tendsto_nhds_unique (tendsto_sum_Icc_cpow_neg hs) hlim

/-! ### Continuation across the open right half-plane `0 < re s` -/

/-- Auxiliary holomorphic part of the sawtooth representation at cutoff `a > 0`:
`s ↦ ∑_{n=1}^{⌊a⌋₊} n ^ (-s) + B₁(fract a) * a ^ (-s)` minus the upper-tail sawtooth integral. -/
private noncomputable def sawtoothReg (a : ℝ) (s : ℂ) : ℂ :=
  (∑ n ∈ Finset.Icc 1 ⌊a⌋₊, (n : ℂ) ^ (-s)) +
    (bernoulliFun 1 (Int.fract a) : ℂ) * (a : ℂ) ^ (-s) -
    s * ∫ t in Set.Ioi a, (bernoulliFun 1 (Int.fract t) : ℂ) * (t : ℂ) ^ (-(s + 1))

private lemma differentiableOn_sawtoothReg {a : ℝ} (ha : 0 < a) :
    DifferentiableOn ℂ (sawtoothReg a) {s | 0 < s.re} := by
  unfold sawtoothReg
  have hsum : Differentiable ℂ (fun s : ℂ ↦ ∑ n ∈ Finset.Icc 1 ⌊a⌋₊, (n : ℂ) ^ (-s)) := by
    refine Differentiable.fun_sum fun n hn ↦ ?_
    have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by linarith [(Finset.mem_Icc.mp hn).1])
    exact differentiable_id.neg.const_cpow (Or.inl hn0)
  have hbdry : Differentiable ℂ
      (fun s : ℂ ↦ (bernoulliFun 1 (Int.fract a) : ℂ) * (a : ℂ) ^ (-s)) :=
    (differentiable_id.neg.const_cpow (Or.inl (ofReal_ne_zero.mpr ha.ne'))).const_mul _
  exact (hsum.differentiableOn.add hbdry.differentiableOn).sub
    (differentiableOn_id.mul (differentiableOn_integral_Ioi_bernoulliFun_one_fract_mul_cpow ha))

/-- **Regularized sawtooth Euler–Maclaurin formula on `0 < re s`.** For every `0 < re s` (including
`s = 1`) and every positive real cutoff `0 < a`, Mathlib's entire completion
`riemannZeta₁ s = 1 + (s - 1) * riemannZeta₀ s` equals `a ^ (1 - s)` plus `(s - 1)` times the
holomorphic sawtooth expression at `a`. -/
theorem riemannZeta₁_eq_add_mul_sum_sawtooth {s : ℂ} (hs : 0 < s.re) {a : ℝ} (ha : 0 < a) :
    riemannZeta₁ s =
      (a : ℂ) ^ (1 - s) +
        (s - 1) * ((∑ n ∈ Finset.Icc 1 ⌊a⌋₊, (n : ℂ) ^ (-s)) +
          (bernoulliFun 1 (Int.fract a) : ℂ) * (a : ℂ) ^ (-s) -
          s * ∫ t in Set.Ioi a, (bernoulliFun 1 (Int.fract t) : ℂ) * (t : ℂ) ^ (-(s + 1))) := by
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
  have hZ : AnalyticOnNhd ℂ riemannZeta₁ {z : ℂ | 0 < z.re} :=
    differentiable_riemannZeta₁.differentiableOn.analyticOnNhd hopen
  have hR : AnalyticOnNhd ℂ (fun z : ℂ ↦ (a : ℂ) ^ (1 - z) + (z - 1) * sawtoothReg a z)
      {z : ℂ | 0 < z.re} := by
    have ha0 : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha.ne'
    exact (((differentiable_const (1 : ℂ)).sub differentiable_id).const_cpow
      (Or.inl ha0)).differentiableOn.add
        ((differentiableOn_id.sub_const 1).mul (differentiableOn_sawtoothReg ha)) |>.analyticOnNhd
      hopen
  have heq : riemannZeta₁ =ᶠ[𝓝 (2 : ℂ)]
      fun z : ℂ ↦ (a : ℂ) ^ (1 - z) + (z - 1) * sawtoothReg a z := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (by norm_num : (2 : ℂ) ∈ {z : ℂ | 1 < z.re})] with z hz
    have hz₁ : z ≠ 1 := fun h ↦ by simp [h] at hz
    have hz₁' : z - 1 ≠ 0 := sub_ne_zero.mpr hz₁
    have hζ := riemannZeta_eq_sum_add_integral_sawtooth_of_one_lt_re hz ha
    rw [riemannZeta_eq_inv_sub_mul hz₁] at hζ
    unfold sawtoothReg
    calc
      riemannZeta₁ z = (z - 1) * ((z - 1)⁻¹ * riemannZeta₁ z) := by field_simp [hz₁']
      _ = (z - 1) * _ := by rw [hζ]
      _ = _ := by field_simp [hz₁']; ring
  exact hZ.eqOn_of_preconnected_of_eventuallyEq hR (convex_halfSpace_re_gt 0).isPreconnected
    (by norm_num : (2 : ℂ) ∈ {z : ℂ | 0 < z.re}) heq hs

/-- **Sawtooth Euler–Maclaurin continuation of `riemannZeta`.** On the punctured right half-plane
`0 < re s`, `s ≠ 1`, for any positive real cutoff `0 < a`,
`ζ(s) = ∑_{n=1}^{⌊a⌋₊} n ^ (-s) + a ^ (1 - s) / (s - 1) + B₁(fract a) * a ^ (-s)` minus
`s * ∫ t in Ioi a, B₁(fract t) * t ^ (-(s + 1))`. -/
theorem riemannZeta_eq_sum_add_integral_sawtooth {s : ℂ} (hs : 0 < s.re) (hs₁ : s ≠ 1)
    {a : ℝ} (ha : 0 < a) :
    riemannZeta s =
      (∑ n ∈ Finset.Icc 1 ⌊a⌋₊, (n : ℂ) ^ (-s)) +
        (a : ℂ) ^ (1 - s) / (s - 1) +
        (bernoulliFun 1 (Int.fract a) : ℂ) * (a : ℂ) ^ (-s) -
        s * ∫ t in Set.Ioi a, (bernoulliFun 1 (Int.fract t) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
  have hs₁' : s - 1 ≠ 0 := sub_ne_zero.mpr hs₁
  rw [riemannZeta_eq_inv_sub_mul hs₁, riemannZeta₁_eq_add_mul_sum_sawtooth hs ha]
  field_simp [hs₁']
  ring

/-- **Integer-cutoff Euler–Maclaurin continuation of `riemannZeta`.** On `0 < re s`, `s ≠ 1`, for
any positive integer `1 ≤ N`, the boundary sawtooth term takes the trapezoidal value
`B₁(0) * N ^ (-s) = -N ^ (-s) / 2`. -/
theorem riemannZeta_eq_sum_nat_add_integral_sawtooth {s : ℂ} (hs : 0 < s.re) (hs₁ : s ≠ 1)
    {N : ℕ} (hN : 1 ≤ N) :
    riemannZeta s =
      (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)) +
        (N : ℂ) ^ (1 - s) / (s - 1) - (N : ℂ) ^ (-s) / 2 -
        s * ∫ t in Set.Ioi (N : ℝ), (bernoulliFun 1 (Int.fract t) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  rw [riemannZeta_eq_sum_add_integral_sawtooth hs hs₁ hN0, Nat.floor_natCast, Int.fract_natCast,
    bernoulliFun_one, ofReal_natCast]
  push_cast
  ring

/-- **Half-integer-cutoff Euler–Maclaurin continuation of `riemannZeta`.** At `a = N + 1 / 2`
(`N : ℕ`, including `N = 0`), the periodic Bernoulli function vanishes at the cutoff
(`B₁(1 / 2) = 0`), eliminating the boundary term completely. -/
theorem riemannZeta_eq_sum_half_add_integral_sawtooth {s : ℂ} (hs : 0 < s.re) (hs₁ : s ≠ 1)
    (N : ℕ) :
    riemannZeta s =
      (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)) +
        ((N : ℂ) + 1 / 2) ^ (1 - s) / (s - 1) -
        s * ∫ t in Set.Ioi ((N : ℝ) + 1 / 2),
          (bernoulliFun 1 (Int.fract t) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
  have ha : 0 < (N : ℝ) + 1 / 2 := by positivity
  have hfl : ⌊(N : ℝ) + 1 / 2⌋₊ = N :=
    (Nat.floor_eq_iff ha.le).mpr ⟨by linarith, by linarith⟩
  have hfr : bernoulliFun 1 (Int.fract ((N : ℝ) + 1 / 2)) = 0 := by
    rw [Int.fract_natCast_add, Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩, bernoulliFun_one,
      sub_self]
  have hcast : (((N : ℝ) + 1 / 2 : ℝ) : ℂ) = (N : ℂ) + 1 / 2 := by push_cast; ring
  rw [riemannZeta_eq_sum_add_integral_sawtooth hs hs₁ ha, hfl, hfr, hcast]
  simp only [ofReal_zero, zero_mul, add_zero]

/-! ### Unit-cutoff (`a = 1`) formulas for `riemannZeta₀` and `riemannZeta` -/

/-- On the entire open right half-plane `0 < re s` (including `s = 1`), the pole-removed zeta
function `riemannZeta₀ s` equals `1 / 2 - s * ∫ t in Ioi 1, B₁(fract t) * t ^ (-(s + 1))`. -/
theorem riemannZeta₀_eq_one_half_sub_integral_sawtooth {s : ℂ} (hs : 0 < s.re) :
    riemannZeta₀ s =
      1 / 2 - s * ∫ t in Set.Ioi (1 : ℝ),
        (bernoulliFun 1 (Int.fract t) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
  have hZ : AnalyticOnNhd ℂ riemannZeta₀ {z : ℂ | 0 < z.re} :=
    differentiable_riemannZeta₀.differentiableOn.analyticOnNhd hopen
  have hR : AnalyticOnNhd ℂ (fun z : ℂ ↦
      1 / 2 - z * ∫ t in Set.Ioi (1 : ℝ),
        (bernoulliFun 1 (Int.fract t) : ℂ) * (t : ℂ) ^ (-(z + 1))) {z : ℂ | 0 < z.re} :=
    ((differentiableOn_const (1 / 2 : ℂ)).sub
      (differentiableOn_id.mul
        (differentiableOn_integral_Ioi_bernoulliFun_one_fract_mul_cpow zero_lt_one))).analyticOnNhd
      hopen
  have heq : riemannZeta₀ =ᶠ[𝓝 (2 : ℂ)] fun z : ℂ ↦
      1 / 2 - z * ∫ t in Set.Ioi (1 : ℝ),
        (bernoulliFun 1 (Int.fract t) : ℂ) * (t : ℂ) ^ (-(z + 1)) := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (by norm_num : (2 : ℂ) ∈ {z : ℂ | 1 < z.re})] with z hz
    have hz₁ : z ≠ 1 := fun h ↦ by simp [h] at hz
    have hB0 : (bernoulliFun 1 0 : ℂ) = -1 / 2 := by
      rw [bernoulliFun_one]
      norm_num
    have h₁ := riemannZeta₁_eq_add_mul_sum_sawtooth (zero_lt_one.trans hz) zero_lt_one
    unfold riemannZeta₁ at h₁
    rw [Int.fract_one, hB0] at h₁
    simp only [Nat.floor_one, Finset.Icc_self, Finset.sum_singleton, Nat.cast_one, one_cpow,
      ofReal_one, mul_one] at h₁
    apply mul_left_cancel₀ (sub_ne_zero.mpr hz₁)
    linear_combination h₁
  exact hZ.eqOn_of_preconnected_of_eventuallyEq hR (convex_halfSpace_re_gt 0).isPreconnected
    (by norm_num : (2 : ℂ) ∈ {z : ℂ | 0 < z.re}) heq hs

/-- On the entire open right half-plane `0 < re s` (including `s = 1`), the pole-removed zeta
function `riemannZeta₀ s` equals `1 - s * ∫ t in Ioi 1, fract t * t ^ (-(s + 1))`. -/
theorem riemannZeta₀_eq_one_sub_integral_fract {s : ℂ} (hs : 0 < s.re) :
    riemannZeta₀ s =
      1 - s * ∫ t in Set.Ioi (1 : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
  have hs0 : s ≠ 0 := fun h ↦ by simp [h] at hs
  rw [riemannZeta₀_eq_one_half_sub_integral_sawtooth hs,
    integral_Ioi_bernoulliFun_one_fract_eq_sub zero_lt_one hs, ofReal_one, one_cpow]
  field_simp [hs0]
  ring

/-- Unit-cutoff sawtooth representation on `0 < re s`, `s ≠ 1`:
`ζ(s) = 1 / (s - 1) + 1 / 2 - s * ∫ t in Ioi 1, B₁(fract t) * t ^ (-(s + 1))`. -/
theorem riemannZeta_eq_one_div_add_one_half_sub_integral_sawtooth {s : ℂ} (hs : 0 < s.re)
    (hs₁ : s ≠ 1) :
    riemannZeta s =
      1 / (s - 1) + 1 / 2 - s * ∫ t in Set.Ioi (1 : ℝ),
        (bernoulliFun 1 (Int.fract t) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
  rw [riemannZeta_eq_inv_sub_add hs₁, riemannZeta₀_eq_one_half_sub_integral_sawtooth hs, one_div]
  ring

/-- Classical fractional-part representation (Titchmarsh (2.1.4)) on `0 < re s`, `s ≠ 1`:
`ζ(s) = s / (s - 1) - s * ∫ t in Ioi 1, fract t * t ^ (-(s + 1))`. -/
theorem riemannZeta_eq_div_sub_integral_fract {s : ℂ} (hs : 0 < s.re) (hs₁ : s ≠ 1) :
    riemannZeta s =
      s / (s - 1) - s * ∫ t in Set.Ioi (1 : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
  have hs₁' : s - 1 ≠ 0 := sub_ne_zero.mpr hs₁
  rw [riemannZeta_eq_inv_sub_add hs₁, riemannZeta₀_eq_one_sub_integral_fract hs]
  field_simp [hs₁']
  ring

/-! ### Euler–Mascheroni constant identities from `s = 1` -/

private lemma integral_Ioi_ofReal_cpow_neg_two {g : ℝ → ℝ} {a : ℝ} (ha : 0 < a) :
    (∫ t in Set.Ioi a, (g t : ℂ) * (t : ℂ) ^ (-((1 : ℂ) + 1))) =
      ((∫ t in Set.Ioi a, g t / t ^ 2 : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
  have ht0 : 0 ≤ t := (ha.trans ht).le
  have hexp : (-((1 : ℂ) + 1)) = ((-2 : ℝ) : ℂ) := by norm_num
  rw [hexp, ← ofReal_cpow ht0, ← ofReal_mul, Real.rpow_neg ht0, Real.rpow_two, div_eq_mul_inv]

/-- **First-order Euler–Maclaurin formula for the Euler–Mascheroni constant `γ` at any positive
cutoff `0 < a`.** Obtained by differentiating `riemannZeta₁_eq_add_mul_sum_sawtooth` at `s = 1`,
where `(s - 1)` vanishes and `deriv riemannZeta₁ 1 = γ`. -/
theorem eulerMascheroniConstant_eq_sum_sub_log_add_sawtooth {a : ℝ} (ha : 0 < a) :
    Real.eulerMascheroniConstant =
      (∑ n ∈ Finset.Icc 1 ⌊a⌋₊, (n : ℝ)⁻¹) - Real.log a +
        bernoulliFun 1 (Int.fract a) / a -
        ∫ t in Set.Ioi a, bernoulliFun 1 (Int.fract t) / t ^ 2 := by
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
  have hmem : (1 : ℂ) ∈ {z : ℂ | 0 < z.re} := by simp
  have heq : riemannZeta₁ =ᶠ[𝓝 (1 : ℂ)]
      fun z : ℂ ↦ (a : ℂ) ^ (1 - z) + (z - 1) * sawtoothReg a z := by
    filter_upwards [hopen.mem_nhds hmem] with z hz
    exact riemannZeta₁_eq_add_mul_sum_sawtooth hz ha
  have hd₁ : HasDerivAt (fun z : ℂ ↦ (a : ℂ) ^ (1 - z)) (-(Real.log a : ℂ)) 1 := by
    have h := ((hasDerivAt_const (1 : ℂ) (1 : ℂ)).sub (hasDerivAt_id (1 : ℂ))).const_cpow
      (Or.inl (ofReal_ne_zero.mpr ha.ne'))
    simpa [ofReal_log ha.le] using h
  have hd₂ : HasDerivAt (fun z : ℂ ↦ (z - 1) * sawtoothReg a z) (sawtoothReg a 1) 1 := by
    have hreg :=
      ((differentiableOn_sawtoothReg ha).differentiableAt (hopen.mem_nhds hmem)).hasDerivAt
    have hmul := ((hasDerivAt_id (1 : ℂ)).sub_const (1 : ℂ)).mul hreg
    simpa only [Pi.mul_def, id_eq, sub_self, zero_mul, add_zero, one_mul] using hmul
  have hd : HasDerivAt (fun z : ℂ ↦ (a : ℂ) ^ (1 - z) + (z - 1) * sawtoothReg a z)
      (-(Real.log a : ℂ) + sawtoothReg a 1) 1 := hd₁.add hd₂
  have hγ : (Real.eulerMascheroniConstant : ℂ) = -(Real.log a : ℂ) + sawtoothReg a 1 := by
    rw [← deriv_riemannZeta₁_one, heq.deriv_eq, hd.deriv]
  have hval : sawtoothReg a 1 =
      (((∑ n ∈ Finset.Icc 1 ⌊a⌋₊, (n : ℝ)⁻¹) + bernoulliFun 1 (Int.fract a) / a -
        ∫ t in Set.Ioi a, bernoulliFun 1 (Int.fract t) / t ^ 2 : ℝ) : ℂ) := by
    unfold sawtoothReg
    rw [one_mul, integral_Ioi_ofReal_cpow_neg_two ha, cpow_neg_one, div_eq_mul_inv]
    push_cast
    congr 2
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    rw [cpow_neg_one]
  rw [hval] at hγ
  have hre := congrArg Complex.re hγ
  simp only [ofReal_re, add_re, neg_re] at hre
  linarith

/-- Improper integral of the periodic sawtooth kernel `B₁(fract t) / t ^ 2` on `(1, ∞)`:
`∫ t in Ioi 1, B₁(fract t) / t ^ 2 = 1 / 2 - γ`. -/
theorem integral_Ioi_bernoulliFun_one_fract_div_sq :
    ∫ t in Set.Ioi (1 : ℝ), bernoulliFun 1 (Int.fract t) / t ^ 2 =
      1 / 2 - Real.eulerMascheroniConstant := by
  have h := riemannZeta₀_eq_one_half_sub_integral_sawtooth (s := 1) (by simp)
  rw [riemannZeta₀_one, one_mul, integral_Ioi_ofReal_cpow_neg_two zero_lt_one] at h
  have hre := congrArg Complex.re h
  simp only [ofReal_re, sub_re, div_ofNat_re, one_re] at hre
  linarith

/-- Classical improper integral representation of the Euler–Mascheroni constant:
`∫ t in Ioi 1, fract t / t ^ 2 = 1 - γ`. -/
theorem integral_Ioi_fract_div_sq :
    ∫ t in Set.Ioi (1 : ℝ), Int.fract t / t ^ 2 = 1 - Real.eulerMascheroniConstant := by
  have h := riemannZeta₀_eq_one_sub_integral_fract (s := 1) (by simp)
  rw [riemannZeta₀_one, one_mul, integral_Ioi_ofReal_cpow_neg_two zero_lt_one] at h
  have hre := congrArg Complex.re h
  simp only [ofReal_re, sub_re, one_re] at hre
  linarith

end TauCeti
