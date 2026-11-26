/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.NumberTheory.Explicit.MultiplicativeFunctions.Moebius.Basic
public import TauCeti.NumberTheory.Explicit.MultiplicativeFunctions.Moebius.MacLeod
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.NumberTheory.ZetaValues
import TauCeti.Analysis.Calculus.Deriv.Fract
import TauCeti.NumberTheory.ZetaValues

/-!
# Balazard's kernel, Balazard's identity, and Balazard's conversion inequalities

Combining MacLeod's functions `φ₃` and `φ₄` via
`(4 / 3) φ₃(t) - (1 / 3) φ₄(t) = t - 1 - ε₁(t)` defines Balazard's kernel

`ε₁(t) = 1 / 3 - 1 / (3 t) + (4 / 3) B₃({t}) / t² - (1 / 3) (B₄({t}) - B₄) / t³`

(`TauCeti.balazardKernel`), which is continuous on `{t ≠ 0}` and differentiable off `ℤ` with
nonnegative derivative

`ε₁'(t) = (((2 {t} - 1) t + {t} - {t}²) / t²)²`

(`TauCeti.balazardKernelDeriv`) satisfying `0 ≤ ε₁'(t) ≤ 1 / t²` for `t > 0`. Integrating
`ε₁'` in MacLeod's identity yields Balazard's identity for `m(x) = ∑_{n ≤ x} μ(n) / n`:

`m(x) = M(x) / x + 4 (1 - 1 / x)² / x - 4 (1 - 1 / x)³ / (3 x) +`
`(1 / x) ∫_1^x M(x / t) ε₁'(t) dt`.

Bounding the polynomial terms by `8 / (3 x)` and changing variables `u = x / t` in the integral
gives Balazard's conversion inequality:

`|m(x)| ≤ |M(x)| / x + (∫_1^x |M(t)| dt) / x² + 8 / (3 x)`

for every real `x ≥ 1`, along with its two-range and three-range forms when explicit bounds
`|M(t)| ≤ c √t` and `|M(t)| ≤ ε(t) t` are supplied.

## Main declarations

* `TauCeti.balazardKernel`: Balazard's kernel `ε₁(t)`.
* `TauCeti.balazardKernelDeriv`: the piecewise derivative `ε₁'(t)` of `balazardKernel`.
* `TauCeti.continuousOn_balazardKernel`, `TauCeti.hasDerivAt_balazardKernel`,
  `TauCeti.balazardKernelDeriv_nonneg`, `TauCeti.balazardKernelDeriv_le`,
  `TauCeti.integral_balazardKernelDeriv`: regularity, bounds, and fundamental theorem for `ε₁`.
* `TauCeti.four_thirds_macleodFun_three_sub`:
  `(4 / 3) φ₃(t) - (1 / 3) φ₄(t) = t - 1 - ε₁(t)` for `t ≠ 0`.
* `TauCeti.moebiusDivSum_eq_balazard`: Balazard's identity for `m(x)`.
* `TauCeti.abs_moebiusDivSum_le_balazard`: Balazard's conversion inequality.
* `TauCeti.abs_moebiusDivSum_le_balazard_of_le_mul`,
  `TauCeti.abs_moebiusDivSum_le_balazard_of_le_sqrt_of_le_mul`: two-range and three-range
  `M → m` conversion bounds.

## References

* M. Balazard, *Elementary remarks on Möbius' function*, Proc. Steklov Inst. Math. 276 (2012),
  33–39, Proposition 6 and Proposition 7.
* O. Ramaré, *From explicit estimates for primes to explicit estimates for the Möbius function*,
  Acta Arith. 157 (2013), 365–379, Corollary 1.2.
* O. Ramaré, *Explicit estimates on several summatory functions involving the Moebius function*,
  Math. Comp. 84 (2015), 1359–1387, Theorem 1.1 and equation (2.1).
-/

public section

open Finset MeasureTheory Filter
open scoped Topology ArithmeticFunction.Moebius

namespace TauCeti

/-! ### Balazard's kernel `ε₁` and its derivative `ε₁'` -/

/-- Balazard's kernel
`ε₁(t) = 1 / 3 - 1 / (3 t) + (4 / 3) B₃({t}) / t² - (1 / 3) (B₄({t}) - B₄) / t³`. -/
noncomputable def balazardKernel (t : ℝ) : ℝ :=
  1 / 3 - 1 / (3 * t) + 4 / 3 * bernoulliFun 3 (Int.fract t) / t ^ 2 -
    1 / 3 * (bernoulliFun 4 (Int.fract t) - bernoulli 4) / t ^ 3

/-- The defining formula of `balazardKernel`. -/
theorem balazardKernel_def (t : ℝ) :
    balazardKernel t =
      1 / 3 - 1 / (3 * t) + 4 / 3 * bernoulliFun 3 (Int.fract t) / t ^ 2 -
        1 / 3 * (bernoulliFun 4 (Int.fract t) - bernoulli 4) / t ^ 3 := (rfl)

/-- The piecewise derivative of Balazard's kernel away from the integers:
`ε₁'(t) = (((2 {t} - 1) t + {t} - {t}²) / t²)²`. -/
noncomputable def balazardKernelDeriv (t : ℝ) : ℝ :=
  (((2 * Int.fract t - 1) * t + Int.fract t - Int.fract t ^ 2) / t ^ 2) ^ 2

/-- The defining formula of `balazardKernelDeriv`. -/
theorem balazardKernelDeriv_def (t : ℝ) :
    balazardKernelDeriv t =
      (((2 * Int.fract t - 1) * t + Int.fract t - Int.fract t ^ 2) / t ^ 2) ^ 2 := (rfl)

/-- `ε₁(1) = 0`. -/
@[simp]
theorem balazardKernel_one : balazardKernel 1 = 0 := by
  simp only [balazardKernel, Int.fract_one, bernoulliFun_three, bernoulliFun_four,
    bernoulli_four]
  norm_num

/-- `ε₁'(t) ≥ 0` for every real `t`. -/
theorem balazardKernelDeriv_nonneg (t : ℝ) : 0 ≤ balazardKernelDeriv t :=
  sq_nonneg _

/-- For every `t > 0`, `ε₁'(t) ≤ 1 / t²`. -/
theorem balazardKernelDeriv_le {t : ℝ} (ht : 0 < t) :
    balazardKernelDeriv t ≤ 1 / t ^ 2 := by
  have h0 := Int.fract_nonneg t
  have h1 := Int.fract_lt_one t
  have hbound : |(2 * Int.fract t - 1) * t + Int.fract t - Int.fract t ^ 2| ≤ t := by
    rw [abs_le]
    constructor
    · nlinarith
    · rcases lt_or_ge t 1 with ht1 | ht1
      · rw [Int.fract_eq_self.mpr ⟨ht.le, ht1⟩]
        nlinarith
      · nlinarith
  have hsq :
      (((2 * Int.fract t - 1) * t + Int.fract t - Int.fract t ^ 2) / t ^ 2) ^ 2 ≤
        (t / t ^ 2) ^ 2 := by
    rw [div_pow, div_pow]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    simpa only [sq_abs] using sq_le_sq' (abs_le.mp hbound).1 (abs_le.mp hbound).2
  refine hsq.trans_eq ?_
  field_simp

/-- `ε₁` is continuous on `(0, ∞)` (in fact on `{0}ᶜ`). -/
theorem continuousOn_balazardKernel : ContinuousOn balazardKernel (Set.Ioi 0) := by
  have h3 : Continuous fun t : ℝ ↦ bernoulliFun 3 (Int.fract t) :=
    continuous_bernoulliFun_fract (by decide)
  have h4 : Continuous fun t : ℝ ↦ bernoulliFun 4 (Int.fract t) :=
    continuous_bernoulliFun_fract (by decide)
  have ht0 : ∀ t ∈ Set.Ioi (0 : ℝ), t ≠ 0 := fun _ ht ↦ ne_of_gt ht
  refine (((continuousOn_const.sub (continuousOn_const.div (continuousOn_const.mul continuousOn_id)
    fun t ht ↦ mul_ne_zero three_ne_zero (ht0 t ht))).add
    ((continuousOn_const.mul h3.continuousOn).div (continuousOn_pow 2)
      fun t ht ↦ pow_ne_zero 2 (ht0 t ht))).sub
    ((continuousOn_const.mul (h4.continuousOn.sub continuousOn_const)).div (continuousOn_pow 3)
      fun t ht ↦ pow_ne_zero 3 (ht0 t ht)))

/-- At every non-integer `t : ℝ`, `balazardKernel` has derivative `balazardKernelDeriv t`. -/
theorem hasDerivAt_balazardKernel {t : ℝ} (ht : t ∉ Set.range ((↑) : ℤ → ℝ)) :
    HasDerivAt balazardKernel (balazardKernelDeriv t) t := by
  have ht0 : t ≠ 0 := fun h0 ↦ ht ⟨0, by simp [h0]⟩
  have hfr := Int.hasDerivAt_fract ht
  have hb3 : HasDerivAt (fun u : ℝ ↦ bernoulliFun 3 (Int.fract u))
      (3 * Int.fract t ^ 2 - 3 * Int.fract t + 1 / 2) t := by
    have hpoly :
        HasDerivAt
          (fun u : ℝ ↦ Int.fract u ^ 3 - 3 / 2 * Int.fract u ^ 2 + 1 / 2 * Int.fract u)
          (3 * Int.fract t ^ 2 * 1 - 3 / 2 * (2 * Int.fract t * 1) + 1 / 2 * 1) t :=
      (((hfr.pow 3).sub ((hfr.pow 2).const_mul _)).add (hfr.const_mul _)).congr_deriv (by ring)
    refine (hpoly.congr_of_eventuallyEq
      (Eventually.of_forall fun u ↦ bernoulliFun_three (Int.fract u))).congr_deriv ?_
    ring
  have hb4 : HasDerivAt (fun u : ℝ ↦ bernoulliFun 4 (Int.fract u) - bernoulli 4)
      (4 * Int.fract t ^ 3 - 6 * Int.fract t ^ 2 + 2 * Int.fract t) t := by
    have hpoly :
        HasDerivAt
          (fun u : ℝ ↦ Int.fract u ^ 4 - 2 * Int.fract u ^ 3 + Int.fract u ^ 2)
          (4 * Int.fract t ^ 3 * 1 - 2 * (3 * Int.fract t ^ 2 * 1) + 2 * Int.fract t * 1) t :=
      (((hfr.pow 4).sub ((hfr.pow 3).const_mul _)).add (hfr.pow 2)).congr_deriv (by ring)
    refine (hpoly.congr_of_eventuallyEq (Eventually.of_forall fun u ↦ ?_)).congr_deriv ?_
    · simp only [bernoulliFun_four, bernoulli_four]
      ring
    · ring
  have hinv1 : HasDerivAt (fun u : ℝ ↦ 1 / 3 - 1 / (3 * u)) (1 / (3 * t ^ 2)) t := by
    have hmul : HasDerivAt (fun u : ℝ ↦ 3 * u) 3 t :=
      ((hasDerivAt_id' t).const_mul 3).congr_deriv (by ring)
    have hdiv := (hasDerivAt_const t (1 : ℝ)).div hmul (mul_ne_zero three_ne_zero ht0)
    refine ((hasDerivAt_const t (1 / 3 : ℝ)).sub hdiv).congr_deriv ?_
    field_simp
    ring
  have hterm2 :
      HasDerivAt (fun u : ℝ ↦ 4 / 3 * bernoulliFun 3 (Int.fract u) / u ^ 2)
        ((4 / 3 * (3 * Int.fract t ^ 2 - 3 * Int.fract t + 1 / 2) * t ^ 2 -
          4 / 3 * bernoulliFun 3 (Int.fract t) * (2 * t)) / (t ^ 2) ^ 2) t := by
    have hp2 : HasDerivAt (fun u : ℝ ↦ u ^ 2) (2 * t) t :=
      (hasDerivAt_pow 2 t).congr_deriv (by ring)
    refine ((hb3.const_mul (4 / 3 : ℝ)).div hp2 (pow_ne_zero 2 ht0)).congr_deriv ?_
    ring
  have hterm3 :
      HasDerivAt (fun u : ℝ ↦ 1 / 3 * (bernoulliFun 4 (Int.fract u) - bernoulli 4) / u ^ 3)
        ((1 / 3 * (4 * Int.fract t ^ 3 - 6 * Int.fract t ^ 2 + 2 * Int.fract t) * t ^ 3 -
          1 / 3 * (bernoulliFun 4 (Int.fract t) - bernoulli 4) * (3 * t ^ 2)) / (t ^ 3) ^ 2)
        t := by
    have hp3 : HasDerivAt (fun u : ℝ ↦ u ^ 3) (3 * t ^ 2) t :=
      (hasDerivAt_pow 3 t).congr_deriv (by ring)
    refine ((hb4.const_mul (1 / 3 : ℝ)).div hp3 (pow_ne_zero 3 ht0)).congr_deriv ?_
    ring
  refine ((hinv1.add hterm2).sub hterm3).congr_of_eventuallyEq
    (Eventually.of_forall fun u ↦ (balazardKernel_def u).symm) |>.congr_deriv ?_
  rw [balazardKernelDeriv_def, bernoulliFun_three, bernoulliFun_four, bernoulli_four]
  field_simp
  ring

/-- `balazardKernelDeriv` is interval integrable on `a..b` for positive reals `a, b`. -/
theorem intervalIntegrable_balazardKernelDeriv {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable balazardKernelDeriv volume a b := by
  have hmeas : Measurable balazardKernelDeriv := by
    change Measurable fun t ↦
      (((2 * Int.fract t - 1) * t + Int.fract t - Int.fract t ^ 2) / t ^ 2) ^ 2
    have _hf : Measurable (Int.fract : ℝ → ℝ) := measurable_fract
    fun_prop
  have hm : 0 < min a b := lt_min ha hb
  have hu :
      ∀ t ∈ Set.Ioc (min a b) (max a b), ‖balazardKernelDeriv t‖ ≤ 1 / (min a b) ^ 2 := by
    intro t ht
    have ht0 : 0 < t := hm.trans ht.1
    rw [Real.norm_eq_abs, abs_of_nonneg (balazardKernelDeriv_nonneg t)]
    refine (balazardKernelDeriv_le ht0).trans ?_
    exact div_le_div_of_nonneg_left zero_le_one (sq_pos_of_pos hm)
      (pow_le_pow_left₀ hm.le ht.1.le 2)
  have hbase : IntervalIntegrable balazardKernelDeriv volume (min a b) (max a b) := by
    refine (intervalIntegrable_iff_integrableOn_Ioc_of_le min_le_max).mpr ?_
    refine (integrableOn_const (C := 1 / (min a b) ^ 2) (hs := measure_Ioc_lt_top.ne)).mono'
      hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hu t ht
  rcases le_total a b with hab | hba
  · simpa [min_eq_left hab, max_eq_right hab] using hbase
  · simpa [min_eq_right hba, max_eq_left hba] using hbase.symm

/-- For every `y ≥ 1`, `∫_1^y ε₁'(t) dt = ε₁(y)`. -/
theorem integral_balazardKernelDeriv {y : ℝ} (hy : 1 ≤ y) :
    ∫ t in (1 : ℝ)..y, balazardKernelDeriv t = balazardKernel y := by
  have h := integral_eq_of_hasDerivAt_off_countable balazardKernel balazardKernelDeriv
    (Set.countable_range ((↑) : ℤ → ℝ))
    (continuousOn_balazardKernel.mono (by
      rw [Set.uIcc_of_le hy]
      exact fun _ ht ↦ lt_of_lt_of_le zero_lt_one ht.1))
    (fun _ ht ↦ hasDerivAt_balazardKernel ht.2)
    (intervalIntegrable_balazardKernelDeriv zero_lt_one (zero_lt_one.trans_le hy))
  simpa [balazardKernel_one] using h

/-! ### Balazard's identity for `m(x)` -/

/-- `(4 / 3) φ₃(t) - (1 / 3) φ₄(t) = t - 1 - ε₁(t)` for every nonzero `t : ℝ`. -/
theorem four_thirds_macleodFun_three_sub {t : ℝ} (ht : t ≠ 0) :
    (4 / 3 : ℝ) * macleodFun 3 t - (1 / 3 : ℝ) * macleodFun 4 t = t - 1 - balazardKernel t := by
  simp only [macleodFun_def, balazardKernel_def, bernoulliFun_three, bernoulliFun_four,
    bernoulli_four]
  field_simp
  ring

/-- **Balazard's identity** (Ramaré 2015, (2.1); Balazard 2012): for every real `x ≥ 1`,
`m(x) = M(x) / x + 4 (1 - 1 / x)² / x - 4 (1 - 1 / x)³ / (3 x) +`
`(1 / x) ∫_1^x M(x / t) ε₁'(t) dt`. -/
theorem moebiusDivSum_eq_balazard {x : ℝ} (hx : 1 ≤ x) :
    moebiusDivSum x =
      moebiusSum x / x + 4 * (1 - 1 / x) ^ 2 / x - 4 * (1 - 1 / x) ^ 3 / (3 * x) +
        (1 / x) * ∫ t in (1 : ℝ)..x, moebiusSum (x / t) * balazardKernelDeriv t := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hm3 := sum_moebius_mul_macleodFun 3 hx
  have hm4 := sum_moebius_mul_macleodFun 4 hx
  have hswap := integral_moebiusSum_div_mul hx
    (intervalIntegrable_balazardKernelDeriv zero_lt_one hx0)
  have hε_sum :
      ∫ t in (1 : ℝ)..x, moebiusSum (x / t) * balazardKernelDeriv t =
        ∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) * balazardKernel (x / n) := by
    rw [hswap]
    refine Finset.sum_congr rfl fun n hn ↦ ?_
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hnx : (n : ℝ) ≤ x :=
      le_trans (by exact_mod_cast (Finset.mem_Icc.mp hn).2) (Nat.floor_le hx0.le)
    rw [integral_balazardKernelDeriv ((one_le_div (by exact_mod_cast hn1)).mpr hnx)]
  have hlin :
      (4 / 3 : ℝ) * (∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) * macleodFun 3 (x / n)) -
          (1 / 3 : ℝ) * (∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) * macleodFun 4 (x / n)) =
        x * moebiusDivSum x - moebiusSum x -
          ∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) * balazardKernel (x / n) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      moebiusDivSum_def, moebiusSum_def, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n hn ↦ ?_
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hxn0 : x / n ≠ 0 := div_ne_zero hx0.ne' (by positivity)
    calc (4 / 3 : ℝ) * ((μ n : ℝ) * macleodFun 3 (x / n)) -
          (1 / 3 : ℝ) * ((μ n : ℝ) * macleodFun 4 (x / n))
        = (μ n : ℝ) * ((4 / 3 : ℝ) * macleodFun 3 (x / n) -
            (1 / 3 : ℝ) * macleodFun 4 (x / n)) := by ring
      _ = (μ n : ℝ) * (x / n - 1 - balazardKernel (x / n)) := by
            rw [four_thirds_macleodFun_three_sub hxn0]
      _ = x * ((μ n : ℝ) / n) - (μ n : ℝ) - (μ n : ℝ) * balazardKernel (x / n) := by ring
  rw [hm3, hm4] at hlin
  rw [← hε_sum] at hlin
  have hmul :
      x * moebiusDivSum x =
        moebiusSum x + 4 * (1 - 1 / x) ^ 2 - 4 * (1 - 1 / x) ^ 3 / 3 +
          ∫ t in (1 : ℝ)..x, moebiusSum (x / t) * balazardKernelDeriv t := by
    simp only [one_div] at hlin ⊢
    norm_num at hlin
    linarith
  have hfinal := congrArg (fun y ↦ y / x) hmul
  rw [mul_div_cancel_left₀ _ hx0.ne'] at hfinal
  rw [hfinal]
  field_simp

/-! ### Balazard's conversion inequalities -/

/-- **Balazard's inequality** (Ramaré 2015, Theorem 1.1; Balazard 2012, Proposition 7):
for every real `x ≥ 1`,
`|m(x)| ≤ |M(x)| / x + (∫_1^x |M(t)| dt) / x² + 8 / (3 x)`. -/
theorem abs_moebiusDivSum_le_balazard (x : ℝ) (hx : 1 ≤ x) :
    |moebiusDivSum x| ≤
      |moebiusSum x| / x + (∫ t in (1 : ℝ)..x, |moebiusSum t|) / x ^ 2 + 8 / (3 * x) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  let u : ℝ := 1 - 1 / x
  have hu0 : 0 ≤ u := sub_nonneg.mpr (div_le_one_of_le₀ hx hx0.le)
  have hu1 : u < 1 := by
    dsimp [u]
    linarith [one_div_pos.mpr hx0]
  have hpoly_nonneg : 0 ≤ 4 * u ^ 2 - 4 * u ^ 3 / 3 := by
    have hfac : 4 * u ^ 2 - 4 * u ^ 3 / 3 = (4 / 3) * u ^ 2 * (3 - u) := by ring
    rw [hfac]
    exact mul_nonneg (mul_nonneg (by positivity) (sq_nonneg u)) (by linarith)
  have hpoly_le : 4 * u ^ 2 - 4 * u ^ 3 / 3 ≤ 8 / 3 := by
    have hdiff : 8 / 3 - (4 * u ^ 2 - 4 * u ^ 3 / 3) =
        (4 / 3) * (1 - u) * (2 + u * (2 - u)) := by ring
    have h0 : 0 ≤ 8 / 3 - (4 * u ^ 2 - 4 * u ^ 3 / 3) := by
      rw [hdiff]
      exact mul_nonneg (mul_nonneg (by positivity) (by linarith))
        (add_nonneg zero_le_two (mul_nonneg hu0 (by linarith)))
    linarith
  have hpoly_abs : |4 * (1 - 1 / x) ^ 2 / x - 4 * (1 - 1 / x) ^ 3 / (3 * x)| ≤ 8 / (3 * x) := by
    have hrewrite :
        4 * (1 - 1 / x) ^ 2 / x - 4 * (1 - 1 / x) ^ 3 / (3 * x) =
          (4 * u ^ 2 - 4 * u ^ 3 / 3) / x := by
      dsimp [u]
      ring
    rw [hrewrite, abs_div, abs_of_pos hx0, abs_of_nonneg hpoly_nonneg]
    calc (4 * u ^ 2 - 4 * u ^ 3 / 3) / x ≤ (8 / 3) / x :=
          div_le_div_of_nonneg_right hpoly_le hx0.le
      _ = 8 / (3 * x) := by ring
  have hc_inv : ContinuousOn (fun t : ℝ ↦ (t ^ 2)⁻¹) (Set.Ici 1) :=
    (continuousOn_pow 2).inv₀ fun t ht ↦ ne_of_gt (pow_pos (zero_lt_one.trans_le ht) 2)
  have hw_inv : IntervalIntegrable (fun t : ℝ ↦ (t ^ 2)⁻¹) volume 1 x :=
    (hc_inv.mono (by rw [Set.uIcc_of_le hx]; exact Set.Icc_subset_Ici_self)).intervalIntegrable
  have hint_lhs :
      IntervalIntegrable (fun t ↦ moebiusSum (x / t) * balazardKernelDeriv t) volume 1 x :=
    intervalIntegrable_moebiusSum_div_mul hx
      (intervalIntegrable_balazardKernelDeriv zero_lt_one hx0)
  have hint_rhs : IntervalIntegrable (fun t ↦ |moebiusSum (x / t)| / t ^ 2) volume 1 x := by
    refine (intervalIntegrable_congr fun t _ ↦ ?_).mp
      (intervalIntegrable_moebiusSum_div_mul hx hw_inv).abs
    simp only [abs_mul, abs_inv, abs_of_nonneg (sq_nonneg t), div_eq_mul_inv]
  have hint_abs :
      |∫ t in (1 : ℝ)..x, moebiusSum (x / t) * balazardKernelDeriv t| ≤
        (1 / x) * ∫ t in (1 : ℝ)..x, |moebiusSum t| := by
    calc |∫ t in (1 : ℝ)..x, moebiusSum (x / t) * balazardKernelDeriv t|
        ≤ ∫ t in (1 : ℝ)..x, |moebiusSum (x / t) * balazardKernelDeriv t| :=
          intervalIntegral.abs_integral_le_integral_abs hx
      _ ≤ ∫ t in (1 : ℝ)..x, |moebiusSum (x / t)| / t ^ 2 := by
          refine intervalIntegral.integral_mono_on hx hint_lhs.abs hint_rhs fun t ht ↦ ?_
          have ht0 : 0 < t := zero_lt_one.trans_le ht.1
          rw [abs_mul, abs_of_nonneg (balazardKernelDeriv_nonneg t), div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_left
            ((balazardKernelDeriv_le ht0).trans_eq (one_div _)) (abs_nonneg _)
      _ = (1 / x) * ∫ t in (1 : ℝ)..x, |moebiusSum t| :=
          integral_abs_moebiusSum_div_mul_inv_sq hx
  calc |moebiusDivSum x|
      = |(moebiusSum x / x + (4 * (1 - 1 / x) ^ 2 / x - 4 * (1 - 1 / x) ^ 3 / (3 * x))) +
          (1 / x) * ∫ t in (1 : ℝ)..x, moebiusSum (x / t) * balazardKernelDeriv t| := by
          rw [moebiusDivSum_eq_balazard hx]
          ring_nf
    _ ≤ |moebiusSum x / x + (4 * (1 - 1 / x) ^ 2 / x - 4 * (1 - 1 / x) ^ 3 / (3 * x))| +
          |(1 / x) * ∫ t in (1 : ℝ)..x, moebiusSum (x / t) * balazardKernelDeriv t| :=
          abs_add_le _ _
    _ ≤ (|moebiusSum x / x| + |4 * (1 - 1 / x) ^ 2 / x - 4 * (1 - 1 / x) ^ 3 / (3 * x)|) +
          (1 / x) * |∫ t in (1 : ℝ)..x, moebiusSum (x / t) * balazardKernelDeriv t| := by
          rw [abs_mul, abs_of_pos (one_div_pos.mpr hx0)]
          exact add_le_add (abs_add_le _ _) le_rfl
    _ ≤ (|moebiusSum x| / x + 8 / (3 * x)) +
          (1 / x) * ((1 / x) * ∫ t in (1 : ℝ)..x, |moebiusSum t|) := by
          rw [abs_div, abs_of_pos hx0]
          gcongr
    _ = |moebiusSum x| / x + (∫ t in (1 : ℝ)..x, |moebiusSum t|) / x ^ 2 + 8 / (3 * x) := by
          ring

/-- Interval integrability of `t ↦ |M(t)|` on any `a..b`. -/
private theorem intervalIntegrable_abs_moebiusSum (a b : ℝ) :
    IntervalIntegrable (fun t ↦ |moebiusSum t|) volume a b := by
  have hbase := (intervalIntegrable_moebiusSum_mul (f := fun _ ↦ 1)
    (continuousOn_const.locallyIntegrableOn measurableSet_Ici) a b).abs
  refine (intervalIntegrable_congr fun t _ ↦ ?_).mp hbase
  rw [mul_one]

/-- **Balazard's two-range conversion bound**: if `1 ≤ t₀ ≤ D`, `|M(t)| ≤ ε(t) t` on
`[t₀, D]`, and `ε` is interval integrable on `t₀..D`, then
`|m(D)| ≤ ε(D) + (1 / D²) (∫_1^{t₀} |M(t)| dt + ∫_{t₀}^D ε(t) t dt) + 8 / (3 D)`. -/
theorem abs_moebiusDivSum_le_balazard_of_le_mul {t₀ D : ℝ} (ht₀ : 1 ≤ t₀)
    (hD : t₀ ≤ D) {ε : ℝ → ℝ} (hε : IntervalIntegrable ε volume t₀ D)
    (hM : ∀ t ∈ Set.Icc t₀ D, |moebiusSum t| ≤ ε t * t) :
    |moebiusDivSum D| ≤
      ε D + (1 / D ^ 2) *
          ((∫ t in (1 : ℝ)..t₀, |moebiusSum t|) + ∫ t in t₀..D, ε t * t) +
        8 / (3 * D) := by
  have h1D : 1 ≤ D := ht₀.trans hD
  have hD0 : 0 < D := zero_lt_one.trans_le h1D
  have hsplit :
      ∫ t in (1 : ℝ)..D, |moebiusSum t| =
        (∫ t in (1 : ℝ)..t₀, |moebiusSum t|) + ∫ t in t₀..D, |moebiusSum t| :=
    (intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_abs_moebiusSum 1 t₀)
      (intervalIntegrable_abs_moebiusSum t₀ D)).symm
  have htail : ∫ t in t₀..D, |moebiusSum t| ≤ ∫ t in t₀..D, ε t * t := by
    refine intervalIntegral.integral_mono_on hD
      (intervalIntegrable_abs_moebiusSum t₀ D) (hε.mul_continuousOn continuousOn_id)
      fun t ht ↦ hM t ht
  have hM_D : |moebiusSum D| / D ≤ ε D :=
    (div_le_iff₀ hD0).mpr (hM D ⟨hD, le_rfl⟩)
  have hdiv :
      ((∫ t in (1 : ℝ)..t₀, |moebiusSum t|) + ∫ t in t₀..D, |moebiusSum t|) / D ^ 2 =
        (1 / D ^ 2) *
          ((∫ t in (1 : ℝ)..t₀, |moebiusSum t|) + ∫ t in t₀..D, |moebiusSum t|) := by
    ring
  refine (abs_moebiusDivSum_le_balazard D h1D).trans ?_
  rw [hsplit, hdiv]
  gcongr

/-- **Balazard's three-range conversion bound** (Ramaré 2013, Corollary 1.2, Balazard route):
if `1 ≤ a ≤ t₀ ≤ D`, `|M(t)| ≤ c √t` on `[a, t₀]`, `|M(t)| ≤ ε(t) t` on `[t₀, D]`, and `ε` is
interval integrable on `t₀..D`, then
`|m(D)| ≤ ε(D) + (1 / D²) (∫_1^a |M(t)| dt + (2 c / 3) (t₀^(3/2) - a^(3/2)) +
∫_{t₀}^D ε(t) t dt) + 8 / (3 D)`. -/
theorem abs_moebiusDivSum_le_balazard_of_le_sqrt_of_le_mul {a t₀ D c : ℝ}
    (ha : 1 ≤ a) (hat₀ : a ≤ t₀) (hD : t₀ ≤ D) {ε : ℝ → ℝ}
    (hε : IntervalIntegrable ε volume t₀ D)
    (hM₁ : ∀ t ∈ Set.Icc a t₀, |moebiusSum t| ≤ c * Real.sqrt t)
    (hM₂ : ∀ t ∈ Set.Icc t₀ D, |moebiusSum t| ≤ ε t * t) :
    |moebiusDivSum D| ≤
      ε D +
        (1 / D ^ 2) *
          ((∫ t in (1 : ℝ)..a, |moebiusSum t|) +
            (2 * c / 3) * (t₀ ^ (3 / 2 : ℝ) - a ^ (3 / 2 : ℝ)) +
            ∫ t in t₀..D, ε t * t) +
        8 / (3 * D) := by
  have ht₀ : 1 ≤ t₀ := ha.trans hat₀
  have hsplit :
      ∫ t in (1 : ℝ)..t₀, |moebiusSum t| =
        (∫ t in (1 : ℝ)..a, |moebiusSum t|) + ∫ t in a..t₀, |moebiusSum t| :=
    (intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_abs_moebiusSum 1 a)
      (intervalIntegrable_abs_moebiusSum a t₀)).symm
  have hsqrt_int : IntervalIntegrable (fun t : ℝ ↦ c * Real.sqrt t) volume a t₀ :=
    (Real.continuous_sqrt.continuousOn.const_mul c).intervalIntegrable
  have hmid_le : ∫ t in a..t₀, |moebiusSum t| ≤ ∫ t in a..t₀, c * Real.sqrt t :=
    intervalIntegral.integral_mono_on hat₀
      (intervalIntegrable_abs_moebiusSum a t₀) hsqrt_int fun t ht ↦ hM₁ t ht
  have hsqrt_eval :
      ∫ t in a..t₀, c * Real.sqrt t =
        (2 * c / 3) * (t₀ ^ (3 / 2 : ℝ) - a ^ (3 / 2 : ℝ)) := by
    rw [intervalIntegral.integral_const_mul]
    have hrhs : ∫ t in a..t₀, Real.sqrt t = ∫ t in a..t₀, t ^ (1 / 2 : ℝ) :=
      intervalIntegral.integral_congr fun t _ ↦ Real.sqrt_eq_rpow t
    rw [hrhs, integral_rpow (Or.inl (by norm_num))]
    norm_num
    ring
  refine (abs_moebiusDivSum_le_balazard_of_le_mul ht₀ hD hε hM₂).trans ?_
  rw [hsplit]
  rw [← hsqrt_eval]
  gcongr

end TauCeti
