/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Explicit.MultiplicativeFunctions.Moebius.Basic
public import TauCeti.NumberTheory.Explicit.MultiplicativeFunctions.Moebius.MacLeod
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import TauCeti.Analysis.Calculus.Deriv.Fract
import TauCeti.NumberTheory.Bernoulli.Real

/-!
# Balazard's kernels, identities, and conversion inequalities

At `k = 2`, MacLeod's function `φ₂(t) = t - 1 - ({t}² - {t}) / t` (for `t ≠ 0`) introduces the
kernel `ε₀(t) = ({t}² - {t}) / t` (`TauCeti.balazardTwoKernel`), whose piecewise derivative off
`ℤ` is `ε₀'(t) = ((2 {t} - 1) t + {t} - {t}²) / t²` (`TauCeti.balazardTwoKernelDeriv`).
Integrating `ε₀'` in MacLeod's `k = 2` identity gives Balazard's `k = 2` formula
`x m(x) - M(x) = 2 - 2 / x + ∫_1^x M(x / t) ε₀'(t) dt` for `x ≥ 1`.

Combining MacLeod's functions `φ₃` and `φ₄` via
`(4 / 3) φ₃(t) - (1 / 3) φ₄(t) = t - 1 - ε₁(t)` for `t ≠ 0` defines Balazard's kernel

`ε₁(t) = 1 / 3 - 1 / (3 t) + (4 / 3) B₃({t}) / t² - (1 / 3) (B₄({t}) - B₄) / t³`

(`TauCeti.balazardKernel`), which is continuous on `{0}ᶜ` and differentiable off `ℤ` with
nonnegative derivative

`ε₁'(t) = ε₀'(t)² = (((2 {t} - 1) t + {t} - {t}²) / t²)²`

(`TauCeti.balazardKernelDeriv`) satisfying `0 ≤ balazardKernelDeriv t ≤ 1 / t²` for `t > 0`.
Integrating `ε₁'` in MacLeod's identity yields Balazard's identity for `m(x) = ∑_{n ≤ x} μ(n) / n`:

`m(x) = M(x) / x + 4 (1 - 1 / x)² / x - 4 (1 - 1 / x)³ / (3 x) +`
`(1 / x) ∫_1^x M(x / t) ε₁'(t) dt`

for `x ≥ 1`.

Bounding the polynomial terms by `8 / (3 x)` and changing variables `u = x / t` in the integral
gives Balazard's conversion inequality:

`|m(x)| ≤ |M(x)| / x + (∫_1^x |M(t)| dt) / x² + 8 / (3 x)`

for every real `x ≥ 1`, along with its two-range form when an interval-integrable tail envelope
`ε` satisfying `|M(t)| ≤ ε(t) t` on `[t₀, D]` is supplied, and its three-range form when a
square-root estimate `|M(t)| ≤ c √t` on `[a, t₀]` is additionally supplied alongside an
interval-integrable tail envelope `ε` on `[t₀, D]`.

## Main declarations

* `TauCeti.balazardTwoKernel`, `TauCeti.balazardTwoKernelDeriv`: the `k = 2` remainder kernel
  `ε₀(t)` and its piecewise derivative `ε₀'(t)`.
* `TauCeti.balazardTwoKernel_intCast`: `ε₀(n) = 0` for `n : ℤ`.
* `TauCeti.measurable_balazardTwoKernelDeriv`, `TauCeti.integral_balazardTwoKernelDeriv`:
  measurability and fundamental-theorem integral evaluation of `ε₀'`.
* `TauCeti.macleodFun_two_eq_sub_balazardTwoKernel`: `φ₂(t) = t - 1 - ε₀(t)` for `t ≠ 0`.
* `TauCeti.mul_moebiusDivSum_sub_moebiusSum_eq`: Balazard's `k = 2` identity for `x m(x) - M(x)`.
* `TauCeti.balazardKernel`, `TauCeti.balazardKernelDeriv`: Balazard's kernel `ε₁(t)` and its
  piecewise derivative `ε₁'(t) = ε₀'(t)²`.
* `TauCeti.balazardKernel_intCast`: `ε₁(n) = 1 / 3 - 1 / (3 * n)` for `n : ℤ`.
* `TauCeti.continuousOn_balazardKernel`, `TauCeti.hasDerivAt_balazardKernel`,
  `TauCeti.balazardKernelDeriv_nonneg`, `TauCeti.balazardKernelDeriv_le`,
  `TauCeti.measurable_balazardKernelDeriv`, `TauCeti.integral_balazardKernelDeriv`:
  regularity, bounds, measurability, and fundamental-theorem integral evaluation for `ε₁`.
* `TauCeti.four_div_three_mul_macleodFun_three_sub_one_div_three_mul_macleodFun_four`:
  `(4 / 3) φ₃(t) - (1 / 3) φ₄(t) = t - 1 - ε₁(t)` for `t ≠ 0`.
* `TauCeti.moebiusDivSum_eq_balazard`: Balazard's identity for `m(x)`.
* `TauCeti.abs_moebiusDivSum_le_balazard`: Balazard's conversion inequality.
* `TauCeti.abs_moebiusDivSum_le_balazard_of_le_mul`,
  `TauCeti.abs_moebiusDivSum_le_balazard_of_le_sqrt_of_le_mul`: two-range and three-range
  `M → m` conversion bounds.

## References

* M. Balazard, *Elementary remarks on Möbius' function*, Proc. Steklov Inst. Math. 276 (2012),
  33–39, Proposition 6, Proposition 7, and equation (11).
* O. Ramaré, *From explicit estimates for primes to explicit estimates for the Möbius function*,
  Acta Arith. 157 (2013), 365–379, Corollary 1.2.
* O. Ramaré, *Explicit estimates on several summatory functions involving the Moebius function*,
  Math. Comp. 84 (2015), 1359–1387, Theorem 1.1 and equation (2.1).
-/

public section

open Finset MeasureTheory Filter
open scoped Topology ArithmeticFunction.Moebius

namespace TauCeti

/-! ### The `k = 2` kernel `ε₀` and Balazard's `k = 2` identity -/

/-- The `k = 2` remainder kernel `ε₀(t) = ({t}² - {t}) / t`. -/
noncomputable def balazardTwoKernel (t : ℝ) : ℝ :=
  (Int.fract t ^ 2 - Int.fract t) / t

/-- The defining formula of `balazardTwoKernel`. -/
theorem balazardTwoKernel_def (t : ℝ) :
    balazardTwoKernel t = (Int.fract t ^ 2 - Int.fract t) / t := (rfl)

/-- `ε₀(1) = 0`. -/
@[simp]
theorem balazardTwoKernel_one : balazardTwoKernel 1 = 0 := by
  simp [balazardTwoKernel]

/-- At every integer `n : ℤ`, `ε₀(n) = 0`. -/
@[simp]
theorem balazardTwoKernel_intCast (n : ℤ) : balazardTwoKernel n = 0 := by
  simp [balazardTwoKernel]

/-- `φ₂(t) = t - 1 - ε₀(t)` for every nonzero `t : ℝ`. -/
theorem macleodFun_two_eq_sub_balazardTwoKernel {t : ℝ} (ht : t ≠ 0) :
    macleodFun 2 t = t - 1 - balazardTwoKernel t := by
  rw [macleodFun_two ht, balazardTwoKernel_def]

/-- The piecewise derivative of `balazardTwoKernel` away from the integers:
`ε₀'(t) = ((2 {t} - 1) t + {t} - {t}²) / t²`. -/
noncomputable def balazardTwoKernelDeriv (t : ℝ) : ℝ :=
  ((2 * Int.fract t - 1) * t + Int.fract t - Int.fract t ^ 2) / t ^ 2

/-- The defining formula of `balazardTwoKernelDeriv`. -/
theorem balazardTwoKernelDeriv_def (t : ℝ) :
    balazardTwoKernelDeriv t =
      ((2 * Int.fract t - 1) * t + Int.fract t - Int.fract t ^ 2) / t ^ 2 := (rfl)

/-- For every `t > 0`, `|balazardTwoKernelDeriv t| ≤ 1 / t`. -/
theorem abs_balazardTwoKernelDeriv_le {t : ℝ} (ht : 0 < t) :
    |balazardTwoKernelDeriv t| ≤ 1 / t := by
  have h0 := Int.fract_nonneg t
  have h1 := Int.fract_lt_one t
  have hnum : |(2 * Int.fract t - 1) * t + Int.fract t - Int.fract t ^ 2| ≤ t := by
    rw [abs_le]
    constructor
    · nlinarith
    · rcases lt_or_ge t 1 with ht1 | ht1
      · rw [Int.fract_eq_self.mpr ⟨ht.le, ht1⟩]
        nlinarith
      · nlinarith
  rw [balazardTwoKernelDeriv_def, abs_div, abs_of_pos (sq_pos_of_pos ht)]
  calc |((2 * Int.fract t - 1) * t + Int.fract t - Int.fract t ^ 2)| / t ^ 2
      ≤ t / t ^ 2 := div_le_div_of_nonneg_right hnum (sq_nonneg t)
    _ = 1 / t := by field_simp

/-- `ε₀` is continuous on `{0}ᶜ`. -/
theorem continuousOn_balazardTwoKernel : ContinuousOn balazardTwoKernel ({0}ᶜ : Set ℝ) := by
  unfold balazardTwoKernel
  exact Int.continuous_fract_sq_sub_fract.continuousOn.div continuousOn_id fun _ ht ↦ ht

/-- At every non-integer `t : ℝ`, `balazardTwoKernel` has derivative `balazardTwoKernelDeriv t`. -/
theorem hasDerivAt_balazardTwoKernel {t : ℝ} (ht : t ∉ Set.range ((↑) : ℤ → ℝ)) :
    HasDerivAt balazardTwoKernel (balazardTwoKernelDeriv t) t := by
  have ht0 : t ≠ 0 := fun h0 ↦ ht ⟨0, by simp [h0]⟩
  have hfr := Int.hasDerivAt_fract ht
  have hnum :
      HasDerivAt (fun u : ℝ ↦ Int.fract u ^ 2 - Int.fract u) (2 * Int.fract t - 1) t := by
    refine ((hfr.pow 2).sub hfr).congr_deriv ?_
    ring
  refine (hnum.div (hasDerivAt_id' t) ht0).congr_deriv ?_
  rw [balazardTwoKernelDeriv_def]
  field_simp
  ring

/-- `balazardTwoKernelDeriv` is measurable. -/
@[fun_prop]
theorem measurable_balazardTwoKernelDeriv : Measurable balazardTwoKernelDeriv := by
  unfold balazardTwoKernelDeriv
  have _hf : Measurable (Int.fract : ℝ → ℝ) := measurable_fract
  fun_prop

private theorem abs_balazardTwoKernelDeriv_le_two (t : ℝ) :
    |balazardTwoKernelDeriv t| ≤ 2 := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · rcases le_or_gt (-1) t with ht1 | ht1
    · have hfr : Int.fract t = t + 1 :=
        Int.fract_eq_iff.mpr ⟨by linarith, by linarith, -1, by ring⟩
      rw [balazardTwoKernelDeriv_def, hfr]
      have heq : ((2 * (t + 1) - 1) * t + (t + 1) - (t + 1) ^ 2) / t ^ 2 = 1 := by
        have ht0 : t ≠ 0 := ht.ne
        field_simp
        ring
      rw [heq]
      norm_num
    · rw [balazardTwoKernelDeriv_def, abs_div, abs_of_pos (sq_pos_of_neg ht)]
      have h0 := Int.fract_nonneg t
      have h1 := Int.fract_lt_one t
      refine (div_le_iff₀ (sq_pos_of_neg ht)).mpr ?_
      rw [abs_le]
      constructor <;> nlinarith
  · simp [balazardTwoKernelDeriv_def]
  · rcases lt_or_ge t 1 with ht1 | ht1
    · rw [balazardTwoKernelDeriv_def, Int.fract_eq_self.mpr ⟨ht.le, ht1⟩]
      have heq : ((2 * t - 1) * t + t - t ^ 2) / t ^ 2 = 1 := by
        have ht0 : t ≠ 0 := ht.ne'
        field_simp
        ring
      rw [heq]
      norm_num
    · exact (abs_balazardTwoKernelDeriv_le ht).trans
        (((div_le_one ht).mpr ht1).trans (by norm_num))

/-- `balazardTwoKernelDeriv` is interval integrable between any two reals. -/
theorem intervalIntegrable_balazardTwoKernelDeriv (a b : ℝ) :
    IntervalIntegrable balazardTwoKernelDeriv volume a b :=
  (intervalIntegrable_const (c := (2 : ℝ))).mono_fun'
    measurable_balazardTwoKernelDeriv.aestronglyMeasurable
    (ae_of_all _ fun t ↦ by
      simpa only [Real.norm_eq_abs] using abs_balazardTwoKernelDeriv_le_two t)

/-- **Fundamental theorem of calculus for `balazardTwoKernelDeriv`**: on any interval not
containing `0`, `∫_a^b ε₀'(t) dt = ε₀(b) - ε₀(a)`. -/
theorem integral_balazardTwoKernelDeriv {a b : ℝ} (h0 : (0 : ℝ) ∉ Set.uIcc a b) :
    ∫ t in a..b, balazardTwoKernelDeriv t = balazardTwoKernel b - balazardTwoKernel a :=
  integral_eq_of_hasDerivAt_off_countable balazardTwoKernel
    balazardTwoKernelDeriv (Set.countable_range ((↑) : ℤ → ℝ))
    (continuousOn_balazardTwoKernel.mono fun _ ht h ↦ h0 (h ▸ ht))
    (fun _ ht ↦ hasDerivAt_balazardTwoKernel ht.2)
    (intervalIntegrable_balazardTwoKernelDeriv a b)

/-- **Balazard's `k = 2` identity** (Balazard 2012, equation (11)): for every real `x ≥ 1`,
`x m(x) - M(x) = 2 - 2 / x + ∫_1^x M(x / t) ε₀'(t) dt`. -/
theorem mul_moebiusDivSum_sub_moebiusSum_eq {x : ℝ} (hx : 1 ≤ x) :
    x * moebiusDivSum x - moebiusSum x =
      2 - 2 / x + ∫ t in (1 : ℝ)..x, moebiusSum (x / t) * balazardTwoKernelDeriv t := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  -- Evaluate `∫_1^x M(x / t) ε₀'(t) dt = ∑ μ(n) ε₀(x / n)` via the FTC sum-integral swap.
  have hε₀_sum :
      ∫ t in (1 : ℝ)..x, moebiusSum (x / t) * balazardTwoKernelDeriv t =
        ∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) * balazardTwoKernel (x / n) :=
    integral_moebiusSum_div_mul_of_hasDerivAt_off_countable hx (Set.countable_range ((↑) : ℤ → ℝ))
      (continuousOn_balazardTwoKernel.mono fun _ ht ↦ (zero_lt_one.trans_le ht.1).ne')
      balazardTwoKernel_one (fun _ ht ↦ hasDerivAt_balazardTwoKernel ht.2)
      (intervalIntegrable_balazardTwoKernelDeriv 1 x)
  -- Expand MacLeod's `k = 2` identity using `φ₂(t) = t - 1 - ε₀(t)`.
  have hmacleod2 := sum_moebius_mul_macleodFun 2 hx
  have hdiff :
      ∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) * macleodFun 2 (x / n) =
        x * moebiusDivSum x - moebiusSum x -
          ∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) * balazardTwoKernel (x / n) := by
    rw [moebiusDivSum_def, moebiusSum_def, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n hn ↦ ?_
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    rw [macleodFun_two_eq_sub_balazardTwoKernel (div_ne_zero hx0.ne' (by positivity))]
    ring
  rw [hdiff, ← hε₀_sum] at hmacleod2
  simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one] at hmacleod2
  have h2 : (2 : ℝ) * (1 - 1 / x) = 2 - 2 / x := by ring
  rw [h2] at hmacleod2
  linarith

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
`ε₁'(t) = ε₀'(t)² = (((2 {t} - 1) t + {t} - {t}²) / t²)²`. -/
noncomputable def balazardKernelDeriv (t : ℝ) : ℝ :=
  balazardTwoKernelDeriv t ^ 2

/-- `balazardKernelDeriv t = balazardTwoKernelDeriv t ^ 2` for every real `t`. -/
theorem balazardKernelDeriv_eq_sq (t : ℝ) :
    balazardKernelDeriv t = balazardTwoKernelDeriv t ^ 2 := (rfl)

/-- The defining formula of `balazardKernelDeriv`. -/
theorem balazardKernelDeriv_def (t : ℝ) :
    balazardKernelDeriv t =
      (((2 * Int.fract t - 1) * t + Int.fract t - Int.fract t ^ 2) / t ^ 2) ^ 2 := by
  rw [balazardKernelDeriv, balazardTwoKernelDeriv_def]

/-- `ε₁(1) = 0`. -/
@[simp]
theorem balazardKernel_one : balazardKernel 1 = 0 := by
  simp only [balazardKernel, Int.fract_one, bernoulliFun_three, bernoulliFun_four,
    bernoulli_four]
  norm_num

/-- At every integer `n : ℤ`, `ε₁(n) = 1 / 3 - 1 / (3 * n)`. -/
@[simp]
theorem balazardKernel_intCast (n : ℤ) :
    balazardKernel n = 1 / 3 - 1 / (3 * (n : ℝ)) := by
  simp [balazardKernel, bernoulli_four]

/-- `0 ≤ balazardKernelDeriv t` for every real `t`. -/
theorem balazardKernelDeriv_nonneg (t : ℝ) : 0 ≤ balazardKernelDeriv t :=
  sq_nonneg _

/-- For every `t > 0`, `balazardKernelDeriv t ≤ 1 / t²`. -/
theorem balazardKernelDeriv_le {t : ℝ} (ht : 0 < t) :
    balazardKernelDeriv t ≤ 1 / t ^ 2 := by
  rw [balazardKernelDeriv_eq_sq]
  have h := abs_le.mp (abs_balazardTwoKernelDeriv_le ht)
  refine (sq_le_sq' h.1 h.2).trans_eq ?_
  ring

/-- `ε₁` is continuous on `{0}ᶜ`. -/
theorem continuousOn_balazardKernel : ContinuousOn balazardKernel ({0}ᶜ : Set ℝ) := by
  have h3 : Continuous fun t : ℝ ↦ bernoulliFun 3 (Int.fract t) :=
    continuous_bernoulliFun_fract (by decide)
  have h4 : Continuous fun t : ℝ ↦ bernoulliFun 4 (Int.fract t) :=
    continuous_bernoulliFun_fract (by decide)
  have ht0 : ∀ t ∈ ({0}ᶜ : Set ℝ), t ≠ 0 := fun _ ht ↦ ht
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
  have hb3 := hasDerivAt_bernoulliFun_fract 3 ht
  have hb4 := (hasDerivAt_bernoulliFun_fract 4 ht).sub_const (bernoulli 4 : ℝ)
  have hinv1 : HasDerivAt (fun u : ℝ ↦ 1 / 3 - 1 / (3 * u)) (1 / (3 * t ^ 2)) t := by
    have hmul : HasDerivAt (fun u : ℝ ↦ 3 * u) 3 t :=
      ((hasDerivAt_id' t).const_mul 3).congr_deriv (by ring)
    refine ((hasDerivAt_const t (1 / 3 : ℝ)).sub
      ((hasDerivAt_const t (1 : ℝ)).div hmul (mul_ne_zero three_ne_zero ht0))).congr_deriv ?_
    field_simp
    ring
  have hterm2 := (hb3.const_mul (4 / 3 : ℝ)).div (hasDerivAt_pow 2 t) (pow_ne_zero 2 ht0)
  have hterm3 := (hb4.const_mul (1 / 3 : ℝ)).div (hasDerivAt_pow 3 t) (pow_ne_zero 3 ht0)
  refine ((hinv1.add hterm2).sub hterm3).congr_of_eventuallyEq
    (Eventually.of_forall fun u ↦ (balazardKernel_def u).symm) |>.congr_deriv ?_
  rw [balazardKernelDeriv_def]
  simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, bernoulliFun_two, bernoulliFun_three,
    bernoulliFun_four, bernoulli_four]
  field_simp
  ring

/-- `balazardKernelDeriv` is measurable. -/
@[fun_prop]
theorem measurable_balazardKernelDeriv : Measurable balazardKernelDeriv :=
  measurable_balazardTwoKernelDeriv.pow_const 2

/-- `balazardKernelDeriv` is interval integrable between any two reals. -/
theorem intervalIntegrable_balazardKernelDeriv (a b : ℝ) :
    IntervalIntegrable balazardKernelDeriv volume a b := by
  refine (intervalIntegrable_const (c := (4 : ℝ))).mono_fun'
    measurable_balazardKernelDeriv.aestronglyMeasurable (ae_of_all _ fun t ↦ ?_)
  dsimp only
  rw [Real.norm_eq_abs, abs_of_nonneg (balazardKernelDeriv_nonneg t), balazardKernelDeriv_eq_sq]
  have h := abs_le.mp (abs_balazardTwoKernelDeriv_le_two t)
  exact (sq_le_sq' h.1 h.2).trans_eq (by norm_num)

/-- **Fundamental theorem of calculus for `balazardKernelDeriv`**: on any interval not
containing `0`, `∫_a^b ε₁'(t) dt = ε₁(b) - ε₁(a)`. -/
theorem integral_balazardKernelDeriv {a b : ℝ} (h0 : (0 : ℝ) ∉ Set.uIcc a b) :
    ∫ t in a..b, balazardKernelDeriv t = balazardKernel b - balazardKernel a :=
  integral_eq_of_hasDerivAt_off_countable balazardKernel
    balazardKernelDeriv (Set.countable_range ((↑) : ℤ → ℝ))
    (continuousOn_balazardKernel.mono fun _ ht h ↦ h0 (h ▸ ht))
    (fun _ ht ↦ hasDerivAt_balazardKernel ht.2)
    (intervalIntegrable_balazardKernelDeriv a b)

/-! ### Balazard's identity for `m(x)` -/

/-- `(4 / 3) φ₃(t) - (1 / 3) φ₄(t) = t - 1 - ε₁(t)` for every nonzero `t : ℝ`. -/
theorem four_div_three_mul_macleodFun_three_sub_one_div_three_mul_macleodFun_four {t : ℝ}
    (ht : t ≠ 0) :
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
  -- Evaluate `∫_1^x M(x / t) ε₁'(t) dt = ∑ μ(n) ε₁(x / n)` via the FTC sum-integral swap.
  have hε_sum :
      ∫ t in (1 : ℝ)..x, moebiusSum (x / t) * balazardKernelDeriv t =
        ∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) * balazardKernel (x / n) :=
    integral_moebiusSum_div_mul_of_hasDerivAt_off_countable hx (Set.countable_range ((↑) : ℤ → ℝ))
      (continuousOn_balazardKernel.mono fun _ ht ↦ (zero_lt_one.trans_le ht.1).ne')
      balazardKernel_one (fun _ ht ↦ hasDerivAt_balazardKernel ht.2)
      (intervalIntegrable_balazardKernelDeriv 1 x)
  -- Form the linear combination `(4 / 3) φ₃ - (1 / 3) φ₄` inside MacLeod's identity.
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
            rw [four_div_three_mul_macleodFun_three_sub_one_div_three_mul_macleodFun_four hxn0]
      _ = x * ((μ n : ℝ) / n) - (μ n : ℝ) - (μ n : ℝ) * balazardKernel (x / n) := by ring
  have hm3 := sum_moebius_mul_macleodFun 3 hx
  have hm4 := sum_moebius_mul_macleodFun 4 hx
  simp only [Nat.cast_ofNat, Nat.add_one_sub_one] at hm3 hm4
  rw [hm3, hm4, ← hε_sum] at hlin
  have hmul :
      x * moebiusDivSum x =
        moebiusSum x + 4 * (1 - 1 / x) ^ 2 - 4 * (1 - 1 / x) ^ 3 / 3 +
          ∫ t in (1 : ℝ)..x, moebiusSum (x / t) * balazardKernelDeriv t := by
    linarith
  have hfinal := congrArg (fun y ↦ y / x) hmul
  rw [mul_div_cancel_left₀ _ hx0.ne'] at hfinal
  rw [hfinal]
  field_simp

/-! ### Balazard's conversion inequalities -/

/-- Algebraic bound for the polynomial term in Balazard's identity: for `x ≥ 1`,
`|4 (1 - 1 / x)² / x - 4 (1 - 1 / x)³ / (3 x)| ≤ 8 / (3 x)`. -/
private theorem abs_balazard_poly_le {x : ℝ} (hx : 1 ≤ x) :
    |4 * (1 - 1 / x) ^ 2 / x - 4 * (1 - 1 / x) ^ 3 / (3 * x)| ≤ 8 / (3 * x) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  let u : ℝ := 1 - 1 / x
  have hu0 : 0 ≤ u := sub_nonneg.mpr (div_le_one_of_le₀ hx hx0.le)
  have hu1 : u < 1 := by
    dsimp [u]
    linarith [one_div_pos.mpr hx0]
  have hpoly_nonneg : 0 ≤ 4 * u ^ 2 - 4 * u ^ 3 / 3 := by
    have hpoly_eq : 4 * u ^ 2 - 4 * u ^ 3 / 3 = (4 / 3) * u ^ 2 * (3 - u) := by ring
    rw [hpoly_eq]
    exact mul_nonneg (mul_nonneg (by positivity) (sq_nonneg u)) (by linarith)
  have hpoly_le : 4 * u ^ 2 - 4 * u ^ 3 / 3 ≤ 8 / 3 := by
    have hdiff : 8 / 3 - (4 * u ^ 2 - 4 * u ^ 3 / 3) =
        (4 / 3) * (1 - u) * (2 + u * (2 - u)) := by ring
    have h0 : 0 ≤ 8 / 3 - (4 * u ^ 2 - 4 * u ^ 3 / 3) := by
      rw [hdiff]
      exact mul_nonneg (mul_nonneg (by positivity) (by linarith))
        (add_nonneg zero_le_two (mul_nonneg hu0 (by linarith)))
    linarith
  have hrewrite :
      4 * (1 - 1 / x) ^ 2 / x - 4 * (1 - 1 / x) ^ 3 / (3 * x) =
        (4 * u ^ 2 - 4 * u ^ 3 / 3) / x := by
    dsimp [u]
    ring
  rw [hrewrite, abs_div, abs_of_pos hx0, abs_of_nonneg hpoly_nonneg]
  exact (div_le_div_of_nonneg_right hpoly_le hx0.le).trans_eq (by ring)

/-- Analytic bound for the remainder integral in Balazard's identity: for `x ≥ 1`,
`|∫_1^x M(x / t) ε₁'(t) dt| ≤ (1 / x) ∫_1^x |M(t)| dt`. -/
private theorem abs_integral_moebiusSum_div_mul_balazardKernelDeriv_le {x : ℝ} (hx : 1 ≤ x) :
    |∫ t in (1 : ℝ)..x, moebiusSum (x / t) * balazardKernelDeriv t| ≤
      (1 / x) * ∫ t in (1 : ℝ)..x, |moebiusSum t| := by
  have hint_lhs :
      IntervalIntegrable (fun t ↦ moebiusSum (x / t) * balazardKernelDeriv t) volume 1 x :=
    intervalIntegrable_moebiusSum_div_mul hx (intervalIntegrable_balazardKernelDeriv 1 x)
  calc |∫ t in (1 : ℝ)..x, moebiusSum (x / t) * balazardKernelDeriv t|
      ≤ ∫ t in (1 : ℝ)..x, |moebiusSum (x / t) * balazardKernelDeriv t| :=
        intervalIntegral.abs_integral_le_integral_abs hx
    _ ≤ ∫ t in (1 : ℝ)..x, |moebiusSum (x / t)| / t ^ 2 := by
        refine intervalIntegral.integral_mono_on hx hint_lhs.abs
          (intervalIntegrable_abs_moebiusSum_div_div_sq hx) fun t ht ↦ ?_
        have ht0 : 0 < t := zero_lt_one.trans_le ht.1
        rw [abs_mul, abs_of_nonneg (balazardKernelDeriv_nonneg t), div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left
          ((balazardKernelDeriv_le ht0).trans_eq (one_div _)) (abs_nonneg _)
    _ = (1 / x) * ∫ t in (1 : ℝ)..x, |moebiusSum t| :=
        integral_abs_moebiusSum_div_div_sq hx

/-- **Balazard's inequality** (Ramaré 2015, Theorem 1.1; Balazard 2012, Proposition 7):
for every real `x ≥ 1`,
`|m(x)| ≤ |M(x)| / x + (∫_1^x |M(t)| dt) / x² + 8 / (3 x)`. -/
theorem abs_moebiusDivSum_le_balazard {x : ℝ} (hx : 1 ≤ x) :
    |moebiusDivSum x| ≤
      |moebiusSum x| / x + (∫ t in (1 : ℝ)..x, |moebiusSum t|) / x ^ 2 + 8 / (3 * x) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hpoly := abs_balazard_poly_le hx
  have hint := abs_integral_moebiusSum_div_mul_balazardKernelDeriv_le hx
  -- Combine triangle inequalities on Balazard's identity with `hpoly` and `hint`.
  calc |moebiusDivSum x|
      = |(moebiusSum x / x + (4 * (1 - 1 / x) ^ 2 / x - 4 * (1 - 1 / x) ^ 3 / (3 * x))) +
          (1 / x) * ∫ t in (1 : ℝ)..x, moebiusSum (x / t) * balazardKernelDeriv t| := by
          rw [moebiusDivSum_eq_balazard hx]
          congr 1
          ring
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
  refine (abs_moebiusDivSum_le_balazard h1D).trans ?_
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
