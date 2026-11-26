/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.NumberTheory.ZetaValues
public import TauCeti.NumberTheory.Explicit.MultiplicativeFunctions.Moebius.Basic
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import TauCeti.Algebra.BigOperators.Intervals
import TauCeti.Analysis.Calculus.Deriv.Fract
import TauCeti.NumberTheory.AbelSummation
import TauCeti.NumberTheory.ArithmeticFunction.Misc
import TauCeti.NumberTheory.ZetaValues

/-!
# MacLeod's functions, MacLeod's identity, and El Marraki's conversion inequality

MacLeod's functions
`φ_k(x) = (B_k(x) - B_k({x})) / x ^ (k - 1)` (`TauCeti.macleodFun`) interpolate between
`φ₁(x) = ⌊x⌋` and higher-degree polynomial approximations to `x - 1` built from the Bernoulli
polynomials `B_k` (`bernoulliFun k`). Because `B_k(X + 1) - B_k(X) = k X ^ (k - 1)`,
`φ_k(x)` telescopes to the sum `∑_{1 ≤ n ≤ x} k (1 - n / x) ^ (k - 1)`, and Möbius inversion
gives MacLeod's identity:

`∑_{n ≤ x} μ(n) φ_k(x / n) = k (1 - 1 / x) ^ (k - 1)` for `x ≥ 1`.

At `k = 1` this recovers Meissel's identity `∑_{n ≤ x} μ(n) ⌊x / n⌋ = 1`. At `k = 2`,
differentiating the periodic remainder `({t}² - {t}) / t` away from the integers gives Balazard's
`k = 2` formula for `x m(x) - M(x)`.

This file also proves El Marraki's integral identity
`∫_1^D ⌊D / t⌋ M(t) / t dt = log D`, its consequence
`m(D) = M(D) / D + (1 / D) ∫_1^D {D / t} M(t) / t dt + log D / D`, and the resulting conversion
inequality bounding `|m(D)|` in terms of `|M(D)|` and `∫_1^D |M(t)| / t dt`.

## Main declarations

* `TauCeti.macleodFun`: MacLeod's function `φ_k(x)`.
* `TauCeti.macleodFun_one`, `TauCeti.macleodFun_two`, `TauCeti.macleodFun_eq_sum`: values at
  `k = 1, 2` and the finite sum representation for `x > 0`.
* `TauCeti.sum_moebius_mul_sum_div`: hyperbola Möbius inversion
  `∑_{d ≤ N} μ(d) ∑_{m ≤ N / d} g(d m) = g(1)` for `N ≥ 1`.
* `TauCeti.sum_moebius_mul_macleodFun`: MacLeod's identity.
* `TauCeti.intervalIntegrable_moebiusSum_div_mul`, `TauCeti.integral_moebiusSum_div_mul`:
  interval integrability and sum-integral exchange for `M(x / t) w(t)`.
* `TauCeti.mul_moebiusDivSum_sub_moebiusSum_eq`: the `k = 2` identity for `x m(x) - M(x)`.
* `TauCeti.integral_abs_moebiusSum_div_mul_inv_sq`: substitution `u = x / t` for
  `∫_1^x |M(x / t)| / t² dt`.
* `TauCeti.integral_natFloor_div_mul_moebiusSum_div`, `TauCeti.moebiusDivSum_eq_elMarraki`,
  `TauCeti.abs_moebiusDivSum_le_elMarraki`, `TauCeti.abs_moebiusDivSum_le_elMarraki_of_le_mul`:
  El Marraki's identities and conversion inequalities.

## References

* M. Balazard, *Elementary remarks on Möbius' function*, Proc. Steklov Inst. Math. 276 (2012),
  33–39, Proposition 1, Proposition 2, and equation (11).
* O. Ramaré, *From explicit estimates for primes to explicit estimates for the Möbius function*,
  Acta Arith. 157 (2013), 365–379, Lemma 9.1 and Corollary 1.2.
-/

public section

open Finset MeasureTheory Filter
open scoped Topology ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace TauCeti

/-! ### MacLeod's functions -/

/-- MacLeod's function `φ_k(x) = (B_k(x) - B_k({x})) / x ^ (k - 1)`. For `x > 0`,
this equals `∑_{1 ≤ n ≤ x} k (1 - n / x) ^ (k - 1)`. -/
noncomputable def macleodFun (k : ℕ) (x : ℝ) : ℝ :=
  (bernoulliFun k x - bernoulliFun k (Int.fract x)) / x ^ (k - 1)

/-- The defining formula of `macleodFun`. -/
theorem macleodFun_def (k : ℕ) (x : ℝ) :
    macleodFun k x = (bernoulliFun k x - bernoulliFun k (Int.fract x)) / x ^ (k - 1) := (rfl)

/-- `φ₁(x) = ⌊x⌋` for every real `x`. -/
@[simp]
theorem macleodFun_one (x : ℝ) : macleodFun 1 x = ⌊x⌋ := by
  simp [macleodFun]

/-- `φ₂(x) = x - 1 - ({x}² - {x}) / x` for every nonzero real `x`. -/
theorem macleodFun_two {x : ℝ} (hx : x ≠ 0) :
    macleodFun 2 x = x - 1 - (Int.fract x ^ 2 - Int.fract x) / x := by
  simp only [macleodFun, Nat.add_one_sub_one, pow_one, bernoulliFun_two]
  field_simp
  ring

/-- On `[0, 1)`, `{x} = x`, so `φ_k(x) = 0`. -/
theorem macleodFun_of_mem_Ico (k : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    macleodFun k x = 0 := by
  rw [macleodFun, Int.fract_eq_self.mpr ⟨hx0, hx1⟩, sub_self, zero_div]

/-- For `k ≠ 1`, `B_k(1) = B_k(0)`, so `φ_k(1) = 0`. -/
@[simp]
theorem macleodFun_at_one {k : ℕ} (hk : k ≠ 1) : macleodFun k 1 = 0 := by
  rw [macleodFun, Int.fract_one, bernoulliFun_endpoints_eq_of_ne_one hk, sub_self, zero_div]

/-- Telescoping sum formula for MacLeod's function: for `k : ℕ` and `x > 0`,
`φ_k(x) = ∑_{1 ≤ n ≤ x} k (1 - n / x) ^ (k - 1)`. -/
theorem macleodFun_eq_sum (k : ℕ) {x : ℝ} (hx : 0 < x) :
    macleodFun k x = ∑ n ∈ Icc 1 ⌊x⌋₊, (k : ℝ) * (1 - (n : ℝ) / x) ^ (k - 1) := by
  have hterm (n : ℕ) :
      (k : ℝ) * (1 - ((n + 1 : ℕ) : ℝ) / x) ^ (k - 1) =
        (bernoulliFun k (x - n) - bernoulliFun k (x - (n + 1 : ℕ))) / x ^ (k - 1) := by
    have hdiff := bernoulliFun_add_one k (x - (n + 1 : ℕ))
    have harg : x - (n + 1 : ℕ) + 1 = x - n := by push_cast; ring
    rw [harg] at hdiff
    have hpow : 1 - ((n + 1 : ℕ) : ℝ) / x = (x - (n + 1 : ℕ)) / x := by
      field_simp
    rw [hpow, div_pow, ← mul_div_assoc, ← sub_eq_iff_eq_add'.mpr hdiff]
  have hreindex :
      ∑ n ∈ Icc 1 ⌊x⌋₊, (k : ℝ) * (1 - (n : ℝ) / x) ^ (k - 1) =
        ∑ n ∈ range ⌊x⌋₊, (k : ℝ) * (1 - ((n + 1 : ℕ) : ℝ) / x) ^ (k - 1) := by
    refine Finset.sum_nbij' (fun n ↦ n - 1) (fun n ↦ n + 1) ?_ ?_ ?_ ?_ ?_ <;> intro n hn
    · simp only [mem_Icc, mem_range] at hn ⊢; omega
    · simp only [mem_Icc, mem_range] at hn ⊢; omega
    · simp only [mem_Icc] at hn; omega
    · rfl
    · simp only [mem_Icc] at hn
      congr 3
      rw [Nat.sub_add_cancel hn.1]
  rw [hreindex]
  simp_rw [hterm, ← Finset.sum_div,
    Finset.sum_range_sub' (fun n ↦ bernoulliFun k (x - n)) ⌊x⌋₊]
  have hfl : (⌊x⌋₊ : ℝ) = ⌊x⌋ := by
    rw [← Int.cast_natCast, Int.natCast_floor_eq_floor hx.le]
  rw [Nat.cast_zero, sub_zero, hfl, macleodFun, Int.fract]

/-! ### Hyperbola Möbius inversion and MacLeod's identity -/

/-- Hyperbola Möbius inversion: for `g : ℕ → ℝ` and `N : ℕ`,
`∑_{1 ≤ d ≤ N} μ(d) ∑_{1 ≤ m ≤ N / d} g(d m)` equals `g(1)` when `1 ≤ N`, and `0`
when `N = 0`. -/
theorem sum_moebius_mul_sum_div (N : ℕ) (g : ℕ → ℝ) :
    ∑ d ∈ Icc 1 N, (μ d : ℝ) * ∑ m ∈ Icc 1 (N / d), g (d * m) =
      if 1 ≤ N then g 1 else 0 := by
  have h := ArithmeticFunction.sum_Ioc_mul_smul_eq_sum_sum
    (μ : ArithmeticFunction ℝ) (ζ : ArithmeticFunction ℝ) g N
  rw [ArithmeticFunction.coe_moebius_mul_coe_zeta] at h
  simp_rw [← Icc_add_one_left_eq_Ioc, zero_add, smul_eq_mul,
    ArithmeticFunction.intCoe_apply] at h
  have hzeta : ∀ d ∈ Icc 1 N,
      ∑ m ∈ Icc 1 (N / d), ((ζ : ArithmeticFunction ℝ) m) * g (d * m) =
        ∑ m ∈ Icc 1 (N / d), g (d * m) := fun d _ ↦
    Finset.sum_congr rfl fun m hm ↦ by
      rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply_ne
        (Nat.pos_iff_ne_zero.mp (Finset.mem_Icc.mp hm).1), Nat.cast_one, one_mul]
  rw [Finset.sum_congr rfl fun d hd ↦ congrArg ((↑(μ d) : ℝ) * ·) (hzeta d hd)] at h
  rw [← h]
  by_cases hN : 1 ≤ N
  · simp only [hN, ↓reduceIte]
    rw [Finset.sum_eq_single_of_mem 1 (Finset.mem_Icc.mpr ⟨le_rfl, hN⟩)
      fun n _ hn ↦ by simp [ArithmeticFunction.one_apply_ne hn]]
    simp
  · obtain rfl : N = 0 := Nat.lt_one_iff.mp (not_le.mp hN)
    simp

/-- **MacLeod's identity**: for every natural `k : ℕ` and real `x ≥ 1`,
`∑_{n ≤ x} μ(n) φ_k(x / n) = k (1 - 1 / x) ^ (k - 1)`. -/
theorem sum_moebius_mul_macleodFun (k : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) * macleodFun k (x / n) =
      k * (1 - 1 / x) ^ (k - 1) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hsum :
      ∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) * macleodFun k (x / n) =
        ∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) *
          ∑ m ∈ Icc 1 (⌊x⌋₊ / n),
            (k : ℝ) * (1 - ((n * m : ℕ) : ℝ) / x) ^ (k - 1) := by
    refine Finset.sum_congr rfl fun n hn ↦ ?_
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hxn : 0 < x / n := div_pos hx0 hn0
    rw [macleodFun_eq_sum k hxn, Nat.floor_div_natCast]
    congr 1
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    congr 2
    rw [Nat.cast_mul]
    field_simp
  rw [hsum, sum_moebius_mul_sum_div ⌊x⌋₊
    (fun n ↦ (k : ℝ) * (1 - (n : ℝ) / x) ^ (k - 1))]
  have h1 : 1 ≤ ⌊x⌋₊ := Nat.succ_le_of_lt (Nat.floor_pos.mpr hx)
  simp [h1]

/-! ### Step-function integral exchange for `M(x / t)` -/

/-- On `(1, x]`, `M(x / t) * w(t)` agrees with the finite sum of indicator-weighted copies
`∑_{1 ≤ n ≤ x} μ(n) * (Iic (x / n)).indicator w t`. -/
private theorem eqOn_moebiusSum_div_mul {x : ℝ} (hx : 1 ≤ x) (w : ℝ → ℝ) :
    Set.EqOn (fun t ↦ moebiusSum (x / t) * w t)
      (fun t ↦ ∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) * (Set.Iic (x / n)).indicator w t)
      (Set.Ioc 1 x) := by
  intro t ht
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht.1.le
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have hfloor : ⌊x / t⌋₊ ≤ ⌊x⌋₊ := Nat.floor_mono (div_le_self hx0 ht.1.le)
  dsimp only
  rw [moebiusSum_def, Finset.sum_mul]
  symm
  calc ∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) * (Set.Iic (x / n)).indicator w t
      = ∑ n ∈ Icc 1 ⌊x⌋₊, if n ≤ ⌊x / t⌋₊ then (μ n : ℝ) * w t else 0 := by
        refine Finset.sum_congr rfl fun n hn ↦ ?_
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
        have hmem : t ∈ Set.Iic (x / n) ↔ n ≤ ⌊x / t⌋₊ := by
          rw [Set.mem_Iic, le_div_iff₀ hn0, mul_comm t (n : ℝ), ← le_div_iff₀ ht0,
            ← Nat.le_floor_iff (div_nonneg hx0 ht0.le)]
        by_cases h : t ∈ Set.Iic (x / n)
        · simp [h, hmem.mp h]
        · simp [h, mt hmem.mpr h]
    _ = ∑ n ∈ (Icc 1 ⌊x⌋₊).filter (· ≤ ⌊x / t⌋₊), (μ n : ℝ) * w t := by
        rw [Finset.sum_filter]
    _ = ∑ n ∈ Icc 1 ⌊x / t⌋₊, (μ n : ℝ) * w t := by
        congr 1
        ext n
        simp only [Finset.mem_filter, Finset.mem_Icc]
        exact ⟨fun h ↦ ⟨h.1.1, h.2⟩, fun h ↦ ⟨⟨h.1, h.2.trans hfloor⟩, h.2⟩⟩

/-- If `w` is interval integrable on `1..x`, then so is `t ↦ M(x / t) * w(t)`. -/
theorem intervalIntegrable_moebiusSum_div_mul {x : ℝ} (hx : 1 ≤ x) {w : ℝ → ℝ}
    (hw : IntervalIntegrable w volume 1 x) :
    IntervalIntegrable (fun t ↦ moebiusSum (x / t) * w t) volume 1 x := by
  have hwi : IntegrableOn w (Set.Ioc 1 x) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hx).mp hw
  have hterm (n : ℕ) (_ : n ∈ Icc 1 ⌊x⌋₊) :
      IntegrableOn (fun t ↦ (μ n : ℝ) * (Set.Iic (x / n)).indicator w t) (Set.Ioc 1 x) :=
    (hwi.indicator measurableSet_Iic).const_mul _
  refine (intervalIntegrable_iff_integrableOn_Ioc_of_le hx).mpr ?_
  exact IntegrableOn.congr_fun (integrable_finsetSum (Icc 1 ⌊x⌋₊) hterm)
    (eqOn_moebiusSum_div_mul hx w).symm measurableSet_Ioc

/-- Integrating `M(x / t) * w(t)` over `[1, x]` swaps with the sum defining `M(x / t)`:
`∫_1^x M(x / t) w(t) dt = ∑_{1 ≤ n ≤ x} μ(n) ∫_1^{x / n} w(t) dt`. -/
theorem integral_moebiusSum_div_mul {x : ℝ} (hx : 1 ≤ x) {w : ℝ → ℝ}
    (hw : IntervalIntegrable w volume 1 x) :
    ∫ t in (1 : ℝ)..x, moebiusSum (x / t) * w t =
      ∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) * ∫ t in (1 : ℝ)..(x / n), w t := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hwi : IntegrableOn w (Set.Ioc 1 x) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hx).mp hw
  have hterm (n : ℕ) (_ : n ∈ Icc 1 ⌊x⌋₊) :
      IntegrableOn (fun t ↦ (μ n : ℝ) * (Set.Iic (x / n)).indicator w t) (Set.Ioc 1 x) :=
    (hwi.indicator measurableSet_Iic).const_mul _
  rw [intervalIntegral.integral_of_le hx,
    setIntegral_congr_fun measurableSet_Ioc (eqOn_moebiusSum_div_mul hx w)]
  have hswap :
      ∫ t in Set.Ioc 1 x,
          ∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) * (Set.Iic (x / n)).indicator w t =
        ∑ n ∈ Icc 1 ⌊x⌋₊,
          ∫ t in Set.Ioc 1 x, (μ n : ℝ) * (Set.Iic (x / n)).indicator w t :=
    integral_finsetSum (Icc 1 ⌊x⌋₊) hterm
  rw [hswap]
  refine Finset.sum_congr rfl fun n hn ↦ ?_
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hnx : (n : ℝ) ≤ x :=
    le_trans (by exact_mod_cast (Finset.mem_Icc.mp hn).2) (Nat.floor_le hx0.le)
  have h1xn : 1 ≤ x / n := (one_le_div (by exact_mod_cast hn1)).mpr hnx
  have hxn_le : x / n ≤ x := div_le_self hx0.le (by exact_mod_cast hn1)
  rw [integral_const_mul, setIntegral_indicator measurableSet_Iic, Set.Ioc_inter_Iic,
    min_eq_right hxn_le, intervalIntegral.integral_of_le h1xn]

/-! ### Balazard's `k = 2` identity -/

/-- **Balazard's `k = 2` identity**: for every real `x ≥ 1`,
`x m(x) - M(x) = 2 - 2 / x + ∫_1^x M(x / t) (((2 {t} - 1) t + {t} - {t}²) / t²) dt`. -/
theorem mul_moebiusDivSum_sub_moebiusSum_eq {x : ℝ} (hx : 1 ≤ x) :
    x * moebiusDivSum x - moebiusSum x =
      2 - 2 / x + ∫ t in (1 : ℝ)..x,
        moebiusSum (x / t) *
          (((2 * Int.fract t - 1) * t + Int.fract t - Int.fract t ^ 2) / t ^ 2) := by
  let ε₀ : ℝ → ℝ := fun t ↦ (Int.fract t ^ 2 - Int.fract t) / t
  let ε₀' : ℝ → ℝ := fun t ↦
    ((2 * Int.fract t - 1) * t + Int.fract t - Int.fract t ^ 2) / t ^ 2
  have hcont : ContinuousOn ε₀ (Set.Ici 1) :=
    Int.continuous_fract_sq_sub_fract.continuousOn.div continuousOn_id fun t ht ↦
      ne_of_gt (lt_of_lt_of_le zero_lt_one ht)
  have hmeas : Measurable ε₀' := by
    have _hf : Measurable (Int.fract : ℝ → ℝ) := measurable_fract
    fun_prop
  have hbound (t : ℝ) (ht : 0 ≤ t) :
      |(2 * Int.fract t - 1) * t + Int.fract t - Int.fract t ^ 2| ≤ t := by
    have h0 := Int.fract_nonneg t
    have h1 := Int.fract_lt_one t
    rw [abs_le]
    constructor
    · nlinarith
    · rcases lt_or_ge t 1 with ht1 | ht1
      · rw [Int.fract_eq_self.mpr ⟨ht, ht1⟩]
        nlinarith
      · nlinarith
  have hi (y : ℝ) (hy : 1 ≤ y) : IntervalIntegrable ε₀' volume 1 y := by
    refine (intervalIntegrable_iff_integrableOn_Ioc_of_le hy).mpr ?_
    refine (integrableOn_const (C := (1 : ℝ)) (hs := measure_Ioc_lt_top.ne)).mono'
      hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht1 : 1 ≤ t := ht.1.le
    have hbd := hbound t (zero_le_one.trans ht1)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos (zero_lt_one.trans ht.1) 2)]
    exact (div_le_one (pow_pos (zero_lt_one.trans ht.1) 2)).mpr
      (hbd.trans (by nlinarith))
  have hderiv (t : ℝ) (ht : t ∈ Set.Ioi 0 \ Set.range ((↑) : ℤ → ℝ)) :
      HasDerivAt ε₀ (ε₀' t) t := by
    have ht0 : t ≠ 0 := ne_of_gt ht.1
    have hfr := Int.hasDerivAt_fract ht.2
    have hnum : HasDerivAt (fun u : ℝ ↦ Int.fract u ^ 2 - Int.fract u)
        (2 * Int.fract t - 1) t := by
      have h := (hfr.pow 2).sub hfr
      refine h.congr_deriv ?_
      ring
    refine (hnum.div (hasDerivAt_id' t) ht0).congr_deriv ?_
    dsimp [ε₀']
    field_simp
    ring
  have hε₀_int (y : ℝ) (hy : 1 ≤ y) : ∫ t in (1 : ℝ)..y, ε₀' t = ε₀ y := by
    have h := integral_eq_of_hasDerivAt_off_countable ε₀ ε₀'
      (Set.countable_range ((↑) : ℤ → ℝ))
      (hcont.mono (by rw [Set.uIcc_of_le hy]; exact Set.Icc_subset_Ici_self))
      (fun t ht ↦ hderiv t
        ⟨lt_of_lt_of_le zero_lt_one (by
          have hlt := ht.1.1
          rw [min_eq_left hy] at hlt
          exact hlt.le), ht.2⟩)
      (hi y hy)
    have h1 : ε₀ 1 = 0 := by simp [ε₀]
    simpa [h1] using h
  have hswap := integral_moebiusSum_div_mul hx (hi x hx)
  have hε₀_sum :
      ∫ t in (1 : ℝ)..x, moebiusSum (x / t) * ε₀' t =
        ∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) * ε₀ (x / n) := by
    rw [hswap]
    refine Finset.sum_congr rfl fun n hn ↦ ?_
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hnx : (n : ℝ) ≤ x := le_trans (by exact_mod_cast (Finset.mem_Icc.mp hn).2)
      (Nat.floor_le (zero_le_one.trans hx))
    rw [hε₀_int (x / n) ((one_le_div (by exact_mod_cast hn1)).mpr hnx)]
  have hmacleod2 := sum_moebius_mul_macleodFun 2 hx
  have hdiff :
      ∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) * macleodFun 2 (x / n) =
        x * moebiusDivSum x - moebiusSum x -
          ∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) * ε₀ (x / n) := by
    rw [moebiusDivSum_def, moebiusSum_def, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n hn ↦ ?_
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hxn0 : x / n ≠ 0 := div_ne_zero (by linarith) (by positivity)
    rw [macleodFun_two hxn0]
    dsimp [ε₀]
    ring
  rw [hdiff, ← hε₀_sum] at hmacleod2
  simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one] at hmacleod2
  rw [show (2 : ℝ) * (1 - 1 / x) = 2 - 2 / x by ring] at hmacleod2
  change x * moebiusDivSum x - moebiusSum x =
    2 - 2 / x + ∫ t in (1 : ℝ)..x, moebiusSum (x / t) * ε₀' t
  linarith

/-! ### El Marraki's identities and conversion inequalities -/

/-- Interval integrability of `u ↦ ⌊u⌋₊ / u` on `1..D`. -/
private theorem intervalIntegrable_natFloor_div (D : ℝ) :
    IntervalIntegrable (fun u : ℝ ↦ (⌊u⌋₊ : ℝ) / u) volume 1 D := by
  have hc : ContinuousOn (fun t : ℝ ↦ t⁻¹) (Set.Ici 1) :=
    continuousOn_inv₀.mono fun t ht ↦ ne_of_gt (lt_of_lt_of_le zero_lt_one ht)
  have hbase := intervalIntegrable_mul_sum_Icc (fun _ : ℕ ↦ (1 : ℝ))
    (hc.locallyIntegrableOn measurableSet_Ici) 1 D
  refine (intervalIntegrable_congr fun t _ ↦ ?_).mp hbase
  simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one]
  rw [div_eq_inv_mul]

/-- Substitution `u = D / t` turns `IntervalIntegrable` on `1..D` of `g (D / u) * w u` into
`IntervalIntegrable` of `g t * w (D / t) * D / t ^ 2` (and gives the integral identity). -/
private theorem intervalIntegrable_comp_div_and_integral {D : ℝ} (hD : 1 ≤ D)
    {g w : ℝ → ℝ} (hgw : IntervalIntegrable (fun u ↦ g (D / u) * w u) volume 1 D) :
    IntervalIntegrable (fun t ↦ g t * w (D / t) * D / t ^ 2) volume 1 D ∧
      ∫ t in (1 : ℝ)..D, g t * w (D / t) * D / t ^ 2 =
        ∫ u in (1 : ℝ)..D, g (D / u) * w u := by
  have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hf_cont : ContinuousOn (fun t : ℝ ↦ D / t) (Set.uIcc 1 D) :=
    continuousOn_const.div continuousOn_id fun t ht ↦ by
      rw [Set.uIcc_of_le hD] at ht; exact ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1)
  have hf_deriv :
      ∀ t ∈ Set.Ioo (min 1 D) (max 1 D), HasDerivAt (fun t : ℝ ↦ D / t) (-D / t ^ 2) t := by
    intro t ht
    rw [min_eq_left hD, max_eq_right hD] at ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1.le)
    refine ((hasDerivAt_const t D).div (hasDerivAt_id' t) ht0).congr_deriv ?_
    ring
  have hf_nonpos : ∀ t ∈ Set.Ioo (min 1 D) (max 1 D), -D / t ^ 2 ≤ 0 := by
    intro t _
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hD0.le) (sq_nonneg t)
  have hif := (intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonpos
    (g := fun u ↦ g (D / u) * w u) hf_cont hf_deriv hf_nonpos).mpr
    (by rw [div_one, div_self hD0.ne']; exact hgw.symm)
  have hint := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos
    (g := fun u ↦ g (D / u) * w u) hf_cont hf_deriv hf_nonpos
  rw [div_one, div_self hD0.ne', intervalIntegral.integral_symm 1 D] at hint
  have heq :
      Set.EqOn (fun t ↦ -(((fun u ↦ g (D / u) * w u) ∘ fun t ↦ D / t) t * (-D / t ^ 2)))
        (fun t ↦ g t * w (D / t) * D / t ^ 2) (Set.uIcc 1 D) := by
    intro t ht
    rw [Set.uIcc_of_le hD] at ht
    dsimp [Function.comp]
    rw [div_div_eq_mul_div, mul_div_cancel_left₀ t hD0.ne']
    ring
  constructor
  · exact (intervalIntegrable_congr (fun t ht ↦ heq (Set.uIoc_subset_uIcc ht))).mp hif.neg
  · rw [← neg_inj, neg_neg] at hint
    rw [← hint, ← intervalIntegral.integral_neg]
    exact intervalIntegral.integral_congr heq.symm

/-- Substitution `u = x / t` converts `∫_1^x |M(x / t)| / t² dt` into
`(1 / x) ∫_1^x |M(t)| dt`. -/
theorem integral_abs_moebiusSum_div_mul_inv_sq {x : ℝ} (hx : 1 ≤ x) :
    ∫ t in (1 : ℝ)..x, |moebiusSum (x / t)| / t ^ 2 =
      (1 / x) * ∫ t in (1 : ℝ)..x, |moebiusSum t| := by
  have hc : ContinuousOn (fun t : ℝ ↦ (t ^ 2)⁻¹) (Set.Ici 1) :=
    (continuousOn_pow 2).inv₀ fun t ht ↦ ne_of_gt (pow_pos (lt_of_lt_of_le zero_lt_one ht) 2)
  have hw : IntervalIntegrable (fun t : ℝ ↦ (t ^ 2)⁻¹) volume 1 x :=
    (hc.mono (by rw [Set.uIcc_of_le hx]; exact Set.Icc_subset_Ici_self)).intervalIntegrable
  have hgw : IntervalIntegrable (fun u ↦ |moebiusSum (x / u)| * (u ^ 2)⁻¹) volume 1 x := by
    refine (intervalIntegrable_congr fun u _hu ↦ ?_).mp
      (intervalIntegrable_moebiusSum_div_mul hx hw).abs
    rw [abs_mul, abs_inv, abs_of_nonneg (sq_nonneg u)]
  have hint := (intervalIntegrable_comp_div_and_integral
    (g := fun t ↦ |moebiusSum t|) (w := fun u ↦ (u ^ 2)⁻¹) hx hgw).2
  have hlhs :
      ∫ t in (1 : ℝ)..x, |moebiusSum t| * ((x / t) ^ 2)⁻¹ * x / t ^ 2 =
        (1 / x) * ∫ t in (1 : ℝ)..x, |moebiusSum t| := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [Set.uIcc_of_le hx] at ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1)
    field_simp
  have hrhs :
      ∫ u in (1 : ℝ)..x, |moebiusSum (x / u)| * (u ^ 2)⁻¹ =
        ∫ t in (1 : ℝ)..x, |moebiusSum (x / t)| / t ^ 2 :=
    intervalIntegral.integral_congr fun t _ ↦ (div_eq_mul_inv _ _).symm
  rw [← hrhs, ← hint, hlhs]

/-- Integrability of the three El Marraki integrands on `1..D`. -/
private theorem intervalIntegrable_elMarraki_pieces {D : ℝ} (hD : 1 ≤ D) :
    IntervalIntegrable (fun t ↦ moebiusSum t / t ^ 2) volume 1 D ∧
      IntervalIntegrable (fun t ↦ (⌊D / t⌋₊ : ℝ) * moebiusSum t / t) volume 1 D ∧
      IntervalIntegrable (fun t ↦ (D / t - ⌊D / t⌋₊) * moebiusSum t / t) volume 1 D := by
  have h1 : IntervalIntegrable (fun t ↦ moebiusSum t / t ^ 2) volume 1 D := by
    have hc : ContinuousOn (fun t : ℝ ↦ (t ^ 2)⁻¹) (Set.Ici 1) :=
      (continuousOn_pow 2).inv₀ fun t ht ↦ ne_of_gt (pow_pos (lt_of_lt_of_le zero_lt_one ht) 2)
    simpa only [div_eq_mul_inv] using
      intervalIntegrable_moebiusSum_mul (hc.locallyIntegrableOn measurableSet_Ici) 1 D
  have h2_aux := (intervalIntegrable_comp_div_and_integral hD
    (intervalIntegrable_moebiusSum_div_mul hD (intervalIntegrable_natFloor_div D))).1
  have h2 :
      IntervalIntegrable (fun t ↦ (⌊D / t⌋₊ : ℝ) * moebiusSum t / t) volume 1 D := by
    refine (intervalIntegrable_congr fun t ht ↦ ?_).mp h2_aux
    have ht1 : 1 ≤ t := by
      have h := Set.uIoc_subset_uIcc ht
      rw [Set.uIcc_of_le hD] at h
      exact h.1
    have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one ht1)
    field_simp
  have h3 :
      IntervalIntegrable (fun t ↦ (D / t - ⌊D / t⌋₊) * moebiusSum t / t) volume 1 D := by
    refine (intervalIntegrable_congr fun t ht ↦ ?_).mp ((h1.const_mul D).sub h2)
    have ht1 : 1 ≤ t := by
      have h := Set.uIoc_subset_uIcc ht
      rw [Set.uIcc_of_le hD] at h
      exact h.1
    have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one ht1)
    field_simp
  exact ⟨h1, h2, h3⟩

/-- **El Marraki's second identity**: for every real `D ≥ 1`,
`∫_1^D ⌊D / t⌋ M(t) / t dt = log D`. -/
theorem integral_natFloor_div_mul_moebiusSum_div {D : ℝ} (hD : 1 ≤ D) :
    ∫ t in (1 : ℝ)..D, (⌊D / t⌋₊ : ℝ) * moebiusSum t / t = Real.log D := by
  have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hD
  let w : ℝ → ℝ := fun u ↦ (⌊u⌋₊ : ℝ) / u
  have hw := intervalIntegrable_natFloor_div D
  have hsub := (intervalIntegrable_comp_div_and_integral hD
    (intervalIntegrable_moebiusSum_div_mul hD hw)).2
  have hcongr :
      ∫ t in (1 : ℝ)..D, (⌊D / t⌋₊ : ℝ) * moebiusSum t / t =
        ∫ t in (1 : ℝ)..D, moebiusSum t * w (D / t) * D / t ^ 2 := by
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [Set.uIcc_of_le hD] at ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1)
    dsimp [w]
    field_simp
  rw [hcongr, hsub, integral_moebiusSum_div_mul hD hw]
  have hinner (y : ℝ) (hy : 1 ≤ y) :
      ∫ u in (1 : ℝ)..y, w u =
        (⌊y⌋₊ : ℝ) * Real.log y - ∑ m ∈ Icc 1 ⌊y⌋₊, Real.log m := by
    let c : ℕ → ℝ := fun k ↦ if k = 0 then 0 else 1
    have habel := sum_mul_eq_sub_integral_mul₀ c rfl y
      (fun t ht ↦ Real.differentiableAt_log (by linarith [ht.1]))
      (by
        rw [Real.deriv_log']
        exact (continuousOn_inv₀.mono fun t ht ↦
          ne_of_gt (by linarith [ht.1] : (0 : ℝ) < t)).integrableOn_Icc)
    have hsum1 :
        ∑ k ∈ Icc 0 ⌊y⌋₊, Real.log k * c k = ∑ m ∈ Icc 1 ⌊y⌋₊, Real.log m := by
      rw [sum_Icc_zero_eq_sum_Icc_one (f := fun k ↦ Real.log k * c k) (by simp [c])]
      refine Finset.sum_congr rfl fun m hm ↦ ?_
      have hm0 : m ≠ 0 := Nat.pos_iff_ne_zero.mp (Finset.mem_Icc.mp hm).1
      simp [c, hm0]
    have hsum2 : ∑ k ∈ Icc 0 ⌊y⌋₊, c k = (⌊y⌋₊ : ℝ) := by
      rw [sum_Icc_zero_eq_sum_Icc_one (f := c) (by simp [c])]
      have : ∑ m ∈ Icc 1 ⌊y⌋₊, c m = ∑ _m ∈ Icc 1 ⌊y⌋₊, (1 : ℝ) :=
        Finset.sum_congr rfl fun m hm ↦ by
          simp [c, Nat.pos_iff_ne_zero.mp (Finset.mem_Icc.mp hm).1]
      rw [this]
      simp
    rw [hsum1, hsum2, Real.deriv_log'] at habel
    have hint :
        ∫ u in (1 : ℝ)..y, w u = ∫ t in Set.Ioc 1 y, t⁻¹ * ∑ k ∈ Icc 0 ⌊t⌋₊, c k := by
      rw [intervalIntegral.integral_of_le hy]
      refine setIntegral_congr_fun measurableSet_Ioc fun t _ht ↦ ?_
      have hc_t : ∑ k ∈ Icc 0 ⌊t⌋₊, c k = (⌊t⌋₊ : ℝ) := by
        rw [sum_Icc_zero_eq_sum_Icc_one (f := c) (by simp [c])]
        have : ∑ m ∈ Icc 1 ⌊t⌋₊, c m = ∑ _m ∈ Icc 1 ⌊t⌋₊, (1 : ℝ) :=
          Finset.sum_congr rfl fun m hm ↦ by
            simp [c, Nat.pos_iff_ne_zero.mp (Finset.mem_Icc.mp hm).1]
        rw [this]
        simp
      rw [hc_t]
      dsimp [w]
      ring
    rw [hint]
    linarith
  have hlog :
      ∑ n ∈ Icc 1 ⌊D⌋₊, (μ n : ℝ) * ∫ u in (1 : ℝ)..(D / n), w u =
        (∑ n ∈ Icc 1 ⌊D⌋₊, (μ n : ℝ) * ⌊D / n⌋₊) * Real.log D -
          ∑ n ∈ Icc 1 ⌊D⌋₊, (μ n : ℝ) *
            ∑ m ∈ Icc 1 (⌊D⌋₊ / n), Real.log ((n * m : ℕ) : ℝ) := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n hn ↦ ?_
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hnx : (n : ℝ) ≤ D :=
      le_trans (by exact_mod_cast (Finset.mem_Icc.mp hn).2) (Nat.floor_le hD0.le)
    rw [hinner (D / n) ((one_le_div hn0).mpr hnx), Nat.floor_div_natCast,
      Real.log_div hD0.ne' hn0.ne']
    have hsplit :
        ∑ m ∈ Icc 1 (⌊D⌋₊ / n), Real.log ((n * m : ℕ) : ℝ) =
          (⌊D⌋₊ / n : ℕ) * Real.log n + ∑ m ∈ Icc 1 (⌊D⌋₊ / n), Real.log m := by
      have hterm (m : ℕ) (hm : m ∈ Icc 1 (⌊D⌋₊ / n)) :
          Real.log ((n * m : ℕ) : ℝ) = Real.log n + Real.log m := by
        have hm0 : (m : ℝ) ≠ 0 := by
          exact_mod_cast Nat.pos_iff_ne_zero.mp (Finset.mem_Icc.mp hm).1
        rw [Nat.cast_mul, Real.log_mul hn0.ne' hm0]
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc,
        Nat.add_sub_cancel, nsmul_eq_mul]
    rw [hsplit]
    ring
  rw [hlog, sum_moebius_mul_natFloor_div hD, one_mul,
    sum_moebius_mul_sum_div ⌊D⌋₊ (fun k ↦ Real.log k)]
  simp

/-- **El Marraki's identity**: for every real `D ≥ 1`,
`m(D) = M(D) / D + (1 / D) ∫_1^D (D / t - ⌊D / t⌋) M(t) / t dt + (log D) / D`. -/
theorem moebiusDivSum_eq_elMarraki {D : ℝ} (hD : 1 ≤ D) :
    moebiusDivSum D =
      moebiusSum D / D +
        (1 / D) * (∫ t in (1 : ℝ)..D, (D / t - ⌊D / t⌋₊) * moebiusSum t / t) +
        Real.log D / D := by
  have habel := moebiusDivSum_eq_div_add_integral D
  obtain ⟨_, h2, hrem⟩ := intervalIntegrable_elMarraki_pieces hD
  have hsplit :
      (1 / D) * (∫ t in (1 : ℝ)..D, (D / t - ⌊D / t⌋₊) * moebiusSum t / t) +
          (1 / D) * (∫ t in (1 : ℝ)..D, (⌊D / t⌋₊ : ℝ) * moebiusSum t / t) =
        ∫ t in (1 : ℝ)..D, moebiusSum t / t ^ 2 := by
    rw [← mul_add, ← intervalIntegral.integral_add hrem h2,
      ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [Set.uIcc_of_le hD] at ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1)
    field_simp
    ring
  rw [integral_natFloor_div_mul_moebiusSum_div hD] at hsplit
  rw [habel, ← hsplit]
  ring

/-- Interval integrability of `t ↦ |M(t)| / t` on `a..b` for `1 ≤ a ≤ b`. -/
private theorem intervalIntegrable_abs_moebiusSum_div {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t ↦ |moebiusSum t| / t) volume a b := by
  have hc_inv : ContinuousOn (fun t : ℝ ↦ t⁻¹) (Set.Ici 1) :=
    continuousOn_inv₀.mono fun t ht ↦ ne_of_gt (lt_of_lt_of_le zero_lt_one ht)
  have hbase :=
    (intervalIntegrable_moebiusSum_mul (hc_inv.locallyIntegrableOn measurableSet_Ici) a b).abs
  refine (intervalIntegrable_congr fun t ht ↦ ?_).mp hbase
  have hta : a ≤ t := by
    have h := Set.uIoc_subset_uIcc ht
    rw [Set.uIcc_of_le hab] at h
    exact h.1
  rw [abs_mul, abs_inv, abs_of_pos (lt_of_lt_of_le zero_lt_one (ha.trans hta)), div_eq_mul_inv]

/-- **El Marraki's conversion inequality** (Ramaré 2013, Lemma 9.1): for every real `D ≥ 1`,
`|m(D)| ≤ |M(D)| / D + (1 / D) ∫_1^D |M(t)| / t dt + (log D) / D`. -/
theorem abs_moebiusDivSum_le_elMarraki {D : ℝ} (hD : 1 ≤ D) :
    |moebiusDivSum D| ≤
      |moebiusSum D| / D + (1 / D) * (∫ t in (1 : ℝ)..D, |moebiusSum t| / t) +
        Real.log D / D := by
  have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hlog : 0 ≤ Real.log D / D := div_nonneg (Real.log_nonneg hD) hD0.le
  have habs_int := intervalIntegrable_abs_moebiusSum_div le_rfl hD
  have hrem := (intervalIntegrable_elMarraki_pieces hD).2.2
  have hle_int :
      |∫ t in (1 : ℝ)..D, (D / t - ⌊D / t⌋₊) * moebiusSum t / t| ≤
        ∫ t in (1 : ℝ)..D, |moebiusSum t| / t := by
    refine (intervalIntegral.abs_integral_le_integral_abs hD).trans ?_
    refine intervalIntegral.integral_mono_on hD hrem.abs habs_int fun t ht ↦ ?_
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
    have hfr0 : 0 ≤ D / t - ⌊D / t⌋₊ :=
      sub_nonneg.mpr (Nat.floor_le (div_nonneg hD0.le ht0.le))
    have hfr1 : D / t - ⌊D / t⌋₊ ≤ 1 := by linarith [Nat.lt_floor_add_one (D / t)]
    rw [abs_div, abs_mul, abs_of_nonneg hfr0, abs_of_pos ht0]
    exact div_le_div_of_nonneg_right (mul_le_of_le_one_left (abs_nonneg _) hfr1) ht0.le
  calc |moebiusDivSum D|
      = |moebiusSum D / D +
          (1 / D) * (∫ t in (1 : ℝ)..D, (D / t - ⌊D / t⌋₊) * moebiusSum t / t) +
          Real.log D / D| := by rw [moebiusDivSum_eq_elMarraki hD]
    _ ≤ |moebiusSum D / D +
          (1 / D) * (∫ t in (1 : ℝ)..D, (D / t - ⌊D / t⌋₊) * moebiusSum t / t)| +
          |Real.log D / D| := abs_add_le _ _
    _ ≤ (|moebiusSum D / D| +
          |(1 / D) * (∫ t in (1 : ℝ)..D, (D / t - ⌊D / t⌋₊) * moebiusSum t / t)|) +
          |Real.log D / D| := add_le_add (abs_add_le _ _) le_rfl
    _ = |moebiusSum D| / D +
          (1 / D) * |∫ t in (1 : ℝ)..D, (D / t - ⌊D / t⌋₊) * moebiusSum t / t| +
          Real.log D / D := by
        rw [abs_div, abs_of_pos hD0, abs_mul, abs_of_pos (one_div_pos.mpr hD0),
          abs_of_nonneg hlog]
    _ ≤ |moebiusSum D| / D + (1 / D) * (∫ t in (1 : ℝ)..D, |moebiusSum t| / t) +
          Real.log D / D := by gcongr

/-- **El Marraki's two-range conversion bound** (Ramaré 2013, Corollary 1.2):
if `1 ≤ t₀ ≤ D`, `|M(t)| ≤ ε(t) t` on `[t₀, D]`, and `ε` is interval integrable on `t₀..D`,
then
`|m(D)| ≤ ε(D) + (1 / D) (∫_1^{t₀} |M(t)| / t dt + ∫_{t₀}^D ε(t) dt) + (log D) / D`. -/
theorem abs_moebiusDivSum_le_elMarraki_of_le_mul {t₀ D : ℝ} (ht₀ : 1 ≤ t₀)
    (hD : t₀ ≤ D) {ε : ℝ → ℝ} (hε : IntervalIntegrable ε volume t₀ D)
    (hM : ∀ t ∈ Set.Icc t₀ D, |moebiusSum t| ≤ ε t * t) :
    |moebiusDivSum D| ≤
      ε D + (1 / D) * ((∫ t in (1 : ℝ)..t₀, |moebiusSum t| / t) + ∫ t in t₀..D, ε t) +
        Real.log D / D := by
  have h1D : 1 ≤ D := ht₀.trans hD
  have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one h1D
  have hsplit :
      ∫ t in (1 : ℝ)..D, |moebiusSum t| / t =
        (∫ t in (1 : ℝ)..t₀, |moebiusSum t| / t) + ∫ t in t₀..D, |moebiusSum t| / t :=
    (intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_abs_moebiusSum_div le_rfl ht₀)
      (intervalIntegrable_abs_moebiusSum_div ht₀ hD)).symm
  have htail : ∫ t in t₀..D, |moebiusSum t| / t ≤ ∫ t in t₀..D, ε t := by
    refine intervalIntegral.integral_mono_on hD
      (intervalIntegrable_abs_moebiusSum_div ht₀ hD) hε fun t ht ↦ ?_
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one (ht₀.trans ht.1)
    exact (div_le_iff₀ ht0).mpr (hM t ht)
  have hM_D : |moebiusSum D| / D ≤ ε D :=
    (div_le_iff₀ hD0).mpr (hM D ⟨hD, le_rfl⟩)
  refine (abs_moebiusDivSum_le_elMarraki h1D).trans ?_
  rw [hsplit]
  gcongr

end TauCeti
