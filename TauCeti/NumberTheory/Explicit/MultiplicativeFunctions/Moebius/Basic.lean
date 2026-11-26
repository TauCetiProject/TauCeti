/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import TauCeti.Algebra.BigOperators.Intervals
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Basic
import TauCeti.NumberTheory.AbelSummation
import TauCeti.Topology.Algebra.Order.Floor

/-!
# The summatory functions of the Möbius function at a real argument

Explicit bounds for the Möbius function are stated for three summatory functions of a real
variable `x`:

* the Mertens function `M(x) = ∑_{n ≤ x} μ(n)` (`TauCeti.moebiusSum`);
* the logarithmic sum `m(x) = ∑_{n ≤ x} μ(n) / n` (`TauCeti.moebiusDivSum`);
* the logarithmically weighted sum `ℓ(x) = ∑_{n ≤ x} μ(n) log (x / n) / n`
  (`TauCeti.moebiusLogSum`), which Ramaré writes as `m` with a caron.

Each sum runs over the natural numbers in `Finset.Icc 1 ⌊x⌋₊`, so all three vanish for `x < 1`,
and `M` and `m` are step functions, constant on each `[N, N + 1)`. The weighted
sum `ℓ` is not a step function: it is the primitive `ℓ(x) = ∫_1^x m(t) / t dt`, hence
continuous on all of `ℝ` and differentiable off the natural numbers with derivative `m(x) / x`.

This file records how the three are related. Abel summation against `1 / t` writes `m` through
`M`, and Abel summation against `log (x / t) / t` writes `ℓ` through `M`:
`m(x) = M(x) / x + ∫_1^x M(t) / t² dt` and
`ℓ(x) = ∫_1^x M(t) log (x / t) / t² dt + ∫_1^x M(t) / t² dt`.
These are the identities through which explicit bounds for `M` are carried over to `m` and `ℓ`
(Balazard's and Ramaré's conversion inequalities). Finally, Meissel's identity
`∑_{n ≤ x} μ(n) ⌊x / n⌋ = 1` for `x ≥ 1`, the summed form of `μ * ζ = 1`, is the starting point of
the elementary bounds for `M` and `m`.

The integral identities hold for every real `x`: below `1` both sides vanish, as every sum is
empty and every integrand vanishes on `[x, 1)`.

## Main declarations

* `TauCeti.moebiusSum`, `TauCeti.moebiusDivSum`, `TauCeti.moebiusLogSum`: `M`, `m` and `ℓ`.
* `TauCeti.moebiusSum_natCast`, `TauCeti.moebiusSum_natFloor`, `TauCeti.moebiusSum_natCast_add_one`
  and their analogues for `m`: agreement with the sums over `Finset.Icc 1 N`, constancy on
  `[N, N + 1)` and the jump `μ(N + 1)`.
* `TauCeti.abs_moebiusSum_le`: the trivial bound `|M(x)| ≤ x` for `x ≥ 0`.
* `TauCeti.moebiusLogSum_eq_moebiusDivSum_mul_log_sub`:
  `ℓ(x) = m(x) log x - ∑_{n ≤ x} μ(n) log n / n`.
* `TauCeti.moebiusDivSum_eq_div_add_integral`: `m(x) = M(x) / x + ∫_1^x M(t) / t² dt`.
* `TauCeti.moebiusLogSum_eq_integral`: `ℓ(x) = ∫_1^x m(t) / t dt`.
* `TauCeti.moebiusLogSum_eq_integral_moebiusSum`: `ℓ` through `M`.
* `TauCeti.intervalIntegrable_moebiusSum_mul`: `M(t) f(t)` is interval integrable between any two
  reals for `f` locally integrable on `[1, ∞)`.
* `TauCeti.continuous_moebiusLogSum`, `TauCeti.hasDerivAt_moebiusLogSum`: `ℓ` is continuous, with
  derivative `m(x) / x` off the natural numbers.
* `TauCeti.sum_moebius_mul_natFloor_div`: Meissel's identity `∑_{n ≤ x} μ(n) ⌊x / n⌋ = 1`.

## References

* M. Balazard, *Elementary remarks on Möbius' function*, Proc. Steklov Inst. Math. 276 (2012),
  33–39, equation (1) (Meissel's identity).
* O. Ramaré, *Explicit estimates on several summatory functions involving the Moebius function*,
  Math. Comp. 84 (2015), 1359–1387.
-/

public section

open Finset MeasureTheory Filter
open scoped Topology
open scoped ArithmeticFunction.Moebius

namespace TauCeti

variable {x : ℝ}

/-! ### The three summatory functions -/

/-- The Mertens function `M(x) = ∑_{n ≤ x} μ(n)` at a real argument; the sum runs over
`Finset.Icc 1 ⌊x⌋₊`, so `M(x) = 0` for `x < 1`. -/
noncomputable def moebiusSum (x : ℝ) : ℝ :=
  ∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ)

/-- The logarithmic Möbius sum `m(x) = ∑_{n ≤ x} μ(n) / n` at a real argument; the sum runs over
`Finset.Icc 1 ⌊x⌋₊`, so `m(x) = 0` for `x < 1`. -/
noncomputable def moebiusDivSum (x : ℝ) : ℝ :=
  ∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) / n

/-- The logarithmically weighted Möbius sum `ℓ(x) = ∑_{n ≤ x} μ(n) log (x / n) / n` at a real
argument; the sum runs over `Finset.Icc 1 ⌊x⌋₊`, so `ℓ(x) = 0` for `x < 1`. -/
noncomputable def moebiusLogSum (x : ℝ) : ℝ :=
  ∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) * Real.log (x / n) / n

/-- The defining sum of `M(x)`. -/
theorem moebiusSum_def (x : ℝ) : moebiusSum x = ∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) := (rfl)

/-- The defining sum of `m(x)`. -/
theorem moebiusDivSum_def (x : ℝ) : moebiusDivSum x = ∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) / n := (rfl)

/-- The defining sum of `ℓ(x)`. -/
theorem moebiusLogSum_def (x : ℝ) :
    moebiusLogSum x = ∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) * Real.log (x / n) / n := (rfl)

/-! ### Values below `1` and at the natural numbers -/

/-- `M(x) = 0` for `x < 1`: the sum is empty. -/
theorem moebiusSum_of_lt_one (hx : x < 1) : moebiusSum x = 0 :=
  sum_Icc_one_natFloor_eq_zero _ hx

/-- `m(x) = 0` for `x < 1`: the sum is empty. -/
theorem moebiusDivSum_of_lt_one (hx : x < 1) : moebiusDivSum x = 0 :=
  sum_Icc_one_natFloor_eq_zero _ hx

/-- `ℓ(x) = 0` for `x < 1`: the sum is empty. -/
theorem moebiusLogSum_of_lt_one (hx : x < 1) : moebiusLogSum x = 0 :=
  sum_Icc_one_natFloor_eq_zero _ hx

/-- At a natural number `N`, `M(N)` is the sum of `μ` over `Finset.Icc 1 N`. -/
@[simp]
theorem moebiusSum_natCast (N : ℕ) : moebiusSum N = ∑ n ∈ Icc 1 N, (μ n : ℝ) := by
  simp [moebiusSum]

/-- At a natural number `N`, `m(N)` is the sum of `μ(n) / n` over `Finset.Icc 1 N`. -/
@[simp]
theorem moebiusDivSum_natCast (N : ℕ) : moebiusDivSum N = ∑ n ∈ Icc 1 N, (μ n : ℝ) / n := by
  simp [moebiusDivSum]

/-- `M` is constant on each interval `[N, N + 1)`: `M(x) = M(⌊x⌋₊)`. -/
@[simp high]
theorem moebiusSum_natFloor (x : ℝ) : moebiusSum ⌊x⌋₊ = moebiusSum x := by
  simp [moebiusSum]

/-- `m` is constant on each interval `[N, N + 1)`: `m(x) = m(⌊x⌋₊)`. -/
@[simp high]
theorem moebiusDivSum_natFloor (x : ℝ) : moebiusDivSum ⌊x⌋₊ = moebiusDivSum x := by
  simp [moebiusDivSum]

/-- `M` jumps by `μ(N + 1)` at `N + 1`. -/
theorem moebiusSum_natCast_add_one (N : ℕ) :
    moebiusSum (N + 1) = moebiusSum N + μ (N + 1) := by
  rw [← Nat.cast_add_one, moebiusSum_natCast, moebiusSum_natCast,
    Finset.sum_Icc_succ_top (Nat.le_add_left 1 N)]

/-- `m` jumps by `μ(N + 1) / (N + 1)` at `N + 1`. -/
theorem moebiusDivSum_natCast_add_one (N : ℕ) :
    moebiusDivSum (N + 1) = moebiusDivSum N + μ (N + 1) / (N + 1) := by
  rw [← Nat.cast_add_one, moebiusDivSum_natCast, moebiusDivSum_natCast,
    Finset.sum_Icc_succ_top (Nat.le_add_left 1 N)]

/-- `M(1) = μ(1) = 1`. -/
@[simp]
theorem moebiusSum_one : moebiusSum 1 = 1 := by
  simpa using moebiusSum_natCast 1

/-- The trivial bound `|M(x)| ≤ x` for `x ≥ 0`, as `|μ(n)| ≤ 1`. -/
theorem abs_moebiusSum_le (hx : 0 ≤ x) : |moebiusSum x| ≤ x := by
  rw [moebiusSum_def]
  exact abs_sum_Icc_one_natFloor_le (fun _ ↦ mod_cast ArithmeticFunction.abs_moebius_le_one) hx

/-- `m(1) = μ(1) = 1`. -/
@[simp]
theorem moebiusDivSum_one : moebiusDivSum 1 = 1 := by
  simpa using moebiusDivSum_natCast 1

/-- `ℓ(1) = μ(1) log 1 = 0`. -/
@[simp]
theorem moebiusLogSum_one : moebiusLogSum 1 = 0 := by
  simp [moebiusLogSum]

/-! ### `ℓ` through `m` and `M`, and `m` through `M` -/

/-- `ℓ(x) = m(x) log x - ∑_{n ≤ x} μ(n) log n / n`. -/
theorem moebiusLogSum_eq_moebiusDivSum_mul_log_sub (x : ℝ) :
    moebiusLogSum x =
      moebiusDivSum x * Real.log x - ∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) * Real.log n / n := by
  rw [moebiusLogSum, moebiusDivSum, sum_mul, ← sum_sub_distrib]
  refine sum_congr rfl fun n hn ↦ ?_
  have hn1 : 1 ≤ n := (mem_Icc.mp hn).1
  have hx : (1 : ℝ) ≤ x := Nat.one_le_floor_iff x |>.mp (hn1.trans (mem_Icc.mp hn).2)
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  rw [Real.log_div (by positivity) hn0]
  ring

/-- Abel summation against `1 / t`: `m(x) = M(x) / x + ∫_1^x M(t) / t² dt` for every real `x`. -/
theorem moebiusDivSum_eq_div_add_integral (x : ℝ) :
    moebiusDivSum x = moebiusSum x / x + ∫ t in (1 : ℝ)..x, moebiusSum t / t ^ 2 := by
  have h := sum_Icc_rpow_mul_eq (fun n ↦ (μ n : ℝ)) (-1) x
  have hpow (t : ℝ) : t ^ ((-1 : ℝ) - 1) = (t ^ 2)⁻¹ := by
    rw [show (-1 : ℝ) - 1 = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast, zpow_neg,
      zpow_ofNat]
  simp only [Real.rpow_neg_one, hpow, neg_one_mul, sub_neg_eq_add, ← div_eq_inv_mul] at h
  simpa only [moebiusDivSum, moebiusSum] using h

/-- `ℓ(x) = ∫_1^x m(t) / t dt` for every real `x`: `ℓ` is the primitive of `m(t) / t`
vanishing at `1`. -/
theorem moebiusLogSum_eq_integral (x : ℝ) :
    moebiusLogSum x = ∫ t in (1 : ℝ)..x, moebiusDivSum t / t := by
  rcases lt_or_ge x 1 with hx | hx
  · rw [moebiusLogSum_of_lt_one hx, intervalIntegral.integral_eq_zero_of_forall_lt
      (fun t ht ↦ by rw [moebiusDivSum_of_lt_one ht, zero_div]) hx.le]
  have habel := sum_mul_eq_sub_integral_mul₀ (fun n ↦ (μ n : ℝ) / n) (f := Real.log)
    (by simp) x (fun t ht ↦ Real.differentiableAt_log (by linarith [ht.1]))
    (by
      rw [Real.deriv_log']
      exact (continuousOn_inv₀.mono fun t ht ↦ by
        exact ne_of_gt (by linarith [ht.1] : (0 : ℝ) < t)).integrableOn_Icc)
  simp only [sum_Icc_zero_eq_sum_Icc_one (f := fun k ↦ Real.log k * ((μ k : ℝ) / k)) (by simp),
    sum_Icc_zero_eq_sum_Icc_one (f := fun k ↦ (μ k : ℝ) / k) (by simp), Real.deriv_log'] at habel
  rw [moebiusLogSum_eq_moebiusDivSum_mul_log_sub, intervalIntegral.integral_of_le hx,
    moebiusDivSum]
  have hsum : ∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) * Real.log n / n =
      ∑ k ∈ Icc 1 ⌊x⌋₊, Real.log k * ((μ k : ℝ) / k) :=
    sum_congr rfl fun n _ ↦ by ring
  rw [hsum, habel, mul_comm, sub_sub_cancel]
  exact setIntegral_congr_fun measurableSet_Ioc fun t _ ↦ by rw [moebiusDivSum, div_eq_inv_mul]

/-- `M(t)`, weighted by a function locally integrable on `[1, ∞)`, is interval integrable between
any two reals. -/
theorem intervalIntegrable_moebiusSum_mul {f : ℝ → ℝ}
    (hf : LocallyIntegrableOn f (Set.Ici 1))
    (a b : ℝ) : IntervalIntegrable (fun t ↦ moebiusSum t * f t) volume a b := by
  simpa only [moebiusSum, mul_comm] using
    intervalIntegrable_mul_sum_Icc (fun n ↦ (μ n : ℝ)) hf a b

/-- Abel summation against `log (x / t) / t`:
`ℓ(x) = ∫_1^x M(t) log (x / t) / t² dt + ∫_1^x M(t) / t² dt` for every real `x`. -/
theorem moebiusLogSum_eq_integral_moebiusSum (x : ℝ) :
    moebiusLogSum x = (∫ t in (1 : ℝ)..x, moebiusSum t * Real.log (x / t) / t ^ 2) +
      ∫ t in (1 : ℝ)..x, moebiusSum t / t ^ 2 := by
  rcases lt_or_ge x 1 with hx | hx
  · rw [moebiusLogSum_of_lt_one hx, intervalIntegral.integral_eq_zero_of_forall_lt _ hx.le,
      intervalIntegral.integral_eq_zero_of_forall_lt _ hx.le, add_zero] <;>
      exact fun t ht ↦ by rw [moebiusSum_of_lt_one ht]; ring
  have hx0 : 0 < x := by linarith
  -- the weight `log (x / t) / t`, written so that it is differentiable on `(0, ∞)`
  have hderiv (t : ℝ) (ht : 0 < t) :
      HasDerivAt (fun u ↦ (Real.log x - Real.log u) / u) (-(1 + Real.log (x / t)) / t ^ 2) t := by
    refine (((hasDerivAt_const t (Real.log x)).sub (Real.hasDerivAt_log ht.ne')).div
      (hasDerivAt_id t) ht.ne').congr_deriv ?_
    rw [Pi.sub_apply, id, Real.log_div hx0.ne' ht.ne']
    field_simp
    ring
  have hc₁ : ContinuousOn (fun t : ℝ ↦ (t ^ 2)⁻¹) (Set.Ici 1) :=
    (continuousOn_pow 2).inv₀ fun t ht ↦ by have : (1 : ℝ) ≤ t := ht; positivity
  have hc₂ : ContinuousOn (fun t : ℝ ↦ Real.log (x / t) / t ^ 2) (Set.Ici 1) := by
    refine ContinuousOn.div ?_ (continuousOn_pow 2) fun t ht ↦ ?_
    · refine (continuousOn_const.div (continuousOn_id' _) fun t ht ↦ ?_).log fun t ht ↦ ?_
      · have : (1 : ℝ) ≤ t := ht; positivity
      · have : (1 : ℝ) ≤ t := ht; exact (div_pos hx0 (by linarith)).ne'
    · have : (1 : ℝ) ≤ t := ht; positivity
  have habel := sum_mul_eq_sub_integral_mul₀ (fun n ↦ (μ n : ℝ))
    (f := fun u ↦ (Real.log x - Real.log u) / u) (by simp) x
    (fun t ht ↦ (hderiv t (by linarith [ht.1])).differentiableAt)
    (by
      refine ((hc₁.neg.sub hc₂).mono Set.Icc_subset_Ici_self).integrableOn_Icc.congr_fun
        (fun t ht ↦ ?_) measurableSet_Icc
      rw [(hderiv t (by linarith [ht.1])).deriv, Pi.sub_apply, Pi.neg_apply]
      ring)
  simp only [sum_Icc_zero_eq_sum_Icc_one
      (f := fun k ↦ (Real.log x - Real.log k) / k * (μ k : ℝ)) (by simp),
    sum_Icc_zero_eq_sum_Icc_one (f := fun k ↦ (μ k : ℝ)) (by simp), sub_self, zero_div,
    zero_mul, zero_sub] at habel
  rw [← intervalIntegral.integral_add
    (by simpa only [mul_div_assoc] using intervalIntegrable_moebiusSum_mul
          (hc₂.locallyIntegrableOn measurableSet_Ici) 1 x)
    (by simpa only [div_eq_mul_inv] using intervalIntegrable_moebiusSum_mul
          (hc₁.locallyIntegrableOn measurableSet_Ici) 1 x),
    intervalIntegral.integral_of_le hx]
  have hsum : moebiusLogSum x =
      ∑ k ∈ Icc 1 ⌊x⌋₊, (Real.log x - Real.log k) / k * (μ k : ℝ) := by
    refine sum_congr rfl fun n hn ↦ ?_
    have hn0 : (n : ℝ) ≠ 0 := by have := (mem_Icc.mp hn).1; positivity
    rw [Real.log_div hx0.ne' hn0]
    ring
  rw [hsum, habel, ← integral_neg]
  refine setIntegral_congr_fun measurableSet_Ioc fun t ht ↦ ?_
  rw [(hderiv t (by linarith [ht.1])).deriv, moebiusSum]
  ring

/-! ### Regularity of `ℓ` -/

/-- `ℓ` is continuous on all of `ℝ`: it is the primitive of the locally integrable `m(t) / t`. -/
theorem continuous_moebiusLogSum : Continuous moebiusLogSum := by
  have hc : ContinuousOn (fun t : ℝ ↦ t⁻¹) (Set.Ici 1) :=
    continuousOn_inv₀.mono fun t ht ↦ ne_of_gt (zero_lt_one.trans_le ht)
  have hfun : (fun t ↦ moebiusDivSum t / t) =
      fun t ↦ t⁻¹ * ∑ n ∈ Icc 1 ⌊t⌋₊, (μ n : ℝ) / n :=
    funext fun t ↦ by rw [moebiusDivSum, div_eq_inv_mul]
  rw [funext moebiusLogSum_eq_integral, hfun]
  exact intervalIntegral.continuous_primitive
    (intervalIntegrable_mul_sum_Icc (fun n ↦ (μ n : ℝ) / n)
      (hc.locallyIntegrableOn measurableSet_Ici)) 1

/-- Off the natural numbers, `ℓ` is differentiable with derivative `m(x) / x`. -/
theorem hasDerivAt_moebiusLogSum (hx : ∀ n : ℕ, x ≠ n) :
    HasDerivAt moebiusLogSum (moebiusDivSum x / x) x := by
  have hx0 : x ≠ 0 := by simpa using hx 0
  have heq : (fun y ↦ moebiusDivSum x * Real.log y -
      ∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) * Real.log n / n) =ᶠ[𝓝 x] moebiusLogSum := by
    filter_upwards [eventually_natFloor_eq hx] with y hy
    rw [moebiusLogSum_eq_moebiusDivSum_mul_log_sub, ← moebiusDivSum_natFloor y, hy,
      moebiusDivSum_natFloor]
  rw [div_eq_mul_inv]
  exact (((Real.hasDerivAt_log hx0).const_mul _).sub_const _).congr_of_eventuallyEq heq.symm

/-! ### Meissel's identity -/

/-- Meissel's identity `∑_{n ≤ x} μ(n) ⌊x / n⌋ = 1` for every real `x ≥ 1`, the summed form of
`μ * ζ = 1`. -/
theorem sum_moebius_mul_natFloor_div (hx : 1 ≤ x) :
    ∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) * ⌊x / n⌋₊ = 1 := by
  have h := ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum (μ : ArithmeticFunction ℝ) ⌊x⌋₊
  rw [ArithmeticFunction.coe_moebius_mul_coe_zeta, ← Icc_add_one_left_eq_Ioc, zero_add] at h
  simp only [Nat.floor_div_natCast, ← ArithmeticFunction.intCoe_apply, ← h]
  rw [sum_eq_single_of_mem 1 (mem_Icc.mpr ⟨le_rfl, Nat.one_le_floor_iff x |>.mpr hx⟩)
    fun n _ hn ↦ ArithmeticFunction.one_apply_ne hn, ArithmeticFunction.one_one]

end TauCeti
