/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Mul
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.Basic
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Lipschitz bounds for first Riesz sums

For coefficients `c : ℕ → ℂ` the first Riesz sum `S(y) = TauCeti.rieszSum c y` is the sum of the
ramps `c(n) max (y / n - 1) 0` (`TauCeti.rieszSum_eq_sum_max`), so it is Lipschitz in `y` with
constant `∑_{n ≤ y} ‖c(n)‖ / n`. Its weighted form `w · S(a / w) = ∑_n c(n) max (a / n - w) 0` is
Lipschitz in the weight `w` with constant `∑_{n ≤ a / w} ‖c(n)‖`.

For real coefficients the sum `∑ n ∈ Ioc 0 ⌊y⌋₊, c n * (y / n - 1)`, on the index set of
Mathlib's `Chebyshev.psi`, is the real form of `TauCeti.rieszSum`
(`TauCeti.ofReal_sum_Ioc_floor_mul_div_sub_one`). Its weighted form is antitone in the weight when
the coefficients are nonnegative, it is continuous, and it has right derivative
`∑_{n ≤ y} c(n) / n`.

## Main results

* `TauCeti.mul_rieszSum_div_eq_sum_max`: the weighted Riesz sum as a sum of ramps in the weight.
* `TauCeti.norm_rieszSum_sub_rieszSum_le`: Lipschitz bound in `y`.
* `TauCeti.norm_mul_rieszSum_div_sub_mul_rieszSum_div_le`: Lipschitz bound in the weight.
* `TauCeti.ofReal_sum_Ioc_floor_mul_div_sub_one`: the real form of the Riesz sum.
* `TauCeti.mul_sum_Ioc_floor_div_le_mul_sum`: antitonicity in the weight.
* `TauCeti.continuous_sum_Ioc_floor_mul_div_sub_one`,
  `TauCeti.hasDerivWithinAt_sum_Ioc_floor_mul_div_sub_one`: continuity and the right derivative of
  the real form.

## References

* The ramp decomposition and the Lipschitz bounds in the weight are the ingredients of the bounds
  for the Riesz remainder in the formal proof of the Riemann hypothesis for Dirichlet
  `L`-functions, https://github.com/leanprover-community/riemann-hypothesis.
-/

public section

open Finset

namespace TauCeti

/-- The weighted Riesz sum `w' · S(a / w')`, `S = TauCeti.rieszSum c`, as a sum of ramps in the
weight: for `0 < w ≤ w'` it equals `∑_{1 ≤ n ≤ a / w} c(n) max (a / n - w') 0`. -/
theorem mul_rieszSum_div_eq_sum_max (c : ℕ → ℂ) {a w w' : ℝ} (hw : 0 < w) (hww' : w ≤ w') :
    (w' : ℂ) * rieszSum c (a / w') =
      ∑ n ∈ Icc 1 ⌊a / w⌋₊, c n * ((max (a / n - w') 0 : ℝ) : ℂ) := by
  have hw' := hw.trans_le hww'
  have hN : ⌊a / w'⌋₊ ≤ ⌊a / w⌋₊ := by
    rcases le_total a 0 with ha | ha
    · simp [Nat.floor_of_nonpos (div_nonpos_of_nonpos_of_nonneg ha hw'.le)]
    · exact Nat.floor_le_floor (div_le_div_of_nonneg_left ha hw hww')
  rw [rieszSum_eq_sum_max c hN, mul_sum]
  refine sum_congr rfl fun n hn ↦ ?_
  have hn : (n : ℝ) ≠ 0 := by
    have := (mem_Icc.1 hn).1
    positivity
  have h : w' * (a / w' / n - 1) = a / n - w' := by field_simp
  rw [mul_left_comm, ← Complex.ofReal_mul, mul_max_of_nonneg _ _ hw'.le, mul_zero, h]

/-- **Lipschitz bound for a Riesz sum.** For `z ≤ y`,
`‖S(y) - S(z)‖ ≤ (∑_{1 ≤ n ≤ y} ‖c(n)‖ / n) (y - z)`, where `S = TauCeti.rieszSum c`. -/
theorem norm_rieszSum_sub_rieszSum_le (c : ℕ → ℂ) {y z : ℝ} (hzy : z ≤ y) :
    ‖rieszSum c y - rieszSum c z‖ ≤ (∑ n ∈ Icc 1 ⌊y⌋₊, ‖c n‖ / n) * (y - z) := by
  rw [rieszSum_eq_sum_max c le_rfl, rieszSum_eq_sum_max c (Nat.floor_le_floor hzy),
    ← sum_sub_distrib, sum_mul]
  refine (norm_sum_le _ _).trans (sum_le_sum fun n _ ↦ ?_)
  simp only [← mul_sub, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have h : |max (y / n - 1) 0 - max (z / n - 1) 0| ≤ (y - z) / n :=
    (abs_max_sub_max_le_abs _ _ _).trans_eq (by
      rw [sub_sub_sub_cancel_right, ← sub_div,
        abs_of_nonneg (div_nonneg (sub_nonneg.2 hzy) n.cast_nonneg)])
  calc _ ≤ ‖c n‖ * ((y - z) / n) := by gcongr
    _ = ‖c n‖ / n * (y - z) := by ring

/-- **Lipschitz bound for a weighted Riesz sum in the weight.** For `0 < w ≤ w'`,
`‖w S(a / w) - w' S(a / w')‖ ≤ (∑_{1 ≤ n ≤ a / w} ‖c(n)‖) (w' - w)`, where
`S = TauCeti.rieszSum c`. -/
theorem norm_mul_rieszSum_div_sub_mul_rieszSum_div_le (c : ℕ → ℂ) {a w w' : ℝ} (hw : 0 < w)
    (hww' : w ≤ w') :
    ‖(w : ℂ) * rieszSum c (a / w) - (w' : ℂ) * rieszSum c (a / w')‖ ≤
      (∑ n ∈ Icc 1 ⌊a / w⌋₊, ‖c n‖) * (w' - w) := by
  rw [mul_rieszSum_div_eq_sum_max c hw le_rfl, mul_rieszSum_div_eq_sum_max c hw hww',
    ← sum_sub_distrib, sum_mul]
  refine (norm_sum_le _ _).trans (sum_le_sum fun n _ ↦ ?_)
  rw [← mul_sub, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  gcongr
  calc _ ≤ |(a / n - w) - (a / n - w')| := abs_max_sub_max_le_abs _ _ _
    _ = w' - w := by rw [sub_sub_sub_cancel_left, abs_of_nonneg (sub_nonneg.2 hww')]

/-! ### Real coefficients -/

/-- **The real form of the Riesz sum.** For real coefficients, the sum
`∑_{1 ≤ n ≤ y} c(n) (y / n - 1)` over Mathlib's index set `Ioc 0 ⌊y⌋₊` is
`TauCeti.rieszSum` of the coefficients cast to `ℂ`. -/
theorem ofReal_sum_Ioc_floor_mul_div_sub_one (c : ℕ → ℝ) (y : ℝ) :
    ((∑ n ∈ Ioc 0 ⌊y⌋₊, c n * (y / n - 1) : ℝ) : ℂ) = rieszSum (fun n ↦ (c n : ℂ)) y := by
  rw [rieszSum_def, ← Icc_succ_left_eq_Ioc]
  push_cast
  rfl

/-- **The weighted Riesz sum is antitone in the weight** for nonnegative coefficients: for
`0 < w ≤ w'`, `w' S(a / w') ≤ w S(a / w)`, where `S(y) = ∑_{1 ≤ n ≤ y} c(n) (y / n - 1)`. -/
theorem mul_sum_Ioc_floor_div_le_mul_sum {c : ℕ → ℝ} (hc : ∀ n, 0 ≤ c n) {a w w' : ℝ} (hw : 0 < w)
    (hww' : w ≤ w') :
    w' * ∑ n ∈ Ioc 0 ⌊a / w'⌋₊, c n * (a / w' / n - 1) ≤
      w * ∑ n ∈ Ioc 0 ⌊a / w⌋₊, c n * (a / w / n - 1) := by
  have key {v : ℝ} (hv : w ≤ v) : v * ∑ n ∈ Ioc 0 ⌊a / v⌋₊, c n * (a / v / n - 1) =
      ∑ n ∈ Icc 1 ⌊a / w⌋₊, c n * max (a / n - v) 0 := by
    have h := mul_rieszSum_div_eq_sum_max (fun n ↦ (c n : ℂ)) (a := a) hw hv
    rw [← ofReal_sum_Ioc_floor_mul_div_sub_one] at h
    exact_mod_cast h
  rw [key hww', key le_rfl]
  exact sum_le_sum fun n _ ↦ mul_le_mul_of_nonneg_left (by gcongr) (hc n)

/-- **The Riesz sum is continuous**: `y ↦ ∑_{1 ≤ n ≤ y} c(n) (y / n - 1)` is continuous on `ℝ`. It
is the real part of `TauCeti.rieszSum`, continuous by `TauCeti.continuous_rieszSum`. -/
theorem continuous_sum_Ioc_floor_mul_div_sub_one (c : ℕ → ℝ) :
    Continuous fun t : ℝ ↦ ∑ n ∈ Ioc 0 ⌊t⌋₊, c n * (t / n - 1) := by
  refine (Complex.continuous_re.comp (continuous_rieszSum fun n ↦ (c n : ℂ))).congr fun t ↦ ?_
  rw [Function.comp_apply, ← ofReal_sum_Ioc_floor_mul_div_sub_one, Complex.ofReal_re]

/-- **Right derivative of the Riesz sum.** `y ↦ ∑_{1 ≤ n ≤ y} c(n) (y / n - 1)` has right
derivative `∑_{1 ≤ n ≤ x} c(n) / n` at every `x`. -/
theorem hasDerivWithinAt_sum_Ioc_floor_mul_div_sub_one (c : ℕ → ℝ) (x : ℝ) :
    HasDerivWithinAt (fun t ↦ ∑ n ∈ Ioc 0 ⌊t⌋₊, c n * (t / n - 1))
      (∑ n ∈ Ioc 0 ⌊x⌋₊, c n * (1 / n)) (Set.Ici x) x := by
  have hlin : HasDerivAt (fun t ↦ ∑ n ∈ Ioc 0 ⌊x⌋₊, c n * (t / n - 1))
      (∑ n ∈ Ioc 0 ⌊x⌋₊, c n * (1 / n)) x :=
    HasDerivAt.fun_sum fun n _ ↦ (((hasDerivAt_id' x).div_const (n : ℝ)).sub_const 1).const_mul
      (c n)
  refine hlin.hasDerivWithinAt.congr_of_eventuallyEq ?_ rfl
  filter_upwards [Ico_mem_nhdsGE (Nat.lt_floor_add_one x)] with t ht
  have hlt : ⌊t⌋₊ < ⌊x⌋₊ + 1 :=
    (Nat.floor_lt' (Nat.succ_ne_zero _)).2 (by exact_mod_cast ht.2)
  rw [le_antisymm (Nat.lt_succ_iff.1 hlt) (Nat.floor_le_floor ht.1)]

end TauCeti
