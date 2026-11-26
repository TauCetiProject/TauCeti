/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Mul
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Topology.Algebra.Order.Floor

/-!
# Lipschitz bounds for first Riesz sums

For coefficients `c : ℕ → ℂ` the first Riesz sum `S(y) = TauCeti.rieszSum c y` is the sum of the
ramps `c(n) max (y / n - 1) 0` (`TauCeti.rieszSum_eq_sum_max_of_floor_le`). Hence:
* on every half-line `(-∞, Y]`, `S` is Lipschitz with constant `∑_{n ≤ Y} ‖c(n)‖ / n`;
* for `W > 0`, the weighted form `w ↦ w · S(a / w) = ∑_n c(n) max (a / n - w) 0` is Lipschitz on
  `[W, ∞)` with constant `∑_{n ≤ a / W} ‖c(n)‖`, and its real part is antitone in `w > 0` when
  the coefficients have nonnegative real parts;
* the unweighted sum `S` has right derivative `∑_{n ≤ y} c(n) / n` at every `y`.

The real sums `∑ n ∈ Ioc 0 ⌊y⌋₊, c n * (y / n - 1)` with `c : ℕ → ℝ`, on the index set of
Mathlib's `Chebyshev.psi`, are the real forms of `TauCeti.rieszSum`
(`TauCeti.ofReal_sum_Ioc_floor_mul_div_sub_one`); for them the file also gives the antitonicity in
the weight and the right derivative.

## Main results

* `TauCeti.mul_rieszSum_div_eq_sum_max`: the weighted Riesz sum as a sum of ramps in the weight.
* `TauCeti.norm_rieszSum_sub_rieszSum_le`: Lipschitz bound in `y`.
* `TauCeti.norm_mul_rieszSum_div_sub_mul_rieszSum_div_le`: Lipschitz bound in the weight.
* `TauCeti.hasDerivWithinAt_rieszSum`: the right derivative of `TauCeti.rieszSum c`.
* `TauCeti.mul_sum_Ioc_floor_mul_div_sub_one_le`: antitonicity of the real weighted sum in the
  weight.
* `TauCeti.hasDerivWithinAt_sum_Ioc_floor_mul_div_sub_one`: the right derivative of the real sum.

## References

* These bounds feed the Riesz-remainder bounds of `TauCeti.NumberTheory.Chebyshev.RieszRemainder`,
  whose Riesz remainder and absolute-constant form are those of the formal proof of the Riemann
  hypothesis for Dirichlet `L`-functions, https://github.com/leanprover-community/riemann-hypothesis.
-/

public section

open Finset

namespace TauCeti

/-- **The weighted Riesz sum as a sum of ramps in the weight.** For `w > 0` and every
`N ≥ ⌊a / w⌋₊`, `w · rieszSum c (a / w) = ∑_{1 ≤ n ≤ N} c(n) max (a / n - w) 0`. -/
theorem mul_rieszSum_div_eq_sum_max (c : ℕ → ℂ) {a w : ℝ} (hw : 0 < w) {N : ℕ}
    (hN : ⌊a / w⌋₊ ≤ N) :
    (w : ℂ) * rieszSum c (a / w) = ∑ n ∈ Icc 1 N, c n * ((max (a / n - w) 0 : ℝ) : ℂ) := by
  rw [rieszSum_eq_sum_max_of_floor_le c hN, mul_sum]
  refine sum_congr rfl fun n hn ↦ ?_
  have hn : (n : ℝ) ≠ 0 := by
    have := (mem_Icc.1 hn).1
    positivity
  have h : w * (a / w / n - 1) = a / n - w := by field_simp
  rw [mul_left_comm, ← Complex.ofReal_mul, mul_max_of_nonneg _ _ hw.le, mul_zero, h]

/-- The ramp form of `w' · rieszSum c (a / w')` over the cutoff of a smaller weight `w ≤ w'`. -/
private theorem mul_rieszSum_div_eq_sum_max_of_le (c : ℕ → ℂ) {a w w' : ℝ} (hw : 0 < w)
    (hww' : w ≤ w') :
    (w' : ℂ) * rieszSum c (a / w') =
      ∑ n ∈ Icc 1 ⌊a / w⌋₊, c n * ((max (a / n - w') 0 : ℝ) : ℂ) := by
  refine mul_rieszSum_div_eq_sum_max c (hw.trans_le hww') ?_
  rcases le_total a 0 with ha | ha
  · simp [Nat.floor_of_nonpos (div_nonpos_of_nonpos_of_nonneg ha (hw.trans_le hww').le)]
  · exact Nat.floor_le_floor (div_le_div_of_nonneg_left ha hw hww')

/-- **Lipschitz bound for a Riesz sum.** For `z ≤ y`,
`‖S(y) - S(z)‖ ≤ (∑_{1 ≤ n ≤ y} ‖c(n)‖ / n) (y - z)`, where `S = TauCeti.rieszSum c`. -/
theorem norm_rieszSum_sub_rieszSum_le (c : ℕ → ℂ) {y z : ℝ} (hzy : z ≤ y) :
    ‖rieszSum c y - rieszSum c z‖ ≤ (∑ n ∈ Icc 1 ⌊y⌋₊, ‖c n‖ / n) * (y - z) := by
  rw [rieszSum_eq_sum_max_of_floor_le c le_rfl,
    rieszSum_eq_sum_max_of_floor_le c (Nat.floor_le_floor hzy), ← sum_sub_distrib, sum_mul]
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
  rw [mul_rieszSum_div_eq_sum_max c hw le_rfl, mul_rieszSum_div_eq_sum_max_of_le c hw hww',
    ← sum_sub_distrib, sum_mul]
  refine (norm_sum_le _ _).trans (sum_le_sum fun n _ ↦ ?_)
  simp only [← mul_sub, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  gcongr
  calc _ ≤ |(a / n - w) - (a / n - w')| := abs_max_sub_max_le_abs _ _ _
    _ = w' - w := by rw [sub_sub_sub_cancel_left, abs_of_nonneg (sub_nonneg.2 hww')]

/-- **Right derivative of the Riesz sum.** `TauCeti.rieszSum c` has right derivative
`∑_{1 ≤ n ≤ x} c(n) / n` at every `x`. -/
theorem hasDerivWithinAt_rieszSum (c : ℕ → ℂ) (x : ℝ) :
    HasDerivWithinAt (rieszSum c) (∑ n ∈ Icc 1 ⌊x⌋₊, c n / n) (Set.Ici x) x := by
  have hlin : HasDerivAt (fun t : ℝ ↦ ∑ n ∈ Icc 1 ⌊x⌋₊, c n * ((t : ℂ) / n - 1))
      (∑ n ∈ Icc 1 ⌊x⌋₊, c n * (((1 : ℝ) : ℂ) / n)) x :=
    HasDerivAt.fun_sum fun n _ ↦
      ((HasDerivAt.div_const (hasDerivAt_id' x).ofReal_comp (n : ℂ)).sub_const 1).const_mul (c n)
  simp only [Complex.ofReal_one, mul_one_div] at hlin
  refine hlin.hasDerivWithinAt.congr_of_eventuallyEq ?_ (rieszSum_def c x)
  filter_upwards [Filter.tendsto_pure.mp (tendsto_floor_right_pure_floor x)] with t ht
  have h : ⌊t⌋₊ = ⌊x⌋₊ := by rw [← Int.floor_toNat, ← Int.floor_toNat, ht]
  rw [rieszSum_def, h]

/-! ### Real coefficients -/

/-- **The weighted real Riesz sum is antitone in the weight** for nonnegative coefficients: for
`0 < w ≤ w'`, `w' S(a / w') ≤ w S(a / w)`, where `S(y) = ∑_{1 ≤ n ≤ y} c(n) (y / n - 1)`. -/
theorem mul_sum_Ioc_floor_mul_div_sub_one_le {c : ℕ → ℝ} (hc : ∀ n, 0 ≤ c n) {a w w' : ℝ}
    (hw : 0 < w) (hww' : w ≤ w') :
    w' * ∑ n ∈ Ioc 0 ⌊a / w'⌋₊, c n * (a / w' / n - 1) ≤
      w * ∑ n ∈ Ioc 0 ⌊a / w⌋₊, c n * (a / w / n - 1) := by
  have key {v : ℝ} (hv : w ≤ v) : v * ∑ n ∈ Ioc 0 ⌊a / v⌋₊, c n * (a / v / n - 1) =
      ∑ n ∈ Icc 1 ⌊a / w⌋₊, c n * max (a / n - v) 0 := by
    have h := mul_rieszSum_div_eq_sum_max_of_le (fun n ↦ (c n : ℂ)) (a := a) hw hv
    rw [← ofReal_sum_Ioc_floor_mul_div_sub_one] at h
    exact_mod_cast h
  rw [key hww', key le_rfl]
  exact sum_le_sum fun n _ ↦ mul_le_mul_of_nonneg_left (by gcongr) (hc n)

/-- **Right derivative of the real Riesz sum.** `y ↦ ∑_{1 ≤ n ≤ y} c(n) (y / n - 1)` has right
derivative `∑_{1 ≤ n ≤ x} c(n) / n` at every `x`; it is the real part of
`TauCeti.hasDerivWithinAt_rieszSum`. -/
theorem hasDerivWithinAt_sum_Ioc_floor_mul_div_sub_one (c : ℕ → ℝ) (x : ℝ) :
    HasDerivWithinAt (fun t ↦ ∑ n ∈ Ioc 0 ⌊t⌋₊, c n * (t / n - 1))
      (∑ n ∈ Ioc 0 ⌊x⌋₊, c n / n) (Set.Ici x) x := by
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt x
    (hasDerivWithinAt_rieszSum (fun n ↦ (c n : ℂ)) x)
  have hf : (Complex.reCLM ∘ rieszSum fun n ↦ (c n : ℂ)) =
      fun t ↦ ∑ n ∈ Ioc 0 ⌊t⌋₊, c n * (t / n - 1) := by
    ext t
    rw [Function.comp_apply, Complex.reCLM_apply, ← ofReal_sum_Ioc_floor_mul_div_sub_one,
      Complex.ofReal_re]
  rw [hf] at h
  refine h.congr_deriv ?_
  simp [← Icc_add_one_left_eq_Ioc]

end TauCeti
