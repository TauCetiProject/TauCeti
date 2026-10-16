/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Discrete Grönwall estimates for implicit time stepping

A discrete Grönwall argument shows that a quantity growing at most by the factor `1 + aτ` per
time step of length `τ` grows at most like `exp (a t)` up to time `t`. This file records the
growth factor estimate `(1 + aτ) ^ ⌈t / τ⌉₊ ≤ exp (a (t + τ))`, valid uniformly in the time
step (`TauCeti.one_add_mul_pow_ceil_div_le_exp`), and a discrete Grönwall bound for sequences
that move in steps paid for by an energy which is bounded below in terms of the distance
travelled (`TauCeti.sq_le_mul_one_add_div_pow_of_sq_le_mul_sub`).

The second estimate is the shape of the a priori bound for implicit Euler schemes of gradient
flows whose energy is not bounded below. A sequence `D n ≥ 0` with `D 0 = 0` grows by steps
`D (n + 1) ≤ D n + d n` whose squared lengths are bounded by the energy dissipated,
`d n ² ≤ 2τ (e n - e (n + 1))`, and the energy obeys the coercivity bound
`2τ' (A - e n) ≤ D n ²`. Then `D n ² ≤ 2τ' (e 0 - A) (1 + 8τ / τ')ⁿ` whenever `4τ ≤ τ'`.

## Main declarations

* `TauCeti.one_add_mul_pow_ceil_div_le_exp`: `(1 + aτ) ^ ⌈t / τ⌉₊ ≤ exp (a (t + τ))`.
* `TauCeti.sq_le_mul_one_add_div_pow_of_sq_le_mul_sub`: the discrete Grönwall bound
  `D n ² ≤ 2τ' (e 0 - A) (1 + 8τ / τ')ⁿ` under coercivity.

## References

* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd ed., Birkhäuser 2008, Chapter 3, Section 3.2.
-/

public section

namespace TauCeti

/-- After `⌈t / τ⌉₊` time steps of length `τ`, a growth factor `1 + aτ` per step accumulates to at
most `exp (a (t + τ))`, since less than `t + τ` time has passed. The bound is uniform in the time
step `τ`. -/
theorem one_add_mul_pow_ceil_div_le_exp {a τ t : ℝ} (ha : 0 ≤ a) (hτ : 0 < τ) (ht : 0 ≤ t) :
    (1 + a * τ) ^ ⌈t / τ⌉₊ ≤ Real.exp (a * (t + τ)) := by
  have h1 : (⌈t / τ⌉₊ : ℝ) * τ ≤ t + τ := by
    have := mul_lt_mul_of_pos_right (Nat.ceil_lt_add_one (div_nonneg ht hτ.le)) hτ
    rw [add_mul, div_mul_cancel₀ _ hτ.ne', one_mul] at this
    exact this.le
  calc (1 + a * τ) ^ ⌈t / τ⌉₊ ≤ Real.exp (a * τ) ^ ⌈t / τ⌉₊ :=
        pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (a * τ)]) _
    _ = Real.exp (⌈t / τ⌉₊ * (a * τ)) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (a * (t + τ)) := by
        rw [Real.exp_le_exp, show (⌈t / τ⌉₊ : ℝ) * (a * τ) = a * (⌈t / τ⌉₊ * τ) by ring]
        gcongr

/-- **Discrete Grönwall bound under coercivity.** Let `D n ≥ 0` with `D 0 = 0` grow by steps
`D (n + 1) ≤ D n + d n` whose squared lengths are paid for by an energy `e`,
`d n ² ≤ 2τ (e n - e (n + 1))`, and let the energy satisfy the coercivity bound
`2τ' (A - e n) ≤ D n ²`, where `4τ ≤ τ'`. Then `D n ² ≤ 2τ' (e 0 - A) (1 + 8τ / τ')ⁿ`.

With `c = τ + τ' / 4`, the quantity `N n = D n ² + 2c (e n - A)` dominates `D n ² / 2` by the
coercivity bound, and grows at most by the factor `1 + 8τ / τ'` per step by the triangle
inequality, Young's inequality and the energy decrease along a step. -/
theorem sq_le_mul_one_add_div_pow_of_sq_le_mul_sub {D d e : ℕ → ℝ} {τ τ' A : ℝ} (hτ : 0 < τ)
    (hττ' : 4 * τ ≤ τ') (hD0 : D 0 = 0) (hD : ∀ n, 0 ≤ D n) (htri : ∀ n, D (n + 1) ≤ D n + d n)
    (hstep : ∀ n, d n ^ 2 ≤ 2 * τ * (e n - e (n + 1)))
    (hcoer : ∀ n, 2 * τ' * (A - e n) ≤ D n ^ 2) (n : ℕ) :
    D n ^ 2 ≤ 2 * τ' * (e 0 - A) * (1 + 8 * τ / τ') ^ n := by
  have hτ' : 0 < τ' := by linarith
  set c := τ + τ' / 4 with hc
  set N : ℕ → ℝ := fun n ↦ D n ^ 2 + 2 * c * (e n - A) with hN
  -- `N` dominates `D ² / 2`.
  have hQ n : D n ^ 2 ≤ 2 * N n := by
    have h1 := mul_le_mul_of_nonneg_left (hcoer n) (by positivity : (0 : ℝ) ≤ 2 * c)
    have h2 : 0 ≤ τ' * (D n ^ 2 + 4 * c * (e n - A)) := by
      nlinarith [mul_nonneg (sq_nonneg (D n)) (by linarith : (0 : ℝ) ≤ τ' - 2 * c)]
    have h3 := (mul_nonneg_iff_of_pos_left hτ').1 h2
    simp only [hN]
    linarith
  -- One step multiplies `N` by at most `1 + 8τ / τ'`.
  have hNstep n : N (n + 1) ≤ (1 + 8 * τ / τ') * N n := by
    have h1 : D (n + 1) ^ 2 ≤ (D n + d n) ^ 2 := pow_le_pow_left₀ (hD _) (htri n) 2
    have hY : (D n + d n) ^ 2 ≤ (1 + 4 * τ / τ') * D n ^ 2 + c / τ * d n ^ 2 := by
      rw [hc]
      field_simp
      nlinarith [sq_nonneg (4 * τ * D n - τ' * d n)]
    have hd' : c / τ * d n ^ 2 ≤ 2 * c * (e n - e (n + 1)) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hτ]
      nlinarith [hstep n, (by positivity : (0 : ℝ) ≤ c)]
    have hQ' : 4 * τ / τ' * D n ^ 2 ≤ 8 * τ / τ' * N n := by
      have := mul_le_mul_of_nonneg_left (hQ n) (by positivity : (0 : ℝ) ≤ 4 * τ / τ')
      linarith [show 4 * τ / τ' * (2 * N n) = 8 * τ / τ' * N n by ring]
    simp only [hN] at hQ' ⊢
    nlinarith
  -- Iterating from `N 0 = 2c (e 0 - A) ≤ τ' (e 0 - A)`.
  have hA0 : A ≤ e 0 := by nlinarith [hcoer 0, hD0]
  have hNn : N n ≤ (1 + 8 * τ / τ') ^ n * (τ' * (e 0 - A)) := by
    induction n with
    | zero =>
      simp only [hN, hD0, pow_zero, one_mul]
      nlinarith
    | succ n ih =>
      calc N (n + 1) ≤ (1 + 8 * τ / τ') * N n := hNstep n
        _ ≤ (1 + 8 * τ / τ') * ((1 + 8 * τ / τ') ^ n * (τ' * (e 0 - A))) :=
          mul_le_mul_of_nonneg_left ih (by positivity)
        _ = _ := by ring
  nlinarith [hQ n]

end TauCeti
