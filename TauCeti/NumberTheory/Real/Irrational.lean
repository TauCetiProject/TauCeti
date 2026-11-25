/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.LinearCombination

/-!
# Irrationality of squares of real fourth roots and of integer combinations

For a nonnegative real number `x`, the square of the fourth root `x ^ (1 / 4 : ℝ)` is `√x`, so
`(x ^ (1 / 4 : ℝ)) ^ 2` is irrational if and only if `√x` is irrational
(`TauCeti.irrational_rpow_one_quarter_sq_iff`). In particular, for any prime `p` — and specifically
for `p = 2` (`TauCeti.irrational_two_rpow_one_quarter_sq`) — the square of `(p : ℝ) ^ (1 / 4 : ℝ)`
is irrational. This supplies the irrational-square condition `Irrational (c ^ 2)` for rank-one
non-integral lattices `c ℤ ⊆ ℝ` such as `2 ^ (1 / 4) ℤ`.

The ratio `(√3 - 1) / (√2 - 1)` is irrational
(`TauCeti.irrational_sqrt_three_sub_one_div_sqrt_two_sub_one`).

For an irrational real number `θ`, the only integer solution of `a + b * θ = 0` has
`a = b = 0` (`Irrational.intCast_add_mul_eq_zero_iff`), and for nonzero `c` the multiple `c * θ`
is not an integer multiple of `c` (`Irrational.intCast_mul_ne_mul`).

If `θ₁` or `θ₂` is irrational, an integer matrix of nonzero determinant cannot send `(θ₁, θ₂)`
into `ℚ²`: for `j ≠ 0` and `a d - b c ≠ 0`, `j (a θ₁ + b θ₂)` and `j (c θ₁ + d θ₂)` are not both
integers (`TauCeti.notMem_range_intCast_or_notMem_range_intCast_of_irrational`). These are the
twists of the powers and finite-cover pullbacks of a flat line over a torus with holonomy
`exp (2πiθ₁)`, `exp (2πiθ₂)`.

## Main statements

* `Irrational.intCast_add_mul_eq_zero_iff`: an integer relation between one and an irrational
  real number has both coefficients zero.
* `Irrational.intCast_mul_ne_mul`: for irrational `a` and nonzero `c`, `k * c ≠ c * a` for every
  integer `k`.
* `TauCeti.irrational_rpow_one_quarter_sq_iff`: for `0 ≤ x`,
  `Irrational ((x ^ (1 / 4 : ℝ)) ^ 2) ↔ Irrational √x`.
* `Nat.Prime.irrational_rpow_one_quarter_sq`: for prime `p`,
  `Irrational (((p : ℝ) ^ (1 / 4 : ℝ)) ^ 2)`.
* `TauCeti.irrational_two_rpow_one_quarter_sq`: `Irrational (((2 : ℝ) ^ (1 / 4 : ℝ)) ^ 2)`.
* `TauCeti.irrational_sqrt_three_sub_one_div_sqrt_two_sub_one`:
  `Irrational ((√3 - 1) / (√2 - 1))`.
* `TauCeti.notMem_range_intCast_or_notMem_range_intCast_of_irrational`: if `θ₁` or `θ₂` is
  irrational, `j ≠ 0` and `a d - b c ≠ 0`, then `j (a θ₁ + b θ₂)` or `j (c θ₁ + d θ₂)` is not an
  integer.
-/

public section

namespace TauCeti

/-- For a nonnegative real number `x`, the square of `x ^ (1 / 4)` equals `√x` and is therefore
irrational if and only if `√x` is irrational. Nonnegativity cannot be dropped: at `x = -2`,
`((-2) ^ (1 / 4)) ^ 2 = √2 / 2` is irrational whereas `√(-2) = 0` is rational. -/
theorem irrational_rpow_one_quarter_sq_iff {x : ℝ} (hx : 0 ≤ x) :
    Irrational ((x ^ ((1 : ℝ) / 4)) ^ 2) ↔ Irrational √x := by
  have hhalf : (1 : ℝ) / 4 * (2 : ℕ) = 1 / (2 : ℝ) := by norm_num
  have hsq : (x ^ ((1 : ℝ) / 4)) ^ 2 = √x := by
    rw [← Real.rpow_mul_natCast hx, hhalf, ← Real.sqrt_eq_rpow]
  rw [hsq]

/-- For a prime `p`, the square of `(p : ℝ) ^ (1 / 4)` is `√p`, hence irrational. -/
theorem _root_.Nat.Prime.irrational_rpow_one_quarter_sq {p : ℕ} (hp : p.Prime) :
    Irrational (((p : ℝ) ^ ((1 : ℝ) / 4)) ^ 2) :=
  (irrational_rpow_one_quarter_sq_iff p.cast_nonneg).mpr hp.irrational_sqrt

/-- The square of `2 ^ (1 / 4 : ℝ)` is `√2`, hence irrational. -/
theorem irrational_two_rpow_one_quarter_sq :
    Irrational (((2 : ℝ) ^ ((1 : ℝ) / 4)) ^ 2) :=
  Nat.prime_two.irrational_rpow_one_quarter_sq

/-- The ratio `(√3 - 1) / (√2 - 1)` is irrational. -/
theorem irrational_sqrt_three_sub_one_div_sqrt_two_sub_one : Irrational ((√3 - 1) / (√2 - 1)) := by
  -- If the ratio were a rational `q`, then `√3 = q √2 + (1 - q)`, and squaring gives
  -- `3 = 2 q (1 - q) √2 + 2 q ^ 2 + (1 - q) ^ 2`, so `√2` would be rational unless
  -- `q (1 - q) = 0`; but `q = 0` gives `√3 = 1` and `q = 1` gives `√3 = √2`.
  have h2 := Real.one_lt_sqrt_two
  rintro ⟨q, hq⟩
  have h3 : √3 = q * √2 + (1 - q) := by
    rw [eq_div_iff (by linarith)] at hq
    linarith
  have hsq : 2 * q * (1 - q) * √2 + (2 * q ^ 2 + (1 - q) ^ 2) = ((3 : ℕ) : ℝ) := by
    have h3sq := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
    rw [h3] at h3sq
    push_cast
    linear_combination h3sq - (q : ℝ) ^ 2 * Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  by_cases hq₀ : 2 * q * (1 - q) = 0
  · rcases mul_eq_zero.1 hq₀ with hq₀ | hq₀
    · obtain rfl : q = 0 := by simpa using hq₀
      norm_num at h3
    · obtain rfl : q = 1 := (sub_eq_zero.1 hq₀).symm
      norm_num at h3
  · refine ((irrational_sqrt_two.ratCast_mul hq₀).add_ratCast (2 * q ^ 2 + (1 - q) ^ 2)).ne_nat
      3 ?_
    exact_mod_cast hsq

open Set in
/-- **Powers and finite-cover pullbacks of a flat line with infinite holonomy are nontrivial.** If
`θ₁` or `θ₂` is irrational, then for every nonzero integer `j` and every integer matrix
`(a, b; c, d)` of nonzero determinant, `j (a θ₁ + b θ₂)` and `j (c θ₁ + d θ₂)` are not both
integers. These are the twists of the `j`-th power of the line with holonomy `exp (2πiθ₁)`,
`exp (2πiθ₂)` along the sublattice basis `a ω₁ + b ω₂`, `c ω₁ + d ω₂`. -/
theorem notMem_range_intCast_or_notMem_range_intCast_of_irrational {θ₁ θ₂ : ℝ}
    (hθ : Irrational θ₁ ∨ Irrational θ₂) {j a b c d : ℤ} (hj : j ≠ 0)
    (hdet : a * d - b * c ≠ 0) :
    (j * (a * θ₁ + b * θ₂) : ℝ) ∉ range ((↑) : ℤ → ℝ) ∨
      (j * (c * θ₁ + d * θ₂) : ℝ) ∉ range ((↑) : ℤ → ℝ) := by
  by_contra hcon
  rw [not_or, not_not, not_not] at hcon
  obtain ⟨⟨m, hm⟩, ⟨n, hn⟩⟩ := hcon
  have hjd : ((j * (a * d - b * c) : ℤ) : ℝ) ≠ 0 := by exact_mod_cast mul_ne_zero hj hdet
  -- Solving the two equations for `θ₁` and `θ₂` by Cramer's rule makes both rational.
  rcases hθ with hθ | hθ
  · refine (irrational_iff_ne_rational θ₁).1 hθ (d * m - b * n) (j * (a * d - b * c))
      (mul_ne_zero hj hdet) ?_
    rw [eq_div_iff hjd]
    push_cast
    linear_combination (-(d : ℝ)) * hm + (b : ℝ) * hn
  · refine (irrational_iff_ne_rational θ₂).1 hθ (a * n - c * m) (j * (a * d - b * c))
      (mul_ne_zero hj hdet) ?_
    rw [eq_div_iff hjd]
    push_cast
    linear_combination (-(a : ℝ)) * hn + (c : ℝ) * hm

end TauCeti

namespace Irrational

/-- An integer relation between one and an irrational real number has both coefficients zero. -/
theorem intCast_add_mul_eq_zero_iff {θ : ℝ} (hθ : Irrational θ) {a b : ℤ} :
    (a : ℝ) + (b : ℝ) * θ = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    have hb : b = 0 := by
      by_contra hn
      apply (hθ.intCast_mul hn).ne_int (-a)
      push_cast
      linarith
    have ha : (a : ℝ) = 0 := by
      simpa only [hb, Int.cast_zero, zero_mul, add_zero] using h
    exact ⟨Int.cast_eq_zero.mp ha, hb⟩
  · rintro ⟨rfl, rfl⟩
    simp only [Int.cast_zero, zero_mul, add_zero]

/-- For an irrational real number `a` and a nonzero real number `c`, the multiple `c * a` is not an
integer multiple of `c`. -/
theorem intCast_mul_ne_mul {a c : ℝ} (ha : Irrational a) (hc : c ≠ 0) (k : ℤ) :
    (k : ℝ) * c ≠ c * a := by
  intro h
  exact ha.ne_int k (mul_left_cancel₀ hc (by rw [← h, mul_comm]))

end Irrational
