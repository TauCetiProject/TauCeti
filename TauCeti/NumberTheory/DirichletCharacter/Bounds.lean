/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.NumberTheory.DirichletCharacter.Bounds

/-!
# Bounds on values of complex Dirichlet characters

The values of complex Dirichlet characters have norm at most `1`, so for characters `χ` and `χ'`
of any levels and `n > 1` the factor `1 - χ(n) χ'(n) / n` is nonzero. Taking `χ'` trivial gives
the nonvanishing of the Euler factor `1 - χ(p) / p` of `L(χ, 1)`; products of two characters of
different levels arise for instance in the constant terms of weight-one Eisenstein series. The same
bound makes the weight `1 + re χ(a)` nonnegative, as used in positivity arguments for
combinations of `ζ` and `L`-functions.

## Main results

* `DirichletCharacter.one_sub_mul_div_natCast_ne_zero`: `1 - χ(n) χ'(n) / n ≠ 0` for `1 < n`.
* `DirichletCharacter.one_add_re_nonneg`: `0 ≤ 1 + re χ(a)`.
-/

public section

namespace DirichletCharacter

/-- For complex Dirichlet characters `χ`, `χ'` of any levels and `1 < n`, the Euler-type factor
`1 - χ(n) χ'(n) / n` is nonzero, since `‖χ(n) χ'(n) / n‖ ≤ 1 / n < 1`. -/
theorem one_sub_mul_div_natCast_ne_zero {M N n : ℕ} (χ : DirichletCharacter ℂ M)
    (χ' : DirichletCharacter ℂ N) (hn : 1 < n) : 1 - χ n * χ' n / n ≠ 0 := by
  intro h
  have hn' : (1 : ℝ) < n := by exact_mod_cast hn
  have hlt : ‖χ n * χ' n / (n : ℂ)‖ < 1 := by
    rw [norm_div, norm_mul, Complex.norm_natCast, div_lt_one (by linarith)]
    calc ‖χ n‖ * ‖χ' n‖ ≤ 1 * 1 :=
          mul_le_mul (χ.norm_le_one _) (χ'.norm_le_one _) (norm_nonneg _) zero_le_one
      _ < n := by linarith
  rw [← sub_eq_zero.mp h, norm_one] at hlt
  exact lt_irrefl _ hlt

/-- The weight `1 + re χ(a)` is nonnegative, since `‖χ(a)‖ ≤ 1`. -/
theorem one_add_re_nonneg {N : ℕ} (χ : DirichletCharacter ℂ N) (a : ZMod N) :
    0 ≤ 1 + (χ a).re := by
  have := (Complex.abs_re_le_norm (χ a)).trans (χ.norm_le_one a)
  linarith [neg_abs_le (χ a).re]

end DirichletCharacter
