/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.KLFun

/-!
# Scaled values of `klFun`

Mathlib's `InformationTheory.klFun x = x * log x + 1 - x` is nonnegative on `[0, ∞)` and vanishes
there only at `1` (`InformationTheory.klFun_nonneg`, `InformationTheory.klFun_eq_zero_iff`). This
file expands the scaled value `P Q klFun (p / (P Q))` in logarithms.

## Main results

* `TauCeti.mul_klFun_div_mul`: for nonzero `P` and `Q`,
  `P Q klFun (p / (P Q)) = p log p - p log P - p log Q - p + P Q`.

With `p` the mass of a cell `a ∩ b` and `P`, `Q` the masses of `a` and `b`, the right side is the
contribution of that cell to `H(X) + H(Y) - H((X, Y))`, so the scaled value is the per-cell gap
in the subadditivity of entropy, and Mathlib's lemmas give its sign and its equality case.
-/

public section

open Real InformationTheory

namespace TauCeti

/-- A scaled `klFun` value at a ratio by a product, expanded in logarithms: for nonzero `P` and
`Q`, `P Q klFun (p / (P Q)) = p log p - p log P - p log Q - p + P Q`. -/
theorem mul_klFun_div_mul {p P Q : ℝ} (hP : P ≠ 0) (hQ : Q ≠ 0) :
    P * Q * klFun (p / (P * Q)) = p * log p - p * log P - p * log Q - p + P * Q := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp [klFun_zero]
  rw [klFun_apply, log_div hp (mul_ne_zero hP hQ), log_mul hP hQ]
  field_simp
  ring

end TauCeti
