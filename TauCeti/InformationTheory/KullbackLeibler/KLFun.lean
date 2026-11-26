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
file expands the scaled value `q klFun (p / q)` in logarithms.

## Main results

* `TauCeti.mul_klFun_div`: for nonzero `q`, `q klFun (p / q) = p log p - p log q - p + q`.

With `p` the mass of a cell `a ∩ b` and `q = P Q` the product of the masses `P`, `Q` of `a` and
`b`, splitting `log q = log P + log Q` turns the right side into the contribution of that cell to
`H(X) + H(Y) - H((X, Y))`, so the scaled value is the per-cell gap in the subadditivity of entropy,
and Mathlib's lemmas give its sign and its equality case.
-/

public section

open Real InformationTheory

namespace TauCeti

/-- A scaled `klFun` value at a ratio, expanded in logarithms: for nonzero `q`,
`q klFun (p / q) = p log p - p log q - p + q`. -/
theorem mul_klFun_div {p q : ℝ} (hq : q ≠ 0) :
    q * klFun (p / q) = p * log p - p * log q - p + q := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp [klFun_zero]
  rw [klFun_apply, log_div hp hq]
  field_simp
  ring

end TauCeti
