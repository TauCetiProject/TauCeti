/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.RatFunc.Valuation
import TauCeti.RingTheory.Valuation.Discrete.Order

/-!
# A valuation obstruction to roots of the rational-function variable

The variable `X` is not an `n`-th power in `K(X)` for `n > 1`: its order at infinity is `-1`,
whereas the order of an `n`-th power is divisible by `n`. This supplies non-power coefficients
for Laurent-series pole obstructions over rational function fields.
-/

public section

namespace TauCeti

/-- The rational-function variable is not an `n`-th power when `n > 1`. -/
theorem ratFunc_pow_ne_X {K : Type*} [Field K] {n : ℕ} (hn : 1 < n)
    (b : RatFunc K) : b ^ n ≠ RatFunc.X := by
  classical
  intro hb
  have h := congrArg (RatFunc.inftyValuation K).ord hb
  rw [Valuation.ord_pow] at h
  simp only [Valuation.ord_def, RatFunc.inftyValuation.X, WithZero.log_exp] at h
  have hnZ : (1 : ℤ) < n := by exact_mod_cast hn
  have hd : (n : ℤ) ∣ (-1 : ℤ) := ⟨_, h.symm⟩
  have := Int.le_of_dvd (by omega : (0 : ℤ) < 1) (dvd_neg.mp hd)
  omega

end TauCeti
