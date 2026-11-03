/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.Basic

/-!
# Legendre symbols and square-class changes of radicand

Replacing an integer `a` by `a * u ^ 2`, with `p ∤ u`, does not change its Legendre symbol
modulo `p` (`legendreSym_mul_sq`). This lets a radicand be normalized within its square class,
for instance by removing a factor `4`, before its Legendre symbol is evaluated. The companion
divisibility statement `p ∣ a * u ^ 2 ↔ p ∣ a` is the general `Prime.dvd_mul_pow_iff`.
-/

public section

namespace TauCeti

variable {p : ℕ} [Fact p.Prime]

/-- Multiplying an integer by `u ^ 2` with `p ∤ u` does not change its Legendre symbol. -/
@[simp]
theorem legendreSym_mul_sq {a u : ℤ} (hu : ¬ (p : ℤ) ∣ u) :
    legendreSym p (a * u ^ 2) = legendreSym p a := by
  rw [legendreSym.mul,
    legendreSym.sq_one' p (by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]), mul_one]

end TauCeti
