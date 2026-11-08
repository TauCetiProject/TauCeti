/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.NumberTheory.Padics.PadicIntegers
import TauCeti.RingTheory.AdicCompletion.DerivedComplete

/-!
# Checks for derived completeness of modules

These examples exercise derived `p`-completeness over the `p`-adic integers. The ring `ℤ_[p]` and
every product of copies of it are derived `p`-complete, but the countable direct sum is not,
although each of its summands is. Derived completeness is therefore not a condition that can be
tested summand by summand.
-/

namespace TauCeti.Examples

variable (p : ℕ) [Fact p.Prime]

-- The `p`-adic integers are classically, hence derived, `p`-complete.
example : IsDerivedComplete (Ideal.span {(p : ℤ_[p])}) ℤ_[p] := by
  rw [← PadicInt.maximalIdeal_eq_span_p]
  exact .of_isAdicComplete

-- A countable product of copies of `ℤ_[p]` is derived `p`-complete.
example : IsDerivedComplete (Ideal.span {(p : ℤ_[p])}) (ℕ → ℤ_[p]) := by
  rw [← PadicInt.maximalIdeal_eq_span_p]
  exact .pi fun _ ↦ .of_isAdicComplete

-- The countable direct sum `⊕_ℕ ℤ_[p]` is not derived `p`-complete.
example : ¬IsDerivedComplete (Ideal.span {(p : ℤ_[p])}) (ℕ →₀ ℤ_[p]) :=
  not_isDerivedComplete_finsupp (mem_nonZeroDivisors_of_ne_zero (NeZero.ne _))
    PadicInt.p_nonunit

-- Every module is derived complete for the zero ideal, and only the zero module for the unit
-- ideal.
example : IsDerivedComplete (⊥ : Ideal ℤ) ℚ := isDerivedComplete_bot

example : ¬IsDerivedComplete (⊤ : Ideal ℤ) ℤ := by
  rw [isDerivedComplete_top_iff]
  exact not_subsingleton ℤ

end TauCeti.Examples
