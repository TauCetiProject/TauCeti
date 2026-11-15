/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors

/-!
# Powers of nonzerodivisors

In any monoid with zero `M₀`, a positive power `a ^ n` (`n ≠ 0`) is a left, right, or two-sided
nonzerodivisor if and only if `a` itself is: unlike a general product `a * b` (where
`mul_mem_nonZeroDivisors` requires commutativity), `a` commutes with `a ^ (n - 1)`.

## Main results

* `TauCeti.pow_mem_nonZeroDivisorsLeft_iff`, `TauCeti.pow_mem_nonZeroDivisorsRight_iff`,
  `TauCeti.pow_mem_nonZeroDivisors_iff`: for `n ≠ 0`, `a ^ n` is a (left, right, or two-sided)
  nonzerodivisor if and only if `a` is.
-/

public section

open scoped nonZeroDivisors

namespace TauCeti

variable {M₀ : Type*} [MonoidWithZero M₀] {a : M₀} {n : ℕ}

/-- For `n ≠ 0`, `a ^ n` is a left nonzerodivisor if and only if `a` is. -/
theorem pow_mem_nonZeroDivisorsLeft_iff (hn : n ≠ 0) :
    a ^ n ∈ nonZeroDivisorsLeft M₀ ↔ a ∈ nonZeroDivisorsLeft M₀ := by
  rcases n with _ | n
  · contradiction
  · refine ⟨fun h y hy ↦ h y ?_, fun ha ↦ (nonZeroDivisorsLeft M₀).pow_mem ha (n + 1)⟩
    rw [pow_succ, mul_assoc, hy, mul_zero]

/-- For `n ≠ 0`, `a ^ n` is a right nonzerodivisor if and only if `a` is. -/
theorem pow_mem_nonZeroDivisorsRight_iff (hn : n ≠ 0) :
    a ^ n ∈ nonZeroDivisorsRight M₀ ↔ a ∈ nonZeroDivisorsRight M₀ := by
  rcases n with _ | n
  · contradiction
  · refine ⟨fun h y hy ↦ h y ?_, fun ha ↦ (nonZeroDivisorsRight M₀).pow_mem ha (n + 1)⟩
    rw [pow_succ', ← mul_assoc, hy, zero_mul]

/-- For `n ≠ 0`, `a ^ n` is a nonzerodivisor if and only if `a` is. -/
@[simp]
theorem pow_mem_nonZeroDivisors_iff (hn : n ≠ 0) : a ^ n ∈ M₀⁰ ↔ a ∈ M₀⁰ := by
  rw [mem_nonZeroDivisors_iff', mem_nonZeroDivisors_iff', pow_mem_nonZeroDivisorsLeft_iff hn,
    pow_mem_nonZeroDivisorsRight_iff hn]

end TauCeti

end
