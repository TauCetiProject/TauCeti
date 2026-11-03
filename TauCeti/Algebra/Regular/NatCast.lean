/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors

/-!
# Positive integers are non-zero-divisors without additive torsion

In a semiring `S` without additive torsion, multiplication by a positive integer `n` is `n • ·`,
which is injective. Hence `n` is a non-zero-divisor of `S` (`TauCeti.natCast_mem_nonZeroDivisors`).
This combines Mathlib's `isRegular_natCast` with `IsRegular.mem_nonZeroDivisors`.
-/

public section

open scoped nonZeroDivisors

namespace TauCeti

/-- Positive integers are non-zero-divisors of a semiring without additive torsion. -/
theorem natCast_mem_nonZeroDivisors {S : Type*} [Semiring S] [IsAddTorsionFree S] {n : ℕ}
    (hn : n ≠ 0) : (n : S) ∈ S⁰ :=
  (isRegular_natCast.mpr fun a b h ↦
    eq_of_nsmul_eq_nsmul_of_addCommute hn (AddCommute.all a b) h).mem_nonZeroDivisors

end TauCeti
