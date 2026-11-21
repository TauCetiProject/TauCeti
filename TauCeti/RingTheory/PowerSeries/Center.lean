/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Center of formal power series

A formal power series in `A⟦X⟧` lies in `Subalgebra.center R A⟦X⟧` if and only if each of its
coefficients lies in `Subalgebra.center R A` (`PowerSeries.mem_center_iff`).
-/

public section

namespace PowerSeries

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

/-- A formal power series in `A⟦X⟧` is central if and only if each coefficient is central in `A`. -/
theorem mem_center_iff {f : A⟦X⟧} :
    f ∈ Subalgebra.center R A⟦X⟧ ↔ ∀ n, coeff n f ∈ Subalgebra.center R A := by
  refine ⟨fun hf n ↦ Subalgebra.mem_center_iff.2 fun a ↦ ?_,
    fun hf ↦ Subalgebra.mem_center_iff.2 fun g ↦ ?_⟩
  · simpa only [coeff_C_mul, coeff_mul_C] using
      congrArg (coeff n) (Subalgebra.mem_center_iff.1 hf (C a))
  · ext n
    rw [coeff_mul, coeff_mul, ← Finset.Nat.sum_antidiagonal_swap]
    exact Finset.sum_congr rfl fun p _ ↦ Subalgebra.mem_center_iff.1 (hf p.1) (coeff p.2 g)

end PowerSeries
