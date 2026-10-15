/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Nonzerodivisors in flat algebras

A flat algebra `A` over a commutative ring `R` is torsion-free: multiplication by a nonzerodivisor
of `R` is injective on `A` (`Module.Flat.isSMulRegular_of_nonZeroDivisors`). For a commutative
`A` this says that the structure map sends nonzerodivisors of `R` to nonzerodivisors of `A`.
Over a Bezout domain, such as a discrete valuation ring, torsion-freeness is also sufficient for
flatness, so a commutative algebra over a Bezout domain is flat exactly when every nonzero scalar
becomes a nonzerodivisor.

## Main results

* `Module.Flat.algebraMap_mem_nonZeroDivisors`: the image of a nonzerodivisor of `R` in a flat
  commutative `R`-algebra is a nonzerodivisor.
* `Module.Flat.flat_iff_algebraMap_mem_nonZeroDivisors_of_isBezout`: over a Bezout domain, a
  commutative algebra is flat exactly when the structure map sends nonzero elements to
  nonzerodivisors.
-/

public section

namespace Module.Flat

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [Flat R A]

/-- The structure map of a flat commutative algebra sends nonzerodivisors to nonzerodivisors. -/
theorem algebraMap_mem_nonZeroDivisors {r : R} (hr : r ∈ nonZeroDivisors R) :
    algebraMap R A r ∈ nonZeroDivisors A := by
  have h := (isSMulRegular_algebraMap_iff (M := A) A).mpr
    (isSMulRegular_of_nonZeroDivisors (M := A) hr)
  exact isRegular_iff_mem_nonZeroDivisors.mp (isLeftRegular_iff_isRegular.mp h.isLeftRegular)

omit [Flat R A] in
/-- Over a Bezout domain, a commutative algebra is flat exactly when the structure map sends every
nonzero element to a nonzerodivisor. -/
theorem flat_iff_algebraMap_mem_nonZeroDivisors_of_isBezout [IsDomain R] [IsBezout R] :
    Flat R A ↔ ∀ r : R, r ≠ 0 → algebraMap R A r ∈ nonZeroDivisors A := by
  refine ⟨fun _ r hr ↦ algebraMap_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hr),
    fun h ↦ ?_⟩
  rw [flat_iff_torsion_eq_bot_of_isBezout, Submodule.eq_bot_iff]
  rintro a ⟨⟨r, hr⟩, hra⟩
  rw [Submonoid.smul_def, Algebra.smul_def] at hra
  exact (h r (nonZeroDivisors.ne_zero hr)).2 a (by rw [mul_comm]; exact hra)

end Module.Flat
