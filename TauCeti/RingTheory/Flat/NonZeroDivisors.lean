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

## Main results

* `Module.Flat.algebraMap_mem_nonZeroDivisors`: the image of a nonzerodivisor of `R` in a flat
  commutative `R`-algebra is a nonzerodivisor.
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

end Module.Flat
