/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Finite-basis coordinate expansions in an algebra

For a finite `R`-basis `b` of a (not necessarily commutative) `R`-algebra `A`, Mathlib's
`Module.Basis.sum_repr` expresses every element `x : A` as the scalar combination
`∑ i, b.repr x i • b i`. Rewriting the scalar action through `algebraMap R A` and the coordinate
functionals `b.coord i` yields the multiplicative expansions
`∑ i, algebraMap R A (b.coord i x) * b i = x` and
`∑ i, b i * algebraMap R A (b.coord i x) = x`, needed whenever `algebraMap R A` appears inside ring
homomorphisms, test-function compositions, or coefficientwise algebra maps.

## Main results

* `Module.Basis.sum_algebraMap_coord_mul`: `∑ i, algebraMap R A (b.coord i x) * b i = x`.
* `Module.Basis.sum_mul_algebraMap_coord`: `∑ i, b i * algebraMap R A (b.coord i x) = x`.
-/

public section

namespace Module.Basis

variable {ι R A : Type*} [Fintype ι] [CommSemiring R] [Semiring A] [Algebra R A]

/-- Every element of an `R`-algebra expands along a finite `R`-basis `b` as
`∑ i, algebraMap R A (b.coord i x) * b i`. -/
theorem sum_algebraMap_coord_mul (b : Module.Basis ι R A) (x : A) :
    ∑ i, algebraMap R A (b.coord i x) * b i = x := by
  simp_rw [← Algebra.smul_def, coord_apply, b.sum_repr]

/-- Every element of an `R`-algebra expands along a finite `R`-basis `b` as
`∑ i, b i * algebraMap R A (b.coord i x)`. -/
theorem sum_mul_algebraMap_coord (b : Module.Basis ι R A) (x : A) :
    ∑ i, b i * algebraMap R A (b.coord i x) = x := by
  simp_rw [← Algebra.commutes, b.sum_algebraMap_coord_mul]

section Examples

example {ι R : Type*} [Fintype ι] [CommSemiring R] (b : Module.Basis ι R R) (x : R) :
    ∑ i, b i * b.coord i x = x := by
  simpa using b.sum_mul_algebraMap_coord x

end Examples

end Module.Basis
