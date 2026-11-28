/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Matrix

/-!
# Matrices with entries in a subalgebra

For a subalgebra `S` of an algebra `A`, Mathlib's `Subalgebra.matrix` is the subalgebra of square
matrices over `A` with all entries in `S`. This file records that it acts on vectors with entries
in `S`.

## Main results

* `Subalgebra.mulVec_apply_mem`: if `M` and `y` have entries in `S`, so does `M y`.
-/

public section

open Matrix

namespace Subalgebra

variable {R A : Type*} {n : Type*} [Fintype n] [DecidableEq n]

/-- The entries of `M y` lie in `S` when those of the square matrix `M` and of `y` do. -/
theorem mulVec_apply_mem [CommSemiring R] [Semiring A] [Algebra R A] {S : Subalgebra R A}
    {M : Matrix n n A} (hM : M ∈ S.matrix) {y : n → A} (hy : ∀ j, y j ∈ S) (i : n) :
    (M *ᵥ y) i ∈ S :=
  Subalgebra.sum_mem _ fun j _ ↦ S.mul_mem (hM i j) (hy j)

end Subalgebra
