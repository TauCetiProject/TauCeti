/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Matrix
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Matrices with entries in a subalgebra

For a subalgebra `S` of an algebra `A`, Mathlib's `Subalgebra.matrix` is the subalgebra of square
matrices over `A` with all entries in `S`. This file records that it acts on vectors with entries
in `S`, and that the image in `GL_n(A)` of an invertible matrix over `S` lies in it.

## Main results

* `Subalgebra.mulVec_apply_mem`: if `M` and `y` have entries in `S`, so does `M y`.
* `Subalgebra.coe_map_val_mem_matrix`: the image of `k ∈ GL_n(S)` in `GL_n(A)` has entries in `S`.
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

/-- The image in `GL_n(A)` of an invertible matrix over `S` has entries in `S`. -/
theorem coe_map_val_mem_matrix [CommRing R] [CommRing A] [Algebra R A] {S : Subalgebra R A}
    (k : GL n S) : (GeneralLinearGroup.map S.val.toRingHom k : Matrix n n A) ∈ S.matrix :=
  fun i j ↦ ((k : Matrix n n S) i j).property

end Subalgebra
