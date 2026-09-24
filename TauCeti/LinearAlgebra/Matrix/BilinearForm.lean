/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# Bilinear forms attached to matrices

Mathlib's `Matrix.toBilin'` reads a square matrix `M` over a commutative semiring `R` as the
bilinear form `(x, y) ↦ xᵀ M y` on `n → R`. This file records facts about these forms that
Mathlib lacks. The identity matrix gives the standard form `∑ i, x i * y i`, which takes the value
`1` on every standard basis vector, so over a nontrivial `R` it is alternating only when the index
type is empty (over the trivial semiring `1 = 0` and every form is alternating). Since the identity
matrix is symmetric and invertible, the standard form over a nontrivial `R` is in every positive
dimension a nondegenerate symmetric form that is not alternating, the model for the orthonormal
normal form of such forms.

## Main results

* `Matrix.isAlt_toBilin'_one_iff`: for `R` nontrivial, the standard form on `n → R` is alternating
  exactly when `n` is empty.
-/

public section

namespace Matrix

/-- Over a nontrivial commutative semiring `R`, the standard form `∑ i, x i * y i` on `n → R` is
alternating only when `n` is empty: it takes the value `1 ≠ 0` on every standard basis vector. -/
@[simp]
theorem isAlt_toBilin'_one_iff {n R : Type*} [Fintype n] [DecidableEq n] [CommSemiring R]
    [Nontrivial R] : (toBilin' (1 : Matrix n n R)).IsAlt ↔ IsEmpty n := by
  refine ⟨fun h => ⟨fun i => by simpa using h (Pi.single i 1)⟩, fun hn x => ?_⟩
  simp [Subsingleton.elim x 0]

end Matrix
