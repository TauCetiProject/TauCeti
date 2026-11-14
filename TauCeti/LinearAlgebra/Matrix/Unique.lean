/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.MonoidHom
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Unique

/-!
# Star equivalences for `1 × 1` matrices

For a singleton index type `m` (`[Unique m]`) and a non-unital, non-associative semiring `A`
equipped with a `Star` operation, reading off the unique entry upgrades `Matrix.uniqueRingEquiv` to
a `⋆`-ring equivalence `Matrix.uniqueStarRingEquiv : Matrix m m A ≃⋆+* A` and a `⋆`-multiplicative
equivalence `Matrix.uniqueStarMulEquiv : Matrix m m A ≃⋆* A`.

Both equivalences take `[Fintype m]` as an explicit typeclass argument alongside `[Unique m]` so
that the multiplication instance on `Matrix m m A` agrees definitionally with any ambient
`Fintype m` instance (such as on `Fin 1`), while still synthesizing automatically from `[Unique m]`
when no separate `Fintype m` is in scope.

## Main definitions

* `Matrix.uniqueStarRingEquiv`: the `⋆`-ring equivalence `Matrix m m A ≃⋆+* A` for `[Unique m]`.
* `Matrix.uniqueStarMulEquiv`: the `⋆`-multiplicative equivalence `Matrix m m A ≃⋆* A` for
  `[Unique m]`.
-/

@[expose] public section

namespace Matrix

variable {m A : Type*} [Fintype m] [Unique m] [NonUnitalNonAssocSemiring A] [Star A]

/-- `M₁(A)` and `A` are equivalent as `⋆`-rings by reading off the unique entry. -/
@[simps!]
def uniqueStarRingEquiv : Matrix m m A ≃⋆+* A where
  __ := uniqueAddEquiv
  map_mul' M N := by
    cases Subsingleton.elim ‹Fintype m› Unique.fintype
    exact uniqueRingEquiv.map_mul' M N
  map_star' _ := rfl

/-- `M₁(A)` and `A` are equivalent as `⋆`-monoids by reading off the unique entry. -/
@[simps!]
def uniqueStarMulEquiv : Matrix m m A ≃⋆* A where
  __ := uniqueStarRingEquiv.toRingEquiv.toMulEquiv
  map_star' := uniqueStarRingEquiv.map_star'

end Matrix
