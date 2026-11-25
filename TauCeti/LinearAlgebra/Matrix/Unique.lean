/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Unique

/-!
# Star and algebra equivalences for `1 × 1` matrices

For a singleton index type `m` (`[Unique m]`) and a non-unital, non-associative semiring `A`
equipped with a `Star` operation, reading off the unique entry upgrades `Matrix.uniqueRingEquiv` to
a `⋆`-ring equivalence `Matrix.uniqueStarRingEquiv : Matrix m m A ≃⋆+* A`. For an `R`-algebra `A`,
it is an `R`-algebra equivalence `Matrix.uniqueAlgEquivOfFintype : Matrix m m A ≃ₐ[R] A`.

These equivalences take `[Fintype m]` (and, for the algebra equivalence, `[DecidableEq m]`) as
explicit typeclass arguments alongside `[Unique m]`, so that the multiplication and algebra
instances on `Matrix m m A` agree definitionally with any ambient `Fintype m` and `DecidableEq m`
instances (such as on `Fin 1`). Mathlib's `Matrix.uniqueAlgEquiv` instead uses the instances
derived from `[Unique m]`.

## Main definitions

* `Matrix.uniqueStarRingEquiv`: the `⋆`-ring equivalence `Matrix m m A ≃⋆+* A` for `[Unique m]`.
* `Matrix.uniqueAlgEquivOfFintype`: the `R`-algebra equivalence `Matrix m m A ≃ₐ[R] A` for
  `[Unique m]`, with any `Fintype m` and `DecidableEq m` instances.
-/

public section

namespace Matrix

section Star

variable {m A : Type*} [Fintype m] [Unique m] [NonUnitalNonAssocSemiring A] [Star A]

/-- `M₁(A)` and `A` are equivalent as `⋆`-rings by reading off the unique entry. -/
def uniqueStarRingEquiv : Matrix m m A ≃⋆+* A where
  __ := uniqueAddEquiv
  map_mul' M N := by
    cases Subsingleton.elim ‹Fintype m› Unique.fintype
    exact uniqueRingEquiv.map_mul' M N
  map_star' _ := rfl

@[simp]
theorem uniqueStarRingEquiv_apply (M : Matrix m m A) :
    uniqueStarRingEquiv M = M default default :=
  (rfl)

@[simp]
theorem uniqueStarRingEquiv_symm_apply (a : A) :
    (uniqueStarRingEquiv (m := m)).symm a = Matrix.of fun _ _ ↦ a :=
  (rfl)

end Star

section Algebra

variable {m R A : Type*} [Fintype m] [DecidableEq m] [Unique m] [CommSemiring R] [Semiring A]
  [Algebra R A]

/-- `M₁(A)` and `A` are equivalent as `R`-algebras by reading off the unique entry, for any
`Fintype m` and `DecidableEq m` instances. -/
def uniqueAlgEquivOfFintype : Matrix m m A ≃ₐ[R] A where
  __ := uniqueAddEquiv
  map_mul' M N := by simp [Matrix.mul_apply]
  commutes' r := by simp [Matrix.algebraMap_matrix_apply]

@[simp]
theorem uniqueAlgEquivOfFintype_apply (M : Matrix m m A) :
    uniqueAlgEquivOfFintype (R := R) M = M default default :=
  (rfl)

@[simp]
theorem uniqueAlgEquivOfFintype_symm_apply (a : A) :
    (uniqueAlgEquivOfFintype (m := m) (R := R)).symm a = Matrix.of fun _ _ ↦ a :=
  (rfl)

end Algebra

end Matrix
