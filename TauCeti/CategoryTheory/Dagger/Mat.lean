/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.BigOperators
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import TauCeti.CategoryTheory.Dagger.Linear
public import TauCeti.CategoryTheory.Linear.Mat

/-!
# The matrix category as a dagger category

For a semiring `R` with an involution reversing products (a `StarRing`), Mathlib's matrix
category `Mat R`, whose objects are finite types and whose morphisms `X ⟶ Y` are `X × Y`
matrices composed by matrix multiplication, is a dagger category with the conjugate transpose
`Matrix.conjTranspose` as dagger. The dagger is additive, and conjugate-linear over any star
semiring `S` for which `R` is a star `S`-module whose scalars commute and associate with
multiplication, such as a star `S`-algebra.

For `R = ℂ` this is the skeleton of the category of finite-dimensional Hilbert spaces: an object
`X` stands for `ℂ^X` with its standard inner product, and the conjugate transpose of a matrix is
the adjoint of the corresponding operator.

## Main declarations

* `CategoryTheory.Mat.instDaggerCategory`, with `CategoryTheory.Mat.dagger_apply`: the conjugate
  transpose as dagger on `Mat R`;
* `CategoryTheory.Mat.instDaggerPreadditive` and `CategoryTheory.Mat.instDaggerLinear`: the
  conjugate transpose is additive and conjugate-linear.
-/

public section

open TauCeti TauCeti.DaggerCategory

universe w u

namespace CategoryTheory.Mat

section Semiring

variable {R : Type u} [Semiring R] [StarRing R]

/-- The conjugate transpose makes the matrix category `Mat R` a dagger category. -/
instance instDaggerCategory : DaggerCategory (Mat R) where
  dagger f := Matrix.conjTranspose f
  dagger_comp f g := by
    ext
    simp [star_sum]
  dagger_dagger f := Matrix.conjTranspose_conjTranspose f

/-- The dagger of a matrix is its conjugate transpose. -/
theorem dagger_def {X Y : Mat R} (f : X ⟶ Y) : dagger f = Matrix.conjTranspose f :=
  (rfl)

@[simp]
theorem dagger_apply {X Y : Mat R} (f : X ⟶ Y) (i : Y) (j : X) : dagger f i j = star (f j i) :=
  (rfl)

end Semiring

variable {R : Type} [Ring R] [StarRing R]

/-- The conjugate transpose is additive. -/
instance instDaggerPreadditive : DaggerPreadditive (Mat R) where
  dagger_add f g := Matrix.conjTranspose_add f g

/-- The conjugate transpose is conjugate-linear over any semiring `S` acting on `R` compatibly
with multiplication and the star operations, for instance `S = R = ℂ`. -/
instance instDaggerLinear (S : Type w) [Semiring S] [Star S] [Module S R] [IsScalarTower S R R]
    [SMulCommClass S R R] [StarModule S R] : DaggerLinear S (Mat R) where
  dagger_smul s f := Matrix.conjTranspose_smul s f

end CategoryTheory.Mat
