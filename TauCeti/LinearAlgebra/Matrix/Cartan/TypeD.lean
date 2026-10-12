/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic

/-!
# Row primitivity of the type-`D` Cartan matrix

In rank at least three, every row of the type-`D` Cartan matrix `CartanMatrix.D n` contains an
entry `-1`. A node of the chain, other than the last two, uses its successor along the chain; the
two fork nodes use the branch node `n - 3` they are both attached to. Rank two is the exception:
`D₂` is `A₁ × A₁`, whose rows `(2, 0)` and `(0, 2)` generate only `2ℤ`.

This file names such a neighbour `TauCeti.typeDCartanNeighbor` and packages the resulting Bezout
certificate `TauCeti.typeDCartanBezout`, the integer coefficients `-1` at that neighbour and `0`
elsewhere, whose pairing with the Cartan row is `1`. It says that every simple root of type `D` in
rank at least three is a primitive character of a split torus whose weights are the Cartan rows.
This is the arithmetic hypothesis in
`TauCeti.UniversalEnvelopingAlgebra.kostantTorusSubgroup_le_kostantElementarySubgroup`, and it is
shared by every carrier built on the type-`D` Serre presentation.

## Main declarations

* `TauCeti.typeDCartanNeighbor`: a node adjacent to a given node with Cartan entry `-1`.
* `TauCeti.cartanMatrixD_typeDCartanNeighbor`: in rank at least three, that Cartan entry is `-1`.
* `TauCeti.typeDCartanBezout` and `TauCeti.sum_cartanMatrixD_mul_typeDCartanBezout`: the explicit
  Bezout certificate for each row of the type-`D` Cartan matrix.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IV.
* `TauCeti.LinearAlgebra.Matrix.Cartan.TypeB`, whose type-`B` certificate this file mirrors.
-/

public section

namespace TauCeti

variable {n : ℕ}

/-- A column index chosen as the successor of `i`, except at the last two indices, the fork
nodes, where it is the branch node `n - 3`. In rank at least three this is an adjacent node of the
type-`D` Dynkin diagram, with Cartan entry `-1` in row `i`. -/
def typeDCartanNeighbor (n : ℕ) (i : Fin n) : Fin n :=
  ⟨if (i : ℕ) + 2 < n then (i : ℕ) + 1 else n - 3, by have := i.isLt; split_ifs <;> omega⟩

@[simp]
theorem val_typeDCartanNeighbor (i : Fin n) :
    (typeDCartanNeighbor n i : ℕ) = if (i : ℕ) + 2 < n then (i : ℕ) + 1 else n - 3 :=
  (rfl)

/-- In rank at least three, the type-`D` Cartan matrix has entry `-1` at each node and its
chosen neighbour. -/
@[simp]
theorem cartanMatrixD_typeDCartanNeighbor (hn : 3 ≤ n) (i : Fin n) :
    CartanMatrix.D n i (typeDCartanNeighbor n i) = -1 := by
  simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff, val_typeDCartanNeighbor]
  split_ifs <;> omega

/-- Integer coefficients supported at the chosen column: `-1` at `typeDCartanNeighbor n i`
and `0` elsewhere. They certify row primitivity in rank at least three. -/
def typeDCartanBezout (n : ℕ) (i j : Fin n) : ℤ :=
  if j = typeDCartanNeighbor n i then -1 else 0

@[simp]
theorem typeDCartanBezout_apply (i j : Fin n) :
    typeDCartanBezout n i j = if j = typeDCartanNeighbor n i then -1 else 0 :=
  (rfl)

/-- In rank at least three, every row of the type-`D` Cartan matrix is a primitive integer
vector, with the explicit certificate `typeDCartanBezout`. -/
theorem sum_cartanMatrixD_mul_typeDCartanBezout (hn : 3 ≤ n) (i : Fin n) :
    ∑ j, CartanMatrix.D n i j * typeDCartanBezout n i j = 1 := by
  rw [Finset.sum_eq_single (typeDCartanNeighbor n i)]
  · simp [cartanMatrixD_typeDCartanNeighbor hn]
  · intro j _ hj
    simp [hj]
  · simp

end TauCeti
