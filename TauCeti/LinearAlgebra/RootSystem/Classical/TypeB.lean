/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import TauCeti.LinearAlgebra.Matrix.Cartan.Classical

/-!
# The simple roots and coroots of type `Bₙ` in classical coordinates

In the lattice `ℤ ^ n` with standard basis `e₀, …, e_{n-1}`, the Bourbaki-numbered simple roots of
type `Bₙ` are the chain roots `eᵢ - eᵢ₊₁` and the short root `e_{n-1}`, and their coroots are
`eᵢ - eᵢ₊₁` and `2 e_{n-1}`. The roots and coroots of type `Cₙ` are the coroots and roots of type
`Bₙ`. The type-`D` counterpart is `TauCeti.DynkinType.typeDSimpleRoot`.

## Main definitions

* `TauCeti.DynkinType.typeBSimpleRoot`, `TauCeti.DynkinType.typeBSimpleCoroot`: the simple roots
  and coroots of type `Bₙ` in classical coordinates.

## Main results

* `TauCeti.DynkinType.typeBSimpleRoot_mul_transpose_typeBSimpleCoroot` and
  `TauCeti.DynkinType.typeBSimpleCoroot_mul_transpose_typeBSimpleRoot`: the roots pair with the
  coroots to the Cartan matrix `CartanMatrix.B n`, and the coroots with the roots to
  `CartanMatrix.C n`.
* `TauCeti.DynkinType.det_typeBSimpleRoot_eq_one` and
  `TauCeti.DynkinType.det_typeBSimpleCoroot_eq_two`: the matrices of simple roots and of simple
  coroots have determinants `1` and `2`.
* `TauCeti.DynkinType.vecMulVec_typeBSimpleCoroot_typeBSimpleRoot`: the ambient reflections of
  types `Bₙ` and `Cₙ` in corresponding simple roots coincide.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plates II and III.
-/

public section

open Matrix

namespace TauCeti.DynkinType

variable {n : ℕ}

/-- The Bourbaki-numbered simple roots of type `Bₙ` in classical orthogonal coordinates: the
chain roots `eᵢ - eᵢ₊₁` and the short root `e_{n-1}`. -/
def typeBSimpleRoot (n : ℕ) (i : Fin n) : Fin n → ℤ :=
  if h : (i : ℕ) + 1 < n then Pi.single i 1 - Pi.single ⟨(i : ℕ) + 1, h⟩ 1 else Pi.single i 1

/-- The simple coroots of type `Bₙ` in classical orthogonal coordinates: the chain coroots
`eᵢ - eᵢ₊₁` and the coroot `2 e_{n-1}` of the short root. They are the simple roots of type
`Cₙ`. -/
def typeBSimpleCoroot (n : ℕ) (i : Fin n) : Fin n → ℤ :=
  if h : (i : ℕ) + 1 < n then Pi.single i 1 - Pi.single ⟨(i : ℕ) + 1, h⟩ 1 else Pi.single i 2

/-- The chain simple roots of type `Bₙ` are `eᵢ - eᵢ₊₁`. -/
@[simp] theorem typeBSimpleRoot_of_add_one_lt {i : Fin n} (hi : (i : ℕ) + 1 < n) :
    typeBSimpleRoot n i = Pi.single i 1 - Pi.single ⟨(i : ℕ) + 1, hi⟩ 1 :=
  dite_eq_left hi

/-- The last simple root of type `Bₙ` is the short root `e_{n-1}`. -/
@[simp] theorem typeBSimpleRoot_of_not_add_one_lt {i : Fin n} (hi : ¬(i : ℕ) + 1 < n) :
    typeBSimpleRoot n i = Pi.single i 1 :=
  dite_eq_right hi

/-- The chain simple coroots of type `Bₙ` are `eᵢ - eᵢ₊₁`. -/
@[simp] theorem typeBSimpleCoroot_of_add_one_lt {i : Fin n} (hi : (i : ℕ) + 1 < n) :
    typeBSimpleCoroot n i = Pi.single i 1 - Pi.single ⟨(i : ℕ) + 1, hi⟩ 1 :=
  dite_eq_left hi

/-- The last simple coroot of type `Bₙ` is `2 e_{n-1}`. -/
@[simp] theorem typeBSimpleCoroot_of_not_add_one_lt {i : Fin n} (hi : ¬(i : ℕ) + 1 < n) :
    typeBSimpleCoroot n i = Pi.single i 2 :=
  dite_eq_right hi

/-- **The simple roots and coroots of type `Bₙ` pair to the Cartan matrix**:
`⟨αᵢ, αⱼ^∨⟩ = CartanMatrix.B n i j`. -/
@[simp]
theorem typeBSimpleRoot_dotProduct_typeBSimpleCoroot (i j : Fin n) :
    typeBSimpleRoot n i ⬝ᵥ typeBSimpleCoroot n j = CartanMatrix.B n i j := by
  by_cases hi : (i : ℕ) + 1 < n <;> by_cases hj : (j : ℕ) + 1 < n <;>
    simp [hi, hj, Pi.single_apply, Fin.ext_iff, CartanMatrix.B] <;> grind

/-- The Cartan matrix of type `Bₙ` is the matrix of pairings of the simple roots with the simple
coroots. -/
theorem typeBSimpleRoot_mul_transpose_typeBSimpleCoroot :
    Matrix.of (typeBSimpleRoot n) * (Matrix.of (typeBSimpleCoroot n))ᵀ = CartanMatrix.B n := by
  ext i j
  rw [Matrix.mul_apply, ← typeBSimpleRoot_dotProduct_typeBSimpleCoroot i j]
  simp [dotProduct]

/-- The Cartan matrix of type `Cₙ` is the matrix of pairings of the simple coroots of type `Bₙ`,
the simple roots of type `Cₙ`, with the simple roots of type `Bₙ`. -/
theorem typeBSimpleCoroot_mul_transpose_typeBSimpleRoot :
    Matrix.of (typeBSimpleCoroot n) * (Matrix.of (typeBSimpleRoot n))ᵀ = CartanMatrix.C n := by
  rw [← CartanMatrix.B_transpose, ← typeBSimpleRoot_mul_transpose_typeBSimpleCoroot,
    transpose_mul, transpose_transpose]

/-- The matrix whose rows are the simple roots of type `Bₙ` is unitriangular, so it has
determinant `1`. -/
@[simp]
theorem det_typeBSimpleRoot_eq_one : (Matrix.of (typeBSimpleRoot n)).det = 1 := by
  rw [det_of_isUpperTriangular fun i j hji => ?_]
  · refine Finset.prod_eq_one fun i _ => ?_
    by_cases hi : (i : ℕ) + 1 < n <;> simp [hi, Fin.ext_iff]
  · have : (j : ℕ) < i := hji
    by_cases hi : (i : ℕ) + 1 < n <;> simp [hi, Pi.single_apply, Fin.ext_iff] <;> omega

/-- The matrix whose rows are the simple coroots of type `Bₙ` has determinant `2`. -/
@[simp]
theorem det_typeBSimpleCoroot_eq_two (hn : 0 < n) : (Matrix.of (typeBSimpleCoroot n)).det = 2 := by
  have := congrArg det (typeBSimpleRoot_mul_transpose_typeBSimpleCoroot (n := n))
  rwa [det_mul, det_transpose, det_typeBSimpleRoot_eq_one, one_mul, CartanMatrix.B_det hn] at this

/-- The ambient reflections in a simple root of type `Bₙ` and in its coroot coincide:
`vecMulVec α^∨ α = vecMulVec α α^∨`. This is why the Weyl groups of types `Bₙ` and `Cₙ` act on
`ℤ ^ n` by the same signed permutations. -/
theorem vecMulVec_typeBSimpleCoroot_typeBSimpleRoot (i : Fin n) :
    vecMulVec (typeBSimpleCoroot n i) (typeBSimpleRoot n i) =
      vecMulVec (typeBSimpleRoot n i) (typeBSimpleCoroot n i) := by
  by_cases hi : (i : ℕ) + 1 < n
  · simp [hi]
  · ext k l
    simp only [hi, not_false_eq_true, typeBSimpleCoroot_of_not_add_one_lt,
      typeBSimpleRoot_of_not_add_one_lt, vecMulVec_apply, Pi.single_apply]
    split_ifs <;> simp

end TauCeti.DynkinType
