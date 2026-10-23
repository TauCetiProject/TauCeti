/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic

/-!
# Row primitivity of the Bourbaki type-`G₂` Cartan matrix

Bourbaki's type-`G₂` Cartan matrix is the transpose of Mathlib's `CartanMatrix.G₂`, and its rows
are the characters through which the two Cartan generators of type `G₂` act on the numbered simple
root generators. This file shows that both rows are primitive integer vectors, with explicit Bezout
coefficients: the short row `(2, -1)` pairs to `1` with `(0, -1)`, while the long row `(-3, 2)` has
no entry `-1` and instead pairs to `1` with `(-1, -1)`.

Row primitivity says that each simple root of type `G₂` is a primitive character of a split torus
whose weights are those rows. It is the arithmetic hypothesis in
`TauCeti.UniversalEnvelopingAlgebra.kostantTorusSubgroup_le_kostantElementarySubgroup`, so it is
shared by every carrier built on the type-`G₂` Serre presentation.

## Main declarations

* `TauCeti.typeG2CartanBezout` and
  `TauCeti.sum_transpose_cartanMatrixG2_mul_typeG2CartanBezout`: the explicit Bezout certificate
  for each row of the Bourbaki type-`G₂` Cartan matrix.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IX.
* `TauCeti.LinearAlgebra.Matrix.Cartan.TypeB`, whose type-`B` certificate this file mirrors.
-/

public section

open scoped Matrix

namespace TauCeti

/-- Integer coefficients pairing to `1` with the `i`-th row of the Bourbaki type-`G₂` Cartan
matrix: `(0, -1)` against the short row `(2, -1)`, and `(-1, -1)` against the long row
`(-3, 2)`. -/
def typeG2CartanBezout (i j : Fin 2) : ℤ :=
  if i = 0 then (if j = 1 then -1 else 0) else -1

@[simp]
theorem typeG2CartanBezout_apply (i j : Fin 2) :
    typeG2CartanBezout i j = if i = 0 then (if j = 1 then -1 else 0) else -1 :=
  (rfl)

/-- Every row of the Bourbaki type-`G₂` Cartan matrix is a primitive integer vector, with the
explicit certificate `typeG2CartanBezout`. -/
theorem sum_transpose_cartanMatrixG2_mul_typeG2CartanBezout (i : Fin 2) :
    ∑ j, CartanMatrix.G₂ᵀ i j * typeG2CartanBezout i j = 1 := by
  fin_cases i <;> decide

end TauCeti
