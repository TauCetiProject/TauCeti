/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic

/-!
# Row primitivity of the type-`F₄` Cartan matrix

Every row of `CartanMatrix.F₄` contains an entry `-1`, at a node adjacent to the row's node in
the Dynkin diagram: node `0` uses its successor `1`, and nodes `1`, `2` and `3` use their
predecessor. The double bond joins nodes `1` and `2`, contributing `-2` in row `1` and `-1` in
row `2`, so row `1` is the one that has to look away from the bond.

Row primitivity says that each simple root of type `F₄` is a primitive character of a split torus
whose weights are those rows. It is the arithmetic hypothesis in
`TauCeti.UniversalEnvelopingAlgebra.kostantTorusSubgroup_le_kostantElementarySubgroup`, so it is
shared by every carrier built on the type-`F₄` Serre presentation.

## Main declarations

* `TauCeti.typeF4CartanBezout` and `TauCeti.sum_cartanMatrixF4_mul_typeF4CartanBezout`: the
  explicit Bezout certificate for each row of the type-`F₄` Cartan matrix.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate VIII.
* `TauCeti.LinearAlgebra.Matrix.Cartan.TypeG2`, the companion certificate for the other
  multiply-laced exceptional diagram, whose formal template this file follows.
-/

public section

namespace TauCeti

/-- Integer coefficients pairing to `1` with the `i`-th row of the type-`F₄` Cartan matrix:
`-1` at the neighbouring node `![1, 0, 1, 2] i`, where the row has entry `-1`, and `0`
elsewhere. -/
def typeF4CartanBezout (i j : Fin 4) : ℤ :=
  if j = ![1, 0, 1, 2] i then -1 else 0

@[simp]
theorem typeF4CartanBezout_apply (i j : Fin 4) :
    typeF4CartanBezout i j = if j = ![1, 0, 1, 2] i then -1 else 0 :=
  (rfl)

/-- Every row of the type-`F₄` Cartan matrix is a primitive integer vector, with the explicit
certificate `typeF4CartanBezout`. -/
theorem sum_cartanMatrixF4_mul_typeF4CartanBezout (i : Fin 4) :
    ∑ j, CartanMatrix.F₄ i j * typeF4CartanBezout i j = 1 := by
  fin_cases i <;> decide

end TauCeti
