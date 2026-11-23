/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Norm
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic
import Mathlib.Algebra.CharP.Invertible
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Polar

/-!
# The orthogonal group of an integral lattice

The orthogonal group `O(V)` of the rational quadratic space of an integral lattice `L` is that of
its norm form `L.norm`. Since `L.norm` is the quadratic form `x ↦ B x x` of the symmetric rational
form `B` of `L`, and `2` is invertible in `ℚ`, this is the isometry group of `B` itself.

## Main results

* `TauCeti.IntegralLattice.orthogonalGroup_norm`: the orthogonal group of the rational norm form
  is the isometry group of the rational form.
-/

public section

namespace TauCeti

namespace IntegralLattice

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- The orthogonal group of the norm form of `L` is the isometry group of its rational form. -/
theorem orthogonalGroup_norm (L : IntegralLattice V) :
    QuadraticMap.orthogonalGroup L.norm = L.form.isometryGroup := by
  rw [norm_def]
  exact QuadraticMap.orthogonalGroup_toQuadraticMap_eq_isometryGroup
    ((isUnit_of_invertible (2 : ℚ)).isSMulRegular ℚ) L.isSymm

end IntegralLattice

end TauCeti
