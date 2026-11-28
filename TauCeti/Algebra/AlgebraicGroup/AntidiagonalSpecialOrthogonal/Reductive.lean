/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.AntidiagonalSpecialOrthogonal.Basic
public import TauCeti.Algebra.AlgebraicGroup.Reductive.Basic
import TauCeti.Algebra.AlgebraicGroup.ConstantForm.Special.Reductive

/-!
# Reductivity of `SO_l^J`

Over a field of characteristic different from two, reductivity of `SO_l^J` follows from
`TauCeti.ConstantForm.Special.reductiveCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra`,
since `J_l` is symmetric and has unit determinant.
-/

public section

namespace TauCeti.AntidiagonalSpecialOrthogonal

universe u

/-- **`SO_l^J` is reductive** over every field of characteristic different from two, whether or
not that field contains a square root of `-1`. -/
theorem reductiveCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra (k : Type u) [Field k]
    [NeZero (2 : k)] (l : ℕ) :
    reductiveCommHopfAlgProperty k (finiteTypeCoordinateHopfAlgebra k l) := by
  rw [finiteTypeCoordinateHopfAlgebra_eq_special]
  exact ConstantForm.Special.reductiveCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra
    (transpose_formMatrix k l) isUnit_det_formMatrix.ne_zero

end TauCeti.AntidiagonalSpecialOrthogonal
