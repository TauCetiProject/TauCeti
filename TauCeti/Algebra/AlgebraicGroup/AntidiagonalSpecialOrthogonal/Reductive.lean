/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.AntidiagonalSpecialOrthogonal.Congruence.Basic
public import TauCeti.Algebra.AlgebraicGroup.Reductive.Basic
import TauCeti.Algebra.AlgebraicGroup.ConstantForm.Special.Reductive

/-!
# Reductivity of `SO_l^J`

Let `R` be a commutative ring in which `2` is invertible and which contains a square root `i`
of `-1`. The coordinate Hopf algebra of `SO_l^J`, the determinant-one subgroup scheme of `GL_l`
preserving the antidiagonal form `J_l`, is isomorphic to that of the special orthogonal group
`SO_l` of the identity form
(`TauCeti.AntidiagonalSpecialOrthogonal.coordinateHopfAlgebraIsoSpecialOrthogonal`).

Over a field of characteristic different from two, reductivity of `SO_l^J` follows from
`TauCeti.ConstantForm.Special.reductiveCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra`,
since `J_l` is symmetric and has unit determinant.

## Main declarations

* `TauCeti.AntidiagonalSpecialOrthogonal.finiteTypeCoordinateHopfAlgebraIsoSpecialOrthogonal`:
  the isomorphism of finite-type coordinate Hopf algebras `O(SO_l^J) ≅ O(SO_l)`.
* `AntidiagonalSpecialOrthogonal.reductiveCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra`:
  `SO_l^J` is reductive over every field of characteristic different from two.
-/

public section

open CategoryTheory

namespace TauCeti.AntidiagonalSpecialOrthogonal

universe u

variable {R : Type u} [CommRing R] [Invertible (2 : R)] (l : ℕ) {i : R}

/-- The isomorphism `O(SO_l^J) ≅ O(SO_l)` of finite-type coordinate Hopf algebras, over a ring
containing `1/2` and a square root `i` of `-1`. -/
noncomputable def finiteTypeCoordinateHopfAlgebraIsoSpecialOrthogonal (hi : i * i = -1) :
    finiteTypeCoordinateHopfAlgebra R l ≅ SpecialOrthogonal.finiteTypeCoordinateHopfAlgebra R l :=
  ObjectProperty.isoMk _
    (eqToIso (ConstantForm.Special.finiteTypeCoordinateHopfAlgebra_obj R l (formMatrix R l)) ≪≫
    coordinateHopfAlgebraIsoSpecialOrthogonal l hi ≪≫
    eqToIso (SpecialOrthogonal.finiteTypeCoordinateHopfAlgebra_obj R l).symm)

/-- The isomorphism of finite-type coordinate Hopf algebras has the isomorphism of coordinate
Hopf algebras as its underlying isomorphism. -/
theorem finiteTypeCoordinateHopfAlgebraIsoSpecialOrthogonal_def (hi : i * i = -1) :
    finiteTypeCoordinateHopfAlgebraIsoSpecialOrthogonal l hi =
      ObjectProperty.isoMk _
        (eqToIso (ConstantForm.Special.finiteTypeCoordinateHopfAlgebra_obj R l (formMatrix R l)) ≪≫
        coordinateHopfAlgebraIsoSpecialOrthogonal l hi ≪≫
        eqToIso (SpecialOrthogonal.finiteTypeCoordinateHopfAlgebra_obj R l).symm) :=
  (rfl)

/-- **`SO_l^J` is reductive** over every field of characteristic different from two, whether or
not that field contains a square root of `-1`. -/
theorem reductiveCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra (k : Type u) [Field k]
    [NeZero (2 : k)] (l : ℕ) :
    reductiveCommHopfAlgProperty k (finiteTypeCoordinateHopfAlgebra k l) :=
  ConstantForm.Special.reductiveCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra
    (transpose_formMatrix k l) isUnit_det_formMatrix.ne_zero

end TauCeti.AntidiagonalSpecialOrthogonal
