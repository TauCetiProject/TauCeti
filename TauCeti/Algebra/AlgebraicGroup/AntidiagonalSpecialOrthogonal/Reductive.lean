/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.AntidiagonalSpecialOrthogonal.Congruence
public import TauCeti.Algebra.AlgebraicGroup.Reductive.Basic
import TauCeti.Algebra.AlgebraicGroup.SpecialOrthogonal.Reductive

/-!
# Reductivity of `SO_l^J`

Let `k` be a field of characteristic different from two containing a square root `i` of `-1`.
The coordinate Hopf algebra of `SO_l^J`, the determinant-one subgroup scheme of `GL_l` preserving
the antidiagonal form `J_l`, is isomorphic to that of the special orthogonal group `SO_l` of the
identity form (`TauCeti.AntidiagonalSpecialOrthogonal.coordinateHopfAlgebraIsoSpecialOrthogonal`).
Reductivity is a property of isomorphism classes of finite-type Hopf algebras, and `SO_l` is
reductive over every field of characteristic different from two
(`TauCeti.SpecialOrthogonal.reductiveCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra`), so
`SO_l^J` is reductive over `k`. Every algebraically closed field contains such an `i`.

## Main declarations

* `TauCeti.AntidiagonalSpecialOrthogonal.finiteTypeCoordinateHopfAlgebraIsoSpecialOrthogonal`:
  the isomorphism of finite-type coordinate Hopf algebras `O(SO_l^J) ≅ O(SO_l)`.
* `AntidiagonalSpecialOrthogonal.reductiveCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra`:
  `SO_l^J` is reductive over a field of characteristic different from two containing `√-1`.
* `TauCeti.AntidiagonalSpecialOrthogonal.reductiveCommHopfAlgProperty_of_isAlgClosed`: `SO_l^J`
  is reductive over every algebraically closed field of characteristic different from two.
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
  ObjectProperty.isoMk _ (eqToIso (finiteTypeCoordinateHopfAlgebra_obj R l) ≪≫
    coordinateHopfAlgebraIsoSpecialOrthogonal l hi ≪≫
    eqToIso (SpecialOrthogonal.finiteTypeCoordinateHopfAlgebra_obj R l).symm)

/-- The isomorphism of finite-type coordinate Hopf algebras has the isomorphism of coordinate
Hopf algebras as its underlying isomorphism. -/
theorem finiteTypeCoordinateHopfAlgebraIsoSpecialOrthogonal_def (hi : i * i = -1) :
    finiteTypeCoordinateHopfAlgebraIsoSpecialOrthogonal l hi =
      ObjectProperty.isoMk _ (eqToIso (finiteTypeCoordinateHopfAlgebra_obj R l) ≪≫
        coordinateHopfAlgebraIsoSpecialOrthogonal l hi ≪≫
        eqToIso (SpecialOrthogonal.finiteTypeCoordinateHopfAlgebra_obj R l).symm) :=
  (rfl)

/-- **`SO_l^J` is reductive** over a field of characteristic different from two that contains a
square root of `-1`. -/
theorem reductiveCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra (k : Type u) [Field k]
    [NeZero (2 : k)] {i : k} (hi : i * i = -1) (l : ℕ) :
    reductiveCommHopfAlgProperty k (finiteTypeCoordinateHopfAlgebra k l) :=
  let _ : Invertible (2 : k) := invertibleOfNonzero (NeZero.ne _)
  (reductiveCommHopfAlgProperty k).prop_of_iso
    (finiteTypeCoordinateHopfAlgebraIsoSpecialOrthogonal l hi).symm
    (SpecialOrthogonal.reductiveCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra k l)

/-- **`SO_l^J` is reductive over every algebraically closed field of characteristic different from
two.** -/
theorem reductiveCommHopfAlgProperty_of_isAlgClosed (k : Type u) [Field k] [IsAlgClosed k]
    [NeZero (2 : k)] (l : ℕ) :
    reductiveCommHopfAlgProperty k (finiteTypeCoordinateHopfAlgebra k l) := by
  obtain ⟨i, hi⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : k) two_pos
  exact reductiveCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra k (by rw [← hi, sq]) l

end TauCeti.AntidiagonalSpecialOrthogonal
