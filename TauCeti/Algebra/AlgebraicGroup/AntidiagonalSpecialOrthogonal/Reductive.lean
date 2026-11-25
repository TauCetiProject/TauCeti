/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.AntidiagonalSpecialOrthogonal.Congruence
public import TauCeti.Algebra.AlgebraicGroup.Reductive.Basic
import Mathlib.RingTheory.Etale.Descent
import TauCeti.Algebra.AlgebraicGroup.Smooth.BaseChange
import TauCeti.Algebra.AlgebraicGroup.SpecialOrthogonal.Reductive
import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Reductive.Basic

/-!
# Reductivity of `SO_l^J`

Let `R` be a commutative ring in which `2` is invertible and which contains a square root `i`
of `-1`. The coordinate Hopf algebra of `SO_l^J`, the determinant-one subgroup scheme of `GL_l`
preserving the antidiagonal form `J_l`, is isomorphic to that of the special orthogonal group
`SO_l` of the identity form
(`TauCeti.AntidiagonalSpecialOrthogonal.coordinateHopfAlgebraIsoSpecialOrthogonal`).

Now let `k` be a field of characteristic different from two. Its algebraic closure `K` contains a
square root of `-1`, so the geometric fibre of `SO_l^J` is isomorphic to `SO_l` over `K`, which
is reductive
(`TauCeti.SpecialOrthogonal.reductiveCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra`).
Reductivity is tested on the geometric fibre, so `SO_l^J` is reductive over `k`, whether or not `k`
itself contains a square root of `-1`.

## Main declarations

* `TauCeti.AntidiagonalSpecialOrthogonal.finiteTypeCoordinateHopfAlgebraIsoSpecialOrthogonal`:
  the isomorphism of finite-type coordinate Hopf algebras `O(SO_l^J) ≅ O(SO_l)`.
* `AntidiagonalSpecialOrthogonal.reductiveCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra`:
  `SO_l^J` is reductive over every field of characteristic different from two.
-/

public section

open CategoryTheory

open scoped TensorProduct

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

/-- **`SO_l^J` is reductive** over every field of characteristic different from two.

An algebraic closure `K` of `k` contains a square root of `-1`, so the geometric fibre of `SO_l^J`
is isomorphic to `SO_l` over `K`, which is reductive. Smoothness, geometric connectedness and
triviality of the geometric unipotent radical then descend from `K` to `k`. -/
theorem reductiveCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra (k : Type u) [Field k]
    [NeZero (2 : k)] (l : ℕ) :
    reductiveCommHopfAlgProperty k (finiteTypeCoordinateHopfAlgebra k l) := by
  let K := AlgebraicClosure k
  let _ : NeZero (2 : K) := ⟨by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap k K)).2 (NeZero.ne (2 : k))⟩
  let _ : Invertible (2 : K) := invertibleOfNonzero (NeZero.ne _)
  obtain ⟨i, hi⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : K) two_pos
  have hK : reductiveCommHopfAlgProperty K
      (FiniteTypeCommHopfAlgCat.baseChange (K := K) (finiteTypeCoordinateHopfAlgebra k l)) :=
    (reductiveCommHopfAlgProperty K).prop_of_iso
      ((finiteTypeCoordinateHopfAlgebraIsoSpecialOrthogonal l (by rw [← hi, sq])).symm ≪≫
        (finiteTypeCoordinateHopfAlgebraBaseChangeIso k l K).symm)
      (SpecialOrthogonal.reductiveCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra K l)
  let _ : Algebra.Smooth K (K ⊗[k] (finiteTypeCoordinateHopfAlgebra k l).obj) :=
    FiniteTypeCommHopfAlgCat.smooth_baseChange_obj hK.smooth
  exact (reductiveCommHopfAlgProperty_iff_unipotentRadicalDefiningIdeal_baseChange_eq_augmentation
      k _).2
    ⟨Algebra.Smooth.of_smooth_tensorProduct_of_faithfullyFlat (R := k)
        (S := (finiteTypeCoordinateHopfAlgebra k l).obj) K,
      geometricallyConnectedCommHopfAlgProperty.of_baseChange k K _ hK.geometricallyConnected,
      hK.unipotentRadicalDefiningIdeal_eq_augmentation⟩

end TauCeti.AntidiagonalSpecialOrthogonal
