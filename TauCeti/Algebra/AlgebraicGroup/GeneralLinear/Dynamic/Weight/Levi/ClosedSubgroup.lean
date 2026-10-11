/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Dynamic.ClosedImmersion
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Dynamic.Weight.Levi.Basic

/-!
# Levis of closed subgroups of a general linear group

Let a closed subgroup of `GL_N` carry a cocharacter whose composite with the inclusion is the
weight cocharacter `t ↦ diag(t ^ w i)`. The dynamic Levi of the subgroup is represented by the
image, in its coordinate Hopf algebra, of the weight-Levi ideal of `GL_N`. Its points over every
commutative algebra are precisely the subgroup's points that preserve the weight spaces.

This includes nonreduced closed subgroups and nonreduced value algebras. It supplies a concrete
closed-subgroup step for constructing dynamic Levis from faithful representations.

## Main result

* `TauCeti.GeneralLinear.Dynamic.mem_weightLeviImagePointsSubgroup_iff`: the image ideal cuts
  out the dynamic Levi of the closed subgroup.
* `TauCeti.GeneralLinear.Dynamic.weightLeviClosedSubgroupPointsIso`: the resulting natural
  representing isomorphism.

## References

* G. R. Kempf, *Instability in invariant theory*, Annals of Mathematics 108 (1978), §2.
-/

public section

open CategoryTheory

namespace TauCeti.GeneralLinear.Dynamic

universe u v

variable {R : Type u} [CommRing R] {N : ℕ}
variable {K : _root_.CommHopfAlgCat.{u} R}

/-- A closed subgroup of `GL_N` with a weight cocharacter has dynamic Levi cut out by the
image of the weight-Levi ideal. -/
theorem mem_weightLeviImagePointsSubgroup_iff (w : Fin N → ℤ)
    (φ : coordinateHopfAlgebra R N ⟶ K) (hφ : Function.Surjective φ.hom)
    (l : K →ₐc[R] LaurentPolynomial R)
    (hl : l.comp φ.hom = weightCocharacter (R := R) w)
    (A : CommAlgCat.{v} R) (g : HopfAlgebra.points (R := R) (H := K) A) :
    g ∈ CommHopfAlgCat.quotientPointsSubgroup K
        ((weightLeviDefiningHopfIdeal R w).map φ.hom) A ↔
      g ∈ Cocharacter.levi A l :=
  Cocharacter.mem_quotientPointsSubgroup_map_iff_mem_levi φ hφ l _ A
    (fun g ↦ by rw [hl]; exact mem_weightLeviDefiningPointsSubgroup_iff (R := R) w g) g

/-- The quotient by the image of the ambient weight-Levi ideal represents the dynamic Levi of
the closed subgroup, naturally in the commutative value algebra. -/
noncomputable def weightLeviClosedSubgroupPointsIso (w : Fin N → ℤ)
    (φ : coordinateHopfAlgebra R N ⟶ K) (hφ : Function.Surjective φ.hom)
    (l : K →ₐc[R] LaurentPolynomial R)
    (hl : l.comp φ.hom = weightCocharacter (R := R) w) :
    HopfAlgebra.pointsFunctor (R := R)
        (H := CommHopfAlgCat.quotient K ((weightLeviDefiningHopfIdeal R w).map φ.hom)) ≅
      Cocharacter.leviFunctor l :=
  Cocharacter.leviClosedSubgroupPointsIso φ hφ l _
    (fun _ g ↦ by rw [hl]; exact mem_weightLeviDefiningPointsSubgroup_iff (R := R) w g)

/-- The ambient point underlying the represented closed-subgroup Levi point is induced by the
quotient coordinate map. -/
@[simp]
theorem coe_weightLeviClosedSubgroupPointsIso_hom_app_apply (w : Fin N → ℤ)
    (φ : coordinateHopfAlgebra R N ⟶ K) (hφ : Function.Surjective φ.hom)
    (l : K →ₐc[R] LaurentPolynomial R)
    (hl : l.comp φ.hom = weightCocharacter (R := R) w)
    (A : CommAlgCat.{v} R)
    (f : HopfAlgebra.points (R := R)
      (H := CommHopfAlgCat.quotient K ((weightLeviDefiningHopfIdeal R w).map φ.hom)) A) :
    (((eqToHom (Cocharacter.leviFunctor_obj l A))
      ((weightLeviClosedSubgroupPointsIso w φ hφ l hl).hom.app A f) :
        Cocharacter.levi A l) : HopfAlgebra.points (R := R) (H := K) A) =
      CommHopfAlgCat.quotientPointsHom K ((weightLeviDefiningHopfIdeal R w).map φ.hom) A f := by
  unfold weightLeviClosedSubgroupPointsIso
  exact Cocharacter.coe_leviClosedSubgroupPointsIso_hom_app_apply φ hφ l _
    (fun _ g ↦ by rw [hl]; exact mem_weightLeviDefiningPointsSubgroup_iff (R := R) w g) A f

/-- Applying the quotient inclusion to the inverse represented point recovers the dynamic-Levi
point. -/
@[simp]
theorem quotientPointsHom_weightLeviClosedSubgroupPointsIso_inv_app_apply (w : Fin N → ℤ)
    (φ : coordinateHopfAlgebra R N ⟶ K) (hφ : Function.Surjective φ.hom)
    (l : K →ₐc[R] LaurentPolynomial R)
    (hl : l.comp φ.hom = weightCocharacter (R := R) w)
    (A : CommAlgCat.{v} R) (g : Cocharacter.levi A l) :
    CommHopfAlgCat.quotientPointsHom K ((weightLeviDefiningHopfIdeal R w).map φ.hom) A
      ((weightLeviClosedSubgroupPointsIso w φ hφ l hl).inv.app A g) = g.1 := by
  unfold weightLeviClosedSubgroupPointsIso
  exact Cocharacter.quotientPointsHom_leviClosedSubgroupPointsIso_inv_app_apply φ hφ l _
    (fun _ g ↦ by rw [hl]; exact mem_weightLeviDefiningPointsSubgroup_iff (R := R) w g) A g

end TauCeti.GeneralLinear.Dynamic
