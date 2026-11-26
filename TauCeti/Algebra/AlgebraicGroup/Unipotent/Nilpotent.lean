/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Embedding
public import TauCeti.Algebra.AlgebraicGroup.UpperUnitriangular.Nilpotent
import TauCeti.RepresentationTheory.Unipotent.Solvable

/-!
# Nilpotence of the rational points of a unipotent group

A finite-type affine group over any field whose rational points are all unipotent has a
nilpotent group of rational points. A faithful finite-dimensional representation and Kolchin's
theorem embed the rational points into an upper-unitriangular matrix group.

For a reduced group over an algebraically closed field, a separate coordinate-algebra argument
allows the field and coordinate ring to lie in independent universes: precomposition with a
surjective coordinate map from `O(U_n)` injects the rational points into the nilpotent group
`U_n(k)`.

## Main declarations

* `TauCeti.HopfAlgebra.isNilpotent_points_of_forall_isUnipotentPoint`: the group of rational
  points of a finite-type affine group with unipotent rational points is nilpotent.
* `TauCeti.HopfAlgebra.isNilpotent_points_of_forall_isUnipotentPoint_of_isAlgClosed`: the
  independent-universe version for reduced groups over an algebraically closed field.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 14.21: a unipotent group is nilpotent.
* A. Borel, *Linear Algebraic Groups*, §4.8.
-/

public section

namespace TauCeti.HopfAlgebra

open WithConv

universe u

/-- The rational points of a finite-type affine group over any field are nilpotent if every
rational point is unipotent. No reducedness hypothesis is required. -/
theorem isNilpotent_points_of_forall_isUnipotentPoint
    {k H : Type u} [Field k] [CommRing H] [_root_.HopfAlgebra k H]
    [Algebra.FiniteType k H]
    (hH : ∀ g : WithConv (H →ₐ[k] k), IsUnipotentPoint g) :
    Group.IsNilpotent (WithConv (H →ₐ[k] k)) := by
  classical
  obtain ⟨M, n, b, hb⟩ :=
    Comodule.exists_isClosedImmersion_coordinateGroupSchemeHom (k := k) (H := H)
  let _ : AddCommGroup M := Module.addCommMonoidToAddCommGroup k
  let _ : Module.Finite k M := Module.Finite.of_basis b
  have hfaithful : Comodule.IsFaithful (k := k) (H := H) (V := M) :=
    (Comodule.isFaithful_iff_isClosedImmersion_coordinateGroupSchemeHom b).mpr hb
  let rho := Comodule.pointsRepresentation (R := k) (H := H) (A := k) M
  apply rho.isNilpotent_of_injective_of_isUnipotent
  · intro g h hgh
    apply Comodule.pointsAction_injective_of_isFaithful hfaithful
    have hrho : rho g = rho h := by
      simpa only [Representation.asGroupHom_apply] using congrArg Units.val hgh
    apply LinearEquiv.ext
    intro x
    exact LinearMap.congr_fun (by
      simpa only [Comodule.pointsAction_toLinearMap, rho,
        Comodule.pointsRepresentation_apply] using hrho) x
  · intro g
    exact (hH g).isNilpotent_pointsRepresentation_sub_one
      (FGComoduleCat.of (R := k) (C := H) M)

variable {k H : Type*} [Field k] [CommRing H] [_root_.HopfAlgebra k H]

/-- **The rational points of a unipotent group are nilpotent.** A reduced finite-type affine group
over an algebraically closed field whose rational points are all unipotent has a nilpotent group
of rational points. The field and coordinate ring may lie in independent universes. -/
theorem isNilpotent_points_of_forall_isUnipotentPoint_of_isAlgClosed
    [IsAlgClosed k] [Algebra.FiniteType k H] [IsReduced H]
    (hH : ∀ g : WithConv (H →ₐ[k] k), IsUnipotentPoint g) :
    Group.IsNilpotent (WithConv (H →ₐ[k] k)) := by
  obtain ⟨M, n, b, hb, hsurj⟩ :=
    Comodule.exists_coordinateBialgHom_surjective_of_forall_isUnipotentPoint hH
  let f := Comodule.upperUnitriangularCoordinateBialgHom (H := H) b hb
  have hf : Function.Surjective f :=
    Comodule.upperUnitriangularCoordinateBialgHom_surjective_of_coordinateBialgHom_surjective
      b hb hsurj
  have := UpperUnitriangular.isNilpotent_points k (Fin n) k
  let ι : WithConv (H →ₐ[k] k) →*
      WithConv (UpperUnitriangular.coordinateHopfAlgebra k (Fin n) →ₐ[k] k) :=
    BialgHom.mapDomain f
  refine Subgroup.isNilpotent_of_ker_le_center ι ?_
  rw [(MonoidHom.ker_eq_bot_iff ι).mpr (BialgHom.mapDomain_injective_of_surjective f hf)]
  exact bot_le

end TauCeti.HopfAlgebra
