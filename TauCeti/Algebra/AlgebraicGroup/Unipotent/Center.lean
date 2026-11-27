/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Center.Connected
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Commutative
import TauCeti.Algebra.AlgebraicGroup.Center.Nilpotent
import TauCeti.Algebra.AlgebraicGroup.Connected.AlgebraicallyClosed
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Vanishing
import TauCeti.Algebra.AlgebraicGroup.Unipotent.ClosedSubgroup

/-!
# The centre of a unipotent group

Let `U` be a unipotent closed subgroup of a finite-type affine group over an algebraically closed
field `k`, cut out by a Hopf ideal `I`, and let `Z(U)°_red` be its reduced connected centre, cut
out by `I.reducedConnectedCenter`. This file shows:

* `Z(U)°_red` is smooth and unipotent;
* in characteristic zero, `Z(U)°_red` is a vector group, the spectrum of the symmetric algebra on
  the primitive elements of its coordinate ring;
* when `U` is reduced and connected, `Z(U)°_red` is nontrivial as soon as `U` is: a nontrivial
  reduced connected unipotent group has nilpotent rational points, hence a nontrivial smooth
  connected central subgroup, which lies in its reduced connected centre.

## Main declarations

* `TauCeti.HopfIdeal.smoothUnipotent_reducedConnectedCenter`: the reduced connected centre of a
  unipotent closed subgroup is smooth and unipotent.
* `TauCeti.HopfIdeal.liftBialgHom_primitive_bijective_reducedConnectedCenter`: in characteristic
  zero, it is a vector group.
* `TauCeti.HopfIdeal.reducedConnectedCenter_eq_augmentation_iff_of_geometricallyUnipotent`: the
  reduced connected centre of a reduced connected unipotent closed subgroup is trivial exactly
  when the subgroup is.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 14.21 for the nilpotence of unipotent
  groups and §14.c for commutative unipotent groups in characteristic zero.
* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), §10.6.
-/

public section

open CategoryTheory WithConv

namespace TauCeti

universe u

noncomputable section

variable {k : Type u} [Field k] [IsAlgClosed k]

namespace HopfIdeal

variable {H : FiniteTypeCommHopfAlgCat.{u, u} k} {I : HopfIdeal k H}

/-- The reduced connected centre of a unipotent closed subgroup is unipotent. -/
private theorem geometricallyUnipotent_reducedConnectedCenter
    (hI : geometricallyUnipotentPointsCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient H I).obj) :
    geometricallyUnipotentPointsCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient H I.reducedConnectedCenter).obj :=
  geometricallyUnipotentPointsCommHopfAlgProperty_of_surjective k
    (CommHopfAlgCat.quotientMapOfLe H.obj I.le_reducedConnectedCenter)
    (CommHopfAlgCat.quotientMapOfLe_surjective _ _) hI

/-- **The reduced connected centre of a unipotent closed subgroup is smooth and unipotent.** Over
an algebraically closed field, if every geometric point of the closed subgroup cut out by `I` is
unipotent, the reduced connected centre of that subgroup is a smooth unipotent group. -/
theorem smoothUnipotent_reducedConnectedCenter
    (hI : geometricallyUnipotentPointsCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient H I).obj) :
    smoothUnipotentCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient H I.reducedConnectedCenter) :=
  (smoothUnipotentCommHopfAlgProperty_iff k _).mpr ⟨smooth_reducedConnectedCenter I,
    (geometricallyUnipotentPointsCommHopfAlgProperty_iff k _).mp
      (geometricallyUnipotent_reducedConnectedCenter hI)⟩

/-- **The reduced connected centre of a unipotent group is a vector group in characteristic
zero.** Over an algebraically closed field of characteristic zero, if every geometric point of
the closed subgroup cut out by `I` is unipotent, the symmetric algebra on the primitive elements
of the coordinate Hopf algebra of its reduced connected centre maps bijectively onto it. -/
theorem liftBialgHom_primitive_bijective_reducedConnectedCenter [CharZero k]
    (hI : geometricallyUnipotentPointsCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient H I).obj) :
    Function.Bijective (SymmetricAlgebra.liftBialgHom
      (Coalgebra.skewPrimitive k (1 : H ⧸ I.reducedConnectedCenter.toIdeal) 1).subtype
      fun p ↦ p.property) :=
  HopfAlgebra.liftBialgHom_primitive_bijective_of_forall_isUnipotentPoint
    (geometricallyUnipotent_reducedConnectedCenter hI).forall_isUnipotentPoint

/-- **The centre of a nontrivial connected unipotent group is nontrivial.** Over an
algebraically closed field, if the closed subgroup cut out by `I` is reduced and geometrically
connected and all its geometric points are unipotent, its reduced connected centre is trivial
exactly when the subgroup is trivial. -/
theorem reducedConnectedCenter_eq_augmentation_iff_of_geometricallyUnipotent
    [IsReduced (FiniteTypeCommHopfAlgCat.quotient H I)]
    (hconn : geometricallyConnectedCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient H I).obj)
    (hI : geometricallyUnipotentPointsCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient H I).obj) :
    I.reducedConnectedCenter = augmentation k H ↔ I = augmentation k H := by
  refine ⟨fun h ↦ ?_, fun h ↦ le_antisymm (le_augmentation k H _)
    (h ▸ le_reducedConnectedCenter _)⟩
  by_contra hne
  -- The subgroup `U` cut out by `I` is a nontrivial reduced connected unipotent group.
  let U := FiniteTypeCommHopfAlgCat.quotient H I
  have : ConnectedSpace (PrimeSpectrum U) := hconn.connectedSpace
  have : Nontrivial (WithConv (U →ₐ[k] k)) := by
    rw [← not_subsingleton_iff_nontrivial, ← augmentation_eq_bot_iff_subsingleton,
      augmentation_quotient_eq_bot_iff]
    exact hne
  -- So `U` has a nontrivial smooth connected central subgroup, which lies in its reduced
  -- connected centre.
  obtain ⟨J, hJc, hJne, hJp⟩ :=
    exists_isCentral_isPrime_ne_augmentation_of_forall_isUnipotentPoint hI.forall_isUnipotentPoint
  have : IsDomain (U ⧸ J.toIdeal) := Ideal.Quotient.isDomain _
  have hle := FiniteTypeCommHopfAlgCat.reducedConnectedCenterDefiningIdeal_le_of_isCentral U hJc
    ((geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace k _).mpr inferInstance)
  rw [reducedConnectedCenter_eq_augmentation_iff] at h
  exact hJne (le_antisymm (le_augmentation k U J) (h ▸ hle))

end HopfIdeal

end

end TauCeti
