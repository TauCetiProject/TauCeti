/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Solvable.Derived.Unipotent
public import TauCeti.Algebra.AlgebraicGroup.Reductive.Basic
import TauCeti.Algebra.Coalgebra.BaseChange

/-!
# Solvable reductive groups are commutative

A reductive affine group with solvable geometric points is commutative, over any field and
in every characteristic. Pass to an algebraic closure: the derived subgroup is connected,
normal, smooth, and unipotent, so reductivity makes it trivial. Cocommutativity of the coordinate
Hopf algebra then descends to the ground field.

This is the commutativity step in the classification of connected solvable reductive groups as
tori. It does not identify the character lattice or assert that the group splits over the
original field.

## References

* A. Borel, *Linear Algebraic Groups*, §11.
* J. S. Milne, *Algebraic Groups* (2017), §§16 and 19.
-/

public section

namespace TauCeti.reductiveCommHopfAlgProperty

open WithConv

universe u

variable {k : Type u} [Field k] {H : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- A solvable reductive affine group is commutative. Equivalently, its coordinate Hopf algebra
is cocommutative. No perfectness or characteristic assumption on the base field is needed. -/
theorem isCocomm_of_geometricallySolvable (hH : reductiveCommHopfAlgProperty k H)
    (hsolv : geometricallySolvablePointsCommHopfAlgProperty k H.obj) :
    _root_.Coalgebra.IsCocomm k H := by
  let K := AlgebraicClosure k
  let G := FiniteTypeCommHopfAlgCat.baseChange (K := K) H
  let _ : Algebra.Smooth k H := hH.smooth
  let _ : Algebra.Smooth K G := inferInstance
  let _ : IsReduced G := isReduced_of_smooth K G
  let _ : ConnectedSpace (PrimeSpectrum G) :=
    hH.geometricallyConnected.connectedSpace_algebraicClosureBaseChange
  let _ : Group.IsSolvable (WithConv (H →ₐ[k] K)) :=
    (geometricallySolvablePointsCommHopfAlgProperty_iff k H.obj).mp hsolv
  let e := (AlgHom.baseChangePointsMulEquiv (k := k) (K := K) (A := H) (R := K)).symm
  let _ : Group.IsSolvable (WithConv (G →ₐ[K] K)) :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  have hD := CommHopfAlgCat.isUnipotentRadicalCandidate_derived_of_isSolvable
    (k := K) (H := G)
  have htrivial := hH.eq_augmentation (CommHopfAlgCat.derivedDefiningIdeal G)
    hD.isNormal hD.geometricallyConnected hD.smoothUnipotent
  let _ : _root_.Coalgebra.IsCocomm K G :=
    (CommHopfAlgCat.derivedDefiningIdeal_eq_augmentation_iff_isCocomm G).mp htrivial
  exact Coalgebra.IsCocomm.of_baseChange (K := K)

end TauCeti.reductiveCommHopfAlgProperty
