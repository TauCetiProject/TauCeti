/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Center.Reduced
public import TauCeti.Algebra.AlgebraicGroup.Connected.GroupScheme
import Mathlib.RingTheory.Finiteness.NilpotentKer
import TauCeti.Algebra.AlgebraicGroup.Connected.ComponentGroup.TrivialIdentity

/-!
# Finiteness of a center from its reduction

Let `H` be a finite-type commutative Hopf algebra over an algebraically closed field. Assuming
that the tensor square of the reduced center coordinate algebra is reduced, this file shows that
the center is finite once its reduction is finite. The quotient map from the center to its
reduction has nilradical kernel; finite type makes that kernel finitely generated, so finiteness
lifts through it.

The reduced center is finite in particular when its identity component is trivial. This is the
algebraic last step in the standard proof that the center of a semisimple affine group is finite:
semisimplicity must still be used geometrically to trivialize that identity component.

## Main declarations

* `moduleFinite_centerCoordinate_of_reducedCenter_identityComponent_eq_augmentation`:
  a center is finite when its reduction has trivial identity component and the tensor square of
  the reduced center coordinate algebra is reduced.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§1.f and 21.10.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §11.4.
-/

public section

open scoped TensorProduct

namespace TauCeti.CommHopfAlgCat

universe u

variable {k : Type u} [Field k]
variable (H : FiniteTypeCommHopfAlgCat.{u, u} k)

variable [IsReduced
  ((((centerCoordinateHopfAlgebra H.obj : _root_.CommHopfAlgCat.{u} k) : Type u) ⧸
      nilradical
        ((centerCoordinateHopfAlgebra H.obj : _root_.CommHopfAlgCat.{u} k) : Type u)) ⊗[k]
    (((centerCoordinateHopfAlgebra H.obj : _root_.CommHopfAlgCat.{u} k) : Type u) ⧸
      nilradical ((centerCoordinateHopfAlgebra H.obj : _root_.CommHopfAlgCat.{u} k) : Type u)))]

/-- Assuming that the tensor square of the reduced center coordinate algebra is reduced, a
finite-type affine group's center is finite when the identity component of its reduced center is
the trivial subgroup scheme. -/
theorem
    moduleFinite_centerCoordinate_of_reducedCenter_identityComponent_eq_augmentation
    [IsAlgClosed k]
    (hidentity : HopfAlgebra.identityComponentHopfIdeal
        (k := k) (H := reducedCenterCoordinateHopfAlgebra H.obj) =
      HopfIdeal.augmentation k (reducedCenterCoordinateHopfAlgebra H.obj)) :
    Module.Finite k (centerCoordinateHopfAlgebra H.obj) := by
  let Hred : FiniteTypeCommHopfAlgCat.{u, u} k :=
    FiniteTypeCommHopfAlgCat.of k (reducedCenterCoordinateHopfAlgebra H.obj)
  let _ : Module.Finite k (reducedCenterCoordinateHopfAlgebra H.obj) :=
    FiniteTypeCommHopfAlgCat.moduleFinite_of_identityComponentHopfIdeal_eq_augmentation
      Hred hidentity
  let C := centerCoordinateHopfAlgebra H.obj
  let I := HopfIdeal.reduction k C
  let q : C →ₐ[k] reducedCenterCoordinateHopfAlgebra H.obj :=
    (mkQuotient C I).hom.toAlgHom
  have hker : RingHom.ker q = nilradical C := by
    rw [show RingHom.ker q = I.toIdeal by
      exact mkQuotient_ker C I, HopfIdeal.reduction_toIdeal]
  apply Module.finite_of_surjective_of_ker_le_nilradical q
    (mkQuotient_surjective C I)
  · exact hker.le
  · rw [hker]
    exact IsNoetherian.noetherian _

end TauCeti.CommHopfAlgCat
