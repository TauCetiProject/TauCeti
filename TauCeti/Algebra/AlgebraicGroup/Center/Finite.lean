/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Center.Reduced
public import TauCeti.RingTheory.FiniteType.Tensor.Product
public import TauCeti.Algebra.AlgebraicGroup.Connected.Comultiplication
import Mathlib.RingTheory.Finiteness.NilpotentKer
import TauCeti.Algebra.AlgebraicGroup.Connected.ComponentGroup.TrivialIdentity

/-!
# Finiteness of a center from its reduction

Let `H` be a finite-type commutative Hopf algebra over a field. Assuming
that the tensor square of the reduced center coordinate algebra is reduced, this file shows that
the center is finite once its reduction is finite. The quotient map from the center to its
reduction has nilradical kernel; finite type makes that kernel finitely generated, so finiteness
lifts through it.

Over an algebraically closed field, the reduced center is finite in particular when its identity
component is trivial. This is the algebraic last step in the standard proof that the center of a
semisimple affine group is finite: semisimplicity must still be used geometrically to trivialize
that identity component.

## Main declarations

* `moduleFinite_centerCoordinate_of_reducedCenter`: a center is finite when its reduction is
  finite and the tensor square of the reduced center coordinate algebra is reduced.
* `moduleFinite_centerCoordinate_of_reducedCenter_identityComponent_eq_augmentation`:
  over an algebraically closed field, a center is finite when its reduction has trivial identity
  component; no tensor-reducedness hypothesis is needed.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§1.f and 21.10.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §11.4.
-/

public section

open scoped TensorProduct

namespace TauCeti.FiniteTypeCommHopfAlgCat

universe u

variable {k : Type u} [Field k]
variable (H : FiniteTypeCommHopfAlgCat.{u, u} k)

/-- The center coordinate algebra modulo its nilradical is reduced. -/
local instance : IsReduced ((CommHopfAlgCat.centerCoordinateHopfAlgebra H.obj) ⧸
    nilradical (CommHopfAlgCat.centerCoordinateHopfAlgebra H.obj)) :=
  (Ideal.isRadical_iff_quotient_reduced _).mp (Ideal.radical_isRadical ⊥)

/-- Assuming that the tensor square of the reduced center coordinate algebra is reduced, a
finite-type affine group's center is finite when its reduced center is finite. -/
theorem moduleFinite_centerCoordinate_of_reducedCenter
    [IsReduced
      ((((CommHopfAlgCat.centerCoordinateHopfAlgebra H.obj :
            _root_.CommHopfAlgCat.{u} k) : Type u) ⧸
          nilradical
            ((CommHopfAlgCat.centerCoordinateHopfAlgebra H.obj :
              _root_.CommHopfAlgCat.{u} k) : Type u)) ⊗[k]
        (((CommHopfAlgCat.centerCoordinateHopfAlgebra H.obj :
            _root_.CommHopfAlgCat.{u} k) : Type u) ⧸
          nilradical ((CommHopfAlgCat.centerCoordinateHopfAlgebra H.obj :
            _root_.CommHopfAlgCat.{u} k) : Type u)))]
    [Module.Finite k (CommHopfAlgCat.reducedCenterCoordinateHopfAlgebra H.obj)] :
    Module.Finite k (CommHopfAlgCat.centerCoordinateHopfAlgebra H.obj) := by
  let C := CommHopfAlgCat.centerCoordinateHopfAlgebra H.obj
  let I := HopfIdeal.reduction k C
  let q : C →ₐ[k] CommHopfAlgCat.reducedCenterCoordinateHopfAlgebra H.obj :=
    (CommHopfAlgCat.mkQuotient C I).hom.toAlgHom
  have hker : RingHom.ker q = nilradical C := by
    calc
      RingHom.ker q =
          RingHom.ker (CommHopfAlgCat.mkQuotient C I).hom.toAlgHom.toRingHom := by
        rfl
      _ = I.toIdeal := CommHopfAlgCat.mkQuotient_ker C I
      _ = nilradical C := by
        simpa only [I] using HopfIdeal.reduction_toIdeal k C
  apply Module.finite_of_surjective_of_ker_le_nilradical q
    (CommHopfAlgCat.mkQuotient_surjective C I)
  · exact hker.le
  · rw [hker]
    exact IsNoetherian.noetherian _

/-- Over an algebraically closed field, a finite-type affine group's center is finite when
the identity component of its reduced center is the trivial subgroup scheme. -/
theorem
    moduleFinite_centerCoordinate_of_reducedCenter_identityComponent_eq_augmentation
    [IsAlgClosed k]
    (hidentity : HopfAlgebra.identityComponentHopfIdeal
        (k := k) (H := CommHopfAlgCat.reducedCenterCoordinateHopfAlgebra H.obj) =
      HopfIdeal.augmentation k (CommHopfAlgCat.reducedCenterCoordinateHopfAlgebra H.obj)) :
    Module.Finite k (CommHopfAlgCat.centerCoordinateHopfAlgebra H.obj) := by
  let Hred : FiniteTypeCommHopfAlgCat.{u, u} k :=
    of k (CommHopfAlgCat.reducedCenterCoordinateHopfAlgebra H.obj)
  let _ : Module.Finite k (CommHopfAlgCat.reducedCenterCoordinateHopfAlgebra H.obj) :=
    moduleFinite_of_identityComponentHopfIdeal_eq_augmentation Hred hidentity
  exact moduleFinite_centerCoordinate_of_reducedCenter H

end TauCeti.FiniteTypeCommHopfAlgCat
