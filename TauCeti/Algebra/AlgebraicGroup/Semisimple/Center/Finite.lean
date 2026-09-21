/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Semisimple.Center.Basic
import TauCeti.Algebra.AlgebraicGroup.Center.Finite
import TauCeti.Algebra.AlgebraicGroup.Center.Descent
import TauCeti.Algebra.AlgebraicGroup.Smooth.IdentityComponent

/-!
# The center of a semisimple group is finite

The scheme-theoretic center of a semisimple affine group is finite over its ground field,
including in positive characteristic, where it can be nonreduced. This is the finiteness
input for the central isogeny from a semisimple group to its adjoint form.

Over the algebraic closure, the reduced center is smooth. Its identity component is a smooth
connected central subgroup of the ambient semisimple group, hence trivial. Finiteness of
the component group and of the nilpotent thickening then gives finiteness of the full center;
finiteness descends to the ground field.

## References

* J. S. Milne, *Algebraic Groups* (2017), §21.
* T. A. Springer, *Linear Algebraic Groups*, §8.1.
-/

public section

open CategoryTheory
open TauCeti.FiniteTypeCommHopfAlgCat

namespace TauCeti.semisimpleCommHopfAlgProperty

universe u

variable {k : Type u} [Field k] {H : FiniteTypeCommHopfAlgCat.{u, u} k}

-- Reducedness of the nilradical quotient supplies the tensor-reducedness required to form
-- the reduced center over the algebraic closure.
local instance (A : Type u) [CommRing A] : IsReduced (A ⧸ nilradical A) :=
  (Ideal.isRadical_iff_quotient_reduced _).mp (Ideal.radical_isRadical ⊥)

private theorem reducedCenter_identityComponent_eq_augmentation
    (hH : semisimpleCommHopfAlgProperty k H) :
    HopfAlgebra.identityComponentHopfIdeal
        (k := AlgebraicClosure k)
        (H := CommHopfAlgCat.reducedCenterCoordinateHopfAlgebra
          (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H).obj) =
      HopfIdeal.augmentation (AlgebraicClosure k)
        (CommHopfAlgCat.reducedCenterCoordinateHopfAlgebra
          (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H).obj) := by
  let G := FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H
  let C := CommHopfAlgCat.reducedCenterCoordinateHopfAlgebra G.obj
  let Cft := FiniteTypeCommHopfAlgCat.of (AlgebraicClosure k) C
  let J := HopfAlgebra.identityComponentHopfIdeal (k := AlgebraicClosure k) (H := C)
  let q : G.obj ⟶ C :=
    CommHopfAlgCat.mkQuotient G.obj (CommHopfAlgCat.centerDefiningIdeal G.obj) ≫
      CommHopfAlgCat.mkQuotient (CommHopfAlgCat.centerCoordinateHopfAlgebra G.obj)
        (HopfIdeal.reduction (AlgebraicClosure k)
          (CommHopfAlgCat.centerCoordinateHopfAlgebra G.obj))
  have hq : Function.Surjective q.hom :=
    (CommHopfAlgCat.mkQuotient_surjective _ _).comp
      (CommHopfAlgCat.mkQuotient_surjective _ _)
  let I := J.comapOfSurjective q.hom hq
  let e := CommHopfAlgCat.quotientIsoOfSurjective q hq J
  have hcentral : I.IsCentral := by
    apply (CommHopfAlgCat.isCentral_centerDefiningIdeal G.obj).mono
    intro x hx
    apply HopfIdeal.mem_comapOfSurjective.mpr
    have hx0 := (CommHopfAlgCat.mkQuotient_eq_zero_iff G.obj
      (CommHopfAlgCat.centerDefiningIdeal G.obj) x).mpr hx
    simp only [q, CommHopfAlgCat.hom_comp, BialgHom.comp_apply, hx0, map_zero]
    exact zero_mem J
  have hconnected : geometricallyConnectedCommHopfAlgProperty (AlgebraicClosure k)
      (CommHopfAlgCat.quotient G.obj I) :=
    (geometricallyConnectedCommHopfAlgProperty (AlgebraicClosure k)).prop_of_iso e.symm
      (FiniteTypeCommHopfAlgCat.geometricallyConnected_identityComponent Cft)
  let _ : Algebra.Smooth (AlgebraicClosure k) Cft :=
    CommHopfAlgCat.smooth_reducedCenterCoordinateHopfAlgebra G.obj
  have hsmooth : Algebra.Smooth (AlgebraicClosure k) (CommHopfAlgCat.quotient G.obj I) :=
    (smoothCommHopfAlgProperty_iff _).mp <|
      (smoothCommHopfAlgProperty (AlgebraicClosure k)).prop_of_iso e.symm
        ((smoothCommHopfAlgProperty_iff _).mpr
          (FiniteTypeCommHopfAlgCat.smooth_identityComponent Cft))
  have hI : I = HopfIdeal.augmentation (AlgebraicClosure k) G :=
    hH.eq_augmentation_of_isCentral I hcentral hconnected hsmooth
  apply (HopfIdeal.comapOfSurjective_eq_comapOfSurjective_iff q.hom hq).mp
  rw [HopfIdeal.comapOfSurjective_augmentation]
  exact hI

/-- The scheme-theoretic center of a semisimple affine group is finite over its ground field.
No restriction on the characteristic or reducedness of the center is needed. -/
theorem moduleFinite_centerCoordinate (hH : semisimpleCommHopfAlgProperty k H) :
    Module.Finite k (CommHopfAlgCat.centerCoordinateHopfAlgebra H.obj) := by
  apply (CommHopfAlgCat.moduleFinite_centerCoordinate_baseChange_iff
    (K := AlgebraicClosure k) H.obj).mp
  exact moduleFinite_centerCoordinate_of_reducedCenter_identityComponent_eq_augmentation
      (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H)
      (reducedCenter_identityComponent_eq_augmentation hH)

end TauCeti.semisimpleCommHopfAlgProperty
