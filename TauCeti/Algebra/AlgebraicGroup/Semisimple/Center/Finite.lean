/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Semisimple.Center.Basic
import TauCeti.Algebra.AlgebraicGroup.Center.Connected
import TauCeti.Algebra.AlgebraicGroup.Center.Finite
import TauCeti.Algebra.AlgebraicGroup.Center.Descent

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
  exact (identityComponentHopfIdeal_reducedCenterCoordinateHopfAlgebra_eq_augmentation_iff G).mpr
    (hH.eq_augmentation_of_isCentral _ (isCentral_reducedConnectedCenterDefiningIdeal G)
      (geometricallyConnected_reducedConnectedCenter G) (smooth_reducedConnectedCenter G))

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
