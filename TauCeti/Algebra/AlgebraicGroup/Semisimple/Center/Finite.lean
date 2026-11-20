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
  let Z := CommHopfAlgCat.reducedCenterDefiningIdeal G.obj
  let e := CommHopfAlgCat.quotientReducedCenterIso G.obj
  have hI : connectedCenterDefiningIdeal G = HopfIdeal.augmentation (AlgebraicClosure k) G :=
    hH.eq_augmentation_of_isCentral _ (isCentral_connectedCenterDefiningIdeal G)
      (geometricallyConnected_connectedCenter G) (smooth_connectedCenter G)
  -- Compare the connected center, cut out in `G`, with the identity component of the
  -- iterated quotient model of the reduced center.
  ext y
  obtain ⟨x, rfl⟩ := (ConcreteCategory.bijective_of_isIso e.hom).2.comp
    (CommHopfAlgCat.mkQuotient_surjective G.obj Z) y
  rw [Function.comp_apply]
  refine (HopfAlgebra.apply_mem_identityComponentHopfIdeal_iff
    (_root_.CommHopfAlgCat.ofIso e)).trans ?_
  rw [← HopfIdeal.mem_identityComponent, ← connectedCenterDefiningIdeal_eq_identityComponent, hI,
    HopfIdeal.mem_augmentation, HopfIdeal.mem_augmentation, CoalgHomClass.counit_comp_apply,
    CoalgHomClass.counit_comp_apply]

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
