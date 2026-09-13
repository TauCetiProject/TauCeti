/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Center.Reduced
public import TauCeti.Algebra.AlgebraicGroup.Connected.Comultiplication
public import TauCeti.RingTheory.FiniteType.Tensor.Product

/-!
# The reduced center's identity component as an ambient closed subgroup

For a finite-type affine group over an algebraically closed field, the identity component of
the reduced center is a central closed subgroup of the original group. Its coordinate algebra
is naturally an iterated quotient: first take the center, then its reduction, then its identity
component. To apply a theorem about closed subgroups of the original group, one instead needs a
single Hopf ideal in the original coordinate algebra.

This file constructs that ambient ideal and identifies its quotient with the iterated quotient.
The comparison respects the quotient maps, and triviality in the ambient group is equivalent to
triviality of the identity component inside the reduced center. These are the coordinate
identifications needed to apply the central-subgroup criterion for semisimplicity and then the
finite-center criterion.

The tensor-product import supplies `TauCeti.instIsReducedTensorProductOfIsAlgClosed`, which
makes the reduced-center construction available under the finite-type hypotheses here.
Open `TauCeti` to use the declarations with dot notation, such as
`H.reducedCenterIdentityComponentDefiningIdeal`.

## Main declarations

* `reducedCenterIdentityComponentDefiningIdeal`: the ambient defining ideal.
* `isCentral_reducedCenterIdentityComponentDefiningIdeal`: its centrality.
* `quotientReducedCenterIdentityComponentIso`: comparison with the iterated quotient.
* `reducedCenterIdentityComponentDefiningIdeal_eq_augmentation_iff`: triviality agrees in the
  two ambient groups.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§2.g and 19.a–b.
-/

public section

open CategoryTheory TauCeti

namespace TauCeti.CommHopfAlgCat

universe u v

variable {k : Type u} [Field k] [IsAlgClosed k]
variable (H : _root_.CommHopfAlgCat.{v} k) [Algebra.FiniteType k H]

/-- The ambient Hopf ideal cutting out the identity component of the reduced center. -/
noncomputable def reducedCenterIdentityComponentDefiningIdeal : HopfIdeal k H :=
  (HopfAlgebra.identityComponentHopfIdeal
    (k := k) (H := reducedCenterCoordinateHopfAlgebra H)).comapOfSurjective
      H.reducedCenterCoordinateMap.hom (reducedCenterCoordinateMap_surjective H)

/-- The ambient defining ideal is the pullback of the reduced center's identity-component ideal
along its coordinate morphism. -/
theorem reducedCenterIdentityComponentDefiningIdeal_def :
    reducedCenterIdentityComponentDefiningIdeal H =
      (HopfAlgebra.identityComponentHopfIdeal
        (k := k) (H := reducedCenterCoordinateHopfAlgebra H)).comapOfSurjective
          H.reducedCenterCoordinateMap.hom (reducedCenterCoordinateMap_surjective H) := (rfl)

/-- Membership in the ambient defining ideal is membership in the identity-component ideal
after restriction to the reduced center. -/
@[simp]
theorem mem_reducedCenterIdentityComponentDefiningIdeal {x : H} :
    x ∈ H.reducedCenterIdentityComponentDefiningIdeal ↔
      (reducedCenterCoordinateMap H).hom x ∈ HopfAlgebra.identityComponentHopfIdeal
        (k := k) (H := reducedCenterCoordinateHopfAlgebra H) := by
  rw [reducedCenterIdentityComponentDefiningIdeal, HopfIdeal.mem_comapOfSurjective]

/-- The reduced-center ideal is contained in the identity-component ideal. Contravariantly,
the identity component is a closed subgroup of the reduced center. -/
theorem reducedCenterDefiningIdeal_le_reducedCenterIdentityComponentDefiningIdeal :
    reducedCenterDefiningIdeal H ≤ reducedCenterIdentityComponentDefiningIdeal H := by
  intro x hx
  rw [mem_reducedCenterIdentityComponentDefiningIdeal,
    (reducedCenterCoordinateMap_eq_zero_iff H x).mpr hx]
  exact HopfIdeal.mem_toIdeal.mp (Ideal.zero_mem _)

/-- The identity component of the reduced center is central in the original affine group. -/
theorem isCentral_reducedCenterIdentityComponentDefiningIdeal :
    (reducedCenterIdentityComponentDefiningIdeal H).IsCentral :=
  (isCentral_reducedCenterDefiningIdeal H).mono
    (reducedCenterDefiningIdeal_le_reducedCenterIdentityComponentDefiningIdeal H)

/-- The ambient quotient by the reduced center's identity-component ideal is canonically the
identity-component quotient of the reduced center coordinate algebra. -/
noncomputable def quotientReducedCenterIdentityComponentIso :
    quotient H (reducedCenterIdentityComponentDefiningIdeal H) ≅
      quotient (reducedCenterCoordinateHopfAlgebra H)
        (HopfAlgebra.identityComponentHopfIdeal
          (k := k) (H := reducedCenterCoordinateHopfAlgebra H)) :=
  quotientIsoOfSurjective (reducedCenterCoordinateMap H)
    (reducedCenterCoordinateMap_surjective H) _

/-- The comparison of the ambient and iterated quotients respects their coordinate maps. -/
@[simp]
theorem mkQuotient_comp_quotientReducedCenterIdentityComponentIso_hom :
    mkQuotient H (reducedCenterIdentityComponentDefiningIdeal H) ≫
        (quotientReducedCenterIdentityComponentIso H).hom =
      reducedCenterCoordinateMap H ≫
        mkQuotient (reducedCenterCoordinateHopfAlgebra H)
          (HopfAlgebra.identityComponentHopfIdeal
            (k := k) (H := reducedCenterCoordinateHopfAlgebra H)) := by
  dsimp only [quotientReducedCenterIdentityComponentIso,
    reducedCenterIdentityComponentDefiningIdeal]
  exact mkQuotient_comp_quotientIsoOfSurjective_hom (reducedCenterCoordinateMap H)
    (reducedCenterCoordinateMap_surjective H) _

/-- The reduced center's identity component is trivial as an ambient closed subgroup exactly
when it is trivial as a closed subgroup of the reduced center. -/
@[simp]
theorem reducedCenterIdentityComponentDefiningIdeal_eq_augmentation_iff :
    reducedCenterIdentityComponentDefiningIdeal H = HopfIdeal.augmentation k H ↔
      HopfAlgebra.identityComponentHopfIdeal
          (k := k) (H := reducedCenterCoordinateHopfAlgebra H) =
        HopfIdeal.augmentation k (reducedCenterCoordinateHopfAlgebra H) := by
  rw [reducedCenterIdentityComponentDefiningIdeal,
    ← HopfIdeal.comapOfSurjective_augmentation (reducedCenterCoordinateMap H).hom
      (reducedCenterCoordinateMap_surjective H),
    HopfIdeal.comapOfSurjective_eq_comapOfSurjective_iff]

end TauCeti.CommHopfAlgCat
