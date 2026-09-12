/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Center.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Reduction
public import TauCeti.Algebra.AlgebraicGroup.Smooth.AlgebraicallyClosed
public import TauCeti.RingTheory.Ideal.Quotient.Nilpotent

/-!
# The reduced center of an affine group

The center of an affine group can be nonreduced, even when the ambient group is smooth. This file
constructs its reduction in Hopf coordinates. First quotient by the center ideal, then quotient
that coordinate algebra by its nilradical. Equivalently, the reduced center is cut out in the
ambient coordinate algebra by the radical of the center ideal.

Assuming the tensor square of the reduced center coordinate algebra is reduced, its nilradical
forms a Hopf ideal; this sufficient commutative-algebra hypothesis is kept explicit by
`TauCeti.HopfIdeal.reduction`. The construction records both the nested quotient and the single
ambient defining ideal, together with their canonical identification.

Open `TauCeti` to use this API with dot notation, such as `H.reducedCenterCoordinateMap`,
alongside `H.reducedCenterDefiningIdeal` and `H.quotientReducedCenterIso`.
The namespace opening is required because these declarations extend a Mathlib type from
within `TauCeti`.

This is the reduced-center input for proving that the center of a semisimple affine group is
finite. Semisimplicity trivializes the smooth connected identity component of this reduction;
the finite component-group theorem then makes the reduction finite, after which nilpotence of the
thickening controls the original center.

## Main declarations

* `TauCeti.CommHopfAlgCat.reducedCenterDefiningIdeal`: the ambient ideal cutting out the reduced
  center.
* `TauCeti.CommHopfAlgCat.reducedCenterCoordinateHopfAlgebra`: its coordinate Hopf algebra.
* `TauCeti.CommHopfAlgCat.reducedCenterDefiningIdeal_toIdeal`: the ambient defining ideal is the
  radical of the center ideal.
* `TauCeti.CommHopfAlgCat.quotientReducedCenterIso`: the ambient and iterated quotient models
  agree.
* `TauCeti.CommHopfAlgCat.reducedCenterCoordinateMap`: the surjective coordinate morphism of
  the reduced-center inclusion, whose vanishing ideal is the reduced-center defining ideal.
* `TauCeti.CommHopfAlgCat.smooth_reducedCenterCoordinateHopfAlgebra`: over an algebraically closed
  field, a finite-type reduced center is smooth.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§1.f and 21.10.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §11.4.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti.CommHopfAlgCat

universe u v

variable {k : Type u} [Field k]

variable (H : _root_.CommHopfAlgCat.{v} k)

variable [IsReduced
  ((((centerCoordinateHopfAlgebra H : _root_.CommHopfAlgCat.{v} k) : Type v) ⧸
      nilradical ((centerCoordinateHopfAlgebra H : _root_.CommHopfAlgCat.{v} k) : Type v)) ⊗[k]
    (((centerCoordinateHopfAlgebra H : _root_.CommHopfAlgCat.{v} k) : Type v) ⧸
      nilradical ((centerCoordinateHopfAlgebra H : _root_.CommHopfAlgCat.{v} k) : Type v)))]

/-- The Hopf ideal in the ambient coordinate algebra cutting out the reduced center.

It is the inverse image of the nilradical Hopf ideal of the center coordinate algebra. -/
noncomputable def reducedCenterDefiningIdeal : HopfIdeal k H :=
  (HopfIdeal.reduction k (centerCoordinateHopfAlgebra H)).comapOfSurjective
    (mkQuotient H (centerDefiningIdeal H)).hom
    (mkQuotient_surjective H (centerDefiningIdeal H))

/-- The center ideal is contained in the reduced-center ideal. Contravariantly, the reduced
center is a closed subgroup of the center. -/
theorem centerDefiningIdeal_le_reducedCenterDefiningIdeal :
    centerDefiningIdeal H ≤ reducedCenterDefiningIdeal H := by
  intro x hx
  rw [reducedCenterDefiningIdeal, HopfIdeal.mem_comapOfSurjective]
  have hzero : (mkQuotient H (centerDefiningIdeal H)).hom x = 0 :=
    (mkQuotient_eq_zero_iff H (centerDefiningIdeal H) x).mpr hx
  rw [hzero]
  exact HopfIdeal.mem_toIdeal.mp
    (HopfIdeal.reduction k (centerCoordinateHopfAlgebra H)).toIdeal.zero_mem

/-- The ideal defining the reduced center is central. -/
theorem isCentral_reducedCenterDefiningIdeal :
    (reducedCenterDefiningIdeal H).IsCentral :=
  (centerDefiningIdeal_le_iff H (reducedCenterDefiningIdeal H)).mp
    (centerDefiningIdeal_le_reducedCenterDefiningIdeal H)

/-- The coordinate Hopf algebra of the reduced center, formed by quotienting the center by its
nilradical. -/
noncomputable abbrev reducedCenterCoordinateHopfAlgebra : _root_.CommHopfAlgCat.{v} k :=
  quotient (centerCoordinateHopfAlgebra H) (HopfIdeal.reduction k (centerCoordinateHopfAlgebra H))

/-- The reduced-center coordinate algebra is reduced. -/
theorem isReduced_reducedCenterCoordinateHopfAlgebra :
    IsReduced (reducedCenterCoordinateHopfAlgebra H) :=
  HopfIdeal.isReduced_quotient_reduction k (centerCoordinateHopfAlgebra H)

/-- The ambient ideal defining the reduced center is the radical of the center ideal. -/
@[simp]
theorem reducedCenterDefiningIdeal_toIdeal :
    (reducedCenterDefiningIdeal H).toIdeal = (centerDefiningIdeal H).toIdeal.radical := by
  have hcomap :
      RingHom.ker ((mkQuotient H (centerDefiningIdeal H)).hom :
        H →+* centerCoordinateHopfAlgebra H) =
        (centerDefiningIdeal H).toIdeal :=
    calc
      RingHom.ker ((mkQuotient H (centerDefiningIdeal H)).hom :
        H →+* centerCoordinateHopfAlgebra H) =
          RingHom.ker (mkQuotient H (centerDefiningIdeal H)).hom.toAlgHom.toRingHom := by
        ext x
        simp only [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          BialgHom.coe_toAlgHom]
      _ = (centerDefiningIdeal H).toIdeal :=
        mkQuotient_ker H (centerDefiningIdeal H)
  rw [reducedCenterDefiningIdeal, HopfIdeal.comapOfSurjective_toIdeal,
    HopfIdeal.reduction_toIdeal, nilradical, Ideal.comap_radical, Ideal.zero_eq_bot,
    ← RingHom.ker_eq_comap_bot, hcomap]

/-- An element belongs to the reduced-center ideal exactly when it belongs to the radical of the
center ideal. -/
@[simp]
theorem mem_reducedCenterDefiningIdeal {x : H} :
    x ∈ reducedCenterDefiningIdeal H ↔ x ∈ (centerDefiningIdeal H).toIdeal.radical := by
  rw [← HopfIdeal.mem_toIdeal, reducedCenterDefiningIdeal_toIdeal]

/-- The quotient by the ambient reduced-center ideal is canonically the iterated quotient formed
by taking the center and then killing its nilradical. -/
noncomputable def quotientReducedCenterIso :
    quotient H (reducedCenterDefiningIdeal H) ≅ reducedCenterCoordinateHopfAlgebra H :=
  quotientIsoOfSurjective (mkQuotient H (centerDefiningIdeal H))
    (mkQuotient_surjective H (centerDefiningIdeal H))
      (HopfIdeal.reduction k (centerCoordinateHopfAlgebra H))

/-- The coordinate morphism of the inclusion of the reduced center into the ambient group. -/
noncomputable def reducedCenterCoordinateMap : H ⟶ reducedCenterCoordinateHopfAlgebra H :=
  mkQuotient H (centerDefiningIdeal H) ≫
    mkQuotient (centerCoordinateHopfAlgebra H)
      (HopfIdeal.reduction k (centerCoordinateHopfAlgebra H))

/-- The reduced-center coordinate morphism first restricts to the center and then quotients
by its nilradical. -/
theorem reducedCenterCoordinateMap_def :
    reducedCenterCoordinateMap H = mkQuotient H (centerDefiningIdeal H) ≫
      mkQuotient (centerCoordinateHopfAlgebra H)
        (HopfIdeal.reduction k (centerCoordinateHopfAlgebra H)) := (rfl)

/-- The canonical reduced-center isomorphism commutes with the ambient and iterated quotient
morphisms. -/
@[simp]
theorem mkQuotient_comp_quotientReducedCenterIso_hom :
    mkQuotient H (reducedCenterDefiningIdeal H) ≫ (quotientReducedCenterIso H).hom =
      reducedCenterCoordinateMap H := by
  rw [quotientReducedCenterIso, reducedCenterCoordinateMap_def]
  exact mkQuotient_comp_quotientIsoOfSurjective_hom
    (mkQuotient H (centerDefiningIdeal H))
      (mkQuotient_surjective H (centerDefiningIdeal H))
        (HopfIdeal.reduction k (centerCoordinateHopfAlgebra H))

/-- The coordinate morphism of the reduced-center inclusion is surjective. -/
theorem reducedCenterCoordinateMap_surjective :
    Function.Surjective (reducedCenterCoordinateMap H).hom := by
  rw [← mkQuotient_comp_quotientReducedCenterIso_hom,
    _root_.CommHopfAlgCat.hom_comp, BialgHom.coe_comp]
  exact (ConcreteCategory.bijective_of_isIso (quotientReducedCenterIso H).hom).2.comp
    (mkQuotient_surjective H (reducedCenterDefiningIdeal H))

/-- Vanishing on the reduced center is membership in its ambient defining ideal. -/
@[simp]
theorem reducedCenterCoordinateMap_eq_zero_iff (x : H) :
    (reducedCenterCoordinateMap H).hom x = 0 ↔ x ∈ reducedCenterDefiningIdeal H := by
  rw [← mkQuotient_comp_quotientReducedCenterIso_hom,
    _root_.CommHopfAlgCat.hom_comp,
    BialgHom.comp_apply, map_eq_zero_iff _
      (ConcreteCategory.bijective_of_isIso (quotientReducedCenterIso H).hom).1,
    mkQuotient_eq_zero_iff, HopfIdeal.mem_toIdeal]

/-- The ambient quotient model of the reduced center has reduced coordinate ring. -/
theorem isReduced_quotient_reducedCenterDefiningIdeal :
    IsReduced (quotient H (reducedCenterDefiningIdeal H)) := by
  let _ : IsReduced (reducedCenterCoordinateHopfAlgebra H) :=
    isReduced_reducedCenterCoordinateHopfAlgebra H
  exact isReduced_of_injective (quotientReducedCenterIso H).hom.hom.toAlgHom.toRingHom
    (ConcreteCategory.bijective_of_isIso (quotientReducedCenterIso H).hom).1

/-- The reduced-center ideal is contained in every central Hopf ideal whose quotient is
reduced. -/
theorem reducedCenterDefiningIdeal_le_of_centerDefiningIdeal_le_of_isReduced_quotient
    (I : HopfIdeal k H)
    (hcenter : centerDefiningIdeal H ≤ I) [IsReduced (quotient H I)] :
    reducedCenterDefiningIdeal H ≤ I := by
  rw [← HopfIdeal.toIdeal_le_toIdeal, reducedCenterDefiningIdeal_toIdeal]
  exact ((Ideal.isRadical_iff_quotient_reduced I.toIdeal).mpr inferInstance).radical_le_iff.mpr
    (HopfIdeal.toIdeal_le_toIdeal.mpr hcenter)

section Smooth

variable (G : _root_.CommHopfAlgCat.{v} k)
variable [IsReduced
  ((((centerCoordinateHopfAlgebra G : _root_.CommHopfAlgCat.{v} k) : Type v) ⧸
      nilradical ((centerCoordinateHopfAlgebra G : _root_.CommHopfAlgCat.{v} k) : Type v)) ⊗[k]
    (((centerCoordinateHopfAlgebra G : _root_.CommHopfAlgCat.{v} k) : Type v) ⧸
      nilradical ((centerCoordinateHopfAlgebra G : _root_.CommHopfAlgCat.{v} k) : Type v)))]

/-- Over an algebraically closed field, a finite-type reduced center is smooth. -/
theorem smooth_reducedCenterCoordinateHopfAlgebra [IsAlgClosed k]
    [Algebra.FiniteType k (reducedCenterCoordinateHopfAlgebra G)] :
    Algebra.Smooth k (reducedCenterCoordinateHopfAlgebra G) := by
  let _ : IsReduced (reducedCenterCoordinateHopfAlgebra G) :=
    isReduced_reducedCenterCoordinateHopfAlgebra G
  exact (smoothCommHopfAlgProperty_iff (reducedCenterCoordinateHopfAlgebra G)).mp
    (smoothCommHopfAlgProperty_of_isAlgClosed_of_isReduced k
      (reducedCenterCoordinateHopfAlgebra G))

end Smooth

end TauCeti.CommHopfAlgCat
