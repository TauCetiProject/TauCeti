/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Orders.NarrowPic
public import TauCeti.NumberTheory.NumberField.NarrowClassGroup.Basic
public import TauCeti.NumberTheory.ClassGroup.Equiv

/-!
# The Picard groups of the maximal order

The maximal order `maximalNumberFieldOrder K` has the ring of integers as its underlying ring, but
as a subalgebra of `K` rather than as the type `𝓞 K`. Its wide and narrow Picard groups are
therefore quotients of a different, though canonically isomorphic, group of fractional ideals than
Mathlib's `ClassGroup (𝓞 K)` and the narrow class group `NarrowClassGroup K`.

This file supplies the canonical identifications of the Picard groups of the maximal order with
these classical groups. Both come from the ring isomorphism between the maximal order and `𝓞 K`
given by `IsIntegralClosure.equiv`: the wide one is Mathlib's `ClassGroup.mulEquiv` of that
isomorphism, and the narrow one is the quotient of the same transport of fractional ideals.

Under these identifications, the forgetful map `narrowToPic` from the narrow to the wide Picard
group becomes the forgetful map `NarrowClassGroup.toClassGroup` from the narrow class group to the
class group. Statements proved for the Picard groups of an arbitrary order thereby specialize to
the class groups of `K`.

## Main definitions

* `TauCeti.GlobalNumberFields.maximalOrderFractionalIdealEquiv`: fractional ideals of the maximal
  order are fractional ideals of `𝓞 K` with the same elements.
* `TauCeti.GlobalNumberFields.maximalOrderPicEquiv`: the Picard group of the maximal order is the
  class group of `𝓞 K`.
* `TauCeti.GlobalNumberFields.maximalOrderNarrowPicEquiv`: the narrow Picard group of the maximal
  order is the narrow class group of `K`.

## Main results

* `TauCeti.GlobalNumberFields.maximalOrderPicEquiv_comp_narrowToPic`: the narrow-to-wide map of
  the maximal order is the forgetful map from the narrow class group to the class group.

## References

* G. S. Kopp and J. C. Lagarias, *Class Field Theory for Orders of Number Fields*, §2.
-/

public section
noncomputable section

open NumberField

namespace TauCeti.GlobalNumberFields

variable (K : Type*) [Field K] [NumberField K]

/-- The canonical ring isomorphism from the maximal order to `𝓞 K`. -/
private abbrev maximalOrderRingEquiv : (maximalNumberFieldOrder K).toSubalgebra ≃+* 𝓞 K :=
  (IsIntegralClosure.equiv ℤ (maximalNumberFieldOrder K).toSubalgebra K (𝓞 K)).toRingEquiv

/-- The isomorphism `maximalOrderRingEquiv` induces the identity of `K`, since it does not move
elements of `K`. -/
private theorem ringEquivOfRingEquiv_maximalOrderRingEquiv_apply (x : K) :
    IsFractionRing.ringEquivOfRingEquiv (K := K) (L := K) (maximalOrderRingEquiv K) x = x := by
  refine RingHom.congr_fun (IsLocalization.ringHom_ext
    (nonZeroDivisors (maximalNumberFieldOrder K).toSubalgebra)
    (j := (IsFractionRing.ringEquivOfRingEquiv (K := K) (L := K) (maximalOrderRingEquiv K) :
      K →+* K))
    (k := RingHom.id K) (RingHom.ext fun a ↦ ?_)) x
  simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
    IsFractionRing.ringEquivOfRingEquiv_algebraMap, RingHom.id_apply]
  exact IsIntegralClosure.algebraMap_equiv ℤ _ K (𝓞 K) a

/-- Fractional ideals of the maximal order are fractional ideals of `𝓞 K`: the two carriers have
the same elements of `K`, by `mem_maximalOrderFractionalIdealEquiv_iff`. -/
def maximalOrderFractionalIdealEquiv :
    FractionalIdeal (nonZeroDivisors (maximalNumberFieldOrder K).toSubalgebra) K ≃+*
      FractionalIdeal (nonZeroDivisors (𝓞 K)) K :=
  FractionalIdeal.ringEquivOfRingEquiv K K (maximalOrderRingEquiv K)

variable {K}

/-- A fractional ideal of the maximal order and the corresponding fractional ideal of `𝓞 K` have
the same elements. -/
@[simp]
theorem mem_maximalOrderFractionalIdealEquiv_iff
    {I : FractionalIdeal (nonZeroDivisors (maximalNumberFieldOrder K).toSubalgebra) K} {x : K} :
    x ∈ maximalOrderFractionalIdealEquiv K I ↔ x ∈ I := by
  have hI := FractionalIdeal.ringEquivOfRingEquiv_apply_val K K (maximalOrderRingEquiv K) I
  rw [FractionalIdeal.val_eq_coe, FractionalIdeal.val_eq_coe] at hI
  rw [maximalOrderFractionalIdealEquiv, ← FractionalIdeal.mem_coe, hI, Submodule.mem_map]
  -- `erw` aligns the inverse-map instance carried by the semilinear equivalence with the one
  -- `LinearEquiv.coe_toLinearMap` infers.
  erw [LinearEquiv.coe_toLinearMap]
  simp only [IsFractionRing.semilinearEquivOfRingEquiv_apply,
    ringEquivOfRingEquiv_maximalOrderRingEquiv_apply, exists_eq_right, FractionalIdeal.mem_coe]

/-- A fractional ideal of `𝓞 K` and the corresponding fractional ideal of the maximal order have
the same elements. -/
@[simp]
theorem mem_maximalOrderFractionalIdealEquiv_symm_iff
    {J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K} {x : K} :
    x ∈ (maximalOrderFractionalIdealEquiv K).symm J ↔ x ∈ J := by
  rw [← mem_maximalOrderFractionalIdealEquiv_iff, RingEquiv.apply_symm_apply]

/-- The principal fractional ideal of the maximal order generated by `x` corresponds to the
principal fractional ideal of `𝓞 K` generated by `x`. -/
@[simp]
theorem maximalOrderFractionalIdealEquiv_spanSingleton (x : K) :
    maximalOrderFractionalIdealEquiv K
        (FractionalIdeal.spanSingleton (nonZeroDivisors (maximalNumberFieldOrder K).toSubalgebra)
          x) =
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) x := by
  rw [maximalOrderFractionalIdealEquiv, FractionalIdeal.ringEquivOfRingEquiv_spanSingleton,
    ringEquivOfRingEquiv_maximalOrderRingEquiv_apply]

/-- The principal fractional ideals of the maximal order correspond to those of `𝓞 K`. -/
@[simp]
theorem mapEquiv_maximalOrderFractionalIdealEquiv_toPrincipalIdeal (x : Kˣ) :
    Units.mapEquiv (maximalOrderFractionalIdealEquiv K : _ ≃* _)
        (toPrincipalIdeal (maximalNumberFieldOrder K).toSubalgebra K x) =
      toPrincipalIdeal (𝓞 K) K x := by
  ext : 1
  simp [coe_toPrincipalIdeal]

/-- The principal fractional ideals of `𝓞 K` correspond to those of the maximal order. -/
@[simp]
theorem mapEquiv_maximalOrderFractionalIdealEquiv_symm_toPrincipalIdeal (x : Kˣ) :
    (Units.mapEquiv (maximalOrderFractionalIdealEquiv K : _ ≃* _)).symm
        (toPrincipalIdeal (𝓞 K) K x) =
      toPrincipalIdeal (maximalNumberFieldOrder K).toSubalgebra K x := by
  rw [MulEquiv.symm_apply_eq, mapEquiv_maximalOrderFractionalIdealEquiv_toPrincipalIdeal]

variable (K)

/-- **The Picard group of the maximal order is the class group of `𝓞 K`.** The class of an
invertible fractional ideal of the maximal order goes to the class of the fractional ideal of
`𝓞 K` with the same elements. -/
def maximalOrderPicEquiv : Pic (maximalNumberFieldOrder K) ≃* ClassGroup (𝓞 K) :=
  ClassGroup.mulEquiv (maximalOrderRingEquiv K)

/-- **The narrow Picard group of the maximal order is the narrow class group of `K`.** The narrow
class of an invertible fractional ideal of the maximal order goes to the narrow class of the
fractional ideal of `𝓞 K` with the same elements. -/
def maximalOrderNarrowPicEquiv : NarrowPic (maximalNumberFieldOrder K) ≃* NarrowClassGroup K :=
  MonoidHom.toMulEquiv
    (NarrowPic.lift _
      (NarrowClassGroup.mk.comp
        (Units.mapEquiv (maximalOrderFractionalIdealEquiv K : _ ≃* _)).toMonoidHom)
      fun I hI ↦ by
        obtain ⟨x, hx, rfl⟩ := (NumberFieldOrder.mem_narrowPrincipal_iff _).mp hI
        rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
          mapEquiv_maximalOrderFractionalIdealEquiv_toPrincipalIdeal,
          ← NarrowClassGroup.mkPrincipal_apply]
        exact NarrowClassGroup.mkPrincipal_eq_one_of_isTotallyPositive hx)
    (NarrowClassGroup.lift
      ((NarrowPic.mk _).comp
        (Units.mapEquiv (maximalOrderFractionalIdealEquiv K : _ ≃* _)).symm.toMonoidHom)
      fun J hJ ↦ by
        obtain ⟨x, hx, rfl⟩ := mem_narrowPrincipalSubgroup.mp hJ
        rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
          mapEquiv_maximalOrderFractionalIdealEquiv_symm_toPrincipalIdeal,
          ← NarrowPic.mkPrincipal_apply]
        exact NarrowPic.mkPrincipal_eq_one_of_isTotallyPositive _ hx)
    (MonoidHom.ext fun c ↦ by
      obtain ⟨I, rfl⟩ := NarrowPic.mk_surjective _ c
      rw [MonoidHom.comp_apply, NarrowPic.lift_mk, MonoidHom.comp_apply, NarrowClassGroup.lift_mk,
        MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom,
        MulEquiv.symm_apply_apply, MonoidHom.id_apply])
    (MonoidHom.ext fun c ↦ by
      obtain ⟨J, rfl⟩ := NarrowClassGroup.mk_surjective c
      rw [MonoidHom.comp_apply, NarrowClassGroup.lift_mk, MonoidHom.comp_apply, NarrowPic.lift_mk,
        MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom,
        MulEquiv.apply_symm_apply, MonoidHom.id_apply])

variable {K}

/-- The Picard class of an invertible fractional ideal of the maximal order goes to the ideal
class of the fractional ideal of `𝓞 K` with the same elements. -/
@[simp]
theorem maximalOrderPicEquiv_mkPic
    (I : (maximalNumberFieldOrder K).invertibleProperFractionalIdeals) :
    maximalOrderPicEquiv K ((maximalNumberFieldOrder K).mkPic I) =
      ClassGroup.mk K (Units.mapEquiv (maximalOrderFractionalIdealEquiv K : _ ≃* _) I) :=
  ClassGroup.mulEquiv_mk K (maximalOrderRingEquiv K) I

/-- The inverse of `maximalOrderPicEquiv` sends the ideal class of a fractional ideal of `𝓞 K` to
the Picard class of the fractional ideal of the maximal order with the same elements. -/
@[simp]
theorem maximalOrderPicEquiv_symm_mk (J : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ) :
    (maximalOrderPicEquiv K).symm (ClassGroup.mk K J) =
      (maximalNumberFieldOrder K).mkPic
        ((Units.mapEquiv (maximalOrderFractionalIdealEquiv K : _ ≃* _)).symm J) := by
  rw [MulEquiv.symm_apply_eq, maximalOrderPicEquiv_mkPic, MulEquiv.apply_symm_apply]

/-- The narrow Picard class of an invertible fractional ideal of the maximal order goes to the
narrow class of the fractional ideal of `𝓞 K` with the same elements. -/
@[simp]
theorem maximalOrderNarrowPicEquiv_mk
    (I : (maximalNumberFieldOrder K).invertibleProperFractionalIdeals) :
    maximalOrderNarrowPicEquiv K (NarrowPic.mk (maximalNumberFieldOrder K) I) =
      NarrowClassGroup.mk (Units.mapEquiv (maximalOrderFractionalIdealEquiv K : _ ≃* _) I) :=
  NarrowPic.lift_mk _ _ _ I

/-- The inverse of `maximalOrderNarrowPicEquiv` sends the narrow class of a fractional ideal of
`𝓞 K` to the narrow Picard class of the fractional ideal of the maximal order with the same
elements. -/
@[simp]
theorem maximalOrderNarrowPicEquiv_symm_mk (J : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ) :
    (maximalOrderNarrowPicEquiv K).symm (NarrowClassGroup.mk J) =
      NarrowPic.mk (maximalNumberFieldOrder K)
        ((Units.mapEquiv (maximalOrderFractionalIdealEquiv K : _ ≃* _)).symm J) := by
  rw [MulEquiv.symm_apply_eq, maximalOrderNarrowPicEquiv_mk, MulEquiv.apply_symm_apply]

/-- **The narrow-to-wide map of the maximal order is the forgetful map from the narrow class
group to the class group**, read through `maximalOrderNarrowPicEquiv` and
`maximalOrderPicEquiv`. -/
@[simp]
theorem maximalOrderPicEquiv_narrowToPic (c : NarrowPic (maximalNumberFieldOrder K)) :
    maximalOrderPicEquiv K ((maximalNumberFieldOrder K).narrowToPic c) =
      NarrowClassGroup.toClassGroup (maximalOrderNarrowPicEquiv K c) := by
  obtain ⟨I, rfl⟩ := NarrowPic.mk_surjective _ c
  simp

variable (K) in
/-- The commuting square identifying the narrow-to-wide map of the maximal order with the
forgetful map `NarrowClassGroup.toClassGroup` from the narrow class group to the class group. -/
theorem maximalOrderPicEquiv_comp_narrowToPic :
    (maximalOrderPicEquiv K).toMonoidHom.comp (maximalNumberFieldOrder K).narrowToPic =
      NarrowClassGroup.toClassGroup.comp (maximalOrderNarrowPicEquiv K).toMonoidHom :=
  MonoidHom.ext maximalOrderPicEquiv_narrowToPic

end TauCeti.GlobalNumberFields
