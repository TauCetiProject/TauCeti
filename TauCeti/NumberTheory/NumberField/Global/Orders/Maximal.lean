/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassGroup.Equiv
public import TauCeti.NumberTheory.NumberField.Global.Orders.NarrowPic
public import TauCeti.NumberTheory.NumberField.NarrowClassGroup.Basic

/-!
# The Picard groups of the maximal order

The maximal order `maximalNumberFieldOrder K` of a number field `K` has the same elements as the
ring of integers `𝓞 K`, but it is a different type: the order-theoretic API (`Pic`, `NarrowPic`,
`NumberFieldOrder.narrowToPic`) is stated for its subalgebra, while the classical API
(`ClassGroup (𝓞 K)`, `NumberField.NarrowClassGroup K`) is stated for `𝓞 K`. This file transports
fractional ideals across that identification and specializes the Picard groups of an order to
the class groups of the maximal order:

* `Pic (maximalNumberFieldOrder K) ≃* ClassGroup (𝓞 K)`,
* `NarrowPic (maximalNumberFieldOrder K) ≃* NumberField.NarrowClassGroup K`,

compatibly with the forgetful maps `NarrowPic O → Pic O` and `Cl⁺(K) → Cl(K)`. Both equivalences
send the class of a fractional ideal to the class of the fractional ideal with the same elements.

## Main definitions and results

* `TauCeti.GlobalNumberFields.maximalOrderRingEquiv`: the maximal order is the ring of integers.
* `TauCeti.GlobalNumberFields.maximalOrderFractionalIdealEquiv`: the induced identification of
  fractional ideals, with `mem_maximalOrderFractionalIdealEquiv`, and its restriction
  `maximalOrderUnitsEquiv` to invertible ideals, which preserves principal ideals
  (`maximalOrderUnitsEquiv_toPrincipalIdeal`).
* `TauCeti.GlobalNumberFields.maximalOrderPicEquiv`: the wide Picard group of the maximal order
  is the class group of `𝓞 K`, via Mathlib's `ClassGroup.mulEquiv`.
* `TauCeti.GlobalNumberFields.maximalOrderNarrowPicEquiv`: the narrow Picard group of the maximal
  order is the narrow class group of `K`.
* `TauCeti.GlobalNumberFields.toClassGroup_comp_maximalOrderNarrowPicEquiv`: under these
  equivalences, `NumberFieldOrder.narrowToPic` becomes `NumberField.NarrowClassGroup.toClassGroup`.

## References

* G. S. Kopp and J. C. Lagarias, *Class Field Theory for Orders of Number Fields*, §2.
-/

public section
noncomputable section

open NumberField
open scoped nonZeroDivisors

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

variable (K) in
/-- The maximal order of `K` is the ring of integers `𝓞 K`: the two rings have the same elements
of `K`. -/
def maximalOrderRingEquiv : (maximalNumberFieldOrder K).toSubalgebra ≃+* 𝓞 K where
  toFun x := ⟨x, by simpa using x.2⟩
  invFun y := ⟨y.1, by simpa using y.2⟩
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- The identification of the maximal order with `𝓞 K` is compatible with the inclusions into
`K`. -/
@[simp]
theorem algebraMap_maximalOrderRingEquiv (x : (maximalNumberFieldOrder K).toSubalgebra) :
    algebraMap (𝓞 K) K (maximalOrderRingEquiv K x) = algebraMap _ K x := (rfl)

variable (K) in
/-- The automorphism of the fraction field induced by `maximalOrderRingEquiv` is the identity. -/
theorem ringEquivOfRingEquiv_maximalOrderRingEquiv :
    IsFractionRing.ringEquivOfRingEquiv (K := K) (L := K) (maximalOrderRingEquiv K) =
      RingEquiv.refl K := by
  refine RingEquiv.toRingHom_injective (IsLocalization.ringHom_ext
    (maximalNumberFieldOrder K).toSubalgebra⁰ (RingHom.ext fun a => ?_))
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    IsFractionRing.ringEquivOfRingEquiv_algebraMap, RingEquiv.refl_apply]
  exact algebraMap_maximalOrderRingEquiv a

variable (K) in
/-- Fractional ideals of the maximal order are fractional ideals of `𝓞 K`, transported along
`maximalOrderRingEquiv`. A fractional ideal and its transport have the same elements
(`mem_maximalOrderFractionalIdealEquiv`). -/
def maximalOrderFractionalIdealEquiv :
    FractionalIdeal (maximalNumberFieldOrder K).toSubalgebra⁰ K ≃+* FractionalIdeal (𝓞 K)⁰ K :=
  FractionalIdeal.ringEquivOfRingEquiv K K (maximalOrderRingEquiv K)

/-- A fractional ideal of the maximal order and its transport to `𝓞 K` have the same elements. -/
@[simp]
theorem mem_maximalOrderFractionalIdealEquiv
    {I : FractionalIdeal (maximalNumberFieldOrder K).toSubalgebra⁰ K} {x : K} :
    x ∈ maximalOrderFractionalIdealEquiv K I ↔ x ∈ I := by
  have h (y : K) : IsFractionRing.ringEquivOfRingEquiv (K := K) (L := K)
      (maximalOrderRingEquiv K) y = y := by
    rw [ringEquivOfRingEquiv_maximalOrderRingEquiv, RingEquiv.refl_apply]
  rw [← FractionalIdeal.mem_coe, maximalOrderFractionalIdealEquiv,
    FractionalIdeal.ringEquivOfRingEquiv_apply, FractionalIdeal.coe_mk]
  simp only [Submodule.mem_map, FractionalIdeal.val_eq_coe, FractionalIdeal.mem_coe]
  -- The semilinear equivalence underlying the transport applies
  -- `IsFractionRing.ringEquivOfRingEquiv` (`IsFractionRing.semilinearEquivOfRingEquiv_apply`).
  refine ⟨fun ⟨y, hy, hyx⟩ => ?_, fun hx => ⟨x, hx, h x⟩⟩
  obtain rfl : y = x := (h y).symm.trans hyx
  exact hy

/-- The transport of a principal fractional ideal is generated by the same element. -/
@[simp]
theorem maximalOrderFractionalIdealEquiv_spanSingleton (x : K) :
    maximalOrderFractionalIdealEquiv K
        (FractionalIdeal.spanSingleton (maximalNumberFieldOrder K).toSubalgebra⁰ x) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ x := by
  rw [maximalOrderFractionalIdealEquiv, FractionalIdeal.ringEquivOfRingEquiv_spanSingleton,
    ringEquivOfRingEquiv_maximalOrderRingEquiv, RingEquiv.refl_apply]

variable (K) in
/-- The invertible fractional ideals of the maximal order are the invertible fractional ideals of
`𝓞 K`, via `maximalOrderFractionalIdealEquiv`. -/
def maximalOrderUnitsEquiv :
    (maximalNumberFieldOrder K).invertibleProperFractionalIdeals ≃* (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Units.mapEquiv (maximalOrderFractionalIdealEquiv K).toMulEquiv

/-- The underlying fractional ideal of `maximalOrderUnitsEquiv K I` is the transport of `I`. -/
@[simp]
theorem coe_maximalOrderUnitsEquiv
    (I : (maximalNumberFieldOrder K).invertibleProperFractionalIdeals) :
    (maximalOrderUnitsEquiv K I : FractionalIdeal (𝓞 K)⁰ K) =
      maximalOrderFractionalIdealEquiv K I := (rfl)

/-- Transport of fractional ideals sends the principal fractional ideal of `x` over the maximal
order to the principal fractional ideal of `x` over `𝓞 K`. -/
@[simp]
theorem maximalOrderUnitsEquiv_toPrincipalIdeal (x : Kˣ) :
    maximalOrderUnitsEquiv K (toPrincipalIdeal (maximalNumberFieldOrder K).toSubalgebra K x) =
      toPrincipalIdeal (𝓞 K) K x := by
  ext : 1
  simp [coe_toPrincipalIdeal]

variable (K) in
/-- **The wide Picard group of the maximal order is the class group of `𝓞 K`.** It is Mathlib's
`ClassGroup.mulEquiv` for `maximalOrderRingEquiv`. -/
def maximalOrderPicEquiv : Pic (maximalNumberFieldOrder K) ≃* ClassGroup (𝓞 K) :=
  ClassGroup.mulEquiv (maximalOrderRingEquiv K)

/-- `maximalOrderPicEquiv` sends the Picard class of an invertible fractional ideal of the maximal
order to the ideal class of the fractional ideal of `𝓞 K` with the same elements. -/
@[simp]
theorem maximalOrderPicEquiv_mkPic
    (I : (maximalNumberFieldOrder K).invertibleProperFractionalIdeals) :
    maximalOrderPicEquiv K ((maximalNumberFieldOrder K).mkPic I) =
      ClassGroup.mk K (maximalOrderUnitsEquiv K I) :=
  ClassGroup.mulEquiv_mk K _ I

private theorem maximalOrderUnitsEquiv_mem_narrowPrincipalSubgroup_iff
    {I : (maximalNumberFieldOrder K).invertibleProperFractionalIdeals} :
    maximalOrderUnitsEquiv K I ∈ narrowPrincipalSubgroup K ↔
      I ∈ (maximalNumberFieldOrder K).narrowPrincipal := by
  rw [mem_narrowPrincipalSubgroup, NumberFieldOrder.mem_narrowPrincipal_iff]
  simp only [← maximalOrderUnitsEquiv_toPrincipalIdeal, EmbeddingLike.apply_eq_iff_eq]

variable (K) in
/-- **The narrow Picard group of the maximal order is the narrow class group of `K`.** -/
def maximalOrderNarrowPicEquiv : NarrowPic (maximalNumberFieldOrder K) ≃* NarrowClassGroup K :=
  MonoidHom.toMulEquiv
    (NarrowPic.lift _ (NarrowClassGroup.mk.comp (maximalOrderUnitsEquiv K).toMonoidHom)
      fun I hI => by
        rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
          NarrowClassGroup.mk_eq_one_iff, maximalOrderUnitsEquiv_mem_narrowPrincipalSubgroup_iff]
        exact hI)
    (NarrowClassGroup.lift
      ((NarrowPic.mk _).comp (maximalOrderUnitsEquiv K).symm.toMonoidHom) fun J hJ => by
        obtain ⟨I, rfl⟩ := (maximalOrderUnitsEquiv K).surjective J
        rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
          MulEquiv.symm_apply_apply, NarrowPic.mk_eq_one_iff,
          ← maximalOrderUnitsEquiv_mem_narrowPrincipalSubgroup_iff]
        exact hJ)
    (MonoidHom.ext fun c => by
      obtain ⟨I, rfl⟩ := NarrowPic.mk_surjective _ c
      simp)
    (MonoidHom.ext fun c => by
      obtain ⟨J, rfl⟩ := NarrowClassGroup.mk_surjective c
      simp)

/-- `maximalOrderNarrowPicEquiv` sends the narrow Picard class of an invertible fractional ideal of
the maximal order to the narrow class of the fractional ideal of `𝓞 K` with the same elements. -/
@[simp]
theorem maximalOrderNarrowPicEquiv_mk
    (I : (maximalNumberFieldOrder K).invertibleProperFractionalIdeals) :
    maximalOrderNarrowPicEquiv K (NarrowPic.mk (maximalNumberFieldOrder K) I) =
      NarrowClassGroup.mk (maximalOrderUnitsEquiv K I) := by
  simp [maximalOrderNarrowPicEquiv]

/-- `maximalOrderNarrowPicEquiv` sends the narrow principal class of `x` to the narrow principal
class of `x`. -/
theorem maximalOrderNarrowPicEquiv_mkPrincipal (x : Kˣ) :
    maximalOrderNarrowPicEquiv K (NarrowPic.mkPrincipal (maximalNumberFieldOrder K) x) =
      NarrowClassGroup.mkPrincipal x := by
  rw [NarrowPic.mkPrincipal_apply, maximalOrderNarrowPicEquiv_mk,
    maximalOrderUnitsEquiv_toPrincipalIdeal, NarrowClassGroup.mkPrincipal_apply]

variable (K) in
/-- **The forgetful maps agree on the maximal order.** Under `maximalOrderNarrowPicEquiv` and
`maximalOrderPicEquiv`, the map `NarrowPic O → Pic O` of the maximal order is the map
`Cl⁺(K) → Cl(K)` forgetting positivity of generators. -/
theorem toClassGroup_comp_maximalOrderNarrowPicEquiv :
    (NarrowClassGroup.toClassGroup (K := K)).comp (maximalOrderNarrowPicEquiv K).toMonoidHom =
      (maximalOrderPicEquiv K).toMonoidHom.comp (maximalNumberFieldOrder K).narrowToPic := by
  refine MonoidHom.ext fun c => ?_
  obtain ⟨I, rfl⟩ := NarrowPic.mk_surjective _ c
  simp

/-- Elementwise form of `toClassGroup_comp_maximalOrderNarrowPicEquiv`. -/
theorem toClassGroup_maximalOrderNarrowPicEquiv (c : NarrowPic (maximalNumberFieldOrder K)) :
    NarrowClassGroup.toClassGroup (maximalOrderNarrowPicEquiv K c) =
      maximalOrderPicEquiv K ((maximalNumberFieldOrder K).narrowToPic c) :=
  DFunLike.congr_fun (toClassGroup_comp_maximalOrderNarrowPicEquiv K) c

end TauCeti.GlobalNumberFields
