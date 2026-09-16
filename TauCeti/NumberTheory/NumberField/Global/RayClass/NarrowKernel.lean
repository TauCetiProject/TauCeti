/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.RayClass.Narrow

import TauCeti.GroupTheory.QuotientGroup.KerEquiv

/-!
# The kernel of the narrow-to-wide class map

The difference between the narrow and ordinary class groups is controlled by signs at the real
places.  The signature of every field unit is realized, while the signatures of integer units
act trivially on principal ideals.  Consequently the quotient of all real sign patterns by the
signatures of integer units is canonically the kernel of the transition
`RayClassGroup (narrowModulus K) → RayClassGroup (Modulus.one K)`.

This file constructs the boundary from sign patterns to the kernel and proves the resulting
isomorphism.  Together with surjectivity of the transition map, this gives the exact
narrow-to-wide sequence

```text
(𝒪 K)ˣ → {±1}ʳ¹ → Cl⁺(K) → Cl(K) → 1.
```

The sign carrier is the one already used by `NumberField.fieldUnitSignature`: at each real place,
`realsˣ / realsˣ₊`.  It is canonically a two-element group at every coordinate.

## Main definitions and results

* `TauCeti.GlobalNumberFields.NarrowSignQuotient`: real sign patterns modulo the signatures of
  integer units.
* `TauCeti.GlobalNumberFields.narrowSignBoundary`: the boundary from sign patterns to the kernel
  of the narrow-to-wide transition.
* `TauCeti.GlobalNumberFields.narrowSignQuotientEquivKerClassMap`: the canonical equivalence from
  the sign quotient to that kernel.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
* S. Lang, *Algebraic Number Theory*, Chapter VI, §1.
-/

public section

open IsDedekindDomain NumberField
open scoped nonZeroDivisors NumberField

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

omit [NumberField K] in
/-- The subgroup of real sign patterns realized by units of the ring of integers. -/
noncomputable def integerUnitSignatures :
    Subgroup ({w : InfinitePlace K // w.IsReal} → (ℝˣ ⧸ Units.posSubgroup ℝ)) :=
  -- Supplying the product group explicitly keeps the `MulOne` projection definitionally aligned
  -- with the one carried by `unitSignature`.
  @MonoidHom.range (RingOfIntegers K)ˣ inferInstance
    ({w : InfinitePlace K // w.IsReal} → (ℝˣ ⧸ Units.posSubgroup ℝ)) Pi.group
    (NumberField.unitSignature (K := K))

omit [NumberField K] in
/-- A sign pattern belongs to `integerUnitSignatures` exactly when an integer unit realizes it. -/
@[simp] theorem mem_integerUnitSignatures_iff
    {s : {w : InfinitePlace K // w.IsReal} → (ℝˣ ⧸ Units.posSubgroup ℝ)} :
    s ∈ integerUnitSignatures (K := K) ↔
      ∃ u : (RingOfIntegers K)ˣ, NumberField.unitSignature u = s := by
  rw [integerUnitSignatures, MonoidHom.mem_range]

omit [NumberField K] in
/-- The subgroup of integer-unit signatures is normal because the real sign group is abelian. -/
noncomputable instance : (integerUnitSignatures (K := K)).Normal :=
  ⟨fun n hn g ↦ by
    rw [show g * n * g⁻¹ = n by
      funext w
      simp only [Pi.mul_apply, Pi.inv_apply]
      rw [mul_comm (g w), mul_assoc, mul_inv_cancel, mul_one]]
    exact hn⟩

/-- Real sign patterns modulo the signatures realized by the units of the ring of integers.

This quotient is the archimedean obstruction separating the narrow class group from the ordinary
class group. -/
abbrev NarrowSignQuotient (K : Type*) [Field K] :=
  ({w : InfinitePlace K // w.IsReal} → (ℝˣ ⧸ Units.posSubgroup ℝ)) ⧸
    integerUnitSignatures (K := K)

private noncomputable def narrowSignRayClass :
    ({w : InfinitePlace K // w.IsReal} → (ℝˣ ⧸ Units.posSubgroup ℝ)) →*
      RayClassGroup (narrowModulus K) :=
  -- As above, this explicit projection matches the product structure used by the signature map.
  @MonoidHom.comp _ _ _ Pi.mulOneClass.toMulOne inferInstance inferInstance
    (QuotientGroup.lift (totallyPositiveUnits (K := K))
      (narrowRayClassPrincipal (K := K)) fun _x hx ↦
        MonoidHom.mem_ker.mpr <| narrowRayClassPrincipal_eq_one_of_isTotallyPositive
          (mem_totallyPositiveUnits.mp hx))
    (NumberField.quotientTotallyPositiveUnitsEquiv (K := K)).symm.toMonoidHom

private theorem narrowSignRayClass_fieldUnitSignature (x : Kˣ) :
    narrowSignRayClass (K := K) (NumberField.fieldUnitSignature x) =
      narrowRayClassPrincipal x := by
  simp only [narrowSignRayClass, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  have hx : (NumberField.quotientTotallyPositiveUnitsEquiv (K := K)).symm
      (NumberField.fieldUnitSignature x) = QuotientGroup.mk x := by
    apply (NumberField.quotientTotallyPositiveUnitsEquiv (K := K)).injective
    simp only [MulEquiv.apply_symm_apply, NumberField.quotientTotallyPositiveUnitsEquiv_mk]
  rw [hx, QuotientGroup.lift_mk]

/-- The ray class of a sign pattern, regarded as an element of the kernel of the transition from
the narrow modulus to the trivial modulus.

Choose a field unit with the prescribed signs and take the narrow class of its principal ideal.
Changing the choice by a totally positive element does not change that ray class. -/
noncomputable def narrowSignBoundary :
    ({w : InfinitePlace K // w.IsReal} → (ℝˣ ⧸ Units.posSubgroup ℝ)) →*
      MonoidHom.ker (classMap (Modulus.one_dvd (narrowModulus K))) :=
  (narrowSignRayClass (K := K)).codRestrict _ fun s ↦ by
    obtain ⟨x, rfl⟩ := NumberField.fieldUnitSignature_surjective s
    rw [ker_classMap_narrowModulus]
    exact ⟨x, (narrowSignRayClass_fieldUnitSignature x).symm⟩

/-- The boundary of the signature of `x` is the narrow ray class of the principal ideal `(x)`. -/
@[simp] theorem coe_narrowSignBoundary_fieldUnitSignature (x : Kˣ) :
    (narrowSignBoundary (K := K) (NumberField.fieldUnitSignature x) :
      RayClassGroup (narrowModulus K)) = narrowRayClassPrincipal x := by
  exact narrowSignRayClass_fieldUnitSignature x

/-- The kernel of the sign boundary consists exactly of the signatures of integer units. -/
theorem ker_narrowSignBoundary :
    @MonoidHom.ker _ Pi.group _ inferInstance (narrowSignBoundary (K := K)) =
      integerUnitSignatures (K := K) := by
  ext s
  rw [MonoidHom.mem_ker, mem_integerUnitSignatures_iff]
  constructor
  · intro hs
    obtain ⟨x, rfl⟩ := NumberField.fieldUnitSignature_surjective s
    have hxray : narrowRayClassPrincipal (K := K) x = 1 := by
      simpa only [coe_narrowSignBoundary_fieldUnitSignature, OneMemClass.coe_one] using
        congrArg Subtype.val hs
    have hxclass : NarrowClassGroup.mkPrincipal (K := K) x = 1 := by
      simpa only [narrowEquivNarrowClassGroup_narrowRayClassPrincipal, map_one] using
        congrArg narrowEquivNarrowClassGroup hxray
    obtain ⟨u, hu⟩ := NarrowClassGroup.mkPrincipal_eq_one_iff.mp hxclass
    have husign : NumberField.unitSignature (K := K) u *
        NumberField.fieldUnitSignature x = 1 := by
      rw [NumberField.unitSignature_eq_fieldUnitSignature]
      rw [← map_mul, NumberField.fieldUnitSignature_eq_one_iff]
      convert hu using 1
      simp only [Units.smul_def, Algebra.smul_def, Units.val_mul, Units.coe_map,
        RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
    refine ⟨u⁻¹, ?_⟩
    rw [map_inv]
    exact inv_eq_of_mul_eq_one_right husign
  · rintro ⟨u, rfl⟩
    apply Subtype.ext
    rw [NumberField.unitSignature_eq_fieldUnitSignature]
    rw [coe_narrowSignBoundary_fieldUnitSignature]
    apply narrowEquivNarrowClassGroup.injective
    have hprincipal : NarrowClassGroup.mkPrincipal (K := K)
        (Units.map (algebraMap (RingOfIntegers K) K).toMonoidHom u) = 1 := by
      rw [NarrowClassGroup.mkPrincipal_eq_one_iff]
      refine ⟨u⁻¹, ?_⟩
      simp only [Units.smul_def, Algebra.smul_def, Units.coe_map, RingHom.toMonoidHom_eq_coe,
        MonoidHom.coe_coe]
      convert isTotallyPositive_one (K := K) using 1
      simp
    simpa only [narrowEquivNarrowClassGroup_narrowRayClassPrincipal,
      OneMemClass.coe_one, map_one] using hprincipal

/-- Every narrow class with trivial wide class is the boundary of a real sign pattern. -/
theorem narrowSignBoundary_surjective :
    Function.Surjective (narrowSignBoundary (K := K)) := by
  rintro ⟨c, hc⟩
  rw [ker_classMap_narrowModulus, MonoidHom.mem_range] at hc
  obtain ⟨x, rfl⟩ := hc
  refine ⟨NumberField.fieldUnitSignature x, Subtype.ext ?_⟩
  exact coe_narrowSignBoundary_fieldUnitSignature x

/-- **The kernel of the narrow-to-wide class map is the quotient of real sign patterns by the
signatures of integer units.** -/
noncomputable def narrowSignQuotientEquivKerClassMap :
    NarrowSignQuotient K ≃*
      MonoidHom.ker (classMap (Modulus.one_dvd (narrowModulus K))) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_narrowSignBoundary (K := K)).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _
      (narrowSignBoundary_surjective (K := K)))

/-- The kernel equivalence sends the class of a sign pattern to its narrow principal class. -/
@[simp] theorem narrowSignQuotientEquivKerClassMap_mk
    (s : {w : InfinitePlace K // w.IsReal} → (ℝˣ ⧸ Units.posSubgroup ℝ)) :
    narrowSignQuotientEquivKerClassMap (K := K) (QuotientGroup.mk s) =
      narrowSignBoundary s := by
  simp only [narrowSignQuotientEquivKerClassMap, MulEquiv.trans_apply,
    QuotientGroup.quotientMulEquivOfEq_mk,
    TauCeti.QuotientGroup.quotientKerEquivOfSurjective_apply_mk]

end TauCeti.GlobalNumberFields
