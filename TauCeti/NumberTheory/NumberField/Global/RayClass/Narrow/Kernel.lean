/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.RayClass.Narrow.Basic

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
noncomputable instance : (integerUnitSignatures (K := K)).Normal := by
  let _ : IsMulCommutative
      ({w : InfinitePlace K // w.IsReal} → (ℝˣ ⧸ Units.posSubgroup ℝ)) :=
    IsMulCommutative.of_comm fun a b ↦ by
      ext w
      exact mul_comm (a w) (b w)
  exact Subgroup.normal_of_isMulCommutative _

/-- Real sign patterns modulo the signatures realized by the units of the ring of integers.

This quotient is the archimedean obstruction separating the narrow class group from the ordinary
class group. -/
abbrev NarrowSignQuotient (K : Type*) [Field K] :=
  ({w : InfinitePlace K // w.IsReal} → (ℝˣ ⧸ Units.posSubgroup ℝ)) ⧸
    integerUnitSignatures (K := K)

/-- The residue-and-sign group for the narrow modulus is just the group of all real sign
patterns: its finite residue factor is trivial, and its infinite part contains every real place. -/
private noncomputable def narrowSignResidueEquiv :
    ({w : InfinitePlace K // w.IsReal} → (ℝˣ ⧸ Units.posSubgroup ℝ)) ≃*
      (RingOfIntegers K ⧸ (narrowModulus K).finitePart)ˣ ×
        ((narrowModulus K).infinitePart → ℤˣ) := by
  let _ : Subsingleton (RingOfIntegers K ⧸ (narrowModulus K).finitePart) :=
    Ideal.Quotient.subsingleton_iff.mpr narrowModulus_finitePart
  exact
    { toFun := fun s ↦ (1, fun w ↦ Units.signEquiv ℝ (s w.1))
      invFun := fun a w ↦ (Units.signEquiv ℝ).symm
        (a.2 ⟨w, mem_narrowModulus_infinitePart w⟩)
      left_inv := fun s ↦ by
        funext w
        exact (Units.signEquiv ℝ).symm_apply_apply (s w)
      right_inv := fun a ↦ by
        apply Prod.ext
        · exact Subsingleton.elim _ _
        · funext w
          exact (Units.signEquiv ℝ).apply_symm_apply (a.2 w)
      map_mul' := fun s t ↦ by
        apply Prod.ext
        · exact Subsingleton.elim _ _
        · funext w
          exact map_mul (Units.signEquiv ℝ) (s w.1) (t w.1) }

private theorem mem_primeToSubgroup_narrowModulus (x : Kˣ) :
    x ∈ primeToSubgroup (narrowModulus K) := by
  rw [mem_primeToSubgroup]
  intro v hv
  exfalso
  have : v ∈ (narrowModulus K).support := (Modulus.mem_support_iff _ _).mpr hv
  simp only [narrowModulus_support, Finset.notMem_empty] at this

private noncomputable def narrowPrimeToEquiv :
    primeToSubgroup (narrowModulus K) ≃* Kˣ where
  toFun x := x
  invFun x := ⟨x, mem_primeToSubgroup_narrowModulus x⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[simp] private theorem narrowSignResidueEquiv_fst
    (s : {w : InfinitePlace K // w.IsReal} → (ℝˣ ⧸ Units.posSubgroup ℝ)) :
    (narrowSignResidueEquiv (K := K) s).1 = 1 := rfl

@[simp] private theorem narrowSignResidueEquiv_snd
    (s : {w : InfinitePlace K // w.IsReal} → (ℝˣ ⧸ Units.posSubgroup ℝ))
    (w : (narrowModulus K).infinitePart) :
    (narrowSignResidueEquiv (K := K) s).2 w = Units.signEquiv ℝ (s w.1) := rfl

@[simp] private theorem coe_narrowPrimeToEquiv_symm (x : Kˣ) :
    ((narrowPrimeToEquiv (K := K)).symm x : Kˣ) = x := rfl

private theorem narrowSignResidueEquiv_fieldUnitSignature (x : Kˣ) :
    narrowSignResidueEquiv (K := K) (NumberField.fieldUnitSignature x) =
      residueSignHom (narrowModulus K) ((narrowPrimeToEquiv (K := K)).symm x) := by
  let _ : Subsingleton (RingOfIntegers K ⧸ (narrowModulus K).finitePart) :=
    Ideal.Quotient.subsingleton_iff.mpr narrowModulus_finitePart
  apply Prod.ext
  · rw [narrowSignResidueEquiv_fst]
    apply Units.ext
    exact Subsingleton.elim _ _
  · funext w
    rw [narrowSignResidueEquiv_snd, residueSignHom_snd, modulusSignHom_apply,
      coe_narrowPrimeToEquiv_symm]
    exact (signHom_apply x w.1).symm

private theorem narrowSignResidueEquiv_unitSignature (u : (RingOfIntegers K)ˣ) :
    narrowSignResidueEquiv (K := K) (NumberField.unitSignature u) =
      unitsResidueSignHom (narrowModulus K) u := by
  rw [NumberField.unitSignature_eq_fieldUnitSignature,
    narrowSignResidueEquiv_fieldUnitSignature, unitsResidueSignHom_apply]
  congr 1
  apply Subtype.ext
  rw [coe_narrowPrimeToEquiv_symm, coe_unitsToPrimeToSubgroup]

private theorem principalRayClass_narrowPrimeToEquiv (x : Kˣ) :
    principalRayClass (narrowModulus K) ((narrowPrimeToEquiv (K := K)).symm x) =
      narrowRayClassPrincipal x := by
  apply narrowEquivNarrowClassGroup.injective
  rw [narrowEquivNarrowClassGroup_narrowRayClassPrincipal, principalRayClass_apply,
    narrowEquivNarrowClassGroup_rayClassMk, NarrowClassGroup.mkPrincipal_apply]
  congr 1
  rw [coe_principalIdealPrimeTo, coe_narrowPrimeToEquiv_symm]

private noncomputable def narrowSignRayClass :
    ({w : InfinitePlace K // w.IsReal} → (ℝˣ ⧸ Units.posSubgroup ℝ)) →*
      RayClassGroup (narrowModulus K) :=
  (residueSignRayClass (narrowModulus K)).comp
    (narrowSignResidueEquiv (K := K)).toMonoidHom

private theorem narrowSignRayClass_fieldUnitSignature (x : Kˣ) :
    narrowSignRayClass (K := K) (NumberField.fieldUnitSignature x) =
      narrowRayClassPrincipal x := by
  rw [narrowSignRayClass, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    narrowSignResidueEquiv_fieldUnitSignature,
    residueSignRayClass_residueSignHom, principalRayClass_narrowPrimeToEquiv]

/-- The ray class of a sign pattern, regarded as an element of the kernel of the transition from
the narrow modulus to the trivial modulus.

Choose a field unit with the prescribed signs and take the narrow class of its principal ideal.
Changing the choice by a totally positive element does not change that ray class. -/
noncomputable def narrowSignBoundary :
    ({w : InfinitePlace K // w.IsReal} → (ℝˣ ⧸ Units.posSubgroup ℝ)) →*
      MonoidHom.ker (classMap (Modulus.one_dvd (narrowModulus K))) :=
  (narrowSignRayClass (K := K)).codRestrict _ fun s ↦ by
    have hs : rayClassToClassGroup (narrowModulus K) (narrowSignRayClass s) = 1 := by
      rw [← MonoidHom.mem_ker, ← range_residueSignRayClass]
      exact ⟨narrowSignResidueEquiv s, rfl⟩
    rw [rayClassToClassGroup_eq_oneEquivClassGroup_comp_classMap,
      MonoidHom.comp_apply] at hs
    exact MonoidHom.mem_ker.mpr <| oneEquivClassGroup.injective <| by simpa only [map_one]

private theorem coe_narrowSignBoundary
    (s : {w : InfinitePlace K // w.IsReal} → (ℝˣ ⧸ Units.posSubgroup ℝ)) :
    (narrowSignBoundary (K := K) s : RayClassGroup (narrowModulus K)) =
      narrowSignRayClass s := rfl

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
    have hs' : narrowSignRayClass s = 1 := by
      simpa only [coe_narrowSignBoundary, OneMemClass.coe_one] using congrArg Subtype.val hs
    rw [narrowSignRayClass, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      ← MonoidHom.mem_ker, ker_residueSignRayClass, MonoidHom.mem_range] at hs'
    obtain ⟨u, hu⟩ := hs'
    refine ⟨u, (narrowSignResidueEquiv (K := K)).injective ?_⟩
    rw [narrowSignResidueEquiv_unitSignature, hu]
  · rintro ⟨u, rfl⟩
    apply Subtype.ext
    rw [coe_narrowSignBoundary, OneMemClass.coe_one, narrowSignRayClass, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, ← MonoidHom.mem_ker, ker_residueSignRayClass,
      MonoidHom.mem_range]
    exact ⟨u, (narrowSignResidueEquiv_unitSignature u).symm⟩

/-- Every narrow class with trivial wide class is the boundary of a real sign pattern. -/
theorem narrowSignBoundary_surjective :
    Function.Surjective (narrowSignBoundary (K := K)) := by
  rintro ⟨c, hc⟩
  have hc' : c ∈ (rayClassToClassGroup (narrowModulus K)).ker := by
    rw [MonoidHom.mem_ker, rayClassToClassGroup_eq_oneEquivClassGroup_comp_classMap,
      MonoidHom.comp_apply, hc, map_one]
  rw [← range_residueSignRayClass, MonoidHom.mem_range] at hc'
  obtain ⟨a, ha⟩ := hc'
  obtain ⟨s, rfl⟩ := (narrowSignResidueEquiv (K := K)).surjective a
  exact ⟨s, Subtype.ext ha⟩

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
