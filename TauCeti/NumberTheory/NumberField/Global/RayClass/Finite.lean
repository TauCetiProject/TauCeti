/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.RayClass.Residue
public import Mathlib.NumberTheory.NumberField.ClassNumber

import TauCeti.RingTheory.ClassGroup.Basic

/-!
# The ray class group of a modulus is finite

Let `𝔪` be a modulus of a number field `K`.  This file proves that `RayClassGroup 𝔪` is finite.

The argument runs along the two steps of the ray class exact sequence. The transition map to the
ordinary class group has finite image because the class group of a number field is finite, and its
kernel is the group of *principal* ideals prime to `𝔪`, modulo the ray.  That kernel is a quotient
of `primeToSubgroup 𝔪 ⧸ congruenceSubgroup 𝔪`, so everything rests on

`TauCeti.GlobalNumberFields.congruenceSubgroup_finiteIndex`: the elements congruent to one modulo
`𝔪` have finite index among the elements that are units at the primes dividing the finite part.

That relative finite-index statement uses the reduction homomorphism `residueHom 𝔪` constructed in
`TauCeti.NumberTheory.NumberField.Global.RayClass.Residue`: an element that reduces to one and is
totally positive is congruent to one modulo `𝔪`.

The unit-group form `unitsCongruenceSubgroup_finiteIndex` — the units of `𝓞 K` congruent to one
modulo `𝔪` have finite index in `(𝓞 K)ˣ` — is the same statement pulled back along
`(𝓞 K)ˣ → Kˣ`; it is the unit correction appearing in the ray class number formula, and the
finite-index input to the geometry-of-numbers count of ideals in a ray class.

## Main results

* `TauCeti.GlobalNumberFields.congruenceSubgroup_finiteIndex` and
  `TauCeti.GlobalNumberFields.unitsCongruenceSubgroup_finiteIndex`: the two finite-index
  statements.
* `TauCeti.GlobalNumberFields.finiteIndex_ray`: the ray has finite index in the group of
  invertible fractional ideals prime to the modulus.
* `TauCeti.GlobalNumberFields.finite_rayClassGroup`: the ray class group of a modulus is finite.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
* S. Lang, *Algebraic Number Theory*, Chapter VI, §1.
-/

public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped nonZeroDivisors NumberField

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-! ### Finiteness of the index -/

/-- **The elements congruent to one modulo `𝔪` have finite index among the elements that are units
at the primes dividing the finite part.**  This relative finite index is the arithmetic content
behind the finiteness of the ray class group. -/
instance congruenceSubgroup_finiteIndex (𝔪 : Modulus K) :
    ((congruenceSubgroup 𝔪).subgroupOf (primeToSubgroup 𝔪)).FiniteIndex := by
  let _ : NeZero 𝔪.finitePart := ⟨𝔪.finitePart_ne_bot⟩
  have hker : (residueHom 𝔪).ker.FiniteIndex := Subgroup.finiteIndex_ker _
  have hle : (residueHom 𝔪).ker ⊓
      (totallyPositiveUnits.subgroupOf (primeToSubgroup 𝔪)) ≤
        (congruenceSubgroup 𝔪).subgroupOf (primeToSubgroup 𝔪) := by
    rintro ⟨x, hx⟩ ⟨h1, h2⟩
    refine Subgroup.mem_subgroupOf.mpr (mem_congruenceSubgroup.mpr ?_)
    refine isCongrOne_of_residue_eq_one hx ?_
      fun w _ ↦ isTotallyPositive_iff.mp (mem_totallyPositiveUnits.mp h2) w.1 w.2
    rw [← coe_residueHom 𝔪 ⟨x, hx⟩, MonoidHom.mem_ker.mp h1, Units.val_one]
  exact Subgroup.finiteIndex_of_le hle

/-- The image of an integer unit is a unit at every finite place, hence lies in
`primeToSubgroup 𝔪`. -/
private theorem unitsMap_mem_primeToSubgroup (𝔪 : Modulus K) (u : (𝓞 K)ˣ) :
    Units.map (algebraMap (𝓞 K) K).toMonoidHom u ∈ primeToSubgroup 𝔪 := by
  refine mem_primeToSubgroup.mpr fun v _ ↦ ?_
  rw [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, valuation_of_algebraMap]
  refine intValuation_eq_one_iff.mpr fun hu ↦ v.isPrime.ne_top ?_
  exact Ideal.eq_top_of_isUnit_mem _ hu u.isUnit

/-- The inclusion of the integer units into the elements that are units at the finite part. -/
private noncomputable def unitsToPrimeToSubgroup (𝔪 : Modulus K) :
    (𝓞 K)ˣ →* primeToSubgroup 𝔪 :=
  MonoidHom.codRestrict (Units.map (algebraMap (𝓞 K) K).toMonoidHom) _
    (unitsMap_mem_primeToSubgroup 𝔪)

@[simp] private theorem coe_unitsToPrimeToSubgroup (𝔪 : Modulus K) (u : (𝓞 K)ˣ) :
    ((unitsToPrimeToSubgroup 𝔪 u : primeToSubgroup 𝔪) : Kˣ) =
      Units.map (algebraMap (𝓞 K) K).toMonoidHom u := by
  rw [unitsToPrimeToSubgroup, MonoidHom.codRestrict_apply]

/-- **The units congruent to one modulo `𝔪` have finite index in `(𝓞 K)ˣ`.**  This is the unit
correction in the ray class number formula, and the input that makes the implied constants of the
ray-class ideal count uniform in the class. -/
instance unitsCongruenceSubgroup_finiteIndex (𝔪 : Modulus K) :
    (unitsCongruenceSubgroup 𝔪).FiniteIndex := by
  have hcomap : ((congruenceSubgroup 𝔪).subgroupOf (primeToSubgroup 𝔪)).comap
      (unitsToPrimeToSubgroup 𝔪) = unitsCongruenceSubgroup 𝔪 := by
    ext u
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, mem_unitsCongruenceSubgroup,
      mem_congruenceSubgroup, coe_unitsToPrimeToSubgroup]
  rw [← hcomap]
  infer_instance

/-! ### Finiteness of the ray class group -/

/-- The principal ideal of an element that is a unit at the finite part, viewed in the kernel of
`idealsPrimeToClassGroup`. -/
private noncomputable def principalIdealHom (𝔪 : Modulus K) :
    primeToSubgroup 𝔪 →* (idealsPrimeToClassGroup 𝔪).ker :=
  MonoidHom.codRestrict (principalIdealPrimeTo 𝔪) (idealsPrimeToClassGroup 𝔪).ker fun x ↦ by
    rw [MonoidHom.mem_ker, idealsPrimeToClassGroup_apply, coe_principalIdealPrimeTo]
    exact ClassGroup.mk_toPrincipalIdeal (x : Kˣ)

@[simp] private theorem coe_principalIdealHom (𝔪 : Modulus K) (x : primeToSubgroup 𝔪) :
    (((principalIdealHom 𝔪 x : (idealsPrimeToClassGroup 𝔪).ker) : idealsPrimeTo 𝔪) :
        (FractionalIdeal (𝓞 K)⁰ K)ˣ) =
      toPrincipalIdeal (𝓞 K) K (x : Kˣ) := by
  rw [principalIdealHom, MonoidHom.codRestrict_apply, coe_principalIdealPrimeTo]

private theorem principalIdealHom_surjective (𝔪 : Modulus K) :
    Function.Surjective (principalIdealHom 𝔪) := by
  intro I
  have hI : (I : idealsPrimeTo 𝔪) ∈ (principalIdealPrimeTo 𝔪).range := by
    rw [range_principalIdealPrimeTo]
    exact I.2
  obtain ⟨x, hx⟩ := hI
  exact ⟨x, Subtype.ext hx⟩

/-- **The ray has finite index in the invertible fractional ideals prime to `𝔪`.**  This index is
the ray class number, and its finiteness is what makes `RayClassGroup 𝔪` a finite group. -/
instance finiteIndex_ray (𝔪 : Modulus K) : (ray 𝔪).FiniteIndex := by
  refine ⟨?_⟩
  have hle : ray 𝔪 ≤ (idealsPrimeToClassGroup 𝔪).ker := by
    intro I hI
    obtain ⟨x, _, hxI⟩ := mem_ray_iff.mp hI
    rw [MonoidHom.mem_ker, idealsPrimeToClassGroup_apply,
      ClassGroup.mk_eq_one_iff_exists]
    exact ⟨x, hxI⟩
  let _ : (idealsPrimeToClassGroup 𝔪).ker.FiniteIndex := Subgroup.finiteIndex_ker _
  have hkerindex : (idealsPrimeToClassGroup 𝔪).ker.index ≠ 0 :=
    Subgroup.FiniteIndex.index_ne_zero
  have hrel : (ray 𝔪).relIndex (idealsPrimeToClassGroup 𝔪).ker ≠ 0 := by
    rw [Subgroup.relIndex, Subgroup.index_eq_card]
    refine Nat.card_ne_zero.mpr ⟨⟨1⟩, ?_⟩
    have hsurj : Function.Surjective
        ((QuotientGroup.mk' ((ray 𝔪).subgroupOf (idealsPrimeToClassGroup 𝔪).ker)).comp
          (principalIdealHom 𝔪)) :=
      (QuotientGroup.mk'_surjective _).comp (principalIdealHom_surjective 𝔪)
    have hkerle : ∀ x ∈ (congruenceSubgroup 𝔪).subgroupOf (primeToSubgroup 𝔪),
        ((QuotientGroup.mk' ((ray 𝔪).subgroupOf (idealsPrimeToClassGroup 𝔪).ker)).comp
          (principalIdealHom 𝔪)) x = 1 := by
      intro x hxmem
      rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
        Subgroup.mem_subgroupOf]
      exact mem_ray_iff.mpr
        ⟨(x : Kˣ), mem_congruenceSubgroup.mp (Subgroup.mem_subgroupOf.mp hxmem),
          (coe_principalIdealHom 𝔪 x).symm⟩
    refine Finite.of_surjective (QuotientGroup.lift _ _ hkerle) fun z ↦ ?_
    obtain ⟨y, hy⟩ := hsurj z
    exact ⟨QuotientGroup.mk y, hy⟩
  rw [← Subgroup.relIndex_mul_index hle]
  exact mul_ne_zero hrel hkerindex

/-- **The ray class group of a modulus is finite.**  This is the finiteness underlying the ray class
number, and what makes a ray class character a character of a finite abelian group. -/
instance finite_rayClassGroup (𝔪 : Modulus K) : Finite (RayClassGroup 𝔪) := by
  have hquot : Finite (idealsPrimeTo 𝔪 ⧸ ray 𝔪) := Subgroup.finite_quotient_of_finiteIndex
  refine Finite.of_surjective
    (QuotientGroup.lift (ray 𝔪) (rayClassMk 𝔪) fun x hx ↦ rayClassMk_eq_one_iff.mpr hx)
    fun c ↦ ?_
  obtain ⟨I, hI⟩ := rayClassMk_surjective 𝔪 c
  exact ⟨QuotientGroup.mk I, hI⟩

end TauCeti.GlobalNumberFields
