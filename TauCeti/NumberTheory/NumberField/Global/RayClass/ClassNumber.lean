/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.RayClass.CongruenceQuotient
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Exact
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Finite

import TauCeti.RingTheory.ClassGroup.Basic

/-!
# The ray class exact sequence and the ray class number formula

Let `𝔪` be a modulus of a number field `K`, and write
`A 𝔪 = (𝓞 K ⧸ 𝔪.finitePart)ˣ × (𝔪.infinitePart → ℤˣ)` for its residue units and prescribed signs.
This file completes the ray class exact sequence

```text
1 → unitsCongruenceSubgroup 𝔪 → (𝓞 K)ˣ → A 𝔪 → RayClassGroup 𝔪 → ClassGroup (𝓞 K) → 1
```

and reads off the ray class number formula

```text
#(RayClassGroup 𝔪) * [(𝓞 K)ˣ : unitsCongruenceSubgroup 𝔪]
  = #(ClassGroup (𝓞 K)) * #(𝓞 K ⧸ 𝔪.finitePart)ˣ * 2 ^ #𝔪.infinitePart.
```

The right-hand tail `A 𝔪 → RayClassGroup 𝔪 → ClassGroup (𝓞 K) → 1` refines the exact tail of
`TauCeti.NumberTheory.NumberField.Global.RayClass.Exact`, whose left-hand term is the larger group
`primeToSubgroup 𝔪`: by `residueSignEquiv`, the principal ray class of an element prime to `𝔪`
depends only on its residue and its signs, so `principalRayClass 𝔪` descends to `A 𝔪`.

The left-hand part is the unit obstruction.  An element prime to `𝔪` has trivial principal ray
class exactly when it becomes congruent to one after multiplication by a global unit
(`principalRayClass_eq_one_iff`), so the kernel of `A 𝔪 → RayClassGroup 𝔪` is the image of the
integer units, and the kernel of `(𝓞 K)ˣ → A 𝔪` is the group of units congruent to one.  That image
is what glues the residue units, the signs and the ordinary class group together inside the ray
class group; in general `RayClassGroup 𝔪` is not the product of the three.

At the narrow modulus the residue factor is trivial and the formula becomes
`#(RayClassGroup (narrowModulus K)) * [(𝓞 K)ˣ : (𝓞 K)ˣ⁺] = #(ClassGroup (𝓞 K)) * 2 ^ r₁`, with
`(𝓞 K)ˣ⁺` the totally positive units and `r₁` the number of real places.

## Main definitions

* `TauCeti.GlobalNumberFields.unitsResidueSignHom`: the residues and signs of the integer units.
* `TauCeti.GlobalNumberFields.residueSignRayClass`: the principal ray class of a residue unit and
  sign pattern.

## Main results

* `TauCeti.GlobalNumberFields.principalRayClass_eq_one_iff`: a principal ray class is trivial
  exactly when a unit multiple of its generator is congruent to one.
* `TauCeti.GlobalNumberFields.ker_unitsResidueSignHom`,
  `TauCeti.GlobalNumberFields.ker_residueSignRayClass` and
  `TauCeti.GlobalNumberFields.range_residueSignRayClass`: exactness at `(𝓞 K)ˣ`, at `A 𝔪` and at
  `RayClassGroup 𝔪`.
* `TauCeti.GlobalNumberFields.card_ker_rayClassToClassGroup_mul_index`: the order of the kernel of
  `RayClassGroup 𝔪 → ClassGroup (𝓞 K)`.
* `TauCeti.GlobalNumberFields.card_rayClassGroup_mul_index` and
  `TauCeti.GlobalNumberFields.card_rayClassGroup`: the ray class number formula.
* `TauCeti.GlobalNumberFields.card_rayClassGroup_narrowModulus_mul_index`: its narrow case.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, (1.10) and (1.11).
* S. Lang, *Algebraic Number Theory*, Chapter VI, §1, Theorem 1.
-/

public section

open IsDedekindDomain NumberField
open scoped nonZeroDivisors NumberField

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-! ### Triviality of a principal ray class -/

/-- **A principal ray class is trivial exactly when a unit multiple of the generator is congruent
to one.**  Two generators of the same principal fractional ideal differ by a unit of `𝓞 K`, so the
ray only sees an element of `primeToSubgroup 𝔪` up to the integer units. -/
theorem principalRayClass_eq_one_iff {𝔪 : Modulus K} (x : primeToSubgroup 𝔪) :
    principalRayClass 𝔪 x = 1 ↔
      ∃ u : (𝓞 K)ˣ, IsCongrOne 𝔪 (Units.map (algebraMap (𝓞 K) K).toMonoidHom u * x) := by
  rw [principalRayClass_apply, rayClassMk_eq_one_iff, mem_ray_iff, coe_principalIdealPrimeTo]
  refine ⟨fun ⟨y, hy, hyx⟩ ↦ ?_, fun ⟨u, hu⟩ ↦ ⟨_, hu, ?_⟩⟩
  · obtain ⟨u, hu⟩ := (FractionalIdeal.toPrincipalIdeal_eq_one_iff (y * (x : Kˣ)⁻¹)).mp
      (by rw [map_mul, map_inv, hyx, mul_inv_cancel])
    refine ⟨u, ?_⟩
    have hu' : Units.map (algebraMap (𝓞 K) K).toMonoidHom u = y * (x : Kˣ)⁻¹ := hu
    rwa [hu', inv_mul_cancel_right]
  · have hu1 : toPrincipalIdeal (𝓞 K) K (Units.map (algebraMap (𝓞 K) K).toMonoidHom u) = 1 :=
      (FractionalIdeal.toPrincipalIdeal_eq_one_iff _).mpr ⟨u, rfl⟩
    rw [map_mul, hu1, one_mul]

/-! ### The residue-and-sign map to the ray class group -/

/-- **The residues and signs of the integer units.**  This is the left-hand map of the ray class
exact sequence; its image is the obstruction that is divided out of the residue units and signs
before they embed into the ray class group. -/
noncomputable def unitsResidueSignHom (𝔪 : Modulus K) :
    (𝓞 K)ˣ →* (𝓞 K ⧸ 𝔪.finitePart)ˣ × (𝔪.infinitePart → ℤˣ) :=
  (residueSignHom 𝔪).comp (unitsToPrimeToSubgroup 𝔪)

@[simp] theorem unitsResidueSignHom_apply (𝔪 : Modulus K) (u : (𝓞 K)ˣ) :
    unitsResidueSignHom 𝔪 u = residueSignHom 𝔪 (unitsToPrimeToSubgroup 𝔪 u) := (rfl)

/-- **Exactness at the integer units**: a unit has trivial residue and trivial signs exactly when
it is congruent to one modulo `𝔪`. -/
theorem ker_unitsResidueSignHom (𝔪 : Modulus K) :
    (unitsResidueSignHom 𝔪).ker = unitsCongruenceSubgroup 𝔪 := by
  ext u
  rw [MonoidHom.mem_ker, unitsResidueSignHom_apply, residueSignHom_eq_one_iff,
    coe_unitsToPrimeToSubgroup, mem_unitsCongruenceSubgroup, mem_congruenceSubgroup]

/-- **The principal ray class of a residue unit and a sign pattern.**  The principal ray class of
an element prime to `𝔪` depends only on its residue modulo the finite part and its signs at the
real places of `𝔪`, and every residue unit and sign pattern arises (`residueSignEquiv`); this is
the induced homomorphism. -/
noncomputable def residueSignRayClass (𝔪 : Modulus K) :
    (𝓞 K ⧸ 𝔪.finitePart)ˣ × (𝔪.infinitePart → ℤˣ) →* RayClassGroup 𝔪 :=
  (QuotientGroup.lift _ (principalRayClass 𝔪) fun _ hx ↦ MonoidHom.mem_ker.mpr <|
      principalRayClass_eq_one_of_isCongrOne
        (mem_congruenceSubgroup.mp (Subgroup.mem_subgroupOf.mp hx))).comp
    (residueSignEquiv 𝔪).symm.toMonoidHom

/-- The class attached to the residue and signs of an element is its principal ray class. -/
@[simp] theorem residueSignRayClass_residueSignHom (𝔪 : Modulus K) (x : primeToSubgroup 𝔪) :
    residueSignRayClass 𝔪 (residueSignHom 𝔪 x) = principalRayClass 𝔪 x := by
  rw [residueSignRayClass, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    (residueSignEquiv 𝔪).symm_apply_eq.mpr (residueSignEquiv_apply_mk 𝔪 x).symm,
    QuotientGroup.lift_mk]

/-- `residueSignRayClass 𝔪` is the factorization of `principalRayClass 𝔪` through the surjection
`residueSignHom 𝔪`. -/
theorem residueSignRayClass_comp_residueSignHom (𝔪 : Modulus K) :
    (residueSignRayClass 𝔪).comp (residueSignHom 𝔪) = principalRayClass 𝔪 :=
  MonoidHom.ext (residueSignRayClass_residueSignHom 𝔪)

/-- **Exactness at the residue units and signs**: a residue unit and sign pattern has trivial ray
class exactly when it is the residue and sign pattern of an integer unit. -/
theorem ker_residueSignRayClass (𝔪 : Modulus K) :
    (residueSignRayClass 𝔪).ker = (unitsResidueSignHom 𝔪).range := by
  ext a
  obtain ⟨x, rfl⟩ := residueSignHom_surjective 𝔪 a
  rw [MonoidHom.mem_ker, residueSignRayClass_residueSignHom, principalRayClass_eq_one_iff,
    MonoidHom.mem_range]
  refine ⟨fun ⟨u, hu⟩ ↦ ⟨u⁻¹, ?_⟩, fun ⟨u, hu⟩ ↦ ⟨u⁻¹, ?_⟩⟩
  · have h := (residueSignHom_eq_one_iff (unitsToPrimeToSubgroup 𝔪 u * x)).mpr
      (by rwa [Subgroup.coe_mul, coe_unitsToPrimeToSubgroup, mem_congruenceSubgroup])
    rw [map_mul] at h
    rw [unitsResidueSignHom_apply, map_inv, map_inv, inv_eq_of_mul_eq_one_right h]
  · have h : residueSignHom 𝔪 (unitsToPrimeToSubgroup 𝔪 u⁻¹ * x) = 1 := by
      rw [map_mul, map_inv, map_inv, ← unitsResidueSignHom_apply, hu, inv_mul_cancel]
    rwa [residueSignHom_eq_one_iff, Subgroup.coe_mul, coe_unitsToPrimeToSubgroup,
      mem_congruenceSubgroup] at h

/-- **Exactness at the ray class group**: the ray classes with trivial ordinary ideal class are
exactly the classes of residue units and sign patterns. -/
theorem range_residueSignRayClass (𝔪 : Modulus K) :
    (residueSignRayClass 𝔪).range = (rayClassToClassGroup 𝔪).ker := by
  rw [ker_rayClassToClassGroup, ← residueSignRayClass_comp_residueSignHom, MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr (residueSignHom_surjective 𝔪), ← MonoidHom.range_eq_map]

/-- Exactness at the residue units and signs, as a `Function.MulExact` statement. -/
theorem mulExact_unitsResidueSignHom_residueSignRayClass (𝔪 : Modulus K) :
    Function.MulExact (unitsResidueSignHom 𝔪) (residueSignRayClass 𝔪) :=
  MonoidHom.mulExact_iff.mpr (ker_residueSignRayClass 𝔪)

/-- Exactness at the ray class group, as a `Function.MulExact` statement. -/
theorem mulExact_residueSignRayClass_rayClassToClassGroup (𝔪 : Modulus K) :
    Function.MulExact (residueSignRayClass 𝔪) (rayClassToClassGroup 𝔪) :=
  MonoidHom.mulExact_iff.mpr (range_residueSignRayClass 𝔪).symm

/-! ### The ray class number formula -/

/-- **The order of the kernel of `RayClassGroup 𝔪 → ClassGroup (𝓞 K)`.**  The kernel is the group of
residue units and sign patterns modulo the image of the integer units, and that image has order the
index of the units congruent to one. -/
theorem card_ker_rayClassToClassGroup_mul_index (𝔪 : Modulus K) :
    Nat.card (rayClassToClassGroup 𝔪).ker * (unitsCongruenceSubgroup 𝔪).index =
      Nat.card (𝓞 K ⧸ 𝔪.finitePart)ˣ * 2 ^ 𝔪.infinitePart.card := by
  -- The image of the units has order the index of its kernel, and the residue units and signs
  -- are counted by the index of the kernel of the (surjective) residue-and-sign presentation.
  have hunits : Nat.card (unitsResidueSignHom 𝔪).range = (unitsCongruenceSubgroup 𝔪).index := by
    rw [← Subgroup.index_ker, ker_unitsResidueSignHom]
  have hA : Nat.card ((𝓞 K ⧸ 𝔪.finitePart)ˣ × (𝔪.infinitePart → ℤˣ)) =
      Nat.card (𝓞 K ⧸ 𝔪.finitePart)ˣ * 2 ^ 𝔪.infinitePart.card := by
    rw [← relIndex_congruenceSubgroup, Subgroup.relIndex, ← ker_residueSignHom, Subgroup.index_ker,
      MonoidHom.range_eq_top.mpr (residueSignHom_surjective 𝔪), Subgroup.card_top]
  rw [← range_residueSignRayClass, ← hunits, ← hA, ← (residueSignRayClass 𝔪).ker.card_mul_index,
    Subgroup.index_ker, ker_residueSignRayClass, mul_comm]

/-- **The ray class number formula.**  The order of the ray class group, times the index of the
units congruent to one modulo `𝔪`, is the class number times the number of residue units modulo the
finite part times two for each real place of the infinite part. -/
theorem card_rayClassGroup_mul_index (𝔪 : Modulus K) :
    Nat.card (RayClassGroup 𝔪) * (unitsCongruenceSubgroup 𝔪).index =
      Nat.card (ClassGroup (𝓞 K)) *
        (Nat.card (𝓞 K ⧸ 𝔪.finitePart)ˣ * 2 ^ 𝔪.infinitePart.card) := by
  rw [← card_ker_rayClassToClassGroup_mul_index, ← (rayClassToClassGroup 𝔪).ker.card_mul_index,
    Subgroup.index_ker, MonoidHom.range_eq_top.mpr (rayClassToClassGroup_surjective 𝔪),
    Subgroup.card_top]
  ring

/-- **The ray class number formula**, solved for the ray class number:
`h_𝔪 = h · #(𝓞 K ⧸ 𝔪₀)ˣ · 2 ^ #𝔪∞ / [(𝓞 K)ˣ : unitsCongruenceSubgroup 𝔪]`. -/
theorem card_rayClassGroup (𝔪 : Modulus K) :
    Nat.card (RayClassGroup 𝔪) =
      Nat.card (ClassGroup (𝓞 K)) *
        (Nat.card (𝓞 K ⧸ 𝔪.finitePart)ˣ * 2 ^ 𝔪.infinitePart.card) /
          (unitsCongruenceSubgroup 𝔪).index :=
  Nat.eq_div_of_mul_eq_left Subgroup.FiniteIndex.index_ne_zero (card_rayClassGroup_mul_index 𝔪)

/-- **The narrow class number formula.**  At the narrow modulus there are no residue units to count,
and the units congruent to one are the totally positive units, so
`h⁺ · [(𝓞 K)ˣ : (𝓞 K)ˣ⁺] = h · 2 ^ r₁`. -/
theorem card_rayClassGroup_narrowModulus_mul_index :
    Nat.card (RayClassGroup (narrowModulus K)) * (unitsCongruenceSubgroup (narrowModulus K)).index =
      Nat.card (ClassGroup (𝓞 K)) * 2 ^ InfinitePlace.nrRealPlaces K := by
  have hres : Nat.card (𝓞 K ⧸ (narrowModulus K).finitePart)ˣ = 1 := by
    rw [narrowModulus_finitePart]
    exact Nat.card_unique
  have hinf : (narrowModulus K).infinitePart.card = InfinitePlace.nrRealPlaces K := by
    classical
    rw [Finset.eq_univ_of_forall mem_narrowModulus_infinitePart]
    -- `nrRealPlaces` counts with Mathlib's classical `Fintype` instance on the real places;
    -- `convert` identifies it with the one chosen here.
    convert Finset.card_univ
  rw [card_rayClassGroup_mul_index, hres, hinf, one_mul]

end TauCeti.GlobalNumberFields
