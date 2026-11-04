/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.RayClass.Exact
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Finite

/-!
# The ray class number formula

Let `𝔪` be a modulus of a number field `K`, and write
`A 𝔪 = (𝓞 K ⧸ 𝔪.finitePart)ˣ × (𝔪.infinitePart → ℤˣ)` for its residue units and prescribed signs.
The exact sequence constructed in `TauCeti.NumberTheory.NumberField.Global.RayClass.Exact` is

```text
1 → unitsCongruenceSubgroup 𝔪 → (𝓞 K)ˣ → A 𝔪 → RayClassGroup 𝔪 → ClassGroup (𝓞 K) → 1
```

and this file reads off the ray class number formula

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
class group.  The ray class number therefore equals the order of the product of the three exactly
when every integer unit is congruent to one modulo `𝔪`, and otherwise `RayClassGroup 𝔪` is not
isomorphic to that product.  Since `-1` is a unit, the decomposition fails whenever `𝔪` selects a
real place or `2` does not lie in its finite part.

At the narrow modulus the residue factor is trivial and the formula becomes
`#(RayClassGroup (narrowModulus K)) * [(𝓞 K)ˣ : (𝓞 K)ˣ⁺] = #(ClassGroup (𝓞 K)) * 2 ^ r₁`, with
`(𝓞 K)ˣ⁺` the totally positive units and `r₁` the number of real places.

## Main results

* `TauCeti.GlobalNumberFields.card_ker_rayClassToClassGroup_mul_index`: the order of the kernel of
  `RayClassGroup 𝔪 → ClassGroup (𝓞 K)`.
* `TauCeti.GlobalNumberFields.card_rayClassGroup_mul_index` and
  `TauCeti.GlobalNumberFields.card_rayClassGroup`: the ray class number formula.
* `TauCeti.GlobalNumberFields.card_rayClassGroup_narrowModulus_mul_index`: its narrow case.
* `TauCeti.GlobalNumberFields.card_rayClassGroup_eq_iff` and
  `TauCeti.GlobalNumberFields.nonempty_rayClassGroup_equiv_prod_iff`: the ray class number is the
  order of the product of residue units, signs and the class group exactly when every integer unit
  is congruent to one.
* `TauCeti.GlobalNumberFields.isEmpty_rayClassGroup_mulEquiv_prod`: otherwise the ray class group
  is not the direct product of the three.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, (1.10) and (1.11).
* S. Lang, *Algebraic Number Theory*, Chapter VI, §1, Theorem 1.
-/

public section

open IsDedekindDomain NumberField
open scoped nonZeroDivisors NumberField

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

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
    Nat.card (RayClassGroup (narrowModulus K)) *
        (totallyPositiveIntegerUnits (K := K)).index =
      Nat.card (ClassGroup (𝓞 K)) * 2 ^ InfinitePlace.nrRealPlaces K := by
  rw [← unitsCongruenceSubgroup_narrowModulus (K := K)]
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

/-! ### The ray class group is not the product of its pieces -/

/-- **The ray class number equals the product of the class number, the number of residue units and
the number of sign patterns exactly when every integer unit is congruent to one modulo `𝔪`.**
Otherwise it is smaller by a factor of the index of the units congruent to one. -/
theorem card_rayClassGroup_eq_iff (𝔪 : Modulus K) :
    Nat.card (RayClassGroup 𝔪) =
        Nat.card (ClassGroup (𝓞 K)) *
          (Nat.card (𝓞 K ⧸ 𝔪.finitePart)ˣ * 2 ^ 𝔪.infinitePart.card) ↔
      unitsCongruenceSubgroup 𝔪 = ⊤ := by
  rw [← Subgroup.index_eq_one, ← card_rayClassGroup_mul_index, eq_comm,
    Nat.mul_eq_left Finite.card_pos.ne']

/-- **The ray class group is in bijection with the product of the residue units, the sign patterns
and the class group exactly when every integer unit is congruent to one modulo `𝔪`.**  This is a
statement about cardinalities only; it does not assert that the group extension of the class group
by the residue units and signs splits. -/
theorem nonempty_rayClassGroup_equiv_prod_iff (𝔪 : Modulus K) :
    Nonempty (RayClassGroup 𝔪 ≃
        ((𝓞 K ⧸ 𝔪.finitePart)ˣ × (𝔪.infinitePart → ℤˣ)) × ClassGroup (𝓞 K)) ↔
      unitsCongruenceSubgroup 𝔪 = ⊤ := by
  have : Finite (𝓞 K ⧸ 𝔪.finitePart) := Ring.HasFiniteQuotients.finiteQuotient 𝔪.finitePart_ne_bot
  rw [← Finite.card_eq, ← card_rayClassGroup_eq_iff]
  simp [Nat.card_fun, mul_comm]

/-- **The ray class group is not the direct product of the residue units, the sign patterns and the
class group** as soon as some integer unit is not congruent to one modulo `𝔪`, for instance when `𝔪`
selects a real place (`unitsCongruenceSubgroup_ne_top`).  The residues and signs of the integer
units glue the three factors together. -/
theorem isEmpty_rayClassGroup_mulEquiv_prod {𝔪 : Modulus K} (h𝔪 : unitsCongruenceSubgroup 𝔪 ≠ ⊤) :
    IsEmpty (RayClassGroup 𝔪 ≃*
      ((𝓞 K ⧸ 𝔪.finitePart)ˣ × (𝔪.infinitePart → ℤˣ)) × ClassGroup (𝓞 K)) :=
  ⟨fun e ↦ h𝔪 ((nonempty_rayClassGroup_equiv_prod_iff 𝔪).mp ⟨e.toEquiv⟩)⟩

end TauCeti.GlobalNumberFields
