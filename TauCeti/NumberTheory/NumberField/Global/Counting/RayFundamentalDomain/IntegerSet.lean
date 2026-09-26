/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Counting.RayFundamentalDomain.Basic

/-!
# Algebraic integers in the ray fundamental domain

Counting the integral ideals of a ray class goes through the points of the ray fundamental domain
that are images of algebraic integers.  This file introduces that carrier, `rayIntegerSet 𝔪`, and
the map recovering the integer a point comes from.

An element of `rayIntegerSet 𝔪` has a *unique* preimage in `𝓞 K`, because `mixedEmbedding` is
injective, and that preimage is nonzero, since the ray fundamental domain has no point of
vanishing norm (`norm_pos_of_mem_rayFundamentalDomain`).  The preimage is therefore recorded in
`(𝓞 K)⁰`, so that its nonzero-ness travels with the value.

For the trivial modulus this is Mathlib's `NumberField.mixedEmbedding.fundamentalCone.integerSet`.

The carrier also carries an action: a congruence unit sends a point of the domain back into the
domain exactly when it is a root of unity, so the roots of unity congruent to one modulo `𝔪` act
on `rayIntegerSet 𝔪`, and that action is free.  Counting a ray class will divide by the size of
its orbits, which is what makes freeness the fact worth isolating here.

## Main definitions

* `TauCeti.GlobalNumberFields.rayIntegerSet`: the points of the ray fundamental domain that are
  images of algebraic integers;
* `TauCeti.GlobalNumberFields.preimageOfMemRayIntegerSet`: the nonzero algebraic integer a point
  of `rayIntegerSet` is the image of;
* `TauCeti.GlobalNumberFields.unitsCongruenceTorsion`: the roots of unity congruent to one
  modulo `𝔪`, which act on `rayIntegerSet 𝔪`.

## Main results

* `TauCeti.GlobalNumberFields.mem_rayIntegerSet`: the defining membership condition;
* `TauCeti.GlobalNumberFields.mixedEmbedding_preimageOfMemRayIntegerSet`: the preimage map is a
  section of `mixedEmbedding`;
* `TauCeti.GlobalNumberFields.rayIntegerSet_one`: the trivial modulus recovers Mathlib's
  `integerSet`;
* `TauCeti.GlobalNumberFields.preimageOfMemRayIntegerSet_smul`: a congruence root of unity acts
  by multiplying the underlying algebraic integer;
* `TauCeti.GlobalNumberFields.stabilizer_rayIntegerSet_eq_bot`: the action is free, also
  available as an `IsCancelSMul` instance.

## References

* S. Lang, *Algebraic Number Theory*, Chapter VI, §2.
* `Mathlib/NumberTheory/NumberField/CanonicalEmbedding/FundamentalCone.lean`: the `integerSet`
  layer there — that set, its preimage API and its torsion action — is the model for
  `rayIntegerSet`, with the fundamental cone replaced by the ray fundamental domain and the full
  torsion group by the congruence torsion.
-/

public section

open NumberField NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
open TauCeti.NumberField.Units

open scoped nonZeroDivisors

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-- The points of the ray fundamental domain of `𝔪` that are images of algebraic integers. -/
def rayIntegerSet (𝔪 : Modulus K) : Set (mixedSpace K) :=
  rayFundamentalDomain 𝔪 ∩ mixedEmbedding.integerLattice K

/-- Membership in `rayIntegerSet`: a point of the ray fundamental domain that is the image of an
algebraic integer. -/
theorem mem_rayIntegerSet {𝔪 : Modulus K} {a : mixedSpace K} :
    a ∈ rayIntegerSet 𝔪 ↔
      a ∈ rayFundamentalDomain 𝔪 ∧ ∃ x : 𝓞 K, mixedEmbedding K x = a := by
  simp only [rayIntegerSet, Set.mem_inter_iff, SetLike.mem_coe, LinearMap.mem_range,
    AlgHom.toLinearMap_apply, RingHom.toIntAlgHom_coe, RingHom.coe_comp, Function.comp_apply]

/-- A point of the ray fundamental domain that is the image of an algebraic integer is the image
of exactly one, since `mixedEmbedding` is injective. -/
theorem existsUnique_preimage_of_mem_rayIntegerSet {𝔪 : Modulus K} {a : mixedSpace K}
    (ha : a ∈ rayIntegerSet 𝔪) : ∃! x : 𝓞 K, mixedEmbedding K x = a := by
  obtain ⟨_, ⟨x, rfl⟩⟩ := mem_rayIntegerSet.mp ha
  refine Function.Injective.existsUnique_of_mem_range ?_ (Set.mem_range_self x)
  exact (mixedEmbedding_injective K).comp RingOfIntegers.coe_injective

/-- A point of `rayIntegerSet` is nonzero, since the ray fundamental domain has no point of
vanishing norm. -/
theorem ne_zero_of_mem_rayIntegerSet {𝔪 : Modulus K} (a : rayIntegerSet 𝔪) :
    (a : mixedSpace K) ≠ 0 := by
  intro h
  have hpos := norm_pos_of_mem_rayFundamentalDomain (mem_rayIntegerSet.mp a.prop).1
  rw [h] at hpos
  simp at hpos

/-- The unique algebraic integer a point of `rayIntegerSet 𝔪` is the image of, recorded as an
element of the nonzero divisors `(𝓞 K)⁰`. -/
noncomputable def preimageOfMemRayIntegerSet {𝔪 : Modulus K} (a : rayIntegerSet 𝔪) : (𝓞 K)⁰ :=
  ⟨(mem_rayIntegerSet.mp a.prop).2.choose, mem_nonZeroDivisors_of_ne_zero fun h ↦
    ne_zero_of_mem_rayIntegerSet a <| by
      simpa [h] using (mem_rayIntegerSet.mp a.prop).2.choose_spec.symm⟩

/-- The preimage map is a section of `mixedEmbedding`: embedding the integer it returns recovers
the point. -/
@[simp]
theorem mixedEmbedding_preimageOfMemRayIntegerSet {𝔪 : Modulus K} (a : rayIntegerSet 𝔪) :
    mixedEmbedding K (preimageOfMemRayIntegerSet a : 𝓞 K) = (a : mixedSpace K) := by
  rw [preimageOfMemRayIntegerSet, (mem_rayIntegerSet.mp a.prop).2.choose_spec]

/-- The preimage map is a retraction of `mixedEmbedding`: an integer whose image lies in the
carrier is returned unchanged. -/
theorem preimageOfMemRayIntegerSet_mixedEmbedding {𝔪 : Modulus K} {x : 𝓞 K}
    (hx : mixedEmbedding K (x : 𝓞 K) ∈ rayIntegerSet 𝔪) :
    preimageOfMemRayIntegerSet ⟨mixedEmbedding K (x : 𝓞 K), hx⟩ = x := by
  simp_rw [RingOfIntegers.ext_iff, ← (mixedEmbedding_injective K).eq_iff,
    mixedEmbedding_preimageOfMemRayIntegerSet]

/-- **Agreement with Mathlib at the trivial modulus.**  The trivial modulus recovers
`NumberField.mixedEmbedding.fundamentalCone.integerSet`, since its ray fundamental domain is the
fundamental cone. -/
@[simp]
theorem rayIntegerSet_one : rayIntegerSet (Modulus.one K) = integerSet K := by
  rw [rayIntegerSet, rayFundamentalDomain_one, integerSet]

/-! ### The free action of the congruence roots of unity -/

/-- `rayIntegerSet 𝔪` is stable under the congruence roots of unity. -/
theorem unitsCongruenceTorsion_smul_mem_rayIntegerSet {𝔪 : Modulus K} {ζ : (𝓞 K)ˣ}
    (hζ : ζ ∈ unitsCongruenceTorsion 𝔪) {a : mixedSpace K} (ha : a ∈ rayIntegerSet 𝔪) :
    ζ • a ∈ rayIntegerSet 𝔪 := by
  obtain ⟨hdom, x, rfl⟩ := mem_rayIntegerSet.mp ha
  exact mem_rayIntegerSet.mpr
    ⟨(torsion_smul_mem_rayFundamentalDomain_iff (mem_unitsCongruenceTorsion.mp hζ).2
      (mem_unitsCongruenceTorsion.mp hζ).1).mpr hdom, ζ * x, by simp⟩

/-- The action of the congruence roots of unity on `rayIntegerSet 𝔪`. -/
@[simps]
noncomputable instance rayIntegerSetUnitsCongruenceTorsionSMul (𝔪 : Modulus K) :
    SMul (unitsCongruenceTorsion 𝔪) (rayIntegerSet 𝔪) where
  smul := fun ⟨ζ, hζ⟩ ⟨a, ha⟩ ↦ ⟨ζ • a, unitsCongruenceTorsion_smul_mem_rayIntegerSet hζ ha⟩

/-- The scalar action of the congruence roots of unity is a group action, which is what
`stabilizer_rayIntegerSet_eq_bot` below speaks about.  It is transported along the injection
into the mixed space, where the action laws are Mathlib's. -/
noncomputable instance (𝔪 : Modulus K) :
    MulAction (unitsCongruenceTorsion 𝔪) (rayIntegerSet 𝔪) :=
  Subtype.val_injective.mulAction Subtype.val fun ζ ↦
    rayIntegerSetUnitsCongruenceTorsionSMul_smul_coe 𝔪 ζ

/-- A congruence root of unity acts on `rayIntegerSet 𝔪` by multiplying the underlying algebraic
integer. -/
@[simp]
theorem preimageOfMemRayIntegerSet_smul {𝔪 : Modulus K} (ζ : unitsCongruenceTorsion 𝔪)
    (a : rayIntegerSet 𝔪) :
    (preimageOfMemRayIntegerSet (ζ • a) : 𝓞 K) =
      ((ζ : (𝓞 K)ˣ) : 𝓞 K) * preimageOfMemRayIntegerSet a := by
  refine RingOfIntegers.ext <| mixedEmbedding_injective K ?_
  simp [mixedEmbedding_preimageOfMemRayIntegerSet,
    rayIntegerSetUnitsCongruenceTorsionSMul_smul_coe, unitSMul_smul]

/-- **The action is free.**  A congruence root of unity fixing a point of `rayIntegerSet 𝔪` is
the identity, because the point is the image of a nonzero algebraic integer. -/
theorem stabilizer_rayIntegerSet_eq_bot {𝔪 : Modulus K} (a : rayIntegerSet 𝔪) :
    MulAction.stabilizer (unitsCongruenceTorsion 𝔪) a = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).mpr fun ζ hζ ↦ ?_
  rw [MulAction.mem_stabilizer_iff, Subtype.ext_iff,
    rayIntegerSetUnitsCongruenceTorsionSMul_smul_coe] at hζ
  rw [← mixedEmbedding_preimageOfMemRayIntegerSet a] at hζ
  exact OneMemClass.coe_eq_one.mp
    (eq_one_of_unitSMul_mixedEmbedding_eq
      (RingOfIntegers.coe_ne_zero_iff.mpr (nonZeroDivisors.coe_ne_zero _)) hζ)

/-- **Freeness as a typeclass.**  Exposing `stabilizer_rayIntegerSet_eq_bot` as `IsCancelSMul`
lets the generic free-action and orbit-cardinality results apply to this action by instance
resolution, which is how the ray class count consumes it. -/
instance (𝔪 : Modulus K) : IsCancelSMul (unitsCongruenceTorsion 𝔪) (rayIntegerSet 𝔪) :=
  isCancelSMul_iff_stabilizer_eq_bot.mpr stabilizer_rayIntegerSet_eq_bot

end TauCeti.GlobalNumberFields
