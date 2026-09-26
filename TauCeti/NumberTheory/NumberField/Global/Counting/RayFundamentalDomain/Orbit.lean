/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Counting.RayFundamentalDomain.IntegerSet

/-!
# Orbits of the congruence roots of unity on the ray integer set

Two points of `rayIntegerSet 𝔪` lie in the same orbit of the congruence roots of unity exactly
when some unit congruent to one modulo `𝔪` carries one to the other.  So orbits of the *small*
group `unitsCongruenceTorsion 𝔪` on the domain are the traces of the *large* group
`unitsCongruenceSubgroup 𝔪` acting on the whole space: the large group identifies no two points
of the domain that the small group does not already identify.  Together with
`exists_unitsCongruenceSubgroup_smul_mem_rayFundamentalDomain`, which moves each point of
nonzero norm in `posRegion 𝔪` into the domain, that is the sense in which the domain is
fundamental for the large group modulo the small one.

For the trivial modulus the large group is all of `(𝓞 K)ˣ`, translation by it is associatedness
in `(𝓞 K)⁰`, and the statement is Mathlib's `integerSetToAssociates_eq_iff`, whose left-hand side
reads the orbit off in `Associates (𝓞 K)⁰`.  Mathlib has no such quotient type for a proper
subgroup of the units, so this file states the orbit relation directly.

## Main results

* `TauCeti.GlobalNumberFields.exists_mem_unitsCongruenceTorsion_smul_iff`: the orbit relation for
  any two points of the domain;
* `TauCeti.GlobalNumberFields.exists_unitsCongruenceTorsion_smul_iff`: the same on
  `rayIntegerSet 𝔪`, which is the form the count consumes.
-/

public section

open NumberField NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone

open scoped nonZeroDivisors

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-- **The orbit relation, for any two points of the domain.**  A congruence unit carrying one
point of `rayFundamentalDomain 𝔪` to another is automatically a root of unity, so the two
subgroups have the same orbits on the domain.  Only membership of the domain is needed; the
points need not be images of algebraic integers. -/
theorem exists_mem_unitsCongruenceTorsion_smul_iff {𝔪 : Modulus K} {a b : mixedSpace K}
    (ha : a ∈ rayFundamentalDomain 𝔪) (hb : b ∈ rayFundamentalDomain 𝔪) :
    (∃ ζ ∈ unitsCongruenceTorsion 𝔪, ζ • a = b) ↔
      ∃ u ∈ unitsCongruenceSubgroup 𝔪, u • a = b := by
  refine ⟨fun ⟨ζ, hζ, h⟩ ↦ ⟨ζ, (mem_unitsCongruenceTorsion.mp hζ).1, h⟩, fun ⟨u, hu, hsmul⟩ ↦ ?_⟩
  -- the unit is constrained only by a congruence; membership of both points in the domain is
  -- what upgrades it to a root of unity
  exact ⟨u, mem_unitsCongruenceTorsion.mpr ⟨hu,
    (unitsCongruenceSubgroup_smul_mem_rayFundamentalDomain_iff_mem_torsion ha hu).mp
      (hsmul ▸ hb)⟩, hsmul⟩

/-- **The orbit relation on the ray integer set.**  Two points of `rayIntegerSet 𝔪` lie in one
orbit of the congruence roots of unity exactly when some unit congruent to one modulo `𝔪` carries
one to the other in the mixed space.  Since `mixedEmbedding` is injective and multiplicative, that
is the same as their algebraic integers differing by such a unit, which is the form the ray class
count consumes. -/
theorem exists_unitsCongruenceTorsion_smul_iff {𝔪 : Modulus K} (a b : rayIntegerSet 𝔪) :
    (∃ ζ : unitsCongruenceTorsion 𝔪, ζ • a = b) ↔
      ∃ u ∈ unitsCongruenceSubgroup 𝔪, u • (a : mixedSpace K) = (b : mixedSpace K) := by
  rw [← exists_mem_unitsCongruenceTorsion_smul_iff (mem_rayIntegerSet.mp a.prop).1
    (mem_rayIntegerSet.mp b.prop).1]
  exact ⟨fun ⟨⟨ζ, hζ⟩, h⟩ ↦ ⟨ζ, hζ, by simpa using congrArg Subtype.val h⟩,
    fun ⟨ζ, hζ, h⟩ ↦ ⟨⟨ζ, hζ⟩, Subtype.ext (by simpa using h)⟩⟩

end TauCeti.GlobalNumberFields
