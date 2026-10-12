/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Counting.RayFundamentalDomain.Lipschitz
public import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.MulVolume
public import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.NormLeOne

/-!
# The volume of the norm-one section of the ray fundamental domain

On the section of norm at most one, the ray fundamental domain of a modulus `𝔪` is the part of
the union of the unit translates of Mathlib's `fundamentalCone.normLeOne K` that carries the
signs prescribed by the infinite part of `𝔪`. The translates are indexed by the cosets of
`unitsCongruenceSubgroupSupTorsion 𝔪`; they are pairwise disjoint and each has the volume of
`normLeOne K`, and their union is stable under reflection at every real place. Prescribing the
sign at the `s` real places of the infinite part therefore divides the volume of the union by
`2 ^ s`.

## Main results

* `TauCeti.GlobalNumberFields.two_pow_mul_volume_rayFundamentalDomain_inter_normLeOne`:
  `2 ^ s` times the volume of the norm-one section of `rayFundamentalDomain 𝔪` is the index of
  `unitsCongruenceSubgroupSupTorsion 𝔪` times the volume of `normLeOne K`.
* `TauCeti.GlobalNumberFields.measureReal_rayFundamentalDomain_inter_normLeOne`: the same
  volume as an explicit real number, the index times `2 ^ r₁ · π ^ r₂ · Reg_K / 2 ^ s`.

## References

* S. Lang, *Algebraic Number Theory*, Chapter VI, §2.
-/

public section

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open NumberField.mixedEmbedding.fundamentalCone TauCeti.NumberField.mixedEmbedding
open NumberField.Units
open scoped Pointwise Real

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

private theorem pairwise_disjoint_rayUnitRepresentative_smul_normLeOne (𝔪 : Modulus K) :
    Pairwise (Function.onFun Disjoint fun q ↦ rayUnitRepresentative 𝔪 q • normLeOne K) := by
  refine fun q q' hqq' ↦ Set.disjoint_left.mpr fun x hx hx' ↦ hqq' ?_
  rw [Set.mem_smul_set_iff_inv_smul_mem] at hx hx'
  -- two representatives carrying the same point into the cone differ by a root of unity
  rw [← rayUnitRepresentative_mk 𝔪 q, ← rayUnitRepresentative_mk 𝔪 q', QuotientGroup.eq]
  refine torsion_le_unitsCongruenceSubgroupSupTorsion 𝔪 <|
    (fundamentalCone.unit_smul_mem_iff_mem_torsion hx'.1 _).mp ?_
  rw [mul_smul, smul_inv_smul]
  exact hx.1

open scoped Classical in
/-- **The volume of the norm-≤-one section of the ray fundamental domain.**  With `s` real places
in the infinite part of `𝔪`, the section of `rayFundamentalDomain 𝔪` of norm at most one has
`1 / 2 ^ s` of the volume of Mathlib's `normLeOne K` for each coset of
`unitsCongruenceSubgroupSupTorsion 𝔪`; the statement clears the denominator `2 ^ s`. For the
trivial modulus both factors are one, and the section has the volume of `normLeOne K`. -/
theorem two_pow_mul_volume_rayFundamentalDomain_inter_normLeOne (𝔪 : Modulus K) :
    2 ^ 𝔪.infinitePart.card * volume (rayFundamentalDomain 𝔪 ∩ {x | mixedEmbedding.norm x ≤ 1}) =
      (unitsCongruenceSubgroupSupTorsion 𝔪).index * volume (normLeOne K) := by
  have hm (q) : MeasurableSet (rayUnitRepresentative 𝔪 q • normLeOne K) :=
    (measurableSet_normLeOne K).const_smul _
  -- the union of the translates is stable under reflection at each real place, so the sign cut
  -- divides its volume by `2 ^ s`; the translates are disjoint, each with the volume of
  -- `normLeOne K`
  rw [rayFundamentalDomain_inter_normLeOne_eq, Set.inter_comm, posRegion_def,
    ← volume_eq_two_pow_mul_volume_inter_pos _ (by simp) (.iUnion hm),
    measure_iUnion (pairwise_disjoint_rayUnitRepresentative_smul_normLeOne 𝔪) hm]
  simp [ENat.card_eq_coe_natCard, Subgroup.index]

open scoped Classical in
/-- **The real volume of the norm-≤-one section of the ray fundamental domain.**  With `s` real
places in the infinite part of `𝔪`, the section of `rayFundamentalDomain 𝔪` of norm at most one
has real volume `i · 2 ^ r₁ · π ^ r₂ · Reg_K / 2 ^ s`, where `i` is the index of
`unitsCongruenceSubgroupSupTorsion 𝔪`, `r₁` and `r₂` are the numbers of real and complex places
of `K`, and `Reg_K` is its regulator. -/
theorem measureReal_rayFundamentalDomain_inter_normLeOne (𝔪 : Modulus K) :
    volume.real (rayFundamentalDomain 𝔪 ∩ {x | mixedEmbedding.norm x ≤ 1}) =
      (unitsCongruenceSubgroupSupTorsion 𝔪).index *
        (2 ^ nrRealPlaces K * π ^ nrComplexPlaces K * regulator K) / 2 ^ 𝔪.infinitePart.card := by
  rw [eq_div_iff (by positivity), mul_comm, measureReal_def]
  simpa [volume_normLeOne, (regulator_pos K).le] using
    congrArg ENNReal.toReal (two_pow_mul_volume_rayFundamentalDomain_inter_normLeOne 𝔪)

end TauCeti.GlobalNumberFields
