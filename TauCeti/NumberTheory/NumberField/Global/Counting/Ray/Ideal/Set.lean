/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Counting.Ray.Coset
public import TauCeti.NumberTheory.NumberField.Global.Counting.RayFundamentalDomain.IntegerSet

/-!
# Elements of an ideal congruent to one, in the ray fundamental domain

For a modulus `𝔪` with finite part `𝔪₀` and a nonzero integral ideal `𝔞`, this file names the set
of points of the ray fundamental domain of `𝔪` that are images of elements of `𝔞` congruent to
one modulo `𝔪₀`, and records two descriptions of it.

Only the finite part appears in the set-builder: the conditions the infinite part imposes are
already carried by the ray fundamental domain, which lies in `posRegion 𝔪`
(`mem_posRegion_of_mem_rayFundamentalDomain`).

Nothing here asks that `𝔞` represent a given ray class, nor divides out the congruence roots of
unity acting on the domain; a ray-class ideal count imposes both itself.

## Main definitions

* `TauCeti.GlobalNumberFields.rayIdealSet`: the set described above;
* `TauCeti.GlobalNumberFields.rayIdealSetEquiv`: a bijection from it onto the points of
  `rayIntegerSet 𝔪` whose underlying algebraic integer lies in `𝔞` and is congruent to one
  modulo `𝔪₀`, with `rayIdealSetEquiv_apply` and `rayIdealSetEquiv_symm_apply` for the two
  directions.

## Main results

* `TauCeti.GlobalNumberFields.mem_rayIdealSet`: its points, unfolded;
* `TauCeti.GlobalNumberFields.rayIdealSet_one`: the trivial modulus recovers Mathlib's
  `NumberField.mixedEmbedding.fundamentalCone.idealSet`;
* `TauCeti.GlobalNumberFields.rayIdealSet_eq_inter_vadd`: the same set as a translate of the
  congruence lattice, intersected with the domain;
* `TauCeti.GlobalNumberFields.rayIdealSet_subset_rayIntegerSet` and
  `TauCeti.GlobalNumberFields.preimageOfMemRayIntegerSet_mem_and_sub_one_mem_of_mem_rayIdealSet`:
  its points lie in `rayIntegerSet 𝔪`, and the algebraic integer each of them is the image of
  lies in `𝔞` and is congruent to one modulo `𝔪₀`.

## Implementation notes

The set takes no base point, while its description as a translate does, which is why
`rayIdealSet_eq_inter_vadd` takes a witness `ξ`.  Taking `ξ = 0` would describe a different set
instead of dispensing with the witness: `coe_congruenceLattice_mk0_eq_image`
identifies `congruenceLattice 𝔪 (FractionalIdeal.mk0 K 𝔞)` with the image of `𝔞 * 𝔪₀`, and an
element of `𝔞 * 𝔪₀` congruent to one modulo `𝔪₀` forces `1 ∈ 𝔪₀`, so the two agree only for a
trivial finite part.

## References

* `Mathlib/NumberTheory/NumberField/CanonicalEmbedding/FundamentalCone.lean`: the `idealSet` and
  `idealSetEquiv` layer there is the model for this file, with the fundamental cone replaced by
  the ray fundamental domain and the congruence condition added.
-/

public section

open NumberField NumberField.mixedEmbedding

open scoped Pointwise nonZeroDivisors

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-- The images, inside the ray fundamental domain of `𝔪`, of the elements of `𝔞` that are
congruent to one modulo the finite part of `𝔪`.  This is the ray analogue of
`NumberField.mixedEmbedding.fundamentalCone.idealSet`. -/
def rayIdealSet (𝔪 : Modulus K) (𝔞 : (Ideal (𝓞 K))⁰) : Set (mixedSpace K) :=
  rayFundamentalDomain 𝔪 ∩ (fun y : 𝓞 K ↦ mixedEmbedding K (y : K)) ''
      {α : 𝓞 K | α ∈ (𝔞 : Ideal (𝓞 K)) ∧ α - 1 ∈ 𝔪.finitePart}

/-- **The points of `rayIdealSet`.**  A point lies in it exactly when it lies in the ray
fundamental domain and is the image of an element of `𝔞` congruent to one modulo `𝔪₀`. -/
theorem mem_rayIdealSet {𝔪 : Modulus K} {𝔞 : (Ideal (𝓞 K))⁰} {x : mixedSpace K} :
    x ∈ rayIdealSet 𝔪 𝔞 ↔ x ∈ rayFundamentalDomain 𝔪 ∧
      ∃ α : 𝓞 K, (α ∈ (𝔞 : Ideal (𝓞 K)) ∧ α - 1 ∈ 𝔪.finitePart) ∧ mixedEmbedding K (α : K) = x :=
  Iff.rfl

/-- **The trivial modulus recovers Mathlib's ideal set.**  Its finite part is the whole ring, so
the congruence condition holds vacuously, and its ray fundamental domain is the fundamental cone
(`rayFundamentalDomain_one`); what is left is
`NumberField.mixedEmbedding.fundamentalCone.idealSet`. -/
@[simp]
theorem rayIdealSet_one (𝔞 : (Ideal (𝓞 K))⁰) :
    rayIdealSet (Modulus.one K) 𝔞 = fundamentalCone.idealSet K 𝔞 := by
  ext x
  simp [mem_rayIdealSet, fundamentalCone.mem_idealSet, rayFundamentalDomain_one]

/-- **`rayIdealSet` as the domain met with a translate of the congruence lattice.**  For any
element `ξ` of `𝔞` congruent to one modulo `𝔪₀`, the set is the ray fundamental domain
intersected with the translate of `congruenceLattice 𝔪 (FractionalIdeal.mk0 K 𝔞)` by the image
of `ξ`.

The lattice on the right does not involve `ξ`, so a different witness only renames the translate;
and such a `ξ` exists exactly when `𝔞` and `𝔪₀` are coprime
(`Ideal.isCoprime_iff_exists_mem_and_sub_one_mem`).  Without one, `rayIdealSet 𝔪 𝔞` is empty. -/
theorem rayIdealSet_eq_inter_vadd (𝔪 : Modulus K) (𝔞 : (Ideal (𝓞 K))⁰) {ξ : 𝓞 K}
    (hξ𝔞 : ξ ∈ (𝔞 : Ideal (𝓞 K))) (hξ𝔪 : ξ - 1 ∈ 𝔪.finitePart) : rayIdealSet 𝔪 𝔞 =
      rayFundamentalDomain 𝔪 ∩ (mixedEmbedding K (ξ : K) +ᵥ
        (congruenceLattice 𝔪 (FractionalIdeal.mk0 K 𝔞) : Set (mixedSpace K))) := by
  rw [rayIdealSet, image_setOf_mem_and_sub_one_mem_eq_vadd_congruenceLattice 𝔪 𝔞 hξ𝔞 hξ𝔪]

/-- Every point of `rayIdealSet 𝔪 𝔞` lies in `rayIntegerSet 𝔪`: it lies in the ray fundamental
domain and is the image of an algebraic integer.  Both the membership in `𝔞` and the congruence
condition are forgotten.

This inclusion is what lets `rayIdealSetEquiv` land in a subtype of `rayIntegerSet 𝔪`; Mathlib
packages the corresponding map as a definition,
`NumberField.mixedEmbedding.fundamentalCone.idealSetMap`. -/
theorem rayIdealSet_subset_rayIntegerSet (𝔪 : Modulus K) (𝔞 : (Ideal (𝓞 K))⁰) :
    rayIdealSet 𝔪 𝔞 ⊆ rayIntegerSet 𝔪 := by
  rintro x ⟨hdom, α, -, rfl⟩
  exact mem_rayIntegerSet.mpr ⟨hdom, α, rfl⟩

/-- The algebraic integer underlying a point of `rayIdealSet 𝔪 𝔞` lies in `𝔞` and is congruent to
one modulo `𝔪₀`.

With `rayIdealSet_subset_rayIntegerSet`, this is what makes `rayIdealSetEquiv` well defined.  The
conjunction is stated bundled because it is the predicate defining the set `rayIdealSet` is built
from, and is verbatim the subtype predicate of that equivalence's codomain. -/
theorem preimageOfMemRayIntegerSet_mem_and_sub_one_mem_of_mem_rayIdealSet {𝔪 : Modulus K}
    {𝔞 : (Ideal (𝓞 K))⁰} {a : rayIntegerSet 𝔪} (ha : (a : mixedSpace K) ∈ rayIdealSet 𝔪 𝔞) :
    (preimageOfMemRayIntegerSet a : 𝓞 K) ∈ (𝔞 : Ideal (𝓞 K)) ∧
      (preimageOfMemRayIntegerSet a : 𝓞 K) - 1 ∈ 𝔪.finitePart := by
  obtain ⟨b, hb⟩ := a
  obtain ⟨-, α, hα, rfl⟩ := ha
  rw [preimageOfMemRayIntegerSet_mixedEmbedding]
  exact hα

/-- **`rayIdealSet` as a subtype of the ray integer set.**  A point of `rayIntegerSet 𝔪` comes
from a point of `rayIdealSet 𝔪 𝔞` exactly when the algebraic integer it is the image of lies in
`𝔞` and is congruent to one modulo `𝔪₀`, so the two carriers are in bijection.

This is the ray analogue of `NumberField.mixedEmbedding.fundamentalCone.idealSetEquiv`, with the
forward map applied inline rather than named separately. -/
noncomputable def rayIdealSetEquiv (𝔪 : Modulus K) (𝔞 : (Ideal (𝓞 K))⁰) : rayIdealSet 𝔪 𝔞 ≃
    {a : rayIntegerSet 𝔪 // (preimageOfMemRayIntegerSet a : 𝓞 K) ∈ (𝔞 : Ideal (𝓞 K)) ∧
      (preimageOfMemRayIntegerSet a : 𝓞 K) - 1 ∈ 𝔪.finitePart} :=
  Equiv.ofBijective
    (fun x ↦ ⟨⟨(x : mixedSpace K), rayIdealSet_subset_rayIntegerSet 𝔪 𝔞 x.prop⟩,
      preimageOfMemRayIntegerSet_mem_and_sub_one_mem_of_mem_rayIdealSet x.prop⟩)
    ⟨fun _ _ h ↦ Subtype.ext (congrArg (fun y ↦ ((y.1 : rayIntegerSet 𝔪) : mixedSpace K)) h),
      fun a ↦ ⟨⟨(a : mixedSpace K), mem_rayIdealSet.mpr
        ⟨(mem_rayIntegerSet.mp (a : rayIntegerSet 𝔪).prop).1,
          preimageOfMemRayIntegerSet (a : rayIntegerSet 𝔪), a.prop,
            mixedEmbedding_preimageOfMemRayIntegerSet _⟩⟩,
        Subtype.ext (Subtype.ext rfl)⟩⟩

/-- `rayIdealSetEquiv` leaves the underlying point of the mixed space unchanged; this is the ray
analogue of `NumberField.mixedEmbedding.fundamentalCone.idealSetEquiv_apply`. -/
@[simp]
theorem rayIdealSetEquiv_apply {𝔪 : Modulus K} {𝔞 : (Ideal (𝓞 K))⁰} (x : rayIdealSet 𝔪 𝔞) :
    ((rayIdealSetEquiv 𝔪 𝔞 x : rayIntegerSet 𝔪) : mixedSpace K) = (x : mixedSpace K) :=
  -- `(rfl)`, not `rfl`: this theorem is exported while `rayIdealSetEquiv` is not `@[expose]`,
  -- so a bare `rfl` is rejected as "not a definitional equality".
  (rfl)

/-- The inverse of `rayIdealSetEquiv` also leaves the underlying point of the mixed space
unchanged; this is the ray analogue of
`NumberField.mixedEmbedding.fundamentalCone.idealSetEquiv_symm_apply`. -/
@[simp]
theorem rayIdealSetEquiv_symm_apply {𝔪 : Modulus K} {𝔞 : (Ideal (𝓞 K))⁰}
    (a : {a : rayIntegerSet 𝔪 // (preimageOfMemRayIntegerSet a : 𝓞 K) ∈ (𝔞 : Ideal (𝓞 K)) ∧
      (preimageOfMemRayIntegerSet a : 𝓞 K) - 1 ∈ 𝔪.finitePart}) :
    (((rayIdealSetEquiv 𝔪 𝔞).symm a : rayIdealSet 𝔪 𝔞) : mixedSpace K) =
      ((a : rayIntegerSet 𝔪) : mixedSpace K) := by
  rw [← rayIdealSetEquiv_apply ((rayIdealSetEquiv 𝔪 𝔞).symm a), Equiv.apply_symm_apply]

end TauCeti.GlobalNumberFields
