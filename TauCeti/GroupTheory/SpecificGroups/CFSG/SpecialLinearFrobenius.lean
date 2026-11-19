/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Frobenius
public import TauCeti.GroupTheory.FixedSubgroup
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic

/-!
# The finite-field descent of the special linear group

Let `d` be a valid Lie-type index, so that `d.Closure` is the algebraic closure of the prime field
of characteristic `d.characteristic` and `d.fieldOrder = d.characteristic ^ d.fieldExponent` is the
order of the field of definition attached to the index. This file identifies the points of the
special linear group over the closure that are fixed by the entrywise `d.fieldOrder`-power
Frobenius with Mathlib's finite matrix group over `GaloisField d.characteristic d.fieldExponent`.

The characterization is entrywise: a special linear matrix over the closure is fixed by the
entrywise Frobenius exactly when each of its entries satisfies `x ^ d.fieldOrder = x`. An element of
the closure satisfies that equation exactly when it lies in the image of the coefficient embedding
`TauCeti.ValidLieTypeIndex.galoisFieldEmbedding`, so the fixed subgroup of the entrywise Frobenius
is the range of the induced map on the special linear group. That map is injective, which makes it
a `MulEquiv` from the finite matrix group onto the fixed subgroup, and the fixed subgroup is finite
because the finite matrix group is.

The results are stated for an arbitrary coordinate type `ι`, so they apply to the type-`A` carrier
at `ι = Fin (rank + 1)` and to any other family whose carrier is a special linear group over the
closure.

## Main definition

* `TauCeti.ValidLieTypeIndex.specialLinearEquivFrobeniusFixedPoints`: the isomorphism between the
  finite special linear group and the Frobenius fixed points of the special linear group over the
  closure.

## Main results

* `TauCeti.ValidLieTypeIndex.specialLinear_mem_range_galoisFieldEmbedding_iff` and
  `TauCeti.ValidLieTypeIndex.specialLinear_mem_fixedSubgroup_frobenius_iff`: the two entrywise
  characterizations of the finite-field points.
* `TauCeti.ValidLieTypeIndex.specialLinear_mem_range_extensionGaloisFieldEmbedding_iff`: the
  entrywise characterization of the points over the field with `q ^ k` elements.
* `TauCeti.ValidLieTypeIndex.specialLinear_range_galoisFieldEmbedding_eq_fixedSubgroup`: the range
  of the coefficient embedding is the fixed subgroup of the entrywise Frobenius.
* `TauCeti.ValidLieTypeIndex.finite_fixedSubgroup_specialLinear`: that fixed subgroup is finite.

## Provenance

This file adapts `CFSG/Adapters/SpecialLinearFrobenius.lean` from
`https://github.com/AxiomMath/CFSG` (Apache-2.0), commit
`69cb972f587a3ecc035e092253167ff2e303c962`.
-/

public section

noncomputable section

open Matrix

namespace TauCeti.ValidLieTypeIndex

/-- A special linear matrix over the closure has finite-field coordinates exactly when every entry
is fixed by the `q`-power Frobenius. -/
theorem specialLinear_mem_range_galoisFieldEmbedding_iff
    (d : ValidLieTypeIndex) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : SpecialLinearGroup ι d.Closure) :
    g ∈ (SpecialLinearGroup.map (n := ι) d.galoisFieldEmbedding).range ↔
      ∀ i j, (g i j) ^ d.fieldOrder = g i j := by
  rw [SpecialLinearGroup.mem_range_map_iff d.galoisFieldEmbedding.injective]
  exact forall₂_congr fun _ _ ↦ d.mem_range_galoisFieldEmbedding_iff

/-- A special linear matrix over the closure has coordinates in the field with `q ^ k` elements
exactly when every entry is fixed by the `q ^ k`-power map. -/
theorem specialLinear_mem_range_extensionGaloisFieldEmbedding_iff
    {d : ValidLieTypeIndex} {k : ℕ} (hk : k ≠ 0) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : SpecialLinearGroup ι d.Closure) :
    g ∈ (SpecialLinearGroup.map (n := ι) (d.extensionGaloisFieldEmbedding k hk)).range ↔
      ∀ i j, (g i j) ^ d.fieldOrder ^ k = g i j := by
  rw [SpecialLinearGroup.mem_range_map_iff (d.extensionGaloisFieldEmbedding k hk).injective]
  exact forall₂_congr fun _ _ ↦ mem_range_extensionGaloisFieldEmbedding_iff hk

/-- A special linear matrix over the closure is fixed by the entrywise `q`-power Frobenius exactly
when every entry is. -/
theorem specialLinear_mem_fixedSubgroup_frobenius_iff
    (d : ValidLieTypeIndex) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : SpecialLinearGroup ι d.Closure) :
    g ∈ fixedSubgroup (SpecialLinearGroup.map (n := ι)
      (iterateFrobenius d.Closure d.characteristic d.fieldExponent)) ↔
      ∀ i j, (g i j) ^ d.fieldOrder = g i j := by
  rw [mem_fixedSubgroup]
  constructor
  · intro hg i j
    have hentry := congrArg (fun A : SpecialLinearGroup ι d.Closure => A i j) hg
    rw [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
      at hentry
    simpa only [iterateFrobenius_def, d.fieldOrder_eq_characteristic_pow] using hentry
  · intro hg
    apply Subtype.ext
    ext i j
    rw [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
    simpa only [iterateFrobenius_def, d.fieldOrder_eq_characteristic_pow] using hg i j

/-- The range of the coefficient embedding of the special linear group is the fixed subgroup of
the entrywise `q`-power Frobenius. -/
theorem specialLinear_range_galoisFieldEmbedding_eq_fixedSubgroup
    (d : ValidLieTypeIndex) {ι : Type*} [Fintype ι] [DecidableEq ι] :
    (SpecialLinearGroup.map (n := ι) d.galoisFieldEmbedding).range =
      fixedSubgroup (SpecialLinearGroup.map (n := ι)
        (iterateFrobenius d.Closure d.characteristic d.fieldExponent)) := by
  ext g
  rw [specialLinear_mem_range_galoisFieldEmbedding_iff,
    specialLinear_mem_fixedSubgroup_frobenius_iff]

/-- **The finite special linear group is the group of Frobenius fixed points of the special linear
group over the closure.** The entrywise coefficient extension is injective and its range is that
fixed subgroup, so it restricts to an isomorphism onto the fixed points. -/
def specialLinearEquivFrobeniusFixedPoints
    (d : ValidLieTypeIndex) (ι : Type*) [Fintype ι] [DecidableEq ι] :
    SpecialLinearGroup ι (GaloisField d.characteristic d.fieldExponent) ≃*
      fixedSubgroup (SpecialLinearGroup.map (n := ι)
        (iterateFrobenius d.Closure d.characteristic d.fieldExponent)) :=
  (MonoidHom.ofInjective
      (SpecialLinearGroup.map_injective d.galoisFieldEmbedding.injective)).trans
    (MulEquiv.subgroupCongr (specialLinear_range_galoisFieldEmbedding_eq_fixedSubgroup d))

/-- The isomorphism to the Frobenius fixed points is the entrywise extension of coefficients along
the finite-field embedding. -/
@[simp]
theorem specialLinearEquivFrobeniusFixedPoints_coe
    (d : ValidLieTypeIndex) (ι : Type*) [Fintype ι] [DecidableEq ι]
    (g : SpecialLinearGroup ι (GaloisField d.characteristic d.fieldExponent)) :
    (((specialLinearEquivFrobeniusFixedPoints d ι g : SpecialLinearGroup ι d.Closure)) :
      Matrix ι ι d.Closure) =
      (g : Matrix ι ι (GaloisField d.characteristic d.fieldExponent)).map
        d.galoisFieldEmbedding := (rfl)

/-- The Frobenius fixed points of a special linear group over the closure are finite: they are the
image of the finite matrix group over the field of definition. -/
instance finite_fixedSubgroup_specialLinear (d : ValidLieTypeIndex) (ι : Type*)
    [Fintype ι] [DecidableEq ι] :
    Finite (fixedSubgroup (SpecialLinearGroup.map (n := ι)
      (iterateFrobenius d.Closure d.characteristic d.fieldExponent))) :=
  Finite.of_equiv (SpecialLinearGroup ι (GaloisField d.characteristic d.fieldExponent))
    (specialLinearEquivFrobeniusFixedPoints d ι).toEquiv

end TauCeti.ValidLieTypeIndex

end
