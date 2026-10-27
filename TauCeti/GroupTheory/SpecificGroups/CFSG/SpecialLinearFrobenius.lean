/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.FieldCoordinates
public import TauCeti.GroupTheory.FixedSubgroup

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

## Main definitions

* `TauCeti.ValidLieTypeIndex.specialLinearFrobeniusEmbedding`: the coefficient embedding of the
  finite special linear group into the Frobenius fixed points of the special linear group over the
  closure.
* `TauCeti.ValidLieTypeIndex.specialLinearEquivFrobeniusFixedPoints`: the resulting isomorphism
  between the finite special linear group and those fixed points.

## Main results

* `TauCeti.ValidLieTypeIndex.specialLinear_mem_range_galoisFieldEmbedding_iff` and
  `TauCeti.ValidLieTypeIndex.specialLinear_mem_fixedSubgroup_frobenius_iff`: the two entrywise
  characterizations of the finite-field points.
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
  constructor
  · rintro ⟨g₀, rfl⟩ i j
    exact d.mem_range_galoisFieldEmbedding_iff.mp
      ⟨g₀ i j, by rw [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
        Matrix.map_apply]⟩
  · intro hg
    obtain ⟨A, hA⟩ := (Matrix.exists_map_galoisFieldEmbedding_iff_frobenius
      (d := d) (g : Matrix ι ι d.Closure)).mpr hg
    have hdet : A.det = 1 := by
      apply d.galoisFieldEmbedding.injective
      calc
        d.galoisFieldEmbedding A.det = (A.map d.galoisFieldEmbedding).det :=
          d.galoisFieldEmbedding.map_det A
        _ = (g : Matrix ι ι d.Closure).det := congrArg Matrix.det hA
        _ = 1 := g.property
        _ = d.galoisFieldEmbedding 1 := (map_one _).symm
    refine ⟨⟨A, hdet⟩, ?_⟩
    apply Subtype.ext
    exact hA

/-- The coefficient embedding of the finite special linear group is injective. -/
theorem specialLinear_map_galoisFieldEmbedding_injective
    (d : ValidLieTypeIndex) {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Function.Injective (SpecialLinearGroup.map (n := ι) d.galoisFieldEmbedding) := by
  intro A B hAB
  apply Subtype.ext
  ext i j
  apply d.galoisFieldEmbedding.injective
  exact congrArg (fun g : SpecialLinearGroup ι d.Closure => g i j) hAB

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
    change iterateFrobenius d.Closure d.characteristic d.fieldExponent (g i j) = g i j
      at hentry
    simpa only [iterateFrobenius_def, d.fieldOrder_eq_characteristic_pow] using hentry
  · intro hg
    apply Subtype.ext
    ext i j
    change iterateFrobenius d.Closure d.characteristic d.fieldExponent (g i j) = g i j
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

/-- The coefficient embedding of the finite special linear group into the Frobenius fixed points of
the special linear group over the closure. -/
def specialLinearFrobeniusEmbedding
    (d : ValidLieTypeIndex) (ι : Type*) [Fintype ι] [DecidableEq ι] :
    SpecialLinearGroup ι (GaloisField d.characteristic d.fieldExponent) →*
      fixedSubgroup (SpecialLinearGroup.map (n := ι)
        (iterateFrobenius d.Closure d.characteristic d.fieldExponent)) where
  toFun g := ⟨SpecialLinearGroup.map d.galoisFieldEmbedding g, by
    rw [← specialLinear_range_galoisFieldEmbedding_eq_fixedSubgroup]
    exact ⟨g, rfl⟩⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' g h := Subtype.ext (map_mul _ g h)

/-- The coefficient embedding of the finite special linear group is bijective. -/
theorem specialLinearFrobeniusEmbedding_bijective
    (d : ValidLieTypeIndex) (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Function.Bijective (specialLinearFrobeniusEmbedding d ι) := by
  constructor
  · intro g h heq
    apply specialLinear_map_galoisFieldEmbedding_injective d
    exact congrArg Subtype.val heq
  · intro g
    have hg : (g : SpecialLinearGroup ι d.Closure) ∈
        (SpecialLinearGroup.map (n := ι) d.galoisFieldEmbedding).range :=
      (specialLinear_range_galoisFieldEmbedding_eq_fixedSubgroup d).symm.le g.property
    obtain ⟨h, hh⟩ := hg
    exact ⟨h, Subtype.ext hh⟩

/-- **The finite special linear group is the group of Frobenius fixed points of the special linear
group over the closure.** -/
def specialLinearEquivFrobeniusFixedPoints
    (d : ValidLieTypeIndex) (ι : Type*) [Fintype ι] [DecidableEq ι] :
    SpecialLinearGroup ι (GaloisField d.characteristic d.fieldExponent) ≃*
      fixedSubgroup (SpecialLinearGroup.map (n := ι)
        (iterateFrobenius d.Closure d.characteristic d.fieldExponent)) :=
  MulEquiv.ofBijective (specialLinearFrobeniusEmbedding d ι)
    (specialLinearFrobeniusEmbedding_bijective d ι)

/-- The isomorphism to the Frobenius fixed points is the entrywise extension of coefficients along
the finite-field embedding. -/
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
