/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.FieldCoordinates
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Suzuki.GeneratorInclusion

/-!
# Descent of Suzuki fixed points to the finite field

The Steinberg fixed-point construction of the Suzuki groups lives in a general linear group over
an algebraic closure, whereas the standard generators live over `GaloisField 2 (2 * m + 1)`.
This file proves that the embedding chosen for the generators has exactly the Frobenius-fixed
field as its image. Consequently every Steinberg fixed point has finite-field coordinates for
that same embedding.

The subgroup `finiteFixedSubgroup` is the exact finite-field preimage of the Steinberg fixed
points. Scalar extension identifies it with the fixed-point subgroup in the ambient general
linear group. Identifying this preimage with `Suzuki.suzukiGroup` is the remaining generation
step; it is not asserted here.

## Main results

* `SuzukiLieIndex.fieldRange_generatorFieldEmbedding`: the generator field embeds onto the
  Frobenius-fixed field.
* `SuzukiLieIndex.fixedSubgroup_le_range_generatorEmbedding`: every Suzuki fixed point has
  finite-field coordinates under the generator embedding.
* `SuzukiLieIndex.suzukiGroup_le_finiteFixedSubgroup`: the standard generated group lies in the
  exact finite-field preimage.
* `SuzukiLieIndex.finiteFixedSubgroupEquiv`: scalar extension identifies the finite-field
  preimage with the Suzuki fixed-point subgroup in the algebraic-closure model.

## References

* M. Suzuki, *On a class of doubly transitive groups*, Annals of Mathematics **75** (1962),
  105--145.
-/

public section

noncomputable section

open Matrix

namespace TauCeti.SuzukiLieIndex

/-- The field embedding chosen for the standard Suzuki generators has image exactly the fixed
field of the field Frobenius. -/
theorem fieldRange_generatorFieldEmbedding (m : ℕ)
    (hvalid : (LieTypeIndex.suzuki m).Valid) :
    (generatorFieldEmbedding m hvalid).fieldRange = (of m hvalid).1.fixedField := by
  apply (of m hvalid).1.eq_fixedField_of_natCard
  rw [← Nat.card_congr (generatorFieldEmbedding m hvalid).rangeRestrictFieldEquiv.toEquiv,
    GaloisField.card]
  · exact (LieTypeIndex.fieldOrder_suzuki m).symm
  · omega

/-- An element of the algebraic closure lies in the range of the field embedding used for the
Suzuki generators exactly when the field Frobenius fixes it. -/
theorem mem_range_generatorFieldEmbedding_iff (m : ℕ)
    (hvalid : (LieTypeIndex.suzuki m).Valid)
    {x : (of m hvalid).1.Closure} :
    x ∈ RingHom.range (generatorFieldEmbedding m hvalid) ↔
      x ^ (of m hvalid).1.fieldOrder = x := by
  change x ∈ (generatorFieldEmbedding m hvalid).fieldRange ↔ _
  rw [fieldRange_generatorFieldEmbedding]
  exact (of m hvalid).1.mem_fixedField

/-- Scalar extension after the Suzuki coordinate change has exactly the invertible matrices
whose entries are fixed by the field Frobenius. -/
theorem mem_range_generatorEmbedding_iff (m : ℕ)
    (hvalid : (LieTypeIndex.suzuki m).Valid)
    (g : GL (Fin 4) (of m hvalid).1.Closure) :
    g ∈ MonoidHom.range (generatorEmbedding m hvalid) ↔
      ∀ i j, (g i j) ^ (of m hvalid).1.fieldOrder = g i j := by
  calc
    g ∈ MonoidHom.range (generatorEmbedding m hvalid) ↔
        g ∈ MonoidHom.range
          (Matrix.GeneralLinearGroup.map (generatorFieldEmbedding m hvalid)) := by
      constructor
      · rintro ⟨g₀, rfl⟩
        refine ⟨Suzuki.coordinateEquiv _ g₀, ?_⟩
        ext i j
        rw [Matrix.GeneralLinearGroup.map_apply, generatorEmbedding_apply]
      · rintro ⟨g₀, rfl⟩
        refine ⟨(Suzuki.coordinateEquiv _).symm g₀, ?_⟩
        ext i j
        rw [generatorEmbedding_apply, Matrix.GeneralLinearGroup.map_apply]
        exact congrArg (generatorFieldEmbedding m hvalid)
          (congrArg (fun h : GL (Fin 4) (GaloisField 2 (2 * m + 1)) ↦ h i j)
            ((Suzuki.coordinateEquiv _).apply_symm_apply g₀))
    _ ↔ ∀ i j, g i j ∈ RingHom.range (generatorFieldEmbedding m hvalid) :=
      Matrix.GeneralLinearGroup.mem_range_map_iff _ _
    _ ↔ ∀ i j, (g i j) ^ (of m hvalid).1.fieldOrder = g i j :=
      forall_congr' fun _ ↦ forall_congr' fun _ ↦
        mem_range_generatorFieldEmbedding_iff m hvalid

/-- Every Suzuki Steinberg fixed point in the ambient general linear group has coordinates over
the finite field used by the standard generators. -/
theorem fixedSubgroup_le_range_generatorEmbedding (m : ℕ)
    (hvalid : (LieTypeIndex.suzuki m).Valid) :
    (fixedSubgroup (of m hvalid).steinberg).map
        (SpStd.points 1 (of m hvalid).1.Closure).subtype ≤
      (generatorEmbedding m hvalid).range := by
  rintro g ⟨x, hx, rfl⟩
  rw [mem_range_generatorEmbedding_iff]
  intro i j
  exact (of m hvalid).1.mem_fixedField.mp
    ((of m hvalid).coe_mem_fixedField_of_mem_fixedSubgroup_steinberg x hx i j)

/-- The exact finite-field preimage of the Suzuki Steinberg fixed-point subgroup. This is the
finite matrix group that remains to be identified with `Suzuki.suzukiGroup`. -/
def finiteFixedSubgroup (m : ℕ) (hvalid : (LieTypeIndex.suzuki m).Valid) :
    Subgroup (GL (Fin 4) (GaloisField 2 (2 * m + 1))) :=
  ((fixedSubgroup (of m hvalid).steinberg).map
      (SpStd.points 1 (of m hvalid).1.Closure).subtype).comap
    (generatorEmbedding m hvalid)

/-- Membership in the finite-field preimage is detected by scalar extension to the Suzuki
Steinberg fixed-point subgroup. -/
@[simp]
theorem mem_finiteFixedSubgroup (m : ℕ) (hvalid : (LieTypeIndex.suzuki m).Valid)
    {g : GL (Fin 4) (GaloisField 2 (2 * m + 1))} :
    g ∈ finiteFixedSubgroup m hvalid ↔
      generatorEmbedding m hvalid g ∈
        (fixedSubgroup (of m hvalid).steinberg).map
          (SpStd.points 1 (of m hvalid).1.Closure).subtype :=
  Iff.rfl

/-- The standard generated Suzuki group lies in the exact finite-field preimage of the Steinberg
fixed points. Equality is precisely the remaining finite-field generation theorem. -/
theorem suzukiGroup_le_finiteFixedSubgroup (m : ℕ)
    (hvalid : (LieTypeIndex.suzuki m).Valid) :
    suzukiGroup m ≤ finiteFixedSubgroup m hvalid := by
  intro g hg
  rw [mem_finiteFixedSubgroup]
  exact map_suzukiGroup_le_map_fixedSubgroup m hvalid ⟨g, hg, rfl⟩

/-- Scalar extension maps the finite-field preimage onto the full Suzuki Steinberg fixed-point
subgroup. -/
theorem map_finiteFixedSubgroup (m : ℕ)
    (hvalid : (LieTypeIndex.suzuki m).Valid) :
    (finiteFixedSubgroup m hvalid).map (generatorEmbedding m hvalid) =
      (fixedSubgroup (of m hvalid).steinberg).map
        (SpStd.points 1 (of m hvalid).1.Closure).subtype :=
  Subgroup.map_comap_eq_self (fixedSubgroup_le_range_generatorEmbedding m hvalid)

/-- Scalar extension is an isomorphism from the finite-field preimage onto the Suzuki Steinberg
fixed-point subgroup in the algebraic-closure model. -/
noncomputable def finiteFixedSubgroupEquiv (m : ℕ)
    (hvalid : (LieTypeIndex.suzuki m).Valid) :
    finiteFixedSubgroup m hvalid ≃*
      (fixedSubgroup (of m hvalid).steinberg).map
        (SpStd.points 1 (of m hvalid).1.Closure).subtype :=
  ((finiteFixedSubgroup m hvalid).equivMapOfInjective
      (generatorEmbedding m hvalid) (generatorEmbedding_injective m hvalid)).trans
    (MulEquiv.subgroupCongr (map_finiteFixedSubgroup m hvalid))

@[simp]
theorem coe_finiteFixedSubgroupEquiv_apply (m : ℕ)
    (hvalid : (LieTypeIndex.suzuki m).Valid) (g : finiteFixedSubgroup m hvalid) :
    (finiteFixedSubgroupEquiv m hvalid g :
        GL (Fin 4) (of m hvalid).1.Closure) = generatorEmbedding m hvalid g :=
  by
    simp only [finiteFixedSubgroupEquiv, MulEquiv.trans_apply,
      Subgroup.coe_equivMapOfInjective_apply, MulEquiv.subgroupCongr_apply]

end TauCeti.SuzukiLieIndex
