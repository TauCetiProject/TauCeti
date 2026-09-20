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
linear group. Equality with `Suzuki.suzukiGroup` is the finite-field generation theorem that
identifies the two constructions; it is not asserted here.

## Main results

* `SuzukiLieIndex.fieldRange_generatorFieldEmbedding`: the generator field embeds onto the
  Frobenius-fixed field.
* `SuzukiLieIndex.map_fixedSubgroup_le_range_generatorEmbedding`: every Suzuki fixed point has
  finite-field coordinates under the generator embedding.
* `SuzukiLieIndex.mem_finiteFixedSubgroup_iff`: membership in the finite-field fixed subgroup is
  the alternating-form equation together with the isogeny equation over the generator field.
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
@[simp]
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
@[simp]
theorem mem_range_generatorFieldEmbedding_iff (m : ℕ)
    (hvalid : (LieTypeIndex.suzuki m).Valid)
    {x : (of m hvalid).1.Closure} :
    (∃ y, generatorFieldEmbedding m hvalid y = x) ↔
      x ^ (of m hvalid).1.fieldOrder = x := by
  rw [← RingHom.mem_fieldRange]
  rw [fieldRange_generatorFieldEmbedding]
  exact (of m hvalid).1.mem_fixedField

/-- Scalar extension after the Suzuki coordinate change has exactly the invertible matrices
whose entries are fixed by the field Frobenius. -/
@[simp]
theorem mem_range_generatorEmbedding_iff (m : ℕ)
    (hvalid : (LieTypeIndex.suzuki m).Valid)
    (g : GL (Fin 4) (of m hvalid).1.Closure) :
    (∃ g₀, generatorEmbedding m hvalid g₀ = g) ↔
      ∀ i j, (g i j) ^ (of m hvalid).1.fieldOrder = g i j := by
  rw [← MonoidHom.mem_range]
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
    _ ↔ ∀ i j, (g i j) ^ (of m hvalid).1.fieldOrder = g i j := by
      let f := generatorFieldEmbedding m hvalid
      -- Both finite-field embeddings identify their source with the same fixed subfield.
      let eFixed : GaloisField 2 (2 * m + 1) ≃+* (of m hvalid).1.fixedField :=
        f.rangeRestrictFieldEquiv.trans
          (RingEquiv.subfieldCongr (fieldRange_generatorFieldEmbedding m hvalid))
      let e : GaloisField 2 (2 * m + 1) ≃+*
          GaloisField (of m hvalid).1.characteristic (of m hvalid).1.fieldExponent :=
        eFixed.trans (of m hvalid).1.galoisFieldEquivFixedField.symm
      have hcomp : (of m hvalid).1.galoisFieldEmbedding.comp e.toRingHom = f := by
        ext x
        -- `RingEquiv.subfieldCongr` has no coercion lemma in Mathlib; by definition it is the
        -- identity on underlying elements of the closure.
        have hcongr (y : f.fieldRange) :
            ((RingEquiv.subfieldCongr (fieldRange_generatorFieldEmbedding m hvalid) y :
              (of m hvalid).1.fixedField) : (of m hvalid).1.Closure) = y := rfl
        simp only [RingHom.comp_apply, ValidLieTypeIndex.galoisFieldEmbedding_apply,
          RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, e, RingEquiv.trans_apply,
          RingEquiv.apply_symm_apply, eFixed, hcongr, RingHom.rangeRestrictFieldEquiv_apply_coe]
      have hrange : MonoidHom.range (Matrix.GeneralLinearGroup.map (n := Fin 4) f) =
          MonoidHom.range
            (Matrix.GeneralLinearGroup.map (n := Fin 4)
              (of m hvalid).1.galoisFieldEmbedding) := by
        apply le_antisymm
        · rintro _ ⟨g₀, rfl⟩
          refine ⟨Matrix.GeneralLinearGroup.map (n := Fin 4) e.toRingHom g₀, ?_⟩
          ext i j
          rw [Matrix.GeneralLinearGroup.map_apply, Matrix.GeneralLinearGroup.map_apply]
          have hx := DFunLike.congr_fun hcomp (g₀ i j)
          rw [RingHom.comp_apply] at hx
          exact hx
        · rintro _ ⟨g₀, rfl⟩
          refine ⟨Matrix.GeneralLinearGroup.map (n := Fin 4) e.symm.toRingHom g₀, ?_⟩
          ext i j
          have hx :=
            (DFunLike.congr_fun hcomp (e.symm.toRingHom (g₀ i j))).symm
          rw [RingHom.comp_apply] at hx
          have he : e.toRingHom (e.symm.toRingHom (g₀ i j)) = g₀ i j := by
            exact e.apply_symm_apply (g₀ i j)
          rw [he] at hx
          rw [Matrix.GeneralLinearGroup.map_apply, Matrix.GeneralLinearGroup.map_apply]
          exact hx
      rw [hrange]
      exact Matrix.GeneralLinearGroup.mem_range_map_galoisFieldEmbedding_iff g

/-- Every Suzuki Steinberg fixed point in the ambient general linear group has coordinates over
the finite field used by the standard generators. -/
theorem map_fixedSubgroup_le_range_generatorEmbedding (m : ℕ)
    (hvalid : (LieTypeIndex.suzuki m).Valid) :
    (fixedSubgroup (of m hvalid).steinberg).map
        (SpStd.points 1 (of m hvalid).1.Closure).subtype ≤
      (generatorEmbedding m hvalid).range := by
  rintro g ⟨x, hx, rfl⟩
  rw [MonoidHom.mem_range, mem_range_generatorEmbedding_iff]
  intro i j
  exact (of m hvalid).1.mem_fixedField.mp
    ((of m hvalid).coe_mem_fixedField_of_mem_fixedSubgroup_steinberg x hx i j)

/-- The exact finite-field preimage of the Suzuki Steinberg fixed-point subgroup. Equality with
`Suzuki.suzukiGroup` is the associated finite-field generation theorem. -/
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

/-- Over the generator field, a matrix is a Steinberg fixed point exactly when its coordinate
change preserves the alternating form and has special isogeny equal to its entrywise
`2^(m+1)`-st power. -/
theorem mem_finiteFixedSubgroup_iff (m : ℕ) (hvalid : (LieTypeIndex.suzuki m).Valid)
    {g : GL (Fin 4) (GaloisField 2 (2 * m + 1))} :
    g ∈ finiteFixedSubgroup m hvalid ↔
      ((Suzuki.coordinateEquiv (GaloisField 2 (2 * m + 1)) g :
            GL (Fin 4) (GaloisField 2 (2 * m + 1))) :
          Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * m + 1))) *
          JFin 2 (GaloisField 2 (2 * m + 1)) *
          ((Suzuki.coordinateEquiv (GaloisField 2 (2 * m + 1)) g :
              GL (Fin 4) (GaloisField 2 (2 * m + 1))) :
            Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * m + 1)))ᵀ =
        JFin 2 (GaloisField 2 (2 * m + 1)) ∧
      Matrix.symplecticSpecialIsogeny
          ((Suzuki.coordinateEquiv (GaloisField 2 (2 * m + 1)) g :
              GL (Fin 4) (GaloisField 2 (2 * m + 1))) :
            Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * m + 1))) =
        (((Suzuki.coordinateEquiv (GaloisField 2 (2 * m + 1)) g :
              GL (Fin 4) (GaloisField 2 (2 * m + 1))) :
            Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * m + 1))).map
              (fun x ↦ x ^ 2 ^ (m + 1))) := by
  refine ⟨fun hg ↦ ?_, fun h ↦ (mem_finiteFixedSubgroup m hvalid).mpr
    (generatorEmbedding_mem_map_fixedSubgroup m hvalid g h.1 h.2)⟩
  rw [mem_finiteFixedSubgroup, (of m hvalid).mem_map_fixedSubgroup_steinberg_iff,
    coe_generatorEmbedding, SuzukiReeIndex.halfExponent_suzuki,
    Matrix.symplecticSpecialIsogeny_map] at hg
  obtain ⟨hsymp, hiso⟩ := hg
  have hf := (generatorFieldEmbedding m hvalid).injective
  set G := ((Suzuki.coordinateEquiv (GaloisField 2 (2 * m + 1)) g :
      GL (Fin 4) (GaloisField 2 (2 * m + 1))) : Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * m + 1)))
  refine ⟨Matrix.map_injective hf ?_, ?_⟩
  · have key : (G * JFin 2 (GaloisField 2 (2 * m + 1)) * Gᵀ).map
        (generatorFieldEmbedding m hvalid) =
        (JFin 2 (GaloisField 2 (2 * m + 1))).map (generatorFieldEmbedding m hvalid) := by
      rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, JFin_map]
      exact hsymp
    exact key
  · ext i j
    apply hf
    simpa [Matrix.map_apply, map_pow] using hiso i j

/-- The standard generated Suzuki group lies in the exact finite-field preimage of the Steinberg
fixed points. Equality is the finite-field generation theorem identifying the two constructions. -/
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
  Subgroup.map_comap_eq_self (map_fixedSubgroup_le_range_generatorEmbedding m hvalid)

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

/-- Descending an ambient fixed point and extending scalars again recovers that fixed point. -/
@[simp]
theorem generatorEmbedding_finiteFixedSubgroupEquiv_symm_apply (m : ℕ)
    (hvalid : (LieTypeIndex.suzuki m).Valid)
    (g : (fixedSubgroup (of m hvalid).steinberg).map
      (SpStd.points 1 (of m hvalid).1.Closure).subtype) :
    generatorEmbedding m hvalid ((finiteFixedSubgroupEquiv m hvalid).symm g) =
      (g : GL (Fin 4) (of m hvalid).1.Closure) := by
  rw [← coe_finiteFixedSubgroupEquiv_apply]
  exact congrArg Subtype.val ((finiteFixedSubgroupEquiv m hvalid).apply_symm_apply g)

end TauCeti.SuzukiLieIndex
