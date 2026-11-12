/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Normal.Closure
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification

/-!
# Unramifiedness at infinity in composita and normal closures

An extension unramified at every infinite place remains so in its normal closure. Indeed, over
any real embedding of the base field, all embeddings of the extension are real. The subfield
where an ambient complex embedding takes real values therefore contains every conjugate of the
extension, and hence their compositum.

This supplies the archimedean part of passing from an everywhere-unramified extension to an
everywhere-unramified Galois extension. In particular it applies to the second step of a Hilbert
class-field tower, where transfer is applied over the original ground field.

The compositum theorem `IsUnramifiedAtInfinitePlaces.iSup` and preservation under embedding
images `AlgHom.isUnramifiedAtInfinitePlaces_fieldRange` give the normal-closure result.
The ambient field need only be algebraic over the ground field; it need not be normal or
algebraically closed. No number-field hypothesis is needed.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, §9, and Chapter VI, §7.
-/

public noncomputable section

open IntermediateField NumberField NumberField.InfinitePlace

namespace IsUnramifiedAtInfinitePlaces

variable {K L M : Type*} [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra K M]

/-- The image of an extension unramified at infinite places under a base-field algebra map is
unramified at infinite places. -/
theorem _root_.AlgHom.isUnramifiedAtInfinitePlaces_fieldRange (f : L →ₐ[K] M)
    [IsUnramifiedAtInfinitePlaces K L] :
    IsUnramifiedAtInfinitePlaces K f.fieldRange := by
  refine ⟨fun w ↦ ?_⟩
  let e := f.equivFieldRange
  have he : e.toRingHom.comp (e.symm.toAlgHom : f.fieldRange →+* L) = RingHom.id _ :=
    e.toRingEquiv.comp_symm
  simpa only [← comap_comp, he, comap_id] using
    ((w.comap e.toRingHom).isUnramified K).comap_algHom e.symm.toAlgHom

variable [Algebra.IsAlgebraic K M]

/-- A compositum of intermediate extensions unramified at infinite places is unramified at
infinite places. -/
theorem iSup {ι : Sort*} (E : ι → IntermediateField K M)
    [∀ i, IsUnramifiedAtInfinitePlaces K (E i)] :
    IsUnramifiedAtInfinitePlaces K (⨆ i, E i : IntermediateField K M) := by
  let N := ⨆ i, E i
  refine ⟨fun w ↦ isUnramified_iff.mpr ?_⟩
  by_cases hw : (w.comap (algebraMap K N)).IsReal
  · left
    let φ := ComplexEmbedding.lift M w.embedding
    have hφ : φ.comp (algebraMap N M) = w.embedding :=
      ComplexEmbedding.lift_comp_algebraMap M w.embedding
    have hbase : ComplexEmbedding.IsReal (φ.comp (algebraMap K M)) := by
      rw [IsScalarTower.algebraMap_eq K N M, ← RingHom.comp_assoc, hφ]
      rwa [← isReal_mk_iff, ← comap_mk, mk_embedding]
    -- The real-value equalizer contains the ground field and every member of the family.
    let R : IntermediateField K M :=
      ((ComplexEmbedding.conjugate φ).eqLocusField φ).toIntermediateField fun x ↦
        congrArg (fun f : K →+* ℂ ↦ f x) (ComplexEmbedding.isReal_iff.mp hbase)
    have hN : N ≤ R := by
      apply iSup_le
      intro i y hy
      have hf : ComplexEmbedding.IsReal (φ.comp (algebraMap (E i) M)) := by
        apply (isUnramified_mk_iff_isUnmixed.mp
          ((InfinitePlace.mk (φ.comp (algebraMap (E i) M))).isUnramified K))
        rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]
        exact hbase
      exact congrArg (fun e : E i →+* ℂ ↦ e ⟨y, hy⟩) (ComplexEmbedding.isReal_iff.mp hf)
    apply isReal_iff.mpr
    apply ComplexEmbedding.isReal_iff.mpr
    ext x
    have hx : ComplexEmbedding.conjugate φ x = φ x :=
      RingHom.mem_eqLocusField.mp (hN x.property)
    have hxφ : φ (x : M) = w.embedding x :=
      ComplexEmbedding.lift_algebraMap_apply M w.embedding x
    simpa only [ComplexEmbedding.conjugate_coe_eq, hxφ] using hx
  · exact .inr (not_isReal_iff_isComplex.mp hw)

/-- Taking the normal closure inside an algebraic ambient extension creates no ramification at
infinite places. In particular, real places cannot become complex in the normal closure if
none becomes complex in the original extension. -/
@[instance]
theorem normalClosure [IsUnramifiedAtInfinitePlaces K L] :
    IsUnramifiedAtInfinitePlaces K (IntermediateField.normalClosure K L M) := by
  rw [normalClosure_def]
  let (f : L →ₐ[K] M) : IsUnramifiedAtInfinitePlaces K f.fieldRange :=
    f.isUnramifiedAtInfinitePlaces_fieldRange
  exact iSup _

variable [Algebra L M] [IsScalarTower K L M]

/-- An extension is unramified at every infinite place if and only if its normal closure in an
algebraic ambient extension is. The reverse implication is descent to a subextension. -/
@[simp]
theorem normalClosure_iff :
    IsUnramifiedAtInfinitePlaces K (IntermediateField.normalClosure K L M) ↔
      IsUnramifiedAtInfinitePlaces K L := by
  constructor
  · intro h
    have := Algebra.IsAlgebraic.tower_top (K := K) (A := IntermediateField.normalClosure K L M) L
    exact IsUnramifiedAtInfinitePlaces.bot K L (IntermediateField.normalClosure K L M)
  · intro h
    exact normalClosure

end IsUnramifiedAtInfinitePlaces
