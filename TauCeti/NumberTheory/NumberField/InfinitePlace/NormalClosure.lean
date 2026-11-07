/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Normal.Closure
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification

/-!
# Unramifiedness at infinity in normal closures

An extension unramified at every infinite place remains so in its normal closure. Indeed, over
any real embedding of the base field, all embeddings of the extension are real. The subfield
where an ambient complex embedding takes real values therefore contains every conjugate of the
extension, and hence their compositum.

This supplies the archimedean part of passing from an everywhere-unramified extension to an
everywhere-unramified Galois extension. In particular it applies to the second step of a Hilbert
class-field tower, where transfer is applied over the original ground field.

The ambient field need only be algebraic over the ground field; it need not be normal or
algebraically closed. No number-field hypothesis is needed.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, §9, and Chapter VI, §7.
-/

public noncomputable section

open IntermediateField NumberField NumberField.InfinitePlace

namespace IsUnramifiedAtInfinitePlaces

variable {K L M : Type*} [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
  [Algebra.IsAlgebraic K M]

omit [Algebra L M] [IsScalarTower K L M] in
/-- Taking the normal closure inside an algebraic ambient extension creates no ramification at
infinite places. In particular, real places cannot become complex in the normal closure if
none becomes complex in the original extension. -/
theorem normalClosure [IsUnramifiedAtInfinitePlaces K L] :
    IsUnramifiedAtInfinitePlaces K (IntermediateField.normalClosure K L M) := by
  let N := IntermediateField.normalClosure K L M
  refine ⟨fun w ↦ isUnramified_iff.mpr ?_⟩
  by_cases hw : (w.comap (algebraMap K N)).IsReal
  · left
    let φ := ComplexEmbedding.lift M w.embedding
    have hφ : φ.comp (algebraMap N M) = w.embedding :=
      ComplexEmbedding.lift_comp_algebraMap M w.embedding
    have hbase : ComplexEmbedding.IsReal (φ.comp (algebraMap K M)) := by
      rw [IsScalarTower.algebraMap_eq K N M, ← RingHom.comp_assoc, hφ]
      rwa [← isReal_mk_iff, ← comap_mk, mk_embedding]
    -- The real-value equalizer contains the ground field and every embedding image of `L`.
    let R : IntermediateField K M :=
      ((ComplexEmbedding.conjugate φ).eqLocusField φ).toIntermediateField fun x ↦
        congrArg (fun f : K →+* ℂ ↦ f x) (ComplexEmbedding.isReal_iff.mp hbase)
    have hN : N ≤ R := by
      apply normalClosure_le_iff.mpr
      intro f y hy
      obtain ⟨x, rfl⟩ := hy
      have hf : ComplexEmbedding.IsReal (φ.comp (f : L →+* M)) := by
        apply (isUnramified_mk_iff_isUnmixed.mp
          ((InfinitePlace.mk (φ.comp (f : L →+* M))).isUnramified K))
        rw [RingHom.comp_assoc, AlgHom.comp_algebraMap]
        exact hbase
      exact congrArg (fun e : L →+* ℂ ↦ e x) (ComplexEmbedding.isReal_iff.mp hf)
    apply isReal_iff.mpr
    apply ComplexEmbedding.isReal_iff.mpr
    ext x
    -- Membership in `R` is precisely equality with the conjugate value of `φ`.
    have hx : star (φ (x : M)) = φ (x : M) := hN x.property
    have hxφ : φ (x : M) = w.embedding x :=
      ComplexEmbedding.lift_algebraMap_apply M w.embedding x
    rw [hxφ] at hx
    exact hx
  · exact .inr (not_isReal_iff_isComplex.mp hw)

/-- An extension is unramified at every infinite place if and only if its normal closure in an
algebraic ambient extension is. The reverse implication is descent to a subextension. -/
@[simp]
theorem normalClosure_iff :
    IsUnramifiedAtInfinitePlaces K (IntermediateField.normalClosure K L M) ↔
      IsUnramifiedAtInfinitePlaces K L := by
  constructor
  · intro h
    let := h
    have := Algebra.IsAlgebraic.tower_top (K := K) (A := IntermediateField.normalClosure K L M) L
    exact IsUnramifiedAtInfinitePlaces.bot K L (IntermediateField.normalClosure K L M)
  · intro h
    let := h
    exact normalClosure

end IsUnramifiedAtInfinitePlaces
