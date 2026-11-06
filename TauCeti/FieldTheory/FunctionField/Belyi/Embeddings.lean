/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Belyi.Model
public import TauCeti.FieldTheory.Normal.Embeddings
import TauCeti.GroupTheory.Coset.Basic

/-!
# Embeddings of a field of definition and the Galois orbit

A model over an intermediate field `K` of a normal algebraic extension `k / ℚ` makes
`Gal(k / K)` a subgroup of the stabilizer of its Belyi-pair class `c`. Consequently every
embedding `K →ₐ[ℚ] k` determines a class in the Galois orbit of `c`, independently of the
automorphism extending the embedding. Every orbit class is reached.

The fibre over each class has cardinality `[Stab(c) : Gal(k / K)]`. In particular the degree
of a finite field of definition is the true orbit size times this multiplicity. The field
`K` need not be normal over `ℚ`, and no closedness hypothesis on the stabilizer is used.

The construction uses `TauCeti.FieldTheory.fixingSubgroupQuotientEquivAlgHom` to identify
embeddings with cosets and Mathlib's `MulAction.orbitEquivQuotientStabilizer` to identify
the orbit with cosets of the stabilizer.
-/

public section

namespace TauCeti.AlgebraicBelyiPair.IsoClass

variable {k : Type*} [Field k] [CharZero k] [Normal ℚ k]
  {K : IntermediateField ℚ k} {c : IsoClass k}

/-- An embedding of a field of definition determines a conjugate class. This map sends the
restriction of an automorphism `g` to the class `g • c`. -/
noncomputable def IsDefinedOver.embeddingToOrbit (hc : c.IsDefinedOver K)
    (φ : K →ₐ[ℚ] k) : MulAction.orbit (k ≃ₐ[ℚ] k) c :=
  (MulAction.orbitEquivQuotientStabilizer (k ≃ₐ[ℚ] k) c).symm
    (Subgroup.quotientMapOfLE
      (by simpa only [IntermediateField.fieldRange_val] using hc.fixingSubgroup_le_stabilizer)
      ((FieldTheory.fixingSubgroupQuotientEquivAlgHom K.val).symm φ))

/-- The embedding obtained by restricting `g` gives the conjugate class `g • c`. -/
@[simp]
theorem IsDefinedOver.embeddingToOrbit_comp_val (hc : c.IsDefinedOver K) (g : k ≃ₐ[ℚ] k) :
    (hc.embeddingToOrbit (g.toAlgHom.comp K.val) : IsoClass k) = g • c := by
  rw [embeddingToOrbit, ← FieldTheory.fixingSubgroupQuotientEquivAlgHom_mk K.val g,
    Equiv.symm_apply_apply, Subgroup.quotientMapOfLE_apply_mk,
    MulAction.orbitEquivQuotientStabilizer_symm_apply]

/-- Every conjugate class is produced by an embedding of the field of definition. -/
theorem IsDefinedOver.embeddingToOrbit_surjective (hc : c.IsDefinedOver K) :
    Function.Surjective hc.embeddingToOrbit := by
  rintro ⟨d, g, rfl⟩
  exact ⟨g.toAlgHom.comp K.val, Subtype.ext (hc.embeddingToOrbit_comp_val g)⟩

/-- Postcomposing an embedding with an automorphism conjugates its associated class. -/
theorem IsDefinedOver.embeddingToOrbit_smul (hc : c.IsDefinedOver K)
    (g : k ≃ₐ[ℚ] k) (φ : K →ₐ[ℚ] k) :
    (hc.embeddingToOrbit (g • φ) : IsoClass k) =
      g • (hc.embeddingToOrbit φ : IsoClass k) := by
  obtain ⟨h, rfl⟩ := MulAction.exists_smul_eq (k ≃ₐ[ℚ] k) K.val φ
  rw [← mul_smul, AlgEquiv.smul_algHom_def, hc.embeddingToOrbit_comp_val,
    AlgEquiv.smul_algHom_def, hc.embeddingToOrbit_comp_val, mul_smul]

/-- Two embeddings represented by `g` and `h` give the same conjugate class exactly when
`g` and `h` have the same left coset of the stabilizer. -/
theorem IsDefinedOver.embeddingToOrbit_eq_iff (hc : c.IsDefinedOver K)
    (g h : k ≃ₐ[ℚ] k) :
    hc.embeddingToOrbit (g.toAlgHom.comp K.val) =
        hc.embeddingToOrbit (h.toAlgHom.comp K.val) ↔
      (QuotientGroup.mk g : (k ≃ₐ[ℚ] k) ⧸ MulAction.stabilizer (k ≃ₐ[ℚ] k) c) =
        QuotientGroup.mk h := by
  rw [Subtype.ext_iff, hc.embeddingToOrbit_comp_val, hc.embeddingToOrbit_comp_val,
    QuotientGroup.eq, MulAction.mem_stabilizer_iff, mul_smul, inv_smul_eq_iff]
  exact eq_comm

/-- Every fibre of the embedding map has cardinality equal to the relative index of
`Gal(k / K)` in the stabilizer of the class. This includes infinite fibres, whose `Nat.card`
is zero. -/
theorem IsDefinedOver.card_fiber_embeddingToOrbit (hc : c.IsDefinedOver K)
    (d : MulAction.orbit (k ≃ₐ[ℚ] k) c) :
    Nat.card {φ : K →ₐ[ℚ] k // hc.embeddingToOrbit φ = d} =
      K.fixingSubgroup.relIndex (MulAction.stabilizer (k ≃ₐ[ℚ] k) c) := by
  let e := FieldTheory.fixingSubgroupQuotientEquivAlgHom K.val
  let o := MulAction.orbitEquivQuotientStabilizer (k ≃ₐ[ℚ] k) c
  have hle : K.val.fieldRange.fixingSubgroup ≤ MulAction.stabilizer (k ≃ₐ[ℚ] k) c := by
    simpa only [IntermediateField.fieldRange_val] using hc.fixingSubgroup_le_stabilizer
  have hf (φ) : hc.embeddingToOrbit φ = d ↔
      Subgroup.quotientMapOfLE hle (e.symm φ) = o d := by
    simp only [embeddingToOrbit, e, Equiv.symm_apply_eq, o]
  rw [Nat.card_congr (e.symm.subtypeEquiv
      (q := fun q ↦ Subgroup.quotientMapOfLE hle q = o d) hf),
    Subgroup.card_fiber_quotientMapOfLE]
  rw [IntermediateField.fieldRange_val]

/-- The degree of a field of definition is the true orbit size times the common fibre
multiplicity. As an equality of natural numbers this also holds for infinite degrees. -/
theorem IsDefinedOver.finrank_eq_trueOrbitSize_mul_relIndex (hc : c.IsDefinedOver K) :
    Module.finrank ℚ K = c.trueOrbitSize *
      K.fixingSubgroup.relIndex (MulAction.stabilizer (k ≃ₐ[ℚ] k) c) := by
  let : IsGalois ℚ k := ⟨⟩
  rw [IntermediateField.finrank_eq_fixingSubgroup_index, trueOrbitSize_eq_index, mul_comm]
  exact (Subgroup.relIndex_mul_index hc.fixingSubgroup_le_stabilizer).symm

/-- The true orbit size divides the degree of every field of definition. -/
theorem IsDefinedOver.trueOrbitSize_dvd_finrank (hc : c.IsDefinedOver K) :
    c.trueOrbitSize ∣ Module.finrank ℚ K := by
  rw [hc.finrank_eq_trueOrbitSize_mul_relIndex]
  exact dvd_mul_right _ _

/-- A finite field of definition bounds the number of conjugate classes by its degree. -/
theorem IsDefinedOver.trueOrbitSize_le_finrank [FiniteDimensional ℚ K]
    (hc : c.IsDefinedOver K) : c.trueOrbitSize ≤ Module.finrank ℚ K :=
  Nat.le_of_dvd Module.finrank_pos hc.trueOrbitSize_dvd_finrank

end TauCeti.AlgebraicBelyiPair.IsoClass
