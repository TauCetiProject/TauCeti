/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Belyi.Model
public import TauCeti.FieldTheory.Normal.Embeddings

/-!
# Embeddings of a field of definition and the Galois orbit

A model over an intermediate field `K` of a normal algebraic extension `k / ℚ` makes
`Gal(k / K)` a subgroup of the stabilizer of its Belyi-pair class `c`. Consequently every
embedding `K →ₐ[ℚ] k` determines a class in the Galois orbit of `c`, independently of the
automorphism extending the embedding. Every orbit class is reached.

The fibre over each class has cardinality `[Stab(c) : Gal(k / K)]`. In particular the degree
of a finite field of definition is the true orbit size times this multiplicity. The field
`K` need not be normal over `ℚ`, and no closedness hypothesis on the stabilizer is used.

These are Belyi-pair specializations of `TauCeti.FieldTheory.embeddingToOrbit` and its
fibre and degree formulas for an arbitrary action of the ambient Galois group.
-/

public section

namespace TauCeti.AlgebraicBelyiPair.IsoClass

variable {k : Type*} [Field k] [CharZero k] [Normal ℚ k]
  {K : IntermediateField ℚ k} {c : IsoClass k}

/-- An embedding of a field of definition determines a conjugate class. This map sends the
restriction of an automorphism `g` to the class `g • c`. -/
noncomputable def IsDefinedOver.embeddingToOrbit (hc : c.IsDefinedOver K)
    (φ : K →ₐ[ℚ] k) : MulAction.orbit (k ≃ₐ[ℚ] k) c :=
  FieldTheory.embeddingToOrbit hc.fixingSubgroup_le_stabilizer φ

/-- The embedding obtained by restricting `g` gives the conjugate class `g • c`. -/
@[simp]
theorem IsDefinedOver.embeddingToOrbit_comp_val (hc : c.IsDefinedOver K) (g : k ≃ₐ[ℚ] k) :
    (hc.embeddingToOrbit (g.toAlgHom.comp K.val) : IsoClass k) = g • c :=
  FieldTheory.embeddingToOrbit_comp_val hc.fixingSubgroup_le_stabilizer g

/-- Every conjugate class is produced by an embedding of the field of definition. -/
theorem IsDefinedOver.embeddingToOrbit_surjective (hc : c.IsDefinedOver K) :
    Function.Surjective hc.embeddingToOrbit :=
  FieldTheory.embeddingToOrbit_surjective hc.fixingSubgroup_le_stabilizer

/-- Postcomposing an embedding with an automorphism conjugates its associated class. -/
theorem IsDefinedOver.embeddingToOrbit_smul (hc : c.IsDefinedOver K)
    (g : k ≃ₐ[ℚ] k) (φ : K →ₐ[ℚ] k) :
    (hc.embeddingToOrbit (g • φ) : IsoClass k) =
      g • (hc.embeddingToOrbit φ : IsoClass k) :=
  FieldTheory.embeddingToOrbit_smul hc.fixingSubgroup_le_stabilizer g φ

/-- Two embeddings represented by `g` and `h` give the same conjugate class exactly when
`g` and `h` have the same left coset of the stabilizer. -/
theorem IsDefinedOver.embeddingToOrbit_eq_iff (hc : c.IsDefinedOver K)
    (g h : k ≃ₐ[ℚ] k) :
    hc.embeddingToOrbit (g.toAlgHom.comp K.val) =
        hc.embeddingToOrbit (h.toAlgHom.comp K.val) ↔
      (QuotientGroup.mk g : (k ≃ₐ[ℚ] k) ⧸ MulAction.stabilizer (k ≃ₐ[ℚ] k) c) =
        QuotientGroup.mk h :=
  FieldTheory.embeddingToOrbit_eq_iff hc.fixingSubgroup_le_stabilizer g h

/-- Every fibre of the embedding map has cardinality equal to the relative index of
`Gal(k / K)` in the stabilizer of the class. This includes infinite fibres, whose `Nat.card`
is zero. -/
theorem IsDefinedOver.card_fiber_embeddingToOrbit (hc : c.IsDefinedOver K)
    (d : MulAction.orbit (k ≃ₐ[ℚ] k) c) :
    Nat.card {φ : K →ₐ[ℚ] k // hc.embeddingToOrbit φ = d} =
      K.fixingSubgroup.relIndex (MulAction.stabilizer (k ≃ₐ[ℚ] k) c) :=
  FieldTheory.card_fiber_embeddingToOrbit hc.fixingSubgroup_le_stabilizer d

/-- The degree of a field of definition is the true orbit size times the common fibre
multiplicity. As an equality of natural numbers this also holds for infinite degrees. -/
theorem IsDefinedOver.finrank_eq_trueOrbitSize_mul_relIndex (hc : c.IsDefinedOver K) :
    Module.finrank ℚ K = c.trueOrbitSize *
      K.fixingSubgroup.relIndex (MulAction.stabilizer (k ≃ₐ[ℚ] k) c) := by
  simpa only [trueOrbitSize_eq_index, MulAction.index_stabilizer, Nat.card_coe_set_eq] using
    FieldTheory.finrank_eq_card_orbit_mul_relIndex hc.fixingSubgroup_le_stabilizer

/-- The true orbit size divides the degree of every field of definition. -/
theorem IsDefinedOver.trueOrbitSize_dvd_finrank (hc : c.IsDefinedOver K) :
    c.trueOrbitSize ∣ Module.finrank ℚ K := by
  simpa only [trueOrbitSize_eq_index, MulAction.index_stabilizer, Nat.card_coe_set_eq] using
    FieldTheory.card_orbit_dvd_finrank hc.fixingSubgroup_le_stabilizer

/-- A finite field of definition bounds the number of conjugate classes by its degree. -/
theorem IsDefinedOver.trueOrbitSize_le_finrank [FiniteDimensional ℚ K]
    (hc : c.IsDefinedOver K) : c.trueOrbitSize ≤ Module.finrank ℚ K := by
  simpa only [trueOrbitSize_eq_index, MulAction.index_stabilizer, Nat.card_coe_set_eq] using
    FieldTheory.card_orbit_le_finrank hc.fixingSubgroup_le_stabilizer

end TauCeti.AlgebraicBelyiPair.IsoClass
