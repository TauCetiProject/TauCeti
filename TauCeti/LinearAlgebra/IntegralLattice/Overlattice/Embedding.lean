/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Overlattice.Graph
public import TauCeti.LinearAlgebra.IntegralLattice.PrimitiveEmbedding

/-!
# Primitive embeddings from discriminant gluing

Two even nondegenerate lattices have opposite discriminant forms if and only if they occur
as primitive coordinate sublattices of an even unimodular overlattice of their rational
orthogonal sum. The forward construction is `glueAlongDiscriminant`; the converse reads its
graph from the overlattice. Primitivity is expressed by the native `IsPrimitiveEmbedding`,
not by an assumption about a discriminant subgroup.

In particular, a lattice realizing the negative discriminant form of `L` supplies a primitive
embedding of `L` into an even unimodular lattice. The signature of the ambient lattice is
the sum of the two signatures. This is the gluing direction of the primitive embedding
criterion; it does not assert that a lattice with a prescribed discriminant form exists.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*,
  Proposition 1.6.1 and Theorem 1.12.2.
-/

public section

namespace TauCeti.IntegralLattice

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
variable (L : IntegralLattice V) (M : IntegralLattice W) [L.IsNondegenerate] [M.IsNondegenerate]
variable (hL : L.IsEven) (hM : M.IsEven)
variable (e : FiniteQuadraticModule.Isometry (L.discriminantQuadraticModule hL)
  (M.discriminantQuadraticModule hM).neg)

/-- The first coordinate inclusion into the graph gluing is a primitive embedding. -/
@[simp]
theorem isPrimitiveEmbedding_inl_glueAlongDiscriminant :
    IsPrimitiveEmbedding L (L.glueAlongDiscriminant M hL hM e) (LinearMap.inl ℚ V W) := by
  have hmem (x : V) (hx : x ∈ L.carrier) :
      (LinearMap.inl ℚ V W).restrictScalars ℤ x ∈ (L.glueAlongDiscriminant M hL hM e).carrier :=
    (L.mem_glueAlongDiscriminant_left_iff M hL hM e x).mpr hx
  refine (isPrimitiveEmbedding_iff_isTorsionFree_quotient _ LinearMap.inl_injective
    (fun x y ↦ by simp [glueAlongDiscriminant_form])
    (Submodule.map_le_iff_le_comap.mpr hmem)).mpr ?_
  have hglue : ((LinearMap.inl ℚ V W).restrictScalars ℤ).restrict hmem =
      L.glueLeft M hL hM e :=
    LinearMap.ext fun x ↦ Subtype.ext (L.coe_glueLeft_apply M hL hM e x).symm
  rw [← LinearMap.range_restrict _ hmem, hglue]
  exact L.isTorsionFree_quotient_range_glueLeft M hL hM e

/-- The second coordinate inclusion into the graph gluing is a primitive embedding. -/
@[simp]
theorem isPrimitiveEmbedding_inr_glueAlongDiscriminant :
    IsPrimitiveEmbedding M (L.glueAlongDiscriminant M hL hM e) (LinearMap.inr ℚ V W) := by
  have hmem (y : W) (hy : y ∈ M.carrier) :
      (LinearMap.inr ℚ V W).restrictScalars ℤ y ∈ (L.glueAlongDiscriminant M hL hM e).carrier :=
    (L.mem_glueAlongDiscriminant_right_iff M hL hM e y).mpr hy
  refine (isPrimitiveEmbedding_iff_isTorsionFree_quotient _ LinearMap.inr_injective
    (fun x y ↦ by simp [glueAlongDiscriminant_form])
    (Submodule.map_le_iff_le_comap.mpr hmem)).mpr ?_
  have hglue : ((LinearMap.inr ℚ V W).restrictScalars ℤ).restrict hmem =
      L.glueRight M hL hM e :=
    LinearMap.ext fun y ↦ Subtype.ext (L.coe_glueRight_apply M hL hM e y).symm
  rw [← LinearMap.range_restrict _ hmem, hglue]
  exact L.isTorsionFree_quotient_range_glueRight M hL hM e

/-- Opposite discriminant forms are equivalent to the existence of an even unimodular
overlattice of the rational orthogonal sum in which both coordinate inclusions are primitive.
The inclusions need not give an integral direct-sum decomposition. -/
theorem nonempty_discriminant_neg_isometry_iff_exists_primitive_overlattice :
    Nonempty (FiniteQuadraticModule.Isometry (L.discriminantQuadraticModule hL)
      (M.discriminantQuadraticModule hM).neg) ↔
    ∃ N : IntegralLattice (V × W), N.form = (L.orthogonalSum M).form ∧
      N.IsEven ∧ N.IsUnimodular ∧
      IsPrimitiveEmbedding L N (LinearMap.inl ℚ V W) ∧
      IsPrimitiveEmbedding M N (LinearMap.inr ℚ V W) := by
  constructor
  · rintro ⟨e⟩
    exact ⟨L.glueAlongDiscriminant M hL hM e,
      L.glueAlongDiscriminant_form M hL hM e,
      L.isEven_glueAlongDiscriminant M hL hM e,
      L.isUnimodular_glueAlongDiscriminant M hL hM e,
      L.isPrimitiveEmbedding_inl_glueAlongDiscriminant M hL hM e,
      L.isPrimitiveEmbedding_inr_glueAlongDiscriminant M hL hM e⟩
  · rintro ⟨N, hform, hN, hU, hleft, hright⟩
    have hle : (L.orthogonalSum M).carrier ≤ N.carrier := by
      rintro ⟨x, y⟩ hxy
      rw [orthogonalSum_carrier, Submodule.mem_prod] at hxy
      obtain ⟨hx, hy⟩ := hxy
      simpa using N.carrier.add_mem (hleft.map_carrier ⟨x, hx, rfl⟩)
        (hright.map_carrier ⟨y, hy, rfl⟩)
    obtain ⟨f, _⟩ := L.exists_eq_glueAlongDiscriminant M hL hM N hform hle hN hU
      (fun x ↦ (hleft.apply_mem_carrier_iff x).mp)
      (fun y ↦ (hright.apply_mem_carrier_iff y).mp)
    exact ⟨f⟩

/-- A realization of the negative discriminant form yields an even unimodular target with
the sum signature and a primitive embedding of each of the two lattices. -/
theorem exists_isPrimitiveEmbedding_of_discriminant_neg_isometry
    (he : Nonempty (FiniteQuadraticModule.Isometry (L.discriminantQuadraticModule hL)
      (M.discriminantQuadraticModule hM).neg)) :
    ∃ N : IntegralLattice (V × W), N.IsEven ∧ N.IsUnimodular ∧
      N.signature =
        (L.sigPos + M.sigPos, L.sigNull + M.sigNull, L.sigNeg + M.sigNeg) ∧
      IsPrimitiveEmbedding L N (LinearMap.inl ℚ V W) ∧
      IsPrimitiveEmbedding M N (LinearMap.inr ℚ V W) := by
  obtain ⟨e⟩ := he
  exact ⟨L.glueAlongDiscriminant M hL hM e,
    L.isEven_glueAlongDiscriminant M hL hM e,
    L.isUnimodular_glueAlongDiscriminant M hL hM e,
    L.signature_glueAlongDiscriminant M hL hM e,
    L.isPrimitiveEmbedding_inl_glueAlongDiscriminant M hL hM e,
    L.isPrimitiveEmbedding_inr_glueAlongDiscriminant M hL hM e⟩

end TauCeti.IntegralLattice
