/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import TauCeti.RingTheory.KrullDimension.FiniteType
public import TauCeti.Topology.KrullDimension

/-!
# Krull dimension of schemes and extension of the base field

The Krull dimension of a scheme is the topological Krull dimension of its underlying space. This
file computes it from an open cover and shows that it is unchanged by extending the base field:
if `X` is locally of finite type over a field `K` and `L / K` is a field extension, then
`X ×_{Spec K} Spec L` has the same Krull dimension as `X`.

The affine case is the commutative-algebra statement `dim (A ⊗[K] L) = dim A` for a finitely
generated `K`-algebra `A` (`TauCeti.ringKrullDim_tensorProduct_field_of_finiteType`); the general
case follows by covering `X` with affine opens, whose base changes cover the fibre product.

This is the input for the stability of fibrewise dimension bounds of morphisms under base change:
the fibre of a base change is the base change of a fibre along an extension of residue fields.

On a scheme locally of finite type over a field, a nonempty open part `Z ∩ U` of an irreducible
closed subset `Z` has the Krull dimension of `Z`. On an affine chart this is the corresponding
statement for spectra of finitely generated algebras
(`TauCeti.topologicalKrullDim_inter_eq_of_finiteType`), and `Z` is covered by the charts it meets.
This is the input for the locality of pure-dimensionality on such schemes.

## Main declarations

* `TauCeti.AlgebraicGeometry.topologicalKrullDim_eq_iSup_openCover`: the Krull dimension of a
  scheme is the supremum of the Krull dimensions of the members of an open cover.
* `TauCeti.AlgebraicGeometry.topologicalKrullDim_pullback_Spec_map_of_field`: the Krull dimension
  of a scheme locally of finite type over a field is invariant under extension of the base field.
* `TauCeti.AlgebraicGeometry.topologicalKrullDim_inter_eq_of_locallyOfFiniteType`: on a scheme
  locally of finite type over a field, a nonempty open part of an irreducible closed subset has
  the dimension of that subset.

## References

* [Stacks Project, Tag 00P4](https://stacks.math.columbia.edu/tag/00P4), the pointwise form of the
  invariance of dimension under extension of the base field
-/

public section

open CategoryTheory Limits AlgebraicGeometry Topology

namespace TauCeti

namespace AlgebraicGeometry

universe u

/-- The Krull dimension of a scheme is the supremum of the Krull dimensions of the members of an
open cover. -/
theorem topologicalKrullDim_eq_iSup_openCover {X : Scheme.{u}} (𝒰 : X.OpenCover) :
    topologicalKrullDim X = ⨆ i, topologicalKrullDim (𝒰.X i) :=
  topologicalKrullDim_eq_iSup_of_isOpenEmbedding (fun i ↦ 𝒰.f i)
    (fun i ↦ (𝒰.f i).isOpenEmbedding) fun x ↦ (𝒰.exists_eq x).imp fun _ ↦ id

/-- For a finitely generated algebra `A` over a field `K` and a field extension `L / K`, the fibre
product `Spec A ×_{Spec K} Spec L` has the Krull dimension of `A`. -/
theorem topologicalKrullDim_pullback_Spec_algebraMap (K L A : Type u) [Field K] [Field L]
    [CommRing A] [Algebra K L] [Algebra K A] [Algebra.FiniteType K A] :
    topologicalKrullDim (pullback (Spec.map (CommRingCat.ofHom (algebraMap K A)))
      (Spec.map (CommRingCat.ofHom (algebraMap K L))) : Scheme.{u}) = ringKrullDim A := by
  rw [(pullbackSpecIso K A L).hom.homeomorph.isHomeomorph.topologicalKrullDim_eq]
  -- The underlying space of `Spec R` is `PrimeSpectrum R` by definition.
  exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _).trans <|
    (ringKrullDim_eq_of_ringEquiv (Algebra.TensorProduct.comm K A L).toRingEquiv).trans
      (ringKrullDim_tensorProduct_field_of_finiteType L A)

/-- The Krull dimension of an affine scheme locally of finite type over a field `K` is invariant
under extension of the base field. -/
private theorem topologicalKrullDim_pullback_Spec_of_field {K L : Type u} [Field K] [Field L]
    [Algebra K L] {A : CommRingCat.{u}} (g : Spec A ⟶ Spec (.of K)) [hg : LocallyOfFiniteType g] :
    topologicalKrullDim (pullback g (Spec.map (CommRingCat.ofHom (algebraMap K L))) : Scheme.{u}) =
      topologicalKrullDim (Spec A) := by
  obtain ⟨φ, rfl⟩ : ∃ φ, Spec.map φ = g := ⟨_, Spec.map_preimage g⟩
  let := φ.hom.toAlgebra
  have : Algebra.FiniteType K A :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := φ)).mp ‹_›
  exact (topologicalKrullDim_pullback_Spec_algebraMap K L A).trans
    (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A).symm

/-- The Krull dimension of a scheme locally of finite type over a field `K` is invariant under
extension of the base field. -/
theorem topologicalKrullDim_pullback_Spec_map_of_field {K L : Type u} [Field K] [Field L]
    [Algebra K L] {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] :
    topologicalKrullDim (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K L))) : Scheme.{u}) =
      topologicalKrullDim X := by
  rw [topologicalKrullDim_eq_iSup_openCover
      (Scheme.Pullback.openCoverOfLeft X.affineOpenCover.openCover f _),
    topologicalKrullDim_eq_iSup_openCover X.affineOpenCover.openCover]
  refine iSup_congr fun (i : X.affineOpenCover.openCover.I₀) ↦ ?_
  have : LocallyOfFiniteType (X.affineOpenCover.openCover.f i ≫ f) := inferInstance
  exact topologicalKrullDim_pullback_Spec_of_field (A := X.affineOpenCover.X i) (hg := this) _

/-- On a scheme locally of finite type over a field, a nonempty open part `Z ∩ U` of an
irreducible closed subset `Z` has the Krull dimension of `Z`. -/
theorem topologicalKrullDim_inter_eq_of_locallyOfFiniteType {K : Type u} [Field K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] {Z U : Set X}
    (hZ : IsIrreducible Z) (hZc : IsClosed Z) (hU : IsOpen U) (hZU : (Z ∩ U).Nonempty) :
    topologicalKrullDim ↥(Z ∩ U) = topologicalKrullDim Z := by
  refine le_antisymm (IsEmbedding.inclusion Set.inter_subset_left).isInducing.topologicalKrullDim_le
    ?_
  let 𝒰 := X.affineOpenCover.openCover
  have he (i : 𝒰.I₀) : IsOpenEmbedding (𝒰.f i) := (𝒰.f i).isOpenEmbedding
  -- `Z` is covered by its preimages in the affine charts that meet it.
  let ι := {i : 𝒰.I₀ // (Z ∩ Set.range (𝒰.f i)).Nonempty}
  rw [topologicalKrullDim_eq_iSup_of_isOpenEmbedding (Y := fun i : ι ↦ (𝒰.f i.1) ⁻¹' Z)
    (fun i ↦ Z.restrictPreimage (𝒰.f i.1)) (fun i ↦ (he i.1).restrictPreimage Z) ?_]
  swap
  · intro z
    obtain ⟨i, y, hy⟩ := 𝒰.exists_eq z.1
    exact ⟨⟨i, z.1, z.2, y, hy⟩, ⟨y, by simp [hy]⟩, Subtype.ext (by simp [hy])⟩
  refine iSup_le fun ⟨i, hi⟩ ↦ ?_
  -- Reduce the projection `↑⟨i, hi⟩` to `i`.
  dsimp only
  have hft : LocallyOfFiniteType (𝒰.f i ≫ f) := inferInstance
  obtain ⟨φ, hφ⟩ : ∃ φ, Spec.map φ = 𝒰.f i ≫ f := ⟨_, Spec.map_preimage _⟩
  let := φ.hom.toAlgebra
  have : Algebra.FiniteType K (X.affineOpenCover.X i) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := φ)).mp (hφ ▸ hft)
  -- Since `Z` is irreducible, the chart meets `Z ∩ U`, and the affine case applies; the
  -- underlying space of `Spec Aᵢ` is `PrimeSpectrum Aᵢ` by definition.
  obtain ⟨_, hxZ, ⟨x, rfl⟩, hxU⟩ := hZ.2 _ _ (he i).isOpen_range hU hi hZU
  calc topologicalKrullDim ↥((𝒰.f i) ⁻¹' Z)
      = topologicalKrullDim ↥((𝒰.f i) ⁻¹' Z ∩ (𝒰.f i) ⁻¹' U) :=
        (topologicalKrullDim_inter_eq_of_finiteType K (hZ.preimage (he i) hi)
          (hZc.preimage (𝒰.f i).continuous) (hU.preimage (𝒰.f i).continuous)
          ⟨x, hxZ, hxU⟩).symm
    _ ≤ topologicalKrullDim ↥(Z ∩ U) :=
        (((he i).isEmbedding.comp IsEmbedding.subtypeVal).codRestrict (Z ∩ U)
          fun y ↦ y.2).isInducing.topologicalKrullDim_le

end AlgebraicGeometry

end TauCeti
