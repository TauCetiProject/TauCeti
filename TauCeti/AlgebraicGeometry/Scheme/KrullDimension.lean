/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Properties
public import TauCeti.RingTheory.KrullDimension.Equidimensional
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
Likewise `X` is pure-dimensional of dimension `d` exactly when `X ×_{Spec K} Spec L` is: on affine
charts, the irreducible components of `Spec (L ⊗[K] A)` lie over those of `Spec A` and have the
same dimension (`TauCeti.isPureDimensional_primeSpectrum_tensorProduct_iff`).

On a scheme locally of finite type over a field, a nonempty open part `Z ∩ U` of an irreducible
closed subset `Z` has the Krull dimension of `Z`. On an affine chart this is the corresponding
statement for spectra of finitely generated algebras
(`TauCeti.topologicalKrullDim_inter_eq_of_finiteType`), and `Z` is covered by the charts it meets.
This is the input for the locality of pure-dimensionality on such schemes.

On an irreducible scheme locally of finite type over a field, the local ring at every closed point
has the dimension of the scheme. On an affine chart `Spec A` this is the statement that every
maximal ideal of the finitely generated irreducible algebra `A` has height `dim A`
(`TauCeti.height_eq_ringKrullDim_of_isMaximal`), and the chart has the dimension of the scheme.

## Main declarations

* `TauCeti.AlgebraicGeometry.topologicalKrullDim_eq_iSup_openCover`: the Krull dimension of a
  scheme is the supremum of the Krull dimensions of the members of an open cover.
* `TauCeti.AlgebraicGeometry.topologicalKrullDim_pullback_Spec_map_of_field`: the Krull dimension
  of a scheme locally of finite type over a field is invariant under extension of the base field.
* `TauCeti.AlgebraicGeometry.topologicalKrullDim_inter_eq_of_locallyOfFiniteType`: on a scheme
  locally of finite type over a field, a nonempty open part of an irreducible closed subset has
  the dimension of that subset.
* `TauCeti.AlgebraicGeometry.topologicalKrullDim_eq_of_isOpenEmbedding_of_locallyOfFiniteType`:
  a nonempty open subspace of an irreducible scheme locally of finite type over a field has the
  dimension of the scheme.
* `TauCeti.AlgebraicGeometry.isPureDimensional_pullback_Spec_map_iff_of_field`: pure-dimensionality
  of a scheme locally of finite type over a field is invariant under extension of the base field.
* `TauCeti.AlgebraicGeometry.ringKrullDim_stalk_eq_topologicalKrullDim_of_isClosed`: on an
  irreducible scheme locally of finite type over a field, the local ring at a closed point has the
  dimension of the scheme.

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

/-- A nonempty open subspace of an irreducible scheme locally of finite type over a field has
the Krull dimension of the scheme. -/
theorem topologicalKrullDim_eq_of_isOpenEmbedding_of_locallyOfFiniteType
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
    [LocallyOfFiniteType f] [IrreducibleSpace X] {Y : Type*} [TopologicalSpace Y]
    [Nonempty Y] {g : Y → X} (hg : IsOpenEmbedding g) :
    topologicalKrullDim Y = topologicalKrullDim X := by
  obtain ⟨y⟩ : Nonempty Y := inferInstance
  have hdim := topologicalKrullDim_inter_eq_of_locallyOfFiniteType f
    (IrreducibleSpace.isIrreducible_univ X) isClosed_univ hg.isOpen_range
    ⟨g y, Set.mem_univ _, y, rfl⟩
  rw [Set.univ_inter] at hdim
  rw [(Homeomorph.Set.univ X).symm.isHomeomorph.topologicalKrullDim_eq, ← hdim]
  exact hg.toHomeomorph.isHomeomorph.topologicalKrullDim_eq

/-- The spectrum of a finitely generated algebra over a field `K` is pure-dimensional of dimension
`d` exactly when its base change to a field extension `L / K` is. -/
private theorem isPureDimensional_pullback_Spec_iff_of_field {K L : Type u} [Field K] [Field L]
    [Algebra K L] {A : CommRingCat.{u}} (g : Spec A ⟶ Spec (.of K)) [hg : LocallyOfFiniteType g]
    {d : ℕ} :
    IsPureDimensional d (pullback g (Spec.map (CommRingCat.ofHom (algebraMap K L))) : Scheme.{u})
      ↔ IsPureDimensional d (Spec A) := by
  obtain ⟨φ, rfl⟩ : ∃ φ, Spec.map φ = g := ⟨_, Spec.map_preimage g⟩
  let := φ.hom.toAlgebra
  have : Algebra.FiniteType K A :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := φ)).mp ‹_›
  -- The underlying space of `Spec R` is `PrimeSpectrum R` by definition.
  exact (pullbackSpecIso K A L).hom.homeomorph.isPureDimensional_iff.trans <|
    (PrimeSpectrum.homeomorphOfRingEquiv (Algebra.TensorProduct.comm K A L).toRingEquiv
      |>.isPureDimensional_iff).trans (isPureDimensional_primeSpectrum_tensorProduct_iff L)

/-- A scheme locally of finite type over a field `K` is pure-dimensional of dimension `d` exactly
when its base change to a field extension `L / K` is. -/
theorem isPureDimensional_pullback_Spec_map_iff_of_field {K L : Type u} [Field K] [Field L]
    [Algebra K L] {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] {d : ℕ} :
    IsPureDimensional d (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K L))) : Scheme.{u})
      ↔ IsPureDimensional d X := by
  let 𝒰 := X.affineOpenCover.openCover
  let 𝒱 := Scheme.Pullback.openCoverOfLeft 𝒰 f (Spec.map (CommRingCat.ofHom (algebraMap K L)))
  -- Both sides are local on the affine charts of `X` and on their base changes, since
  -- irreducible components of schemes locally of finite type over a field have open parts of
  -- full dimension.
  rw [isPureDimensional_iff_forall_of_isOpenEmbedding (fun Z hZ _ hU hZU ↦
      topologicalKrullDim_inter_eq_of_locallyOfFiniteType (pullback.snd f _) hZ.1
        (isClosed_of_mem_irreducibleComponents Z hZ) hU hZU)
      (fun i ↦ 𝒱.f i) (fun i ↦ (𝒱.f i).isOpenEmbedding) fun x ↦ (𝒱.exists_eq x).imp fun _ ↦ id,
    isPureDimensional_iff_forall_of_isOpenEmbedding (fun Z hZ _ hU hZU ↦
      topologicalKrullDim_inter_eq_of_locallyOfFiniteType f hZ.1
        (isClosed_of_mem_irreducibleComponents Z hZ) hU hZU)
      (fun i ↦ 𝒰.f i) (fun i ↦ (𝒰.f i).isOpenEmbedding) fun x ↦ (𝒰.exists_eq x).imp fun _ ↦ id]
  refine forall_congr' fun (i : 𝒰.I₀) ↦ ?_
  have : LocallyOfFiniteType (𝒰.f i ≫ f) := inferInstance
  exact isPureDimensional_pullback_Spec_iff_of_field (A := X.affineOpenCover.X i) (hg := this) _

/-- On an irreducible scheme `X` locally of finite type over a field, the local ring at a closed
point has the Krull dimension of `X`. -/
theorem ringKrullDim_stalk_eq_topologicalKrullDim_of_isClosed {K : Type u} [Field K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] [IrreducibleSpace X] {x : X}
    (hx : IsClosed {x}) :
    ringKrullDim (X.presheaf.stalk x) = topologicalKrullDim X := by
  -- Pass to an affine chart `Spec R` around `x`, in which `x` is a maximal ideal of the finitely
  -- generated `K`-algebra `R`; its height is `dim R`, and the chart has the dimension of `X`.
  obtain ⟨R, g, _, ⟨y, rfl⟩, -⟩ :=
    X.exists_affine_mem_range_and_range_subset (x := x) (U := ⊤) (by simp)
  obtain ⟨φ, hφ⟩ : ∃ φ, Spec.map φ = g ≫ f := ⟨_, Spec.map_preimage _⟩
  let := φ.hom.toAlgebra
  have : Algebra.FiniteType K R :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := φ)).mp (hφ ▸ inferInstance)
  have : Nonempty (Spec R) := ⟨y⟩
  have : IrreducibleSpace (PrimeSpectrum R) := g.isOpenEmbedding.irreducibleSpace
  have hy : IsClosed ({y} : Set (Spec R)) := by
    have := hx.preimage g.continuous
    rwa [← Set.image_singleton, g.isOpenEmbedding.injective.preimage_image] at this
  have : y.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal y).mp hy
  rw [ringKrullDim_stalk_eq_coheight, coheight_eq_of_isOpenImmersion, ← idealHeight_eq_coheight,
    height_eq_ringKrullDim_of_isMaximal K, ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact topologicalKrullDim_eq_of_isOpenEmbedding_of_locallyOfFiniteType f g.isOpenEmbedding

end AlgebraicGeometry

end TauCeti
