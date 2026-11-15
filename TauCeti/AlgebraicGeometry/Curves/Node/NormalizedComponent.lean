/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import TauCeti.AlgebraicGeometry.Curves.Basic
public import TauCeti.AlgebraicGeometry.Curves.Node.Blowup
public import TauCeti.AlgebraicGeometry.Curves.Node.Normalization
public import TauCeti.AlgebraicGeometry.Scheme.Regular.Components
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.RiemannRoch.Finiteness
import TauCeti.AlgebraicGeometry.Blowup.ExceptionalDivisor
import TauCeti.AlgebraicGeometry.Blowup.Pullback
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.SchematicDensity
import TauCeti.AlgebraicGeometry.IdealSheaf.Comap
import TauCeti.AlgebraicGeometry.IrreducibleOfConnectedDomainStalk
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension
import TauCeti.AlgebraicGeometry.Scheme.KrullDimension

/-!
# Normalized components of nodal curves over a field

Let `X` be a scheme over a field `K` whose structure morphism `X ↘ Spec K` is at worst nodal of
relative dimension one (`AtWorstNodalOfRelativeDimensionOne`). Blowing up the singular subscheme
`Sing(X/K)` yields a regular scheme `Bl X = (X.singularLocus K).blowup` together with a finite
surjective modification `ν : Bl X ⟶ X` that restricts to an isomorphism over the smooth locus of
`X / K` (`AlgebraicGeometry.Scheme.isRegular_blowup_singularLocus`).

This file develops the component geometry of `Bl X` and relates it to `X` without assuming `K` is
separably closed:

* **Density of the smooth preimage**: `ν ⁻¹' Smooth(X/K)` is dense in `Bl X`, being the complement
  of the exceptional effective Cartier divisor
  (`AlgebraicGeometry.Scheme.dense_preimage_smoothLocus_blowupToBase`), and `ν` is injective on it
  (`AlgebraicGeometry.Scheme.injOn_preimage_smoothLocus_blowupToBase`).
* **Bijection on irreducible components**: pushing forward along `ν` identifies
  `irreducibleComponents (Bl X)` with `irreducibleComponents X`
  (`AlgebraicGeometry.Scheme.irreducibleComponentsBlowupEquiv`). When `X` is proper over `K`, there
  are finitely many components
  (`AlgebraicGeometry.Scheme.finite_irreducibleComponents_blowup_singularLocus`).
* **Normalized component curves**: each `v : irreducibleComponents (Bl X)` is clopen in the regular
  scheme `Bl X`; equipped with its open-subscheme structure
  (`AlgebraicGeometry.Scheme.normalizedComponent`), it is an integral regular `K`-scheme of Krull
  dimension one (`AlgebraicGeometry.Scheme.topologicalKrullDim_normalizedComponent`) embedding into
  `Bl X` via the clopen immersion `AlgebraicGeometry.Scheme.normalizedComponentι`. When `X` is
  proper over `K`, each normalized component is an `IsCurveOver K` whose `H¹(C_v, 𝒪)` is
  finite-dimensional over `K`, so its cohomological genus `(X.normalizedComponent hnodal v).genus K`
  is defined.
* **Lifting smooth markings and base change**: any morphism `s : T ⟶ X` landing in the smooth locus
  of `X / K` lifts canonically to `Bl X` (`AlgebraicGeometry.Scheme.markingLift`), and base change
  along a field extension `L / K` induces a pullback square on the normalization
  (`AlgebraicGeometry.Scheme.blowupSingularLocusMap`) as well as on individual normalized components
  when `K` is separably closed (`AlgebraicGeometry.Scheme.exists_isPullback_normalizedComponent`).

## References

* [The Stacks Project, Tag 0C46](https://stacks.math.columbia.edu/tag/0C46): nodal curves and
  separation of branches.
* [The Stacks Project, Tag 02OG](https://stacks.math.columbia.edu/tag/02OG): universal property of
  blowing up.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TauCeti TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable {K : Type u} [Field K] (X : Scheme.{u}) [X.Over (Spec (.of K))]

/-- Over any field, the preimage of the smooth locus of a nodal curve is dense in the blowup of its
singular subscheme: it is the complement of the exceptional Cartier divisor. -/
theorem dense_preimage_smoothLocus_blowupToBase
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K))) :
    letI := hnodal.syntomic
    Dense ((X.singularLocus K).blowupToBase ⁻¹' ((X ↘ Spec (.of K)).smoothLocus : Set X)) := by
  have := hnodal.syntomic
  have := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of K))
  have := X.isFinite_blowupToBase_singularLocus hnodal
  let I := X.singularLocus K
  let ν := I.blowupToBase
  have : IsLocallyNoetherian I.blowup := LocallyOfFiniteType.isLocallyNoetherian ν
  have : IsSchemeTheoreticallyDominant (Scheme.Opens.ι (I.comap ν).support.compl) :=
    I.isEffectiveCartier_comap_blowupToBase.isSchemeTheoreticallyDominant_support_compl_ι
  have hdr : Dense (Set.range (Scheme.Opens.ι (I.comap ν).support.compl)) :=
    (Scheme.Opens.ι (I.comap ν).support.compl).denseRange
  rw [Scheme.Opens.range_ι] at hdr
  have hset : ((I.comap ν).support.compl : Set I.blowup) =
      ν ⁻¹' ((X ↘ Spec (.of K)).smoothLocus : Set X) := by
    ext y
    rw [TopologicalSpace.Closeds.coe_compl, Set.mem_compl_iff, SetLike.mem_coe,
      IdealSheafData.support_comap, ← SetLike.mem_coe, TopologicalSpace.Closeds.coe_preimage,
      Set.mem_preimage, Set.mem_preimage, SetLike.mem_coe,
      X.mem_support_singularLocus_iff_notMem_smoothLocus, not_not, SetLike.mem_coe]
  rwa [hset] at hdr

/-- The blowup of the singular subscheme of a nodal curve is injective on the preimage of the
smooth locus, over which it restricts to an isomorphism. -/
theorem injOn_preimage_smoothLocus_blowupToBase
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K))) :
    letI := hnodal.syntomic
    Set.InjOn (X.singularLocus K).blowupToBase
      ((X.singularLocus K).blowupToBase ⁻¹' ((X ↘ Spec (.of K)).smoothLocus : Set X)) := by
  have := hnodal.syntomic
  let ν := (X.singularLocus K).blowupToBase
  let U := (X ↘ Spec (.of K)).smoothLocus
  have : IsIso (ν ∣_ U) := X.isIso_blowupToBase_singularLocus_restrict_smoothLocus
  have hinj : Function.Injective ((ν ⁻¹ᵁ U).ι ≫ ν) := by
    rw [← morphismRestrict_ι]
    exact ((ν ∣_ U) ≫ U.ι).isOpenEmbedding.injective
  intro y₁ hy₁ y₂ hy₂ heq
  let q₁ : (ν ⁻¹ᵁ U).toScheme := ⟨y₁, hy₁⟩
  let q₂ : (ν ⁻¹ᵁ U).toScheme := ⟨y₂, hy₂⟩
  have hsub : ((ν ⁻¹ᵁ U).ι ≫ ν) q₁ = ((ν ⁻¹ᵁ U).ι ≫ ν) q₂ := heq
  exact congrArg Subtype.val (hinj hsub)

/-- **Irreducible components of the normalization match those of the nodal curve.** Pushing forward
along the finite surjective blowup `ν : Bl X ⟶ X` defines a bijection between the irreducible
components of `Bl X` and the irreducible components of `X`, over any ground field. -/
def irreducibleComponentsBlowupEquiv
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K))) :
    letI := hnodal.syntomic
    irreducibleComponents (X.singularLocus K).blowup ≃ irreducibleComponents X := by
  letI := hnodal.syntomic
  let Bl := (X.singularLocus K).blowup
  let ν := (X.singularLocus K).blowupToBase
  let U := (X ↘ Spec (.of K)).smoothLocus
  have : IsRegular Bl := X.isRegular_blowup_singularLocus hnodal
  have : IsFinite ν := X.isFinite_blowupToBase_singularLocus hnodal
  have : Surjective ν := X.surjective_blowupToBase_singularLocus hnodal
  have hclosed : IsClosedMap ν := ν.isClosedMap
  -- 1. Distinct components of `Bl` have distinct images because every component meets the dense
  --    open `ν ⁻¹' U`, where `ν` is injective.
  have hinj_sub {v w : irreducibleComponents Bl} (hsub : ν '' (v : Set Bl) ⊆ ν '' (w : Set Bl)) :
      v = w := by
    obtain ⟨y, hy_v, hy_U⟩ := (X.dense_preimage_smoothLocus_blowupToBase hnodal).inter_open_nonempty
      (v : Set Bl) (IsRegular.isOpen_of_mem_irreducibleComponents v.2) v.2.1.nonempty
    obtain ⟨z, hz_w, hzy⟩ := hsub ⟨y, hy_v, rfl⟩
    have hz_U : z ∈ ν ⁻¹' (U : Set X) := by
      rw [Set.mem_preimage, hzy]
      exact hy_U
    have hzeq : z = y := X.injOn_preimage_smoothLocus_blowupToBase hnodal hz_U hy_U hzy
    exact (IsRegular.componentOf_eq_iff.mpr hy_v).symm.trans
      (IsRegular.componentOf_eq_iff.mpr (hzeq ▸ hz_w))
  -- 2. Every irreducible component `Z` of `X` is the image of some component of `Bl`: restrict to
  --    an affine chart `W` meeting `Z`, whose preimage in `Bl` is Noetherian and therefore has
  --    finitely many irreducible components covering `Z ∩ W`.
  have hsurj (Z : Set X) (hZ : Z ∈ irreducibleComponents X) :
      ∃ w : irreducibleComponents Bl, Z = ν '' (w : Set Bl) := by
    obtain ⟨x, hxZ⟩ := hZ.1.nonempty
    obtain ⟨W, hW, hxW, -⟩ := exists_isAffineOpen_mem_and_subset
      (TopologicalSpace.Opens.mem_top x)
    have : IsAffine W.toScheme := hW
    have : IsProper (ν ∣_ W) :=
      MorphismProperty.of_isPullback (isPullback_morphismRestrict ν W).flip inferInstance
    have : Surjective (ν ∣_ W) :=
      MorphismProperty.of_isPullback (isPullback_morphismRestrict ν W).flip inferInstance
    have : CompactSpace (ν ⁻¹ᵁ W).toScheme := QuasiCompact.compactSpace_of_compactSpace (ν ∣_ W)
    have : IsNoetherian (ν ⁻¹ᵁ W).toScheme := {}
    have hfin : (irreducibleComponents (ν ⁻¹ᵁ W).toScheme).Finite :=
      TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
    have hZ' : IsIrreducible (W.ι ⁻¹' Z) :=
      hZ.1.preimage W.ι.isOpenEmbedding ⟨x, hxZ, ⟨⟨x, hxW⟩, rfl⟩⟩
    have hcov : W.ι ⁻¹' Z ⊆ ⋃ C ∈ hfin.toFinset, (ν ∣_ W) '' C := by
      intro u hu
      obtain ⟨q, rfl⟩ := (ν ∣_ W).surjective u
      exact Set.mem_biUnion
        (hfin.mem_toFinset.mpr (irreducibleComponent_mem_irreducibleComponents q))
        ⟨q, mem_irreducibleComponent, rfl⟩
    obtain ⟨C, hC_mem, hZC⟩ := isIrreducible_iff_sUnion_isClosed.mp hZ'
      (hfin.toFinset.image fun C ↦ (ν ∣_ W) '' C)
      (fun T hT ↦ by
        obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hT
        exact (ν ∣_ W).isClosedMap C
          (isClosed_of_mem_irreducibleComponents C (hfin.mem_toFinset.mp hC)))
      (by simpa only [Finset.coe_image, Set.sUnion_image, Finset.mem_coe] using hcov)
    obtain ⟨C, hC_fin, rfl⟩ := Finset.mem_image.mp hC_mem
    have hC : C ∈ irreducibleComponents (ν ⁻¹ᵁ W).toScheme := hfin.mem_toFinset.mp hC_fin
    obtain ⟨q₀, hq₀⟩ := hC.1.nonempty
    let w : irreducibleComponents Bl := IsRegular.componentOf Bl ((ν ⁻¹ᵁ W).ι q₀)
    have hCw : (ν ⁻¹ᵁ W).ι '' C ⊆ (w : Set Bl) := by
      rw [IsRegular.coe_componentOf]
      exact (hC.1.image _ (ν ⁻¹ᵁ W).ι.continuous.continuousOn).isConnected.isPreconnected
        |>.subset_connectedComponent ⟨q₀, hq₀, rfl⟩
    -- Extend `Z ∩ W ⊆ ν '' w` to `Z ⊆ ν '' w` by irreducibility of `Z`.
    have hZW : Z ∩ (W : Set X) ⊆ ν '' (w : Set Bl) := by
      rintro z ⟨hzZ, hzW⟩
      let zW : W.toScheme := ⟨z, hzW⟩
      have hzWZ : zW ∈ W.ι ⁻¹' Z := hzZ
      obtain ⟨q, hqC, hqz⟩ := hZC hzWZ
      refine ⟨(ν ⁻¹ᵁ W).ι q, hCw ⟨q, hqC, rfl⟩, ?_⟩
      have hcomm := congrArg (fun f : (ν ⁻¹ᵁ W).toScheme ⟶ X ↦ f q) (morphismRestrict_ι ν W)
      simpa only [zW, Scheme.Hom.comp_apply, hqz, Scheme.Opens.ι_apply] using hcomm.symm
    have hZsub : Z ⊆ ν '' (w : Set Bl) := by
      have hcl_w : IsClosed (ν '' (w : Set Bl)) :=
        hclosed w.1 (isClosed_of_mem_irreducibleComponents w.1 w.2)
      rcases isIrreducible_iff_sUnion_isClosed.mp hZ.1 {ν '' (w : Set Bl), (W : Set X)ᶜ}
        (by simp [hcl_w, W.isOpen.isClosed_compl])
        (fun z hz ↦ by
          by_cases hzW : z ∈ (W : Set X)
          · exact Set.mem_sUnion.mpr ⟨ν '' (w : Set Bl), by simp, hZW ⟨hz, hzW⟩⟩
          · exact Set.mem_sUnion.mpr ⟨(W : Set X)ᶜ, by simp, hzW⟩) with
        ⟨T, hT, hZT⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hT
      rcases hT with rfl | rfl
      · exact hZT
      · exact absurd hxW (hZT hxZ)
    exact ⟨w, hZsub.antisymm (hZ.2 (w.2.1.image ν ν.continuous.continuousOn) hZsub)⟩
  -- 3. Combine injectivity on inclusions and surjectivity to conclude every `ν '' v` is maximal
  --    irreducible in `X`.
  have himg_mem (v : irreducibleComponents Bl) : ν '' (v : Set Bl) ∈ irreducibleComponents X := by
    obtain ⟨Z, hZ, hvZ⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _
      (v.2.1.image ν ν.continuous.continuousOn)
    obtain ⟨w, rfl⟩ := hsurj Z hZ
    rwa [hinj_sub hvZ]
  exact Equiv.ofBijective (fun v ↦ ⟨ν '' (v : Set Bl), himg_mem v⟩)
    ⟨fun v w h ↦ hinj_sub (congrArg Subtype.val h).le,
      fun ⟨Z, hZ⟩ ↦ (hsurj Z hZ).imp fun w hw ↦ Subtype.ext hw.symm⟩

@[simp]
theorem coe_irreducibleComponentsBlowupEquiv
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    (v : letI := hnodal.syntomic; irreducibleComponents (X.singularLocus K).blowup) :
    letI := hnodal.syntomic
    (X.irreducibleComponentsBlowupEquiv hnodal v : Set X) =
      (X.singularLocus K).blowupToBase '' (v : Set (X.singularLocus K).blowup) :=
  (rfl)

/-- On a proper nodal curve over any field, the blowup of the singular subscheme has finitely many
irreducible components. -/
theorem finite_irreducibleComponents_blowup_singularLocus [IsProper (X ↘ Spec (.of K))]
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K))) :
    letI := hnodal.syntomic
    Finite (irreducibleComponents (X.singularLocus K).blowup) := by
  have := hnodal.syntomic
  have := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of K))
  have := X.isFinite_blowupToBase_singularLocus hnodal
  have : IsLocallyNoetherian (X.singularLocus K).blowup :=
    LocallyOfFiniteType.isLocallyNoetherian (X.singularLocus K).blowupToBase
  have : CompactSpace (X.singularLocus K).blowup :=
    QuasiCompact.compactSpace_of_compactSpace
      ((X.singularLocus K).blowupToBase ≫ (X ↘ Spec (.of K)))
  have : IsNoetherian (X.singularLocus K).blowup := {}
  exact TopologicalSpace.NoetherianSpace.finite_irreducibleComponents

/-- On a nonempty nodal curve over any field, the blowup of the singular subscheme has at least one
irreducible component. -/
theorem nonempty_irreducibleComponents_blowup_singularLocus [Nonempty X]
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K))) :
    letI := hnodal.syntomic
    Nonempty (irreducibleComponents (X.singularLocus K).blowup) := by
  have := hnodal.syntomic
  have := X.isRegular_blowup_singularLocus hnodal
  have := X.surjective_blowupToBase_singularLocus hnodal
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  obtain ⟨y, -⟩ := (X.singularLocus K).blowupToBase.surjective x
  exact ⟨IsRegular.componentOf (X.singularLocus K).blowup y⟩

/-! ### Normalized component schemes -/

/-- **Normalized component of a nodal curve.** Each irreducible component `v` of the blowup `Bl X`
of `Sing(X/K)` is clopen in the regular scheme `Bl X`; equipped with its open-subscheme structure,
it is a connected integral regular `K`-scheme of dimension one. -/
def normalizedComponent
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    (v : letI := hnodal.syntomic; irreducibleComponents (X.singularLocus K).blowup) :
    Scheme.{u} :=
  letI := hnodal.syntomic
  letI := X.isRegular_blowup_singularLocus hnodal
  (IsRegular.componentOpen (X.singularLocus K).blowup v).toScheme

/-- Canonical clopen immersion of a normalized component into the blowup of `Sing(X/K)`. -/
def normalizedComponentι
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    (v : letI := hnodal.syntomic; irreducibleComponents (X.singularLocus K).blowup) :
    letI := hnodal.syntomic
    X.normalizedComponent hnodal v ⟶ (X.singularLocus K).blowup :=
  letI := hnodal.syntomic
  letI := X.isRegular_blowup_singularLocus hnodal
  (IsRegular.componentOpen (X.singularLocus K).blowup v).ι

instance isOpenImmersion_normalizedComponentι
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    (v : letI := hnodal.syntomic; irreducibleComponents (X.singularLocus K).blowup) :
    letI := hnodal.syntomic
    IsOpenImmersion (X.normalizedComponentι hnodal v) :=
  letI := hnodal.syntomic
  letI := X.isRegular_blowup_singularLocus hnodal
  inferInstanceAs (IsOpenImmersion (IsRegular.componentOpen (X.singularLocus K).blowup v).ι)

instance isClosedImmersion_normalizedComponentι
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    (v : letI := hnodal.syntomic; irreducibleComponents (X.singularLocus K).blowup) :
    letI := hnodal.syntomic
    IsClosedImmersion (X.normalizedComponentι hnodal v) :=
  letI := hnodal.syntomic
  letI := X.isRegular_blowup_singularLocus hnodal
  inferInstanceAs (IsClosedImmersion (IsRegular.componentOpen (X.singularLocus K).blowup v).ι)

@[simp]
theorem range_normalizedComponentι
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    (v : letI := hnodal.syntomic; irreducibleComponents (X.singularLocus K).blowup) :
    letI := hnodal.syntomic
    Set.range (X.normalizedComponentι hnodal v) = (v : Set (X.singularLocus K).blowup) := by
  have := hnodal.syntomic
  have := X.isRegular_blowup_singularLocus hnodal
  exact (Scheme.Opens.range_ι (IsRegular.componentOpen (X.singularLocus K).blowup v)).trans
    (IsRegular.coe_componentOpen v)

/-- When `Bl X` is irreducible (`v = Set.univ`), `normalizedComponentι` is an isomorphism. -/
theorem isIso_normalizedComponentι_of_eq_univ
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    (v : letI := hnodal.syntomic; irreducibleComponents (X.singularLocus K).blowup)
    (hv : letI := hnodal.syntomic; (v : Set (X.singularLocus K).blowup) = Set.univ) :
    letI := hnodal.syntomic
    IsIso (X.normalizedComponentι hnodal v) := by
  have := hnodal.syntomic
  have := X.isRegular_blowup_singularLocus hnodal
  have hv_top : IsRegular.componentOpen (X.singularLocus K).blowup v = ⊤ :=
    TopologicalSpace.Opens.ext
      (by rw [IsRegular.coe_componentOpen, TopologicalSpace.Opens.coe_top, hv])
  have aux : ∀ U : (X.singularLocus K).blowup.Opens, U = ⊤ → IsIso U.ι := by
    rintro _ rfl
    exact (X.singularLocus K).blowup.topIso.isIso_hom
  exact aux _ hv_top

instance instOverNormalizedComponent
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    (v : letI := hnodal.syntomic; irreducibleComponents (X.singularLocus K).blowup) :
    (X.normalizedComponent hnodal v).Over (Spec (.of K)) :=
  letI := hnodal.syntomic
  ⟨X.normalizedComponentι hnodal v ≫ (X.singularLocus K).blowupToBase ≫ (X ↘ Spec (.of K))⟩

@[simp, reassoc]
theorem normalizedComponentι_blowupToBase_over
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    (v : letI := hnodal.syntomic; irreducibleComponents (X.singularLocus K).blowup) :
    letI := hnodal.syntomic
    X.normalizedComponentι hnodal v ≫ (X.singularLocus K).blowupToBase ≫ (X ↘ Spec (.of K)) =
      X.normalizedComponent hnodal v ↘ Spec (.of K) :=
  (rfl)

instance isRegular_normalizedComponent
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    (v : letI := hnodal.syntomic; irreducibleComponents (X.singularLocus K).blowup) :
    IsRegular (X.normalizedComponent hnodal v) :=
  letI := hnodal.syntomic
  letI := X.isRegular_blowup_singularLocus hnodal
  inferInstanceAs (IsRegular (IsRegular.componentOpen (X.singularLocus K).blowup v).toScheme)

instance isIntegral_normalizedComponent
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    (v : letI := hnodal.syntomic; irreducibleComponents (X.singularLocus K).blowup) :
    IsIntegral (X.normalizedComponent hnodal v) :=
  letI := hnodal.syntomic
  letI := X.isRegular_blowup_singularLocus hnodal
  inferInstanceAs (IsIntegral (IsRegular.componentOpen (X.singularLocus K).blowup v).toScheme)

instance locallyOfFiniteType_normalizedComponent
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    (v : letI := hnodal.syntomic; irreducibleComponents (X.singularLocus K).blowup) :
    LocallyOfFiniteType (X.normalizedComponent hnodal v ↘ Spec (.of K)) :=
  letI := hnodal.syntomic
  letI := X.isFinite_blowupToBase_singularLocus hnodal
  inferInstanceAs (LocallyOfFiniteType
    (X.normalizedComponentι hnodal v ≫ (X.singularLocus K).blowupToBase ≫ (X ↘ Spec (.of K))))

instance isProper_normalizedComponent [IsProper (X ↘ Spec (.of K))]
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    (v : letI := hnodal.syntomic; irreducibleComponents (X.singularLocus K).blowup) :
    IsProper (X.normalizedComponent hnodal v ↘ Spec (.of K)) :=
  letI := hnodal.syntomic
  letI := X.isFinite_blowupToBase_singularLocus hnodal
  inferInstanceAs (IsProper
    (X.normalizedComponentι hnodal v ≫ (X.singularLocus K).blowupToBase ≫ (X ↘ Spec (.of K))))

/-- Every normalized component of a nodal curve over a field has Krull dimension one. -/
theorem topologicalKrullDim_normalizedComponent
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    (v : letI := hnodal.syntomic; irreducibleComponents (X.singularLocus K).blowup) :
    topologicalKrullDim (X.normalizedComponent hnodal v) = 1 := by
  have := hnodal.syntomic
  let Bl := (X.singularLocus K).blowup
  let ν := (X.singularLocus K).blowupToBase
  let U := (X ↘ Spec (.of K)).smoothLocus
  have : IsRegular Bl := X.isRegular_blowup_singularLocus hnodal
  have : IsFinite ν := X.isFinite_blowupToBase_singularLocus hnodal
  have : IsIso (ν ∣_ U) := X.isIso_blowupToBase_singularLocus_restrict_smoothLocus
  let Cv := IsRegular.componentOpen Bl v
  let Wv : Bl.Opens := Cv ⊓ (ν ⁻¹ᵁ U)
  obtain ⟨y, hy_v, hy_U⟩ := (X.dense_preimage_smoothLocus_blowupToBase hnodal).inter_open_nonempty
    (v : Set Bl) (IsRegular.isOpen_of_mem_irreducibleComponents v.2) v.2.1.nonempty
  have : Nonempty Wv.toScheme := ⟨⟨y, IsRegular.mem_componentOpen.mpr hy_v, hy_U⟩⟩
  let iCv : Wv.toScheme ⟶ Cv.toScheme := Bl.homOfLE inf_le_left
  let iU : Wv.toScheme ⟶ (ν ⁻¹ᵁ U).toScheme := Bl.homOfLE inf_le_right
  have hj_eq : Wv.ι ≫ ν = iU ≫ (ν ∣_ U) ≫ U.ι := by
    rw [morphismRestrict_ι, ← Category.assoc, Bl.homOfLE_ι]
  have : IsOpenImmersion (Wv.ι ≫ ν) := by
    rw [hj_eq]
    infer_instance
  have hdim_Wv : topologicalKrullDim Wv.toScheme = topologicalKrullDim Cv.toScheme :=
    topologicalKrullDim_eq_of_isOpenEmbedding_of_locallyOfFiniteType
      (Cv.ι ≫ ν ≫ (X ↘ Spec (.of K))) iCv.isOpenEmbedding
  let Z : Set X := ν '' (v : Set Bl)
  have hZ : Z ∈ irreducibleComponents X := (X.irreducibleComponentsBlowupEquiv hnodal v).2
  have hrange : Set.range (Wv.ι ≫ ν) = Z ∩ (U : Set X) := by
    ext x
    constructor
    · rintro ⟨⟨z, hz_v, hz_U⟩, rfl⟩
      exact ⟨⟨z, IsRegular.mem_componentOpen.mp hz_v, rfl⟩, hz_U⟩
    · rintro ⟨⟨z, hz_v, rfl⟩, hz_U⟩
      exact ⟨⟨z, IsRegular.mem_componentOpen.mpr hz_v, hz_U⟩, rfl⟩
  have hpure : IsPureDimensional 1 X :=
    ((pureRelativeDimension_iff_of_field (X ↘ Spec (.of K))).mp inferInstance).2
  dsimp only [normalizedComponent]
  calc
    topologicalKrullDim Cv.toScheme
      = topologicalKrullDim Wv.toScheme := hdim_Wv.symm
    _ = topologicalKrullDim ↥(Set.range (Wv.ι ≫ ν)) :=
      (Wv.ι ≫ ν).isOpenEmbedding.toHomeomorph.isHomeomorph.topologicalKrullDim_eq
    _ = topologicalKrullDim ↥(Z ∩ (U : Set X)) := by rw [hrange]
    _ = topologicalKrullDim Z :=
      topologicalKrullDim_inter_eq_of_locallyOfFiniteType (X ↘ Spec (.of K)) hZ.1
        (isClosed_of_mem_irreducibleComponents Z hZ) U.isOpen ⟨ν y, ⟨y, hy_v, rfl⟩, hy_U⟩
    _ = 1 := isPureDimensional_iff.mp hpure Z hZ

/-- Each normalized component of a proper nodal curve over a field is a proper integral curve of
dimension one over that field. -/
instance isCurveOver_normalizedComponent [IsProper (X ↘ Spec (.of K))]
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    (v : letI := hnodal.syntomic; irreducibleComponents (X.singularLocus K).blowup) :
    (X.normalizedComponent hnodal v).IsCurveOver K :=
  isCurveOver_iff.mpr
    ⟨inferInstance, inferInstance, X.topologicalKrullDim_normalizedComponent hnodal v⟩

/-- On a proper nodal curve over any field `K`, the first cohomology of the structure sheaf of each
normalized component is finite-dimensional over `K`, so its genus is well-defined. -/
instance finiteDimensional_cohomology_one_normalizedComponent [IsProper (X ↘ Spec (.of K))]
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    (v : letI := hnodal.syntomic; irreducibleComponents (X.singularLocus K).blowup) :
    FiniteDimensional K
      (Scheme.Modules.Cohomology (InvertibleSheaf.trivial (X.normalizedComponent hnodal v)).obj
        1) :=
  finiteDimensional_cohomology_one_trivial_of_isProper K
    (X.topologicalKrullDim_normalizedComponent hnodal v)

/-- A connected smooth nodal curve over a field is smooth of relative dimension one. -/
theorem smoothOfRelativeDimension_one_of_smooth [ConnectedSpace X] [Smooth (X ↘ Spec (.of K))]
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K))) :
    SmoothOfRelativeDimension 1 (X ↘ Spec (.of K)) := by
  have := hnodal.syntomic
  have : IsRegular X := IsRegular.of_smooth (X ↘ Spec (.of K))
  have : IsIntegral X := isIntegral_of_connected_of_isRegularLocalRing_stalk X
  have hpure : IsPureDimensional 1 X :=
    ((pureRelativeDimension_iff_of_field (X ↘ Spec (.of K))).mp inferInstance).2
  have hdim : topologicalKrullDim X = 1 := by
    rw [(Homeomorph.Set.univ X).symm.isHomeomorph.topologicalKrullDim_eq]
    exact isPureDimensional_iff.mp hpure Set.univ (by simp [irreducibleComponents_eq_singleton])
  exact smoothOfRelativeDimension_of_topologicalKrullDim_eq (X ↘ Spec (.of K)) hdim

/-! ### Smooth markings and their lifts to the normalization -/

/-- A morphism into `X` whose image lies in the smooth locus lifts canonically to the blowup of the
singular subscheme, because the singular subscheme pulls back to the unit ideal sheaf. -/
def markingLift (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    {T : Scheme.{u}} (s : T ⟶ X)
    (hs : letI := hnodal.syntomic; Set.range s ⊆ (X ↘ Spec (.of K)).smoothLocus) :
    letI := hnodal.syntomic
    T ⟶ (X.singularLocus K).blowup := by
  letI := hnodal.syntomic
  refine (X.singularLocus K).blowupLift s ?_
  have htop : (X.singularLocus K).comap s = ⊤ := by
    refine ((X.singularLocus K).comap_eq_top_iff s).mpr (TopologicalSpace.Opens.ext ?_)
    rw [TopologicalSpace.Opens.coe_top, Set.eq_univ_iff_forall]
    intro t
    rw [Scheme.Hom.coe_preimage, Set.mem_preimage, TopologicalSpace.Closeds.coe_compl,
      Set.mem_compl_iff, SetLike.mem_coe, X.mem_support_singularLocus_iff_notMem_smoothLocus,
      not_not]
    exact hs ⟨t, rfl⟩
  rw [htop]
  exact IdealSheafData.isEffectiveCartier_top T

@[reassoc (attr := simp)]
theorem markingLift_blowupToBase (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    {T : Scheme.{u}} (s : T ⟶ X)
    (hs : letI := hnodal.syntomic; Set.range s ⊆ (X ↘ Spec (.of K)).smoothLocus) :
    letI := hnodal.syntomic
    X.markingLift hnodal s hs ≫ (X.singularLocus K).blowupToBase = s := by
  have := hnodal.syntomic
  exact (X.singularLocus K).blowupLift_blowupToBase _ _

/-! ### Base change of the normalization and normalized components -/

section BaseChange

private theorem eqToHom_blowupToBase {Y : Scheme.{u}} {J₁ J₂ : Y.IdealSheafData} (h : J₁ = J₂) :
    eqToHom (congrArg IdealSheafData.blowup h) ≫ J₂.blowupToBase = J₁.blowupToBase := by
  cases h
  simp

/-- Canonical base-change morphism `(X'.singularLocus L).blowup ⟶ (X.singularLocus K).blowup`
induced by a pullback square of nodal curves along a field extension `L / K`. -/
def blowupSingularLocusMap {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X X' : Scheme.{u}} [X.Over (Spec (.of K))] [X'.Over (Spec (.of L))]
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    (hnodal' : AtWorstNodalOfRelativeDimensionOne (X' ↘ Spec (.of L)))
    {g : X' ⟶ X}
    (H : IsPullback g (X' ↘ Spec (.of L)) (X ↘ Spec (.of K))
      (Spec.map (CommRingCat.ofHom (algebraMap K L)))) :
    letI := hnodal.syntomic
    letI := hnodal'.syntomic
    (X'.singularLocus L).blowup ⟶ (X.singularLocus K).blowup :=
  letI := hnodal.syntomic
  letI := hnodal'.syntomic
  eqToHom (congrArg IdealSheafData.blowup (Scheme.singularLocus_eq_comap_of_isPullback H)) ≫
    (X.singularLocus K).blowupMap g

@[reassoc (attr := simp)]
theorem blowupSingularLocusMap_blowupToBase {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X X' : Scheme.{u}} [X.Over (Spec (.of K))] [X'.Over (Spec (.of L))]
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    (hnodal' : AtWorstNodalOfRelativeDimensionOne (X' ↘ Spec (.of L)))
    {g : X' ⟶ X}
    (H : IsPullback g (X' ↘ Spec (.of L)) (X ↘ Spec (.of K))
      (Spec.map (CommRingCat.ofHom (algebraMap K L)))) :
    letI := hnodal.syntomic
    letI := hnodal'.syntomic
    blowupSingularLocusMap hnodal hnodal' H ≫ (X.singularLocus K).blowupToBase =
      (X'.singularLocus L).blowupToBase ≫ g := by
  have := hnodal.syntomic
  have := hnodal'.syntomic
  dsimp only [blowupSingularLocusMap]
  rw [Category.assoc, IdealSheafData.blowupMap_blowupToBase, ← Category.assoc,
    eqToHom_blowupToBase (Scheme.singularLocus_eq_comap_of_isPullback H)]

/-- Blowing up `Sing(X/K)` commutes with base change along any field extension `L / K`. -/
theorem isPullback_blowupSingularLocusMap {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X X' : Scheme.{u}} [X.Over (Spec (.of K))] [X'.Over (Spec (.of L))]
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    (hnodal' : AtWorstNodalOfRelativeDimensionOne (X' ↘ Spec (.of L)))
    {g : X' ⟶ X}
    (H : IsPullback g (X' ↘ Spec (.of L)) (X ↘ Spec (.of K))
      (Spec.map (CommRingCat.ofHom (algebraMap K L)))) :
    letI := hnodal.syntomic
    letI := hnodal'.syntomic
    IsPullback (X'.singularLocus L).blowupToBase (blowupSingularLocusMap hnodal hnodal' H)
      g (X.singularLocus K).blowupToBase := by
  have := hnodal.syntomic
  have := hnodal'.syntomic
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
    rw [Flat.SpecMap_iff, CommRingCat.hom_ofHom, RingHom.flat_algebraMap_iff]
    infer_instance
  have : Flat g := MorphismProperty.of_isPullback H.flip inferInstance
  have hI : X'.singularLocus L = (X.singularLocus K).comap g :=
    Scheme.singularLocus_eq_comap_of_isPullback H
  let eBl : (X'.singularLocus L).blowup ≅ ((X.singularLocus K).comap g).blowup :=
    eqToIso (congrArg IdealSheafData.blowup hI)
  have heBl : eBl.hom ≫ ((X.singularLocus K).comap g).blowupToBase =
      (X'.singularLocus L).blowupToBase :=
    eqToHom_blowupToBase hI
  exact ((X.singularLocus K).isPullback_blowupMap_of_flat g).of_iso
    eBl.symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp [eBl, ← heBl]) (by simp [blowupSingularLocusMap, eBl]) (by simp) (by simp)

/-- Composing with the curve structure morphisms exhibits `(X'.singularLocus L).blowup` as the base
change of `(X.singularLocus K).blowup` along `Spec L ⟶ Spec K`. -/
theorem isPullback_blowupSingularLocusMap_over {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X X' : Scheme.{u}} [X.Over (Spec (.of K))] [X'.Over (Spec (.of L))]
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    (hnodal' : AtWorstNodalOfRelativeDimensionOne (X' ↘ Spec (.of L)))
    {g : X' ⟶ X}
    (H : IsPullback g (X' ↘ Spec (.of L)) (X ↘ Spec (.of K))
      (Spec.map (CommRingCat.ofHom (algebraMap K L)))) :
    letI := hnodal.syntomic
    letI := hnodal'.syntomic
    IsPullback (blowupSingularLocusMap hnodal hnodal' H)
      ((X'.singularLocus L).blowupToBase ≫ (X' ↘ Spec (.of L)))
      ((X.singularLocus K).blowupToBase ≫ (X ↘ Spec (.of K)))
      (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
  have := hnodal.syntomic
  have := hnodal'.syntomic
  exact (isPullback_blowupSingularLocusMap hnodal hnodal' H).flip.paste_vert H

/-- **Over a separably closed ground field `K`, each normalized component of a base change `X'`
along any field extension `L / K` is the base change of the corresponding normalized component of
`X`.** -/
theorem exists_isPullback_normalizedComponent {K L : Type u} [Field K] [IsSepClosed K]
    [Field L] [Algebra K L]
    {X X' : Scheme.{u}} [X.Over (Spec (.of K))] [X'.Over (Spec (.of L))]
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    (hnodal' : AtWorstNodalOfRelativeDimensionOne (X' ↘ Spec (.of L)))
    {g : X' ⟶ X}
    (H : IsPullback g (X' ↘ Spec (.of L)) (X ↘ Spec (.of K))
      (Spec.map (CommRingCat.ofHom (algebraMap K L))))
    (v' : letI := hnodal'.syntomic; irreducibleComponents (X'.singularLocus L).blowup) :
    letI := hnodal.syntomic
    letI := hnodal'.syntomic
    ∃ g_v : X'.normalizedComponent hnodal' v' ⟶
        X.normalizedComponent hnodal
          (irreducibleComponentsEquivOfIsPullback
            (isPullback_blowupSingularLocusMap_over hnodal hnodal' H) v'),
      g_v ≫ X.normalizedComponentι hnodal _ =
        X'.normalizedComponentι hnodal' v' ≫ blowupSingularLocusMap hnodal hnodal' H ∧
      IsPullback g_v
        (X'.normalizedComponent hnodal' v' ↘ Spec (.of L))
        (X.normalizedComponent hnodal
          (irreducibleComponentsEquivOfIsPullback
            (isPullback_blowupSingularLocusMap_over hnodal hnodal' H) v') ↘ Spec (.of K))
        (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
  have := hnodal.syntomic
  have := hnodal'.syntomic
  have := X.isRegular_blowup_singularLocus hnodal
  have := X'.isRegular_blowup_singularLocus hnodal'
  exact IsRegular.exists_isPullback_componentOpen
    (isPullback_blowupSingularLocusMap_over hnodal hnodal' H) v'

end BaseChange

end AlgebraicGeometry.Scheme
