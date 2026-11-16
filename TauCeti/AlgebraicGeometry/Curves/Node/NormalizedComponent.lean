/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import TauCeti.AlgebraicGeometry.Curves.Basic
public import TauCeti.AlgebraicGeometry.Curves.Node.Normalization
public import TauCeti.AlgebraicGeometry.Scheme.Components
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.RiemannRoch.Finiteness
import TauCeti.AlgebraicGeometry.Blowup.ExceptionalDivisor
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.SchematicDensity
import TauCeti.AlgebraicGeometry.IdealSheaf.Comap
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

* **Smooth-locus density, injectivity, and lifts over arbitrary bases**: for any syntomic relative
  curve `X` over a commutative ring `R`, `ν ⁻¹' Smooth(X/R)` is dense in `Bl X`, being the
  complement of the exceptional effective Cartier divisor
  (`AlgebraicGeometry.Scheme.dense_preimage_smoothLocus_blowupToBase`), `ν` is injective on it
  (`AlgebraicGeometry.Scheme.injOn_preimage_smoothLocus_blowupToBase`), `ν` is an isomorphism when
  `X / R` is smooth (`AlgebraicGeometry.Scheme.isIso_blowupToBase_singularLocus_of_smooth`), and
  every morphism `s : T ⟶ X` landing in `Smooth(X/R)` lifts uniquely to `Bl X`
  (`AlgebraicGeometry.Scheme.blowupSingularLocusLift`, built from
  `AlgebraicGeometry.Scheme.IdealSheafData.blowupLift`).
* **Bijection on irreducible components**: for a nodal curve `X` over a field `K`, pushing forward
  along `ν` identifies `irreducibleComponents (Bl X)` with `irreducibleComponents X`
  (`AlgebraicGeometry.Scheme.irreducibleComponentsBlowupEquiv`). When `X` is quasi-compact over
  `K`, there are finitely many components
  (`AlgebraicGeometry.Scheme.finite_irreducibleComponents_blowup_singularLocus`).
* **Normalized component curves**: each `v : irreducibleComponents (Bl X)` is clopen in the regular
  scheme `Bl X`; equipped with its open-subscheme structure
  (`AlgebraicGeometry.Scheme.normalizedComponent`), it is an integral regular `K`-scheme of Krull
  dimension one (`AlgebraicGeometry.Scheme.topologicalKrullDim_normalizedComponent`) embedding into
  `Bl X` via the clopen immersion `AlgebraicGeometry.Scheme.normalizedComponentι`. When `X` is
  proper over `K`, each normalized component is an `IsCurveOver K` whose `H¹(C_v, 𝒪)` is
  finite-dimensional over `K`, so its cohomological genus `(X.normalizedComponent hnodal v).genus K`
  is defined.
* **Base change of normalized components**: combining the base-change morphism
  `TauCeti.AlgebraicGeometry.blowupSingularLocusMap` (built from
  `AlgebraicGeometry.Scheme.IdealSheafData.blowupMap`) with
  `TauCeti.AlgebraicGeometry.exists_isPullback_componentOpen`, base change along a field extension
  `L / K` with geometrically irreducible `Spec L ⟶ Spec K` (in particular whenever `K` is separably
  closed) induces a pullback square on each normalized component
  (`TauCeti.AlgebraicGeometry.exists_isPullback_normalizedComponent`).

## References

* [The Stacks Project, Tag 0C46](https://stacks.math.columbia.edu/tag/0C46): nodal curves and
  separation of branches.
* [The Stacks Project, Tag 0806](https://stacks.math.columbia.edu/tag/0806) and
  [Tag 0805](https://stacks.math.columbia.edu/tag/0805) (in Section
  [Tag 01OF](https://stacks.math.columbia.edu/tag/01OF)): universal property and flat base change
  of blowing up.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TauCeti TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

section Syntomic

variable {R : Type u} [CommRing R] (X : Scheme.{u}) [X.Over (Spec (.of R))]
  [SyntomicOfRelativeDimension 1 (X ↘ Spec (.of R))]

/-- For any syntomic relative curve over a commutative ring `R`, the preimage of the smooth locus is
dense in the blowup of its singular subscheme: it is the complement of the exceptional effective
Cartier divisor. -/
theorem dense_preimage_smoothLocus_blowupToBase :
    Dense ((X.singularLocus R).blowupToBase ⁻¹' ((X ↘ Spec (.of R)).smoothLocus : Set X)) := by
  let I := X.singularLocus R
  have hset : ((I.comap I.blowupToBase).support.compl : Set I.blowup) =
      I.blowupToBase ⁻¹' ((X ↘ Spec (.of R)).smoothLocus : Set X) := by
    ext y
    simp [I]
  exact hset ▸ I.isEffectiveCartier_comap_blowupToBase.dense_support_compl

/-- For any syntomic relative curve over a commutative ring `R`, the blowup of the singular
subscheme is injective on the preimage of the smooth locus, over which it restricts to an
isomorphism. -/
theorem injOn_preimage_smoothLocus_blowupToBase :
    Set.InjOn (X.singularLocus R).blowupToBase
      ((X.singularLocus R).blowupToBase ⁻¹' ((X ↘ Spec (.of R)).smoothLocus : Set X)) := by
  let ν := (X.singularLocus R).blowupToBase
  let U := (X ↘ Spec (.of R)).smoothLocus
  have : IsIso (ν ∣_ U) := X.isIso_blowupToBase_singularLocus_restrict_smoothLocus
  have hinj : Function.Injective ((ν ⁻¹ᵁ U).ι ≫ ν) := by
    rw [← morphismRestrict_ι]
    exact ((ν ∣_ U) ≫ U.ι).isOpenEmbedding.injective
  intro y₁ hy₁ y₂ hy₂ heq
  let q₁ : (ν ⁻¹ᵁ U).toScheme := ⟨y₁, hy₁⟩
  let q₂ : (ν ⁻¹ᵁ U).toScheme := ⟨y₂, hy₂⟩
  have hsub : ((ν ⁻¹ᵁ U).ι ≫ ν) q₁ = ((ν ⁻¹ᵁ U).ι ≫ ν) q₂ := by
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.Opens.ι_apply, Scheme.Opens.ι_apply]
    exact heq
  exact congrArg Subtype.val (hinj hsub)

/-- On a smooth syntomic relative curve, the blowup of the singular subscheme is an isomorphism. -/
theorem isIso_blowupToBase_singularLocus_of_smooth [Smooth (X ↘ Spec (.of R))] :
    IsIso (X.singularLocus R).blowupToBase := by
  rw [IdealSheafData.isIso_blowupToBase_iff, (X.singularLocus_eq_top_iff_smooth (R := R)).mpr ‹_›]
  exact IdealSheafData.isEffectiveCartier_top X

/-! ### Lifting morphisms landing in the smooth locus -/

private theorem isEffectiveCartier_comap_singularLocus_of_range_subset_smoothLocus
    {T : Scheme.{u}} {s : T ⟶ X} (hs : Set.range s ⊆ (X ↘ Spec (.of R)).smoothLocus) :
    ((X.singularLocus R).comap s).IsEffectiveCartier := by
  have htop : (X.singularLocus R).comap s = ⊤ := by
    refine ((X.singularLocus R).comap_eq_top_iff s).mpr ?_
    ext t
    simpa using hs ⟨t, rfl⟩
  rw [htop]
  exact IdealSheafData.isEffectiveCartier_top T

/-- A morphism into a syntomic relative curve `X` whose image lies in the smooth locus lifts
canonically to the blowup of the singular subscheme, because the singular subscheme pulls back to
the unit ideal sheaf. -/
def blowupSingularLocusLift {T : Scheme.{u}} (s : T ⟶ X)
    (hs : Set.range s ⊆ (X ↘ Spec (.of R)).smoothLocus) :
    T ⟶ (X.singularLocus R).blowup :=
  (X.singularLocus R).blowupLift s
    (X.isEffectiveCartier_comap_singularLocus_of_range_subset_smoothLocus hs)

@[reassoc (attr := simp)]
theorem blowupSingularLocusLift_blowupToBase {T : Scheme.{u}} (s : T ⟶ X)
    (hs : Set.range s ⊆ (X ↘ Spec (.of R)).smoothLocus) :
    X.blowupSingularLocusLift s hs ≫ (X.singularLocus R).blowupToBase = s :=
  (X.singularLocus R).blowupLift_blowupToBase _ _

/-- Uniqueness of `blowupSingularLocusLift`: any morphism into `(X.singularLocus R).blowup` lifting
`s` equals `X.blowupSingularLocusLift s hs`. -/
theorem eq_blowupSingularLocusLift {X : Scheme.{u}} [X.Over (Spec (.of R))]
    [SyntomicOfRelativeDimension 1 (X ↘ Spec (.of R))] {T : Scheme.{u}} {s : T ⟶ X}
    (hs : Set.range s ⊆ (X ↘ Spec (.of R)).smoothLocus)
    {g : T ⟶ (X.singularLocus R).blowup}
    (hg : g ≫ (X.singularLocus R).blowupToBase = s) :
    g = X.blowupSingularLocusLift s hs :=
  (X.singularLocus R).eq_blowupLift
    (X.isEffectiveCartier_comap_singularLocus_of_range_subset_smoothLocus hs) hg

/-- Precomposing `blowupSingularLocusLift` with `h : T' ⟶ T` yields the lift of `h ≫ s`. -/
@[reassoc]
theorem comp_blowupSingularLocusLift {T' T : Scheme.{u}} (h : T' ⟶ T) (s : T ⟶ X)
    (hs : Set.range s ⊆ (X ↘ Spec (.of R)).smoothLocus)
    (hhs : Set.range (h ≫ s) ⊆ (X ↘ Spec (.of R)).smoothLocus :=
      (Set.range_comp_subset_range h s).trans hs) :
    h ≫ X.blowupSingularLocusLift s hs = X.blowupSingularLocusLift (h ≫ s) hhs :=
  eq_blowupSingularLocusLift hhs (by simp)

end Syntomic

/-! ### Irreducible components of the normalization of a nodal curve -/

section Nodal

variable {K : Type u} [Field K] (X : Scheme.{u}) [X.Over (Spec (.of K))]

/-- Distinct irreducible components of `(X.singularLocus K).blowup` cannot have nested images in `X`
because every component meets the dense open preimage of the smooth locus, where `blowupToBase` is
injective. -/
private theorem eq_of_image_blowupToBase_subset
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    {v w : letI := hnodal.syntomic; irreducibleComponents (X.singularLocus K).blowup}
    (hsub : letI := hnodal.syntomic
      (X.singularLocus K).blowupToBase '' (v : Set (X.singularLocus K).blowup) ⊆
        (X.singularLocus K).blowupToBase '' (w : Set (X.singularLocus K).blowup)) :
    v = w := by
  have := hnodal.syntomic
  let Bl := (X.singularLocus K).blowup
  let ν := (X.singularLocus K).blowupToBase
  have : IsRegular Bl := X.isRegular_blowup_singularLocus hnodal
  obtain ⟨y, hy_v, hy_U⟩ := (X.dense_preimage_smoothLocus_blowupToBase (R := K)).inter_open_nonempty
    (v : Set Bl) (isOpen_of_mem_irreducibleComponents_of_isDomain_stalk v.2) v.2.1.nonempty
  obtain ⟨z, hz_w, hzy⟩ := hsub ⟨y, hy_v, rfl⟩
  have hz_U : z ∈ ν ⁻¹' ((X ↘ Spec (.of K)).smoothLocus : Set X) := by
    rw [Set.mem_preimage, hzy]
    exact hy_U
  have hzeq : z = y := X.injOn_preimage_smoothLocus_blowupToBase hz_U hy_U hzy
  exact (componentOf_eq_iff.mpr hy_v).symm.trans (componentOf_eq_iff.mpr (hzeq ▸ hz_w))

/-- Every irreducible component of `X` is the image under `blowupToBase` of an irreducible component
of `(X.singularLocus K).blowup`. -/
private theorem exists_eq_image_blowupToBase_of_mem_irreducibleComponents
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    {Z : Set X} (hZ : Z ∈ irreducibleComponents X) :
    letI := hnodal.syntomic
    ∃ w : irreducibleComponents (X.singularLocus K).blowup,
      Z = (X.singularLocus K).blowupToBase '' (w : Set (X.singularLocus K).blowup) := by
  have := hnodal.syntomic
  let Bl := (X.singularLocus K).blowup
  let ν := (X.singularLocus K).blowupToBase
  have : IsRegular Bl := X.isRegular_blowup_singularLocus hnodal
  have : IsFinite ν := X.isFinite_blowupToBase_singularLocus hnodal
  have : Surjective ν := X.surjective_blowupToBase_singularLocus hnodal
  obtain ⟨x, hxZ⟩ := hZ.1.nonempty
  obtain ⟨W, hW, hxW, -⟩ := exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top x)
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
    exact Set.mem_biUnion (hfin.mem_toFinset.mpr (irreducibleComponent_mem_irreducibleComponents q))
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
  let w : irreducibleComponents Bl := componentOf Bl ((ν ⁻¹ᵁ W).ι q₀)
  have hCw : (ν ⁻¹ᵁ W).ι '' C ⊆ (w : Set Bl) := by
    rw [coe_componentOf]
    exact (hC.1.image _ (ν ⁻¹ᵁ W).ι.continuous.continuousOn).isConnected.isPreconnected
      |>.subset_connectedComponent ⟨q₀, hq₀, rfl⟩
  have hZW : Z ∩ (W : Set X) ⊆ ν '' (w : Set Bl) := by
    rintro z ⟨hzZ, hzW⟩
    let zW : W.toScheme := ⟨z, hzW⟩
    have hzWZ : zW ∈ W.ι ⁻¹' Z := by
      rwa [Set.mem_preimage, Scheme.Opens.ι_apply]
    obtain ⟨q, hqC, hqz⟩ := hZC hzWZ
    refine ⟨(ν ⁻¹ᵁ W).ι q, hCw ⟨q, hqC, rfl⟩, ?_⟩
    have hcomm := congrArg (fun f : (ν ⁻¹ᵁ W).toScheme ⟶ X ↦ f q) (morphismRestrict_ι ν W)
    simpa only [zW, Scheme.Hom.comp_apply, hqz, Scheme.Opens.ι_apply] using hcomm.symm
  have hZsub : Z ⊆ ν '' (w : Set Bl) :=
    (subset_closure_inter_of_isPreirreducible_of_isOpen hZ.1.2 W.isOpen ⟨x, hxZ, hxW⟩).trans
      (closure_minimal hZW (ν.isClosedMap w.1 (isClosed_of_mem_irreducibleComponents w.1 w.2)))
  exact ⟨w, hZsub.antisymm (hZ.2 (w.2.1.image ν ν.continuous.continuousOn) hZsub)⟩

private theorem image_blowupToBase_mem_irreducibleComponents
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    (v : letI := hnodal.syntomic; irreducibleComponents (X.singularLocus K).blowup) :
    letI := hnodal.syntomic
    (X.singularLocus K).blowupToBase '' (v : Set (X.singularLocus K).blowup) ∈
      irreducibleComponents X := by
  have := hnodal.syntomic
  let ν := (X.singularLocus K).blowupToBase
  obtain ⟨Z, hZ, hvZ⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _
    (v.2.1.image ν ν.continuous.continuousOn)
  obtain ⟨w, rfl⟩ := X.exists_eq_image_blowupToBase_of_mem_irreducibleComponents hnodal hZ
  rwa [X.eq_of_image_blowupToBase_subset hnodal hvZ]

/-- **Irreducible components of the normalization match those of the nodal curve.** Pushing forward
along the finite surjective blowup `ν : Bl X ⟶ X` defines a bijection between the irreducible
components of `Bl X` and the irreducible components of `X`, over any ground field. -/
def irreducibleComponentsBlowupEquiv
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K))) :
    letI := hnodal.syntomic
    irreducibleComponents (X.singularLocus K).blowup ≃ irreducibleComponents X :=
  letI := hnodal.syntomic
  Equiv.ofBijective
    (fun v ↦ ⟨(X.singularLocus K).blowupToBase '' (v : Set (X.singularLocus K).blowup),
      X.image_blowupToBase_mem_irreducibleComponents hnodal v⟩)
    ⟨fun _ _ h ↦ X.eq_of_image_blowupToBase_subset hnodal (congrArg Subtype.val h).le,
      fun ⟨_, hZ⟩ ↦ (X.exists_eq_image_blowupToBase_of_mem_irreducibleComponents hnodal hZ).imp
        fun _ hw ↦ Subtype.ext hw.symm⟩

@[simp]
theorem coe_irreducibleComponentsBlowupEquiv
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    (v : letI := hnodal.syntomic; irreducibleComponents (X.singularLocus K).blowup) :
    letI := hnodal.syntomic
    (X.irreducibleComponentsBlowupEquiv hnodal v : Set X) =
      (X.singularLocus K).blowupToBase '' (v : Set (X.singularLocus K).blowup) :=
  (rfl)

/-- On a quasi-compact nodal curve over any field, the blowup of the singular subscheme has finitely
many irreducible components. -/
theorem finite_irreducibleComponents_blowup_singularLocus [QuasiCompact (X ↘ Spec (.of K))]
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
  exact ⟨componentOf (X.singularLocus K).blowup y⟩

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
  (componentOpen (X.singularLocus K).blowup v).toScheme

/-- Canonical clopen immersion of a normalized component into the blowup of `Sing(X/K)`. -/
def normalizedComponentι
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    (v : letI := hnodal.syntomic; irreducibleComponents (X.singularLocus K).blowup) :
    letI := hnodal.syntomic
    X.normalizedComponent hnodal v ⟶ (X.singularLocus K).blowup :=
  letI := hnodal.syntomic
  letI := X.isRegular_blowup_singularLocus hnodal
  (componentOpen (X.singularLocus K).blowup v).ι

instance isOpenImmersion_normalizedComponentι
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    (v : letI := hnodal.syntomic; irreducibleComponents (X.singularLocus K).blowup) :
    letI := hnodal.syntomic
    IsOpenImmersion (X.normalizedComponentι hnodal v) :=
  letI := hnodal.syntomic
  letI := X.isRegular_blowup_singularLocus hnodal
  inferInstanceAs (IsOpenImmersion (componentOpen (X.singularLocus K).blowup v).ι)

instance isClosedImmersion_normalizedComponentι
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    (v : letI := hnodal.syntomic; irreducibleComponents (X.singularLocus K).blowup) :
    letI := hnodal.syntomic
    IsClosedImmersion (X.normalizedComponentι hnodal v) :=
  letI := hnodal.syntomic
  letI := X.isRegular_blowup_singularLocus hnodal
  inferInstanceAs (IsClosedImmersion (componentOpen (X.singularLocus K).blowup v).ι)

@[simp]
theorem range_normalizedComponentι
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    (v : letI := hnodal.syntomic; irreducibleComponents (X.singularLocus K).blowup) :
    letI := hnodal.syntomic
    Set.range (X.normalizedComponentι hnodal v) = (v : Set (X.singularLocus K).blowup) := by
  have := hnodal.syntomic
  have := X.isRegular_blowup_singularLocus hnodal
  exact (Scheme.Opens.range_ι (componentOpen (X.singularLocus K).blowup v)).trans
    (coe_componentOpen v)

/-- When `Bl X` is irreducible (`v = Set.univ`), `normalizedComponentι` is an isomorphism. -/
theorem isIso_normalizedComponentι_of_eq_univ
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    (v : letI := hnodal.syntomic; irreducibleComponents (X.singularLocus K).blowup)
    (hv : letI := hnodal.syntomic; (v : Set (X.singularLocus K).blowup) = Set.univ) :
    letI := hnodal.syntomic
    IsIso (X.normalizedComponentι hnodal v) := by
  have := hnodal.syntomic
  refine isIso_of_isOpenImmersion_of_opensRange_eq_top _ (TopologicalSpace.Opens.ext ?_)
  rw [Scheme.Hom.coe_opensRange, X.range_normalizedComponentι hnodal v, hv,
    TopologicalSpace.Opens.coe_top]

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
  inferInstanceAs (IsRegular (componentOpen (X.singularLocus K).blowup v).toScheme)

instance isIntegral_normalizedComponent
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    (v : letI := hnodal.syntomic; irreducibleComponents (X.singularLocus K).blowup) :
    IsIntegral (X.normalizedComponent hnodal v) :=
  letI := hnodal.syntomic
  letI := X.isRegular_blowup_singularLocus hnodal
  inferInstanceAs (IsIntegral (componentOpen (X.singularLocus K).blowup v).toScheme)

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
  let Cv := componentOpen Bl v
  let Wv : Bl.Opens := Cv ⊓ (ν ⁻¹ᵁ U)
  obtain ⟨y, hy_v, hy_U⟩ := (X.dense_preimage_smoothLocus_blowupToBase (R := K)).inter_open_nonempty
    (v : Set Bl) (isOpen_of_mem_irreducibleComponents_of_isDomain_stalk v.2) v.2.1.nonempty
  have : Nonempty Wv.toScheme := ⟨⟨y, mem_componentOpen.mpr hy_v, hy_U⟩⟩
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
      exact ⟨⟨z, mem_componentOpen.mp hz_v, rfl⟩, hz_U⟩
    · rintro ⟨⟨z, hz_v, rfl⟩, hz_U⟩
      exact ⟨⟨z, mem_componentOpen.mpr hz_v, hz_U⟩, rfl⟩
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

end Nodal

end AlgebraicGeometry.Scheme

/-! ### Base change of normalized components -/

namespace TauCeti.AlgebraicGeometry

/-- **Under any field extension `L / K` with geometrically irreducible `Spec L ⟶ Spec K` (in
particular whenever `K` is separably closed), each normalized component of a base change `X'` is the
base change of the corresponding normalized component of `X`.** -/
theorem exists_isPullback_normalizedComponent {K L : Type u} [Field K] [Field L] [Algebra K L]
    [GeometricallyIrreducible (Spec.map (CommRingCat.ofHom (algebraMap K L)))]
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
          (irreducibleComponentsEquivOfIsPullback (isPullback_blowupSingularLocusMap_over H) v'),
      g_v ≫ X.normalizedComponentι hnodal _ =
        X'.normalizedComponentι hnodal' v' ≫ blowupSingularLocusMap H ∧
      IsPullback g_v
        (X'.normalizedComponent hnodal' v' ↘ Spec (.of L))
        (X.normalizedComponent hnodal
          (irreducibleComponentsEquivOfIsPullback (isPullback_blowupSingularLocusMap_over H) v') ↘
            Spec (.of K))
        (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
  have := hnodal.syntomic
  have := hnodal'.syntomic
  have := X.isRegular_blowup_singularLocus hnodal
  have := X'.isRegular_blowup_singularLocus hnodal'
  exact exists_isPullback_componentOpen (isPullback_blowupSingularLocusMap_over H) v'

end TauCeti.AlgebraicGeometry
