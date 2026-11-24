/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Genus
public import TauCeti.AlgebraicGeometry.Curves.Node.Normalization
public import TauCeti.AlgebraicGeometry.Curves.Normalization
public import TauCeti.AlgebraicGeometry.Scheme.IrreducibleComponent
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import TauCeti.AlgebraicGeometry.Cohomology.FlatBaseChange
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.SchematicDensity
import TauCeti.AlgebraicGeometry.Geometrically.Irreducible
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.PureRelativeDimension
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension
import TauCeti.Topology.Irreducible
import TauCeti.Topology.NoetherianSpace.IrreducibleComponents

/-!
# Irreducible components, normalized components, and component genera of a nodal curve

Let `X` be a nodal curve over a field `K` (`AtWorstNodalOfRelativeDimensionOne`), and let
`ν : Bl X ⟶ X` be the blowup of `X` along `Sing(X/K)`. Because `Bl X` is regular, its irreducible
components are clopen integral subschemes (`AlgebraicGeometry.Scheme.blowupComponent`). Over the
dense smooth locus `U`, `ν` restricts to an isomorphism, yielding a canonical bijection
`AlgebraicGeometry.Scheme.blowupComponentEquiv` between `irreducibleComponents (Bl X)` and
`irreducibleComponents X`.

Over an arbitrary field `K` (without perfection, properness, or connectedness assumptions),
`Bl X` is smooth over `Spec K` (`AlgebraicGeometry.Scheme.smooth_blowup_singularLocus`, descended
from the regular blowup over `AlgebraicClosure K`), and each component `X.blowupComponent v` is an
integral scheme smooth of relative dimension one over `Spec K`
(`AlgebraicGeometry.Scheme.smoothOfRelativeDimension_blowupComponent`). When `X` is proper, each
component is a curve over `K`
(`AlgebraicGeometry.Scheme.isCurveOver_blowupComponent_of_atWorstNodal`).

Over a separably closed field `K`, base change of `X` to any extension field `L / K` bijects the
components of `Bl X` and `Bl X'` (`AlgebraicGeometry.Scheme.preimageSingularLocusBlowupEquiv`),
pulls back each component along `AlgebraicGeometry.Scheme.blowupComponentBaseChangeMap`
(`AlgebraicGeometry.Scheme.isPullback_blowupComponentBaseChangeMap`), and preserves its genus
(`AlgebraicGeometry.Scheme.genus_blowupComponent_preimageSingularLocusBlowupEquiv`).

## Main definitions

* `AlgebraicGeometry.Scheme.blowupComponentEquiv`: canonical equivalence
  `irreducibleComponents (Bl X) ≃ irreducibleComponents X`.
* `AlgebraicGeometry.Scheme.blowupComponent`: an irreducible component of `Bl X` as a clopen
  subscheme over `Spec K`.
* `AlgebraicGeometry.Scheme.preimageSingularLocusBlowupEquiv`: equivalence of blowup components
  under base change from a separably closed field `K` to any field `L / K`.
* `AlgebraicGeometry.Scheme.blowupComponentBaseChangeMap`: the base-change morphism between
  corresponding normalized components over `L / K`.

## Main results

* `AlgebraicGeometry.Scheme.smooth_blowup_singularLocus` and
  `AlgebraicGeometry.Scheme.smoothOfRelativeDimension_blowupComponent`: `Bl X` is smooth over `K`
  and each component is smooth of relative dimension one over `K`.
* `AlgebraicGeometry.Scheme.isPullback_blowupComponentBaseChangeMap` and
  `AlgebraicGeometry.Scheme.genus_blowupComponent_preimageSingularLocusBlowupEquiv`: normalized
  components commute with base change from separably closed `K` to any field `L / K`, preserving
  their genera.

## References

* [The Stacks Project, Tags 0C46 and 0C58](https://stacks.math.columbia.edu/tag/0C46)
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Set TauCeti TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

section Components

variable {K : Type u} [Field K] (X : Scheme.{u}) [X.Over (Spec (.of K))]

section BlowupBijection

variable (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))

/-- In the singular-locus blowup of a nodal curve, the preimage of the smooth locus is dense. -/
theorem dense_preimage_smoothLocus_blowupToBase :
    letI := hnodal.syntomic
    Dense ((X.singularLocus K).blowupToBase ⁻¹' ((X ↘ Spec (.of K)).smoothLocus : Set X)) := by
  have := hnodal.syntomic; have := X.isRegular_blowup_singularLocus hnodal
  let I := X.singularLocus K
  have := I.isEffectiveCartier_comap_blowupToBase.isSchemeTheoreticallyDominant_support_compl_ι
  have h := (Opens.ι (I.comap I.blowupToBase).support.compl).denseRange
  rw [DenseRange, Opens.range_ι] at h; convert h using 1; ext y
  simp [I, IdealSheafData.support_comap, X.mem_support_singularLocus_iff_notMem_smoothLocus]

/-- The smooth locus of a nodal curve over a field is dense. -/
theorem dense_smoothLocus :
    letI := hnodal.syntomic; Dense ((X ↘ Spec (.of K)).smoothLocus : Set X) := by
  have := hnodal.syntomic; have := X.surjective_blowupToBase_singularLocus hnodal
  let ν := (X.singularLocus K).blowupToBase; intro x; obtain ⟨y, rfl⟩ := ν.surjective x
  exact image_preimage_eq ((X ↘ Spec (.of K)).smoothLocus : Set X) ν.surjective ▸
    image_closure_subset_closure_image ν.continuous
      ⟨y, X.dense_preimage_smoothLocus_blowupToBase hnodal y, rfl⟩

variable {X} in
/-- Every irreducible component of the blowup meets the preimage of the smooth locus. -/
theorem nonempty_inter_preimage_smoothLocus_of_mem_irreducibleComponents
    {v : Set (letI := hnodal.syntomic; (X.singularLocus K).blowup)}
    (hv : letI := hnodal.syntomic; v ∈ irreducibleComponents (X.singularLocus K).blowup) :
    letI := hnodal.syntomic
    (v ∩ (X.singularLocus K).blowupToBase ⁻¹' ((X ↘ Spec (.of K)).smoothLocus : Set X)).Nonempty :=
  letI := hnodal.syntomic; haveI := X.isRegular_blowup_singularLocus hnodal
  (X.dense_preimage_smoothLocus_blowupToBase hnodal).inter_open_nonempty v
    (isClopen_of_mem_irreducibleComponents hv).isOpen hv.1.nonempty

variable {X} in
/-- Every irreducible component of a nodal curve over a field meets its smooth locus. -/
theorem nonempty_inter_smoothLocus_of_mem_irreducibleComponents
    {E : Set X} (hE : E ∈ irreducibleComponents X) :
    letI := hnodal.syntomic; (E ∩ ((X ↘ Spec (.of K)).smoothLocus : Set X)).Nonempty := by
  have := hnodal.syntomic
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of K))
  obtain ⟨x, hxE⟩ := hE.1.nonempty
  obtain ⟨W, hW, hxW, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  have : IsNoetherianRing Γ(X, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  have : NoetherianSpace (W : Set X) := noetherianSpace_of_isAffineOpen W hW
  have hint := W.isOpen.nonempty_interior_of_mem_irreducibleComponents
    NoetherianSpace.finite_irreducibleComponents hE ⟨x, hxE, hxW⟩
  obtain ⟨z, hzE, hzU⟩ := (X.dense_smoothLocus hnodal).inter_open_nonempty
    (interior E) isOpen_interior hint
  exact ⟨z, interior_subset hzE, hzU⟩

private theorem isOpen_compl_image_compl_of_mem_irreducibleComponents
    {v : Set (letI := hnodal.syntomic; (X.singularLocus K).blowup)}
    (hv : letI := hnodal.syntomic; v ∈ irreducibleComponents (X.singularLocus K).blowup) :
    letI := hnodal.syntomic; let ν := (X.singularLocus K).blowupToBase
    IsOpen (ν '' vᶜ)ᶜ ∧ (ν '' vᶜ)ᶜ ⊆ ν '' v ∧
      ∀ y ∈ v, ν y ∈ (X ↘ Spec (.of K)).smoothLocus → ν y ∈ (ν '' vᶜ)ᶜ := by
  have := hnodal.syntomic; have := X.isRegular_blowup_singularLocus hnodal
  have := X.isFinite_blowupToBase_singularLocus hnodal
  have := X.surjective_blowupToBase_singularLocus hnodal
  let ν := (X.singularLocus K).blowupToBase
  refine ⟨isOpen_compl_iff.mpr (ν.isClosedMap vᶜ
    (isClopen_of_mem_irreducibleComponents hv).isOpen.isClosed_compl), fun x hx ↦ ?_,
    fun y hyv hyU ⟨_, hy'v, hy'eq⟩ ↦
      hy'v (X.eq_of_blowupToBase_singularLocus_eq_of_mem_smoothLocus hy'eq.symm hyU ▸ hyv)⟩
  obtain ⟨y, rfl⟩ := ν.surjective x
  exact ⟨y, Classical.not_not.mp fun hyv ↦ hx ⟨y, hyv, rfl⟩, rfl⟩

variable {X} in
/-- The image of an irreducible component of `Bl X` is an irreducible component of `X`. -/
theorem image_blowupToBase_mem_irreducibleComponents
    {v : Set (letI := hnodal.syntomic; (X.singularLocus K).blowup)}
    (hv : letI := hnodal.syntomic; v ∈ irreducibleComponents (X.singularLocus K).blowup) :
    letI := hnodal.syntomic; (X.singularLocus K).blowupToBase '' v ∈ irreducibleComponents X := by
  have := hnodal.syntomic; have := X.isRegular_blowup_singularLocus hnodal
  have := X.isFinite_blowupToBase_singularLocus hnodal
  let ν := (X.singularLocus K).blowupToBase
  obtain ⟨hOopen, hOsub, hOmem⟩ := isOpen_compl_image_compl_of_mem_irreducibleComponents X hnodal hv
  obtain ⟨y, hyv, hyU⟩ :=
    nonempty_inter_preimage_smoothLocus_of_mem_irreducibleComponents hnodal hv
  exact ⟨hv.1.image ν ν.continuous.continuousOn, fun E hE hsub ↦
    (subset_closure_inter_of_isPreirreducible_of_isOpen hE.2 hOopen
      ⟨ν y, hsub ⟨y, hyv, rfl⟩, hOmem y hyv hyU⟩).trans
      (closure_minimal (inter_subset_right.trans hOsub)
        (ν.isClosedMap v (isClopen_of_mem_irreducibleComponents hv).isClosed))⟩

variable {X} in
/-- Recovering a component `v` of `Bl X` as the closure of the smooth part of `ν '' v`. -/
theorem closure_preimage_inter_smoothLocus_image_blowupToBase
    {v : Set (letI := hnodal.syntomic; (X.singularLocus K).blowup)}
    (hv : letI := hnodal.syntomic; v ∈ irreducibleComponents (X.singularLocus K).blowup) :
    letI := hnodal.syntomic
    closure ((X.singularLocus K).blowupToBase ⁻¹'
      ((X.singularLocus K).blowupToBase '' v ∩ ((X ↘ Spec (.of K)).smoothLocus : Set X))) = v := by
  have := hnodal.syntomic; have := X.isRegular_blowup_singularLocus hnodal
  let ν := (X.singularLocus K).blowupToBase; let U := ((X ↘ Spec (.of K)).smoothLocus : Set X)
  have hpre : ν ⁻¹' (ν '' v ∩ U) = v ∩ ν ⁻¹' U := Set.ext fun y ↦
    ⟨fun ⟨⟨_, hy'v, hy'eq⟩, hyU⟩ ↦
      ⟨X.eq_of_blowupToBase_singularLocus_eq_of_mem_smoothLocus hy'eq.symm hyU ▸ hy'v, hyU⟩,
    fun ⟨hyv, hyU⟩ ↦ ⟨⟨y, hyv, rfl⟩, hyU⟩⟩
  rw [hpre]
  exact Subset.antisymm
    (closure_minimal inter_subset_left (isClopen_of_mem_irreducibleComponents hv).isClosed)
    (subset_closure_inter_of_isPreirreducible_of_isOpen hv.1.2
      ((X ↘ Spec (.of K)).smoothLocus.isOpen.preimage ν.continuous)
      (nonempty_inter_preimage_smoothLocus_of_mem_irreducibleComponents hnodal hv))

/-- Pushing forward along `blowupToBase` maps `irreducibleComponents (Bl X)` bijectively onto
`irreducibleComponents X`. -/
theorem bijOn_image_blowupToBase_irreducibleComponents :
    letI := hnodal.syntomic
    BijOn ((X.singularLocus K).blowupToBase '' ·)
      (irreducibleComponents (X.singularLocus K).blowup) (irreducibleComponents X) := by
  have := hnodal.syntomic; have := X.isRegular_blowup_singularLocus hnodal
  have := X.surjective_blowupToBase_singularLocus hnodal
  refine ⟨fun _ hv ↦ image_blowupToBase_mem_irreducibleComponents hnodal hv,
    fun v₁ hv₁ v₂ hv₂ heq ↦ ?_, fun E hE ↦ ?_⟩
  · dsimp only at heq
    rw [← closure_preimage_inter_smoothLocus_image_blowupToBase hnodal hv₁, heq,
      closure_preimage_inter_smoothLocus_image_blowupToBase hnodal hv₂]
  · obtain ⟨x, hxE, hxU⟩ := nonempty_inter_smoothLocus_of_mem_irreducibleComponents hnodal hE
    obtain ⟨y, rfl⟩ := (X.singularLocus K).blowupToBase.surjective x
    let v := irreducibleComponentOf y
    obtain ⟨hOopen, hOsub, hOmem⟩ :=
      isOpen_compl_image_compl_of_mem_irreducibleComponents X hnodal v.property
    exact ⟨v.val, v.property, (eq_of_mem_irreducibleComponents_of_nonempty_inter_open
      (image_blowupToBase_mem_irreducibleComponents hnodal v.property) hE hOopen hOsub
      ⟨_, hxE, hOmem y (mem_irreducibleComponentOf y) hxU⟩).symm⟩

end BlowupBijection

variable (K) in
/-- The canonical equivalence `irreducibleComponents (Bl X) ≃ irreducibleComponents X`. -/
def blowupComponentEquiv (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K))) :
    letI := hnodal.syntomic
    irreducibleComponents (X.singularLocus K).blowup ≃ irreducibleComponents X :=
  letI := hnodal.syntomic
  let ν := (X.singularLocus K).blowupToBase; let U := ((X ↘ Spec (.of K)).smoothLocus : Set X)
  { toFun v := ⟨ν '' v.val, image_blowupToBase_mem_irreducibleComponents hnodal v.property⟩
    invFun E := ⟨closure (ν ⁻¹' (E.val ∩ U)), by
      obtain ⟨v, hv, hEv⟩ := (X.bijOn_image_blowupToBase_irreducibleComponents hnodal).surjOn
        E.property
      dsimp only at hEv
      rwa [← hEv, closure_preimage_inter_smoothLocus_image_blowupToBase hnodal hv]⟩
    left_inv v := Subtype.ext
      (closure_preimage_inter_smoothLocus_image_blowupToBase hnodal v.property)
    right_inv E := Subtype.ext <| by
      obtain ⟨v, hv, hEv⟩ := (X.bijOn_image_blowupToBase_irreducibleComponents hnodal).surjOn
        E.property
      dsimp only at hEv ⊢
      rw [← hEv, closure_preimage_inter_smoothLocus_image_blowupToBase hnodal hv] }

section BlowupEquivProps

variable (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))

@[simp]
theorem coe_blowupComponentEquiv
    (v : letI := hnodal.syntomic; irreducibleComponents (X.singularLocus K).blowup) :
    letI := hnodal.syntomic
    ((X.blowupComponentEquiv K hnodal v : irreducibleComponents X) : Set X) =
      (X.singularLocus K).blowupToBase '' (v : Set (X.singularLocus K).blowup) := (rfl)

theorem coe_blowupComponentEquiv_symm (E : irreducibleComponents X) :
    letI := hnodal.syntomic
    (((X.blowupComponentEquiv K hnodal).symm E :
        irreducibleComponents (X.singularLocus K).blowup) : Set (X.singularLocus K).blowup) =
      closure ((X.singularLocus K).blowupToBase ⁻¹'
        ((E : Set X) ∩ ((X ↘ Spec (.of K)).smoothLocus : Set X))) := (rfl)

variable {X} in
/-- Over a smooth point `ν y ∈ U`, `ν y ∈ ν '' v` holds if and only if `y ∈ v`. -/
theorem blowupToBase_mem_coe_blowupComponentEquiv_iff_of_mem_smoothLocus
    {y : (letI := hnodal.syntomic; (X.singularLocus K).blowup)}
    (hy : letI := hnodal.syntomic
      (X.singularLocus K).blowupToBase y ∈ (X ↘ Spec (.of K)).smoothLocus)
    (v : letI := hnodal.syntomic; irreducibleComponents (X.singularLocus K).blowup) :
    letI := hnodal.syntomic
    (X.singularLocus K).blowupToBase y ∈ ((X.blowupComponentEquiv K hnodal v :
        irreducibleComponents X) : Set X) ↔ y ∈ (v : Set (X.singularLocus K).blowup) := by
  have := hnodal.syntomic
  exact ⟨fun ⟨_, hy'v, hy'eq⟩ ↦
      X.eq_of_blowupToBase_singularLocus_eq_of_mem_smoothLocus hy'eq.symm hy ▸ hy'v,
    fun hyv ↦ ⟨y, hyv, rfl⟩⟩

variable {X} in
/-- Every smooth point of a nodal curve over a field belongs to a unique irreducible component. -/
theorem existsUnique_mem_irreducibleComponents_of_mem_smoothLocus {x : X}
    (hx : letI := hnodal.syntomic; x ∈ (X ↘ Spec (.of K)).smoothLocus) :
    ∃! E : irreducibleComponents X, x ∈ (E : Set X) := by
  have := hnodal.syntomic; have := X.isRegular_blowup_singularLocus hnodal
  have := X.surjective_blowupToBase_singularLocus hnodal
  obtain ⟨y, rfl⟩ := (X.singularLocus K).blowupToBase.surjective x
  refine ⟨X.blowupComponentEquiv K hnodal (irreducibleComponentOf y),
    ⟨y, mem_irreducibleComponentOf y, rfl⟩, fun E hE ↦ ?_⟩
  obtain ⟨v, rfl⟩ := (X.blowupComponentEquiv K hnodal).surjective E
  rw [blowupToBase_mem_coe_blowupComponentEquiv_iff_of_mem_smoothLocus hnodal hx] at hE
  exact congrArg (X.blowupComponentEquiv K hnodal) (irreducibleComponentOf_eq_iff.mpr hE).symm

end BlowupEquivProps

/-! ### Normalized component schemes and smoothness -/

/-- For a nodal curve `X` over any field `K`, the singular-locus blowup `Bl X` is smooth over
`Spec K`. Over `AlgebraicClosure K` the base-changed blowup is regular over a perfect field hence
smooth, and smoothness descends along `Spec (AlgebraicClosure K) ⟶ Spec K`. -/
theorem smooth_blowup_singularLocus
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K))) :
    letI := hnodal.syntomic
    Smooth ((X.singularLocus K).blowupToBase ≫ X ↘ Spec (.of K)) := by
  have := hnodal.syntomic
  let L := AlgebraicClosure K
  let φ : Spec (.of L) ⟶ Spec (.of K) := Spec.algebraMap K L
  let X' := pullback (X ↘ Spec (.of K)) φ
  let : X'.Over (Spec (.of L)) := ⟨pullback.snd _ _⟩
  have H : IsPullback (pullback.fst (X ↘ Spec (.of K)) φ) (X' ↘ Spec (.of L))
      (X ↘ Spec (.of K)) φ := IsPullback.of_hasPullback _ _
  have hnodal' : AtWorstNodalOfRelativeDimensionOne (X' ↘ Spec (.of L)) :=
    MorphismProperty.of_isPullback H hnodal
  have := hnodal'.syntomic
  have := X'.isRegular_blowup_singularLocus hnodal'
  have := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of K))
  have := LocallyOfFiniteType.isLocallyNoetherian (X' ↘ Spec (.of L))
  have : IsLocallyNoetherian (X'.singularLocus L).blowup :=
    LocallyOfFiniteType.isLocallyNoetherian (X'.singularLocus L).blowupToBase
  have hsm' : Smooth ((X'.singularLocus L).blowupToBase ≫ X' ↘ Spec (.of L)) :=
    ((X'.singularLocus L).blowupToBase ≫ X' ↘ Spec (.of L)).smooth_of_isRegularLocalRing_stalk
  have Hpb := ((isPullback_singularLocusBlowupMap H).flip.paste_vert H).flip
  exact MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) Hpb ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
    hsm'

/-- The singular-locus blowup of a prestable curve over a field is smooth over `Spec K`. -/
instance smooth_blowup_singularLocus_of_prestableFamily [PrestableFamily (X ↘ Spec (.of K))] :
    Smooth ((X.singularLocus K).blowupToBase ≫ X ↘ Spec (.of K)) :=
  X.smooth_blowup_singularLocus PrestableFamily.atWorstNodalOfRelativeDimensionOne

section BlowupComponent

variable [SyntomicOfRelativeDimension 1 (X ↘ Spec (.of K))]
  [IsRegular (X.singularLocus K).blowup]

/-- An irreducible component of the blowup of a nodal curve along its singular subscheme, as a
clopen integral subscheme of `(X.singularLocus K).blowup`. -/
def blowupComponent (v : irreducibleComponents (X.singularLocus K).blowup) :
    (X.singularLocus K).blowup.Opens :=
  have := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of K))
  have : IsLocallyNoetherian (X.singularLocus K).blowup :=
    LocallyOfFiniteType.isLocallyNoetherian (X.singularLocus K).blowupToBase
  (X.singularLocus K).blowup.componentOpens v

@[simp]
theorem coe_blowupComponent (v : irreducibleComponents (X.singularLocus K).blowup) :
    (X.blowupComponent v : Set (X.singularLocus K).blowup) = v := by
  have := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of K))
  have : IsLocallyNoetherian (X.singularLocus K).blowup :=
    LocallyOfFiniteType.isLocallyNoetherian (X.singularLocus K).blowupToBase
  exact (X.singularLocus K).blowup.coe_componentOpens v

@[simp]
theorem mem_blowupComponent {v : irreducibleComponents (X.singularLocus K).blowup}
    {y : (X.singularLocus K).blowup} : y ∈ X.blowupComponent v ↔ y ∈ (v : Set _) := by
  rw [← SetLike.mem_coe, X.coe_blowupComponent v]

/-- The inclusion of a component of the blowup is also a closed immersion. -/
instance isClosedImmersion_blowupComponent_ι
    (v : irreducibleComponents (X.singularLocus K).blowup) :
    IsClosedImmersion (X.blowupComponent v).ι := by
  have := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of K))
  have : IsLocallyNoetherian (X.singularLocus K).blowup :=
    LocallyOfFiniteType.isLocallyNoetherian (X.singularLocus K).blowupToBase
  exact inferInstanceAs (IsClosedImmersion ((X.singularLocus K).blowup.componentOpens v).ι)

/-- A component of the blowup is a scheme over `K` through the blowup morphism to the curve. -/
instance blowupComponentOver (v : irreducibleComponents (X.singularLocus K).blowup) :
    (X.blowupComponent v).toScheme.Over (Spec (.of K)) :=
  ⟨(X.blowupComponent v).ι ≫ (X.singularLocus K).blowupToBase ≫ X ↘ Spec (.of K)⟩

/-- The structure morphism of a component of the blowup to `Spec K` is the composite of its
inclusion, the blowup morphism and the structure morphism of the curve. -/
@[simp]
theorem blowupComponent_over (v : irreducibleComponents (X.singularLocus K).blowup) :
    (X.blowupComponent v).toScheme ↘ Spec (.of K) =
      (X.blowupComponent v).ι ≫ (X.singularLocus K).blowupToBase ≫ X ↘ Spec (.of K) := (rfl)

/-- The structure morphism of a component of the blowup to `Spec K` is locally of finite type. -/
instance locallyOfFiniteType_blowupComponent_over
    (v : irreducibleComponents (X.singularLocus K).blowup) :
    LocallyOfFiniteType ((X.blowupComponent v).toScheme ↘ Spec (.of K)) := by
  have := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of K))
  rw [blowupComponent_over]; infer_instance

/-- Each component of the blowup is an integral scheme. -/
instance isIntegral_blowupComponent (v : irreducibleComponents (X.singularLocus K).blowup) :
    IsIntegral (X.blowupComponent v).toScheme := by
  have := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of K))
  have : IsLocallyNoetherian (X.singularLocus K).blowup :=
    LocallyOfFiniteType.isLocallyNoetherian (X.singularLocus K).blowupToBase
  exact inferInstanceAs (IsIntegral ((X.singularLocus K).blowup.componentOpens v).toScheme)

/-- Each component of the blowup is a regular scheme. -/
instance isRegular_blowupComponent (v : irreducibleComponents (X.singularLocus K).blowup) :
    IsRegular (X.blowupComponent v).toScheme :=
  IsRegular.of_isOpenImmersion (X.blowupComponent v).ι

end BlowupComponent

section BlowupComponentNodal

/-- The image in `X` of `X.blowupComponent v` is the component `blowupComponentEquiv v`. -/
theorem range_blowupComponent_ι_comp_blowupToBase
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    (v : letI := hnodal.syntomic; irreducibleComponents (X.singularLocus K).blowup) :
    letI := hnodal.syntomic; haveI := X.isRegular_blowup_singularLocus hnodal
    Set.range ((X.blowupComponent v).ι ≫ (X.singularLocus K).blowupToBase) =
      ((X.blowupComponentEquiv K hnodal v : irreducibleComponents X) : Set X) := by
  have := hnodal.syntomic; have := X.isRegular_blowup_singularLocus hnodal
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Opens.range_ι,
    X.coe_blowupComponent v, X.coe_blowupComponentEquiv hnodal v]

/-- Every component of the blowup of a nodal curve over a field has Krull dimension one. -/
theorem topologicalKrullDim_blowupComponent
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    (v : letI := hnodal.syntomic; irreducibleComponents (X.singularLocus K).blowup) :
    letI := hnodal.syntomic; haveI := X.isRegular_blowup_singularLocus hnodal
    topologicalKrullDim (X.blowupComponent v).toScheme = 1 := by
  have := hnodal.syntomic; have := X.isRegular_blowup_singularLocus hnodal
  let Bl := (X.singularLocus K).blowup; let ν := (X.singularLocus K).blowupToBase
  let U := (X ↘ Spec (.of K)).smoothLocus; let W : Bl.Opens := X.blowupComponent v ⊓ (ν ⁻¹ᵁ U)
  obtain ⟨y, hyv, hyU⟩ :=
    nonempty_inter_preimage_smoothLocus_of_mem_irreducibleComponents hnodal v.property
  have : Nonempty W.toScheme := ⟨⟨y, (X.mem_blowupComponent).mpr hyv, hyU⟩⟩
  let j : W.toScheme ⟶ (X.blowupComponent v).toScheme := Bl.homOfLE inf_le_left
  have : IsOpenImmersion j :=
    inferInstanceAs (IsOpenImmersion (Bl.homOfLE (inf_le_left : W ≤ X.blowupComponent v)))
  have : IsIso (ν ∣_ U) := X.isIso_blowupToBase_singularLocus_restrict_smoothLocus
  -- `W` embeds openly into `U`, which is smooth of relative dimension 1 over `Spec K`.
  have : Smooth (U.ι ≫ X ↘ Spec (.of K)) := inferInstance
  let gW : W.toScheme ⟶ X := Bl.homOfLE (inf_le_right : W ≤ ν ⁻¹ᵁ U) ≫ (ν ∣_ U) ≫ U.ι
  have : Smooth (gW ≫ X ↘ Spec (.of K)) := by
    dsimp only [gW]; rw [Category.assoc, Category.assoc]; infer_instance
  have : SmoothOfRelativeDimension 1 (gW ≫ X ↘ Spec (.of K)) :=
    (smoothOfRelativeDimension_iff_smooth_and_pureRelativeDimension _).mpr ⟨‹_›, inferInstance⟩
  have hdimW : topologicalKrullDim W.toScheme = 1 :=
    topologicalKrullDim_eq_of_smoothOfRelativeDimension (gW ≫ X ↘ Spec (.of K))
  exact (topologicalKrullDim_eq_of_isOpenEmbedding_of_locallyOfFiniteType
    ((X.blowupComponent v).toScheme ↘ Spec (.of K)) j.isOpenEmbedding).symm.trans hdimW

/-- Every component of the blowup of a nodal curve over any field `K` is smooth of relative
dimension one over `Spec K`. -/
theorem smoothOfRelativeDimension_blowupComponent
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    (v : letI := hnodal.syntomic; irreducibleComponents (X.singularLocus K).blowup) :
    letI := hnodal.syntomic; haveI := X.isRegular_blowup_singularLocus hnodal
    SmoothOfRelativeDimension 1 ((X.blowupComponent v).toScheme ↘ Spec (.of K)) := by
  have := hnodal.syntomic; have := X.isRegular_blowup_singularLocus hnodal
  have := X.smooth_blowup_singularLocus hnodal
  have : Smooth ((X.blowupComponent v).toScheme ↘ Spec (.of K)) := by
    rw [blowupComponent_over]; infer_instance
  exact smoothOfRelativeDimension_of_topologicalKrullDim_eq _
    (X.topologicalKrullDim_blowupComponent hnodal v)

/-- When `X` is a proper nodal curve over `K`, each component of `Bl X` is proper over `K`. -/
theorem isProper_blowupComponent_of_atWorstNodal [IsProper (X ↘ Spec (.of K))]
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    (v : letI := hnodal.syntomic; irreducibleComponents (X.singularLocus K).blowup) :
    letI := hnodal.syntomic; haveI := X.isRegular_blowup_singularLocus hnodal
    IsProper ((X.blowupComponent v).toScheme ↘ Spec (.of K)) := by
  have := hnodal.syntomic; have := X.isRegular_blowup_singularLocus hnodal
  have := X.isFinite_blowupToBase_singularLocus hnodal
  rw [blowupComponent_over]; infer_instance

/-- When `X` is a proper nodal curve over `K`, each component of `Bl X` is a curve over `K`. -/
theorem isCurveOver_blowupComponent_of_atWorstNodal [IsProper (X ↘ Spec (.of K))]
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    (v : letI := hnodal.syntomic; irreducibleComponents (X.singularLocus K).blowup) :
    letI := hnodal.syntomic; haveI := X.isRegular_blowup_singularLocus hnodal
    (X.blowupComponent v).toScheme.IsCurveOver K :=
  letI := hnodal.syntomic; haveI := X.isRegular_blowup_singularLocus hnodal
  haveI := X.isProper_blowupComponent_of_atWorstNodal hnodal v
  ⟨X.topologicalKrullDim_blowupComponent hnodal v⟩

section PrestableInstances

variable [PrestableFamily (X ↘ Spec (.of K))]
  (v : irreducibleComponents (X.singularLocus K).blowup)

/-- Each component of the blowup of a prestable curve is smooth of relative dimension 1 over `K`. -/
instance smoothOfRelativeDimension_blowupComponent_of_prestableFamily :
    SmoothOfRelativeDimension 1 ((X.blowupComponent v).toScheme ↘ Spec (.of K)) :=
  X.smoothOfRelativeDimension_blowupComponent PrestableFamily.atWorstNodalOfRelativeDimensionOne v

/-- Each component of the blowup of a prestable curve is proper over `K`. -/
instance isProper_blowupComponent :
    IsProper ((X.blowupComponent v).toScheme ↘ Spec (.of K)) :=
  X.isProper_blowupComponent_of_atWorstNodal PrestableFamily.atWorstNodalOfRelativeDimensionOne v

/-- Each component of the blowup of a prestable curve has dimension at most one. -/
theorem topologicalKrullDim_blowupComponent_le_one :
    topologicalKrullDim (X.blowupComponent v) ≤ 1 :=
  (X.topologicalKrullDim_blowupComponent PrestableFamily.atWorstNodalOfRelativeDimensionOne v).le

/-- Each component of the blowup of a prestable curve is a curve over `K`. -/
instance isCurveOver_blowupComponent : (X.blowupComponent v).toScheme.IsCurveOver K :=
  X.isCurveOver_blowupComponent_of_atWorstNodal PrestableFamily.atWorstNodalOfRelativeDimensionOne v

end PrestableInstances

end BlowupComponentNodal

end Components

/-! ### Base change of normalized components and component genera -/

section FieldExtension

variable {K L : Type u} [Field K] [IsSepClosed K] [Field L] [Algebra K L]
  {X X' : Scheme.{u}} [X.Over (Spec (.of K))] [X'.Over (Spec (.of L))] {g : X' ⟶ X}
  (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
  (H : IsPullback g (X' ↘ Spec (.of L)) (X ↘ Spec (.of K)) (Spec.algebraMap K L))

/-- Over a separably closed field `K`, base-changing `X` to any field extension `L / K` bijects the
irreducible components of `Bl X` and `Bl X'` via preimage under `singularLocusBlowupMap H`. -/
theorem bijOn_preimage_singularLocusBlowupMap_irreducibleComponents :
    letI := hnodal.syntomic; letI := (MorphismProperty.of_isPullback H hnodal).syntomic
    BijOn (singularLocusBlowupMap H ⁻¹' ·)
      (irreducibleComponents (X.singularLocus K).blowup)
      (irreducibleComponents (X'.singularLocus L).blowup) :=
  letI := hnodal.syntomic; letI := (MorphismProperty.of_isPullback H hnodal).syntomic
  bijOn_preimage_irreducibleComponents_of_isSepClosed
    ((isPullback_singularLocusBlowupMap H).flip.paste_vert H)

/-- Canonical equivalence of irreducible components of singular-locus blowups under base change
from a separably closed field `K` to any field extension `L / K`. -/
def preimageSingularLocusBlowupEquiv :
    letI := hnodal.syntomic; letI := (MorphismProperty.of_isPullback H hnodal).syntomic
    irreducibleComponents (X.singularLocus K).blowup ≃
      irreducibleComponents (X'.singularLocus L).blowup :=
  letI := hnodal.syntomic; letI := (MorphismProperty.of_isPullback H hnodal).syntomic
  (bijOn_preimage_singularLocusBlowupMap_irreducibleComponents hnodal H).equiv

@[simp]
theorem coe_preimageSingularLocusBlowupEquiv
    (v : letI := hnodal.syntomic; irreducibleComponents (X.singularLocus K).blowup) :
    letI := hnodal.syntomic; letI := (MorphismProperty.of_isPullback H hnodal).syntomic
    ((preimageSingularLocusBlowupEquiv hnodal H v :
        irreducibleComponents (X'.singularLocus L).blowup) : Set (X'.singularLocus L).blowup) =
      singularLocusBlowupMap H ⁻¹' (v : Set (X.singularLocus K).blowup) := (rfl)

/-- `preimageSingularLocusBlowupEquiv` carries the component through `singularLocusBlowupMap H b'`
to the component through `b'`. -/
theorem preimageSingularLocusBlowupEquiv_irreducibleComponentOf
    (b' : (letI := (MorphismProperty.of_isPullback H hnodal).syntomic
      (X'.singularLocus L).blowup)) :
    letI := hnodal.syntomic; letI := (MorphismProperty.of_isPullback H hnodal).syntomic
    preimageSingularLocusBlowupEquiv hnodal H
        (irreducibleComponentOf (singularLocusBlowupMap H b')) =
      irreducibleComponentOf b' := by
  have := hnodal.syntomic; have hnodal' := MorphismProperty.of_isPullback H hnodal
  have := hnodal'.syntomic; have := X'.isRegular_blowup_singularLocus hnodal'
  have := LocallyOfFiniteType.isLocallyNoetherian (X' ↘ Spec (.of L))
  have : IsLocallyNoetherian (X'.singularLocus L).blowup :=
    LocallyOfFiniteType.isLocallyNoetherian (X'.singularLocus L).blowupToBase
  refine (irreducibleComponentOf_eq_iff.mpr ?_).symm
  rw [coe_preimageSingularLocusBlowupEquiv, mem_preimage]
  exact mem_irreducibleComponentOf _

/-- Canonical base-change morphism between corresponding normalized components under field
extension `L / K` of a separably closed field `K`. -/
def blowupComponentBaseChangeMap
    (v : letI := hnodal.syntomic; irreducibleComponents (X.singularLocus K).blowup) :
    letI := hnodal.syntomic
    haveI hnodal' := MorphismProperty.of_isPullback H hnodal; letI := hnodal'.syntomic
    haveI := X.isRegular_blowup_singularLocus hnodal
    haveI := X'.isRegular_blowup_singularLocus hnodal'
    (X'.blowupComponent (preimageSingularLocusBlowupEquiv hnodal H v)).toScheme ⟶
      (X.blowupComponent v).toScheme :=
  letI := hnodal.syntomic
  haveI hnodal' := MorphismProperty.of_isPullback H hnodal; letI := hnodal'.syntomic
  haveI := X.isRegular_blowup_singularLocus hnodal
  haveI := X'.isRegular_blowup_singularLocus hnodal'
  let v' := preimageSingularLocusBlowupEquiv hnodal H v
  have hopen : X'.blowupComponent v' = singularLocusBlowupMap H ⁻¹ᵁ X.blowupComponent v :=
    Opens.ext (by simp [v'])
  ((X'.singularLocus L).blowup.isoOfEq hopen).hom ≫
    (singularLocusBlowupMap H ∣_ X.blowupComponent v)

/-- `blowupComponentBaseChangeMap` commutes with the clopen inclusions into the blowups. -/
@[reassoc (attr := simp)]
theorem blowupComponentBaseChangeMap_ι
    (v : letI := hnodal.syntomic; irreducibleComponents (X.singularLocus K).blowup) :
    letI := hnodal.syntomic
    haveI hnodal' := MorphismProperty.of_isPullback H hnodal; letI := hnodal'.syntomic
    haveI := X.isRegular_blowup_singularLocus hnodal
    haveI := X'.isRegular_blowup_singularLocus hnodal'
    blowupComponentBaseChangeMap hnodal H v ≫ (X.blowupComponent v).ι =
      (X'.blowupComponent (preimageSingularLocusBlowupEquiv hnodal H v)).ι ≫
        singularLocusBlowupMap H := by
  have := hnodal.syntomic; have hnodal' := MorphismProperty.of_isPullback H hnodal
  have := hnodal'.syntomic
  have := X.isRegular_blowup_singularLocus hnodal; have := X'.isRegular_blowup_singularLocus hnodal'
  simp [blowupComponentBaseChangeMap]

/-- `blowupComponentBaseChangeMap` forms a cartesian square with the clopen inclusions into the
singular-locus blowups. -/
theorem isPullback_blowupComponentBaseChangeMap_ι
    (v : letI := hnodal.syntomic; irreducibleComponents (X.singularLocus K).blowup) :
    letI := hnodal.syntomic
    haveI hnodal' := MorphismProperty.of_isPullback H hnodal; letI := hnodal'.syntomic
    haveI := X.isRegular_blowup_singularLocus hnodal
    haveI := X'.isRegular_blowup_singularLocus hnodal'
    IsPullback (blowupComponentBaseChangeMap hnodal H v)
      (X'.blowupComponent (preimageSingularLocusBlowupEquiv hnodal H v)).ι
      (X.blowupComponent v).ι (singularLocusBlowupMap H) := by
  have := hnodal.syntomic; have hnodal' := MorphismProperty.of_isPullback H hnodal
  have := hnodal'.syntomic
  have := X.isRegular_blowup_singularLocus hnodal; have := X'.isRegular_blowup_singularLocus hnodal'
  let fBl := singularLocusBlowupMap H
  let v' := preimageSingularLocusBlowupEquiv hnodal H v
  have hopen : X'.blowupComponent v' = fBl ⁻¹ᵁ X.blowupComponent v :=
    Opens.ext (by simp [v', fBl])
  have hsq1 : IsPullback ((X'.singularLocus L).blowup.isoOfEq hopen).hom
      (X'.blowupComponent v').ι (fBl ⁻¹ᵁ X.blowupComponent v).ι (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, Scheme.isoOfEq_hom_ι]⟩
  simpa only [blowupComponentBaseChangeMap, Category.id_comp] using
    hsq1.paste_horiz (isPullback_morphismRestrict fBl (X.blowupComponent v))

/-- `blowupComponentBaseChangeMap` presents the normalized component over `L` as the base change
of the normalized component over `K` along `Spec L ⟶ Spec K`. -/
theorem isPullback_blowupComponentBaseChangeMap
    (v : letI := hnodal.syntomic; irreducibleComponents (X.singularLocus K).blowup) :
    letI := hnodal.syntomic
    haveI hnodal' := MorphismProperty.of_isPullback H hnodal; letI := hnodal'.syntomic
    haveI := X.isRegular_blowup_singularLocus hnodal
    haveI := X'.isRegular_blowup_singularLocus hnodal'
    IsPullback (blowupComponentBaseChangeMap hnodal H v)
      ((X'.blowupComponent (preimageSingularLocusBlowupEquiv hnodal H v)).toScheme ↘ Spec (.of L))
      ((X.blowupComponent v).toScheme ↘ Spec (.of K)) (Spec.algebraMap K L) := by
  have := hnodal.syntomic; have hnodal' := MorphismProperty.of_isPullback H hnodal
  have := hnodal'.syntomic
  have := X.isRegular_blowup_singularLocus hnodal; have := X'.isRegular_blowup_singularLocus hnodal'
  simpa only [blowupComponent_over, Category.assoc] using
    (isPullback_blowupComponentBaseChangeMap_ι hnodal H v).paste_vert
      ((isPullback_singularLocusBlowupMap H).flip.paste_vert H)

/-- Component genera are invariant under arbitrary field extensions of a separably closed base
field. -/
theorem genus_blowupComponent_preimageSingularLocusBlowupEquiv [IsProper (X ↘ Spec (.of K))]
    (v : letI := hnodal.syntomic; irreducibleComponents (X.singularLocus K).blowup) :
    letI := hnodal.syntomic
    haveI hnodal' := MorphismProperty.of_isPullback H hnodal; letI := hnodal'.syntomic
    haveI : IsProper (X' ↘ Spec (.of L)) := MorphismProperty.of_isPullback H ‹_›
    haveI := X.isRegular_blowup_singularLocus hnodal
    haveI := X'.isRegular_blowup_singularLocus hnodal'
    haveI := X.isCurveOver_blowupComponent_of_atWorstNodal hnodal v
    haveI := X'.isCurveOver_blowupComponent_of_atWorstNodal hnodal'
      (preimageSingularLocusBlowupEquiv hnodal H v)
    (X'.blowupComponent (preimageSingularLocusBlowupEquiv hnodal H v)).toScheme.genus L =
      (X.blowupComponent v).toScheme.genus K := by
  have := hnodal.syntomic; have hnodal' := MorphismProperty.of_isPullback H hnodal
  have := hnodal'.syntomic
  have : IsProper (X' ↘ Spec (.of L)) := MorphismProperty.of_isPullback H ‹_›
  have := X.isRegular_blowup_singularLocus hnodal; have := X'.isRegular_blowup_singularLocus hnodal'
  have := X.isCurveOver_blowupComponent_of_atWorstNodal hnodal v
  have := X'.isCurveOver_blowupComponent_of_atWorstNodal hnodal'
    (preimageSingularLocusBlowupEquiv hnodal H v)
  have : CompactSpace (X.blowupComponent v).toScheme :=
    QuasiCompact.compactSpace_of_compactSpace ((X.blowupComponent v).toScheme ↘ Spec (.of K))
  have : QuasiSeparatedSpace (X.blowupComponent v).toScheme :=
    quasiSeparatedSpace_of_quasiSeparated ((X.blowupComponent v).toScheme ↘ Spec (.of K))
  simp only [Scheme.genus_def]
  exact finrank_cohomology_trivial_eq_of_isPullback
    (isPullback_blowupComponentBaseChangeMap hnodal H v) 1

end FieldExtension

end AlgebraicGeometry.Scheme
