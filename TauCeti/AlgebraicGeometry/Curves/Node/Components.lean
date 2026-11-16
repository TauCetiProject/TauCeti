/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.FlatBaseChange
public import TauCeti.AlgebraicGeometry.Cohomology.Genus
public import TauCeti.AlgebraicGeometry.Curves.Cohomology
public import TauCeti.AlgebraicGeometry.Curves.Node.Normalization
public import TauCeti.AlgebraicGeometry.FinitelyPresentedSheaf.Basic
public import TauCeti.AlgebraicGeometry.Geometrically.Irreducible
public import TauCeti.AlgebraicGeometry.Scheme.IrreducibleComponent
import TauCeti.AlgebraicGeometry.Blowup.ExceptionalDivisor
import TauCeti.AlgebraicGeometry.Blowup.Pullback
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.SchematicDensity
import TauCeti.Topology.NoetherianSpace.IrreducibleComponents

/-!
# Irreducible components and component genera of a nodal curve

Let `X` be a nodal curve over a field `K` (`AtWorstNodalOfRelativeDimensionOne`), and let
`ν : Bl X ⟶ X` be the blowup of `X` along `Sing(X/K)`. Because `Bl X` is regular, its irreducible
components are clopen integral subschemes (`AlgebraicGeometry.Scheme.componentOpens`). Over the
dense smooth locus `U`, `ν` restricts to an isomorphism, yielding a canonical bijection
`AlgebraicGeometry.Scheme.blowupComponentEquiv` between `irreducibleComponents (Bl X)` and
`irreducibleComponents X`. Each component `v` defines a regular integral curve
`AlgebraicGeometry.Scheme.normalizedComponent` over `K`, whose geometric genus
`AlgebraicGeometry.Scheme.componentGenus` (when `X` is proper) is invariant under base change from
a separably closed field `K` to any extension field `L`.

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
/-- Two points of the blowup of a nodal curve with the same smooth image in `X` are equal. -/
theorem eq_of_blowupToBase_eq_of_mem_smoothLocus
    {y₁ y₂ : (letI := hnodal.syntomic; (X.singularLocus K).blowup)}
    (heq : letI := hnodal.syntomic
      (X.singularLocus K).blowupToBase y₁ = (X.singularLocus K).blowupToBase y₂)
    (hU : letI := hnodal.syntomic
      (X.singularLocus K).blowupToBase y₁ ∈ (X ↘ Spec (.of K)).smoothLocus) : y₁ = y₂ := by
  have := hnodal.syntomic
  let f := (X.singularLocus K).blowupToBase; let U := (X ↘ Spec (.of K)).smoothLocus
  have : IsIso (f ∣_ U) := X.isIso_blowupToBase_singularLocus_restrict_smoothLocus
  have hy₂ : y₂ ∈ f ⁻¹ᵁ U := by change f y₂ ∈ U; rwa [← heq]
  have hcomp : ((f ∣_ U) ≫ U.ι) ⟨y₁, hU⟩ = ((f ∣_ U) ≫ U.ι) ⟨y₂, hy₂⟩ := by rwa [morphismRestrict_ι]
  exact congrArg Subtype.val ((f ∣_ U).homeomorph.injective (U.ι.isOpenEmbedding.injective hcomp))

variable {X} in
/-- Every smooth point of a nodal curve has a unique preimage in the singular-locus blowup. -/
theorem existsUnique_blowupToBase_eq_of_mem_smoothLocus {x : X}
    (hx : letI := hnodal.syntomic; x ∈ (X ↘ Spec (.of K)).smoothLocus) :
    letI := hnodal.syntomic
    ∃! y : (X.singularLocus K).blowup, (X.singularLocus K).blowupToBase y = x := by
  have := hnodal.syntomic; have := X.surjective_blowupToBase_singularLocus hnodal
  obtain ⟨y, rfl⟩ := (X.singularLocus K).blowupToBase.surjective x
  exact ⟨y, rfl, fun _ hz ↦ eq_of_blowupToBase_eq_of_mem_smoothLocus hnodal hz (hz.symm ▸ hx)⟩

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
  have hEW := preimage_mem_irreducibleComponents hE W.isOpen.isOpenEmbedding_subtypeVal
    ⟨x, hxE, ⟨x, hxW⟩, rfl⟩
  obtain ⟨V₀, hV₀, hV₀ne, hV₀sub⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent _ hEW
  obtain ⟨_, ⟨w, hwV₀, rfl⟩, hzU⟩ := (X.dense_smoothLocus hnodal).inter_open_nonempty
    ((Subtype.val : W → X) '' V₀) (W.isOpen.isOpenMap_subtype_val V₀ hV₀) (hV₀ne.image _)
  exact ⟨w.1, hV₀sub hwV₀, hzU⟩

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
      hy'v (eq_of_blowupToBase_eq_of_mem_smoothLocus hnodal hy'eq.symm hyU ▸ hyv)⟩
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
      ⟨eq_of_blowupToBase_eq_of_mem_smoothLocus hnodal hy'eq.symm hyU ▸ hy'v, hyU⟩,
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
  let Bl := (X.singularLocus K).blowup
  refine ⟨fun _ hv ↦ image_blowupToBase_mem_irreducibleComponents hnodal hv,
    fun v₁ hv₁ v₂ hv₂ heq ↦ ?_, fun E hE ↦ ?_⟩
  · dsimp only at heq
    rw [← closure_preimage_inter_smoothLocus_image_blowupToBase hnodal hv₁, heq,
      closure_preimage_inter_smoothLocus_image_blowupToBase hnodal hv₂]
  · obtain ⟨x, hxE, hxU⟩ := nonempty_inter_smoothLocus_of_mem_irreducibleComponents hnodal hE
    obtain ⟨y, rfl⟩ := (X.singularLocus K).blowupToBase.surjective x; let v := Bl.componentOf y
    obtain ⟨hOopen, hOsub, hOmem⟩ :=
      isOpen_compl_image_compl_of_mem_irreducibleComponents X hnodal v.2
    exact ⟨v.1, v.2, (eq_of_mem_irreducibleComponents_of_nonempty_inter_open
      (image_blowupToBase_mem_irreducibleComponents hnodal v.2) hE hOopen hOsub
      ⟨_, hxE, hOmem y (Bl.mem_componentOf_self y) hxU⟩).symm⟩

end BlowupBijection

variable (K) in
/-- The canonical equivalence `irreducibleComponents (Bl X) ≃ irreducibleComponents X`. -/
def blowupComponentEquiv (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K))) :
    letI := hnodal.syntomic
    irreducibleComponents (X.singularLocus K).blowup ≃ irreducibleComponents X :=
  letI := hnodal.syntomic
  let ν := (X.singularLocus K).blowupToBase; let U := ((X ↘ Spec (.of K)).smoothLocus : Set X)
  { toFun v := ⟨ν '' v.1, image_blowupToBase_mem_irreducibleComponents hnodal v.2⟩
    invFun E := ⟨closure (ν ⁻¹' (E.1 ∩ U)), by
      obtain ⟨v, hv, hEv⟩ := (X.bijOn_image_blowupToBase_irreducibleComponents hnodal).surjOn E.2
      dsimp only at hEv
      rwa [← hEv, closure_preimage_inter_smoothLocus_image_blowupToBase hnodal hv]⟩
    left_inv v := Subtype.ext (closure_preimage_inter_smoothLocus_image_blowupToBase hnodal v.2)
    right_inv E := Subtype.ext <| by
      obtain ⟨v, hv, hEv⟩ := (X.bijOn_image_blowupToBase_irreducibleComponents hnodal).surjOn E.2
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

@[simp]
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
      eq_of_blowupToBase_eq_of_mem_smoothLocus hnodal hy'eq.symm hy ▸ hy'v,
    fun hyv ↦ ⟨y, hyv, rfl⟩⟩

variable {X} in
/-- Every smooth point of a nodal curve over a field belongs to a unique irreducible component. -/
theorem existsUnique_mem_irreducibleComponents_of_mem_smoothLocus {x : X}
    (hx : letI := hnodal.syntomic; x ∈ (X ↘ Spec (.of K)).smoothLocus) :
    ∃! E : irreducibleComponents X, x ∈ (E : Set X) := by
  have := hnodal.syntomic; have := X.isRegular_blowup_singularLocus hnodal
  have := X.surjective_blowupToBase_singularLocus hnodal
  let Bl := (X.singularLocus K).blowup
  obtain ⟨y, rfl⟩ := (X.singularLocus K).blowupToBase.surjective x
  refine ⟨X.blowupComponentEquiv K hnodal (Bl.componentOf y), ⟨y, Bl.mem_componentOf_self y, rfl⟩,
    fun E hE ↦ ?_⟩
  obtain ⟨v, rfl⟩ := (X.blowupComponentEquiv K hnodal).surjective E
  rw [blowupToBase_mem_coe_blowupComponentEquiv_iff_of_mem_smoothLocus hnodal hx] at hE
  exact congrArg (X.blowupComponentEquiv K hnodal) (Bl.eq_componentOf_iff.mpr hE)

end BlowupEquivProps

/-! ### Normalized component schemes and component genera -/

variable (K) in
/-- The normalized component of `X` indexed by `v : irreducibleComponents (Bl X)`. -/
def normalizedComponent (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    (v : letI := hnodal.syntomic; irreducibleComponents (X.singularLocus K).blowup) : Scheme.{u} :=
  letI := hnodal.syntomic; haveI := X.isRegular_blowup_singularLocus hnodal
  ((X.singularLocus K).blowup.componentOpens v).toScheme

variable (K) in
/-- The clopen inclusion of a normalized component into `(X.singularLocus K).blowup`. -/
def normalizedComponentι (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    (v : letI := hnodal.syntomic; irreducibleComponents (X.singularLocus K).blowup) :
    letI := hnodal.syntomic; X.normalizedComponent K hnodal v ⟶ (X.singularLocus K).blowup :=
  letI := hnodal.syntomic; haveI := X.isRegular_blowup_singularLocus hnodal
  ((X.singularLocus K).blowup.componentOpens v).ι

variable (K) in
/-- The finite morphism from a normalized component `C_v` to the nodal curve `X`. -/
def normalizedComponentToCurve (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    (v : letI := hnodal.syntomic; irreducibleComponents (X.singularLocus K).blowup) :
    X.normalizedComponent K hnodal v ⟶ X :=
  letI := hnodal.syntomic; X.normalizedComponentι K hnodal v ≫ (X.singularLocus K).blowupToBase

section NormalizedComponentProps

variable (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
  (v : letI := hnodal.syntomic; irreducibleComponents (X.singularLocus K).blowup)

instance isOpenImmersion_normalizedComponentι :
    letI := hnodal.syntomic; IsOpenImmersion (X.normalizedComponentι K hnodal v) := by
  have := hnodal.syntomic; have := X.isRegular_blowup_singularLocus hnodal
  exact inferInstanceAs (IsOpenImmersion ((X.singularLocus K).blowup.componentOpens v).ι)

instance isClosedImmersion_normalizedComponentι :
    letI := hnodal.syntomic; IsClosedImmersion (X.normalizedComponentι K hnodal v) := by
  have := hnodal.syntomic; have := X.isRegular_blowup_singularLocus hnodal
  exact inferInstanceAs (IsClosedImmersion ((X.singularLocus K).blowup.componentOpens v).ι)

@[simp]
theorem range_normalizedComponentι :
    letI := hnodal.syntomic
    Set.range (X.normalizedComponentι K hnodal v) = (v : Set (X.singularLocus K).blowup) := by
  have := hnodal.syntomic; have := X.isRegular_blowup_singularLocus hnodal
  exact ((X.singularLocus K).blowup.componentOpens v).range_ι.trans
    ((X.singularLocus K).blowup.coe_componentOpens v)

theorem normalizedComponentToCurve_def :
    letI := hnodal.syntomic
    X.normalizedComponentToCurve K hnodal v =
      X.normalizedComponentι K hnodal v ≫ (X.singularLocus K).blowupToBase := (rfl)

instance isFinite_normalizedComponentToCurve :
    IsFinite (X.normalizedComponentToCurve K hnodal v) := by
  have := hnodal.syntomic; have := X.isFinite_blowupToBase_singularLocus hnodal
  exact inferInstanceAs (IsFinite (X.normalizedComponentι K hnodal v ≫ _))

@[simp]
theorem range_normalizedComponentToCurve :
    Set.range (X.normalizedComponentToCurve K hnodal v) =
      ((X.blowupComponentEquiv K hnodal v : irreducibleComponents X) : Set X) := by
  have := hnodal.syntomic
  change Set.range (X.normalizedComponentι K hnodal v ≫ (X.singularLocus K).blowupToBase) = _
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, X.range_normalizedComponentι hnodal v,
    X.coe_blowupComponentEquiv hnodal v]

instance instOverNormalizedComponent : (X.normalizedComponent K hnodal v).Over (Spec (.of K)) :=
  ⟨X.normalizedComponentToCurve K hnodal v ≫ (X ↘ Spec (.of K))⟩

theorem normalizedComponent_over_hom :
    (X.normalizedComponent K hnodal v ↘ Spec (.of K)) =
      X.normalizedComponentToCurve K hnodal v ≫ (X ↘ Spec (.of K)) := (rfl)

instance isOver_normalizedComponentToCurve :
    (X.normalizedComponentToCurve K hnodal v).IsOver (Spec (.of K)) := ⟨rfl⟩

instance locallyOfFinitePresentation_normalizedComponent_over :
    LocallyOfFinitePresentation (X.normalizedComponent K hnodal v ↘ Spec (.of K)) := by
  have := hnodal.syntomic; rw [normalizedComponent_over_hom]; infer_instance

instance isIntegral_normalizedComponent : IsIntegral (X.normalizedComponent K hnodal v) := by
  have := hnodal.syntomic; have := X.isRegular_blowup_singularLocus hnodal
  exact inferInstanceAs (IsIntegral ((X.singularLocus K).blowup.componentOpens v).toScheme)

instance isRegular_normalizedComponent : IsRegular (X.normalizedComponent K hnodal v) := by
  have := hnodal.syntomic; have := X.isRegular_blowup_singularLocus hnodal
  exact IsRegular.of_isOpenImmersion (X.normalizedComponentι K hnodal v)

/-- Every normalized component of a nodal curve over a field has Krull dimension one. -/
theorem topologicalKrullDim_normalizedComponent :
    topologicalKrullDim (X.normalizedComponent K hnodal v) = 1 := by
  have := hnodal.syntomic; have := X.isRegular_blowup_singularLocus hnodal
  have := X.isFinite_blowupToBase_singularLocus hnodal
  have hpureX : IsPureDimensional 1 X :=
    ((pureRelativeDimension_iff_of_field (X ↘ Spec (.of K))).mp inferInstance).2
  let Bl := (X.singularLocus K).blowup; let ν := (X.singularLocus K).blowupToBase
  let U := (X ↘ Spec (.of K)).smoothLocus; let W : Bl.Opens := Bl.componentOpens v ⊓ (ν ⁻¹ᵁ U)
  obtain ⟨y, hyv, hyU⟩ :=
    nonempty_inter_preimage_smoothLocus_of_mem_irreducibleComponents hnodal v.2
  have : Nonempty W.toScheme := ⟨⟨y, Bl.mem_componentOpens.mpr hyv, hyU⟩⟩
  let j : W.toScheme ⟶ X.normalizedComponent K hnodal v := Bl.homOfLE inf_le_left
  have hj : IsOpenImmersion j :=
    inferInstanceAs (IsOpenImmersion (Bl.homOfLE (inf_le_left : W ≤ Bl.componentOpens v)))
  have : IrreducibleSpace W.toScheme := j.isOpenEmbedding.irreducibleSpace
  have : IsIso (ν ∣_ U) := X.isIso_blowupToBase_singularLocus_restrict_smoothLocus
  let φ : W.toScheme ⟶ X := Bl.homOfLE inf_le_right ≫ (ν ∣_ U) ≫ U.ι
  have hpureW : IsPureDimensional 1 W.toScheme :=
    hpureX.of_isOpenEmbedding (fun Z hZ V hV hZV ↦
      topologicalKrullDim_inter_eq_of_locallyOfFiniteType (X ↘ Spec (.of K)) hZ.1
        (isClosed_of_mem_irreducibleComponents Z hZ) hV hZV) φ.isOpenEmbedding
  have hdimW : topologicalKrullDim W.toScheme = 1 := by
    rw [(Homeomorph.Set.univ W.toScheme).symm.isHomeomorph.topologicalKrullDim_eq]
    exact (isPureDimensional_iff.mp hpureW) Set.univ
      ⟨IrreducibleSpace.isIrreducible_univ _, fun _ _ _ ↦ subset_univ _⟩
  exact (topologicalKrullDim_eq_of_isOpenEmbedding_of_locallyOfFiniteType
    (X.normalizedComponent K hnodal v ↘ Spec (.of K)) j.isOpenEmbedding).symm.trans hdimW

/-- When `X` is proper over `K`, each normalized component is a proper integral curve over `K`. -/
instance isCurveOver_normalizedComponent [IsProper (X ↘ Spec (.of K))] :
    (X.normalizedComponent K hnodal v).IsCurveOver K where
  toIsProper := by rw [normalizedComponent_over_hom]; infer_instance
  topologicalKrullDim_eq_one := X.topologicalKrullDim_normalizedComponent hnodal v

/-- Coherent cohomology on a normalized component of a proper nodal curve is finite-dimensional. -/
theorem finiteDimensional_cohomology_normalizedComponent [IsProper (X ↘ Spec (.of K))]
    (M : (X.normalizedComponent K hnodal v).Modules) [M.IsQuasicoherent] [M.IsFiniteType] (n : ℕ) :
    FiniteDimensional K (Scheme.Modules.Cohomology M n) :=
  Scheme.Modules.finiteDimensional_cohomology_of_isCurveOver K M n

/-- Invertible sheaves on a normalized component have finite-dimensional cohomology. -/
theorem finiteDimensional_cohomology_invertibleSheaf_normalizedComponent
    [IsProper (X ↘ Spec (.of K))]
    (L : InvertibleSheaf (X.normalizedComponent K hnodal v)) (n : ℕ) :
    FiniteDimensional K (Scheme.Modules.Cohomology L.obj n) :=
  haveI : L.obj.IsFinitePresentation := ((InvertibleSheaf.toFinitelyPresented _).obj L).property
  X.finiteDimensional_cohomology_normalizedComponent hnodal v L.obj n

end NormalizedComponentProps

variable (K) in
/-- The geometric genus `dim_K H¹(C_v, 𝒪_{C_v})` of the normalized component `C_v`. -/
def componentGenus [IsProper (X ↘ Spec (.of K))]
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    (v : letI := hnodal.syntomic; irreducibleComponents (X.singularLocus K).blowup) : ℕ :=
  haveI := X.finiteDimensional_cohomology_invertibleSheaf_normalizedComponent hnodal v
    (InvertibleSheaf.trivial _) 1
  (X.normalizedComponent K hnodal v).genus K

@[simp]
theorem componentGenus_def [IsProper (X ↘ Spec (.of K))]
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    (v : letI := hnodal.syntomic; irreducibleComponents (X.singularLocus K).blowup) :
    haveI := X.finiteDimensional_cohomology_invertibleSheaf_normalizedComponent hnodal v
      (InvertibleSheaf.trivial _) 1
    X.componentGenus K hnodal v = (X.normalizedComponent K hnodal v).genus K := (rfl)

end Components

/-! ### Base change of the singular-locus blowup and component genera -/

section BaseChange

variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']
  {X X' : Scheme.{u}} [X.Over (Spec (.of R))] [X'.Over (Spec (.of R'))] {g : X' ⟶ X}
  [Flat (X ↘ Spec (.of R))] [LocallyOfFinitePresentation (X ↘ Spec (.of R))]
  [PureRelativeDimension 1 (X ↘ Spec (.of R))]
  [Flat (X' ↘ Spec (.of R'))] [LocallyOfFinitePresentation (X' ↘ Spec (.of R'))]
  [PureRelativeDimension 1 (X' ↘ Spec (.of R'))]
  (H : IsPullback g (X' ↘ Spec (.of R')) (X ↘ Spec (.of R))
    (Spec.map (CommRingCat.ofHom (algebraMap R R'))))

/-- Induced morphism `Bl_{Sing(X'/R')} X' ⟶ Bl_{Sing(X/R)} X` under base change of `X`. -/
def singularLocusBlowupMap : (X'.singularLocus R').blowup ⟶ (X.singularLocus R).blowup :=
  (X.singularLocus R).blowupLift ((X'.singularLocus R').blowupToBase ≫ g) (by
    rw [IdealSheafData.comap_comp, ← Scheme.singularLocus_eq_comap_of_isPullback H]
    exact (X'.singularLocus R').isEffectiveCartier_comap_blowupToBase)

@[reassoc (attr := simp)]
theorem singularLocusBlowupMap_blowupToBase :
    singularLocusBlowupMap H ≫ (X.singularLocus R).blowupToBase =
      (X'.singularLocus R').blowupToBase ≫ g :=
  (X.singularLocus R).blowupLift_blowupToBase _ _

/-- The singular-locus blowup commutes with flat base change. -/
theorem isPullback_singularLocusBlowupMap [Module.Flat R R'] :
    IsPullback (X'.singularLocus R').blowupToBase (singularLocusBlowupMap H)
      g (X.singularLocus R).blowupToBase := by
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap R R'))) := by
    rw [Flat.SpecMap_iff, CommRingCat.hom_ofHom, RingHom.flat_algebraMap_iff]; infer_instance
  have : Flat g := MorphismProperty.of_isPullback H.flip ‹_›
  suffices ∀ (J : X'.IdealSheafData) (_ : J = (X.singularLocus R).comap g)
      (hcart : ((X.singularLocus R).comap (J.blowupToBase ≫ g)).IsEffectiveCartier),
      IsPullback J.blowupToBase ((X.singularLocus R).blowupLift (J.blowupToBase ≫ g) hcart)
        g (X.singularLocus R).blowupToBase from
    this _ (Scheme.singularLocus_eq_comap_of_isPullback H) _
  rintro J rfl hcart
  rw [(X.singularLocus R).eq_blowupMap g ((X.singularLocus R).blowupLift_blowupToBase _ _)]
  exact (X.singularLocus R).isPullback_blowupMap_of_flat g

end BaseChange

section FieldExtension

variable {K L : Type u} [Field K] [IsSepClosed K] [Field L] [Algebra K L]
  {X X' : Scheme.{u}} [X.Over (Spec (.of K))] [X'.Over (Spec (.of L))] {g : X' ⟶ X}
  (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
  (H : IsPullback g (X' ↘ Spec (.of L)) (X ↘ Spec (.of K)) (Spec.algebraMap K L))

/-- Over a separably closed field `K`, base-changing `X` to `L / K` bijects the irreducible
components of `Bl X` and `Bl X'`. -/
theorem bijOn_preimage_singularLocusBlowupMap_irreducibleComponents :
    letI := hnodal.syntomic; letI := (MorphismProperty.of_isPullback H hnodal).syntomic
    BijOn (singularLocusBlowupMap H ⁻¹' ·)
      (irreducibleComponents (X.singularLocus K).blowup)
      (irreducibleComponents (X'.singularLocus L).blowup) :=
  letI := hnodal.syntomic; letI := (MorphismProperty.of_isPullback H hnodal).syntomic
  bijOn_preimage_irreducibleComponents_of_isSepClosed
    ((isPullback_singularLocusBlowupMap H).flip.paste_vert H)

/-- Component genera are invariant under extensions of a separably closed base field. -/
theorem componentGenus_preimage_singularLocusBlowupMap [IsProper (X ↘ Spec (.of K))]
    (v : letI := hnodal.syntomic; irreducibleComponents (X.singularLocus K).blowup) :
    letI := hnodal.syntomic
    haveI hnodal' := MorphismProperty.of_isPullback H hnodal; letI := hnodal'.syntomic
    haveI : IsProper (X' ↘ Spec (.of L)) := MorphismProperty.of_isPullback H ‹_›
    X'.componentGenus L hnodal'
        ⟨singularLocusBlowupMap H ⁻¹' v.1,
          (bijOn_preimage_singularLocusBlowupMap_irreducibleComponents hnodal H).mapsTo v.2⟩ =
      X.componentGenus K hnodal v := by
  have := hnodal.syntomic; have hnodal' := MorphismProperty.of_isPullback H hnodal
  have := hnodal'.syntomic
  have : IsProper (X' ↘ Spec (.of L)) := MorphismProperty.of_isPullback H ‹_›
  have := X.isRegular_blowup_singularLocus hnodal; have := X'.isRegular_blowup_singularLocus hnodal'
  let fBl := singularLocusBlowupMap H
  let v' : irreducibleComponents (X'.singularLocus L).blowup :=
    ⟨fBl ⁻¹' v.1, (bijOn_preimage_singularLocusBlowupMap_irreducibleComponents hnodal H).mapsTo v.2⟩
  have hopen : (X'.singularLocus L).blowup.componentOpens v' =
      fBl ⁻¹ᵁ (X.singularLocus K).blowup.componentOpens v := Opens.ext (by simp [v'])
  let fComp : X'.normalizedComponent L hnodal' v' ⟶ X.normalizedComponent K hnodal v :=
    ((X'.singularLocus L).blowup.isoOfEq hopen).hom ≫
      (fBl ∣_ (X.singularLocus K).blowup.componentOpens v)
  have Hopen : IsPullback fComp (X'.normalizedComponentι L hnodal' v')
      (X.normalizedComponentι K hnodal v) fBl := by
    dsimp only [fComp, normalizedComponent, normalizedComponentι]
    have hsq1 : IsPullback ((X'.singularLocus L).blowup.isoOfEq hopen).hom
        ((X'.singularLocus L).blowup.componentOpens v').ι
        (fBl ⁻¹ᵁ (X.singularLocus K).blowup.componentOpens v).ι (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, Scheme.isoOfEq_hom_ι]⟩
    simpa only [Category.id_comp] using hsq1.paste_horiz
      (isPullback_morphismRestrict fBl ((X.singularLocus K).blowup.componentOpens v))
  have Hcomp : IsPullback fComp (X'.normalizedComponent L hnodal' v' ↘ Spec (.of L))
      (X.normalizedComponent K hnodal v ↘ Spec (.of K))
      (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
    simpa only [normalizedComponent_over_hom, normalizedComponentToCurve, Category.assoc] using
      Hopen.paste_vert ((isPullback_singularLocusBlowupMap H).flip.paste_vert H)
  have := X.finiteDimensional_cohomology_invertibleSheaf_normalizedComponent hnodal v
    (InvertibleSheaf.trivial _) 1
  have := X'.finiteDimensional_cohomology_invertibleSheaf_normalizedComponent hnodal' v'
    (InvertibleSheaf.trivial _) 1
  have : CompactSpace (X.normalizedComponent K hnodal v) :=
    QuasiCompact.compactSpace_of_compactSpace (X.normalizedComponent K hnodal v ↘ Spec (.of K))
  have : QuasiSeparatedSpace (X.normalizedComponent K hnodal v) :=
    quasiSeparatedSpace_of_quasiSeparated (X.normalizedComponent K hnodal v ↘ Spec (.of K))
  simp only [componentGenus_def, Scheme.genus_def]
  exact finrank_cohomology_trivial_eq_of_isPullback Hcomp 1

end FieldExtension

end AlgebraicGeometry.Scheme
