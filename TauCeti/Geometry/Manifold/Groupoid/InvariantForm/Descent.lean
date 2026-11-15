/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Category.InvariantForm
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.LocalDiffeomorph
public import TauCeti.Topology.CategoryTheory.Groupoid.Basic

/-!
# Descent of invariant forms along étale refinements

Let `Φ : C ⥤ D` be a functor into a smooth groupoid `D` whose source and target are local
diffeomorphisms, with `Φ.obj` a local diffeomorphism and `Φ.toPrefunctor.mapTotal` smooth.
When `Φ` is essentially surjective, `Φ` pulls invariant forms back injectively
(`CategoryTheory.Functor.invariantFormsPullback_injective`); this needs neither fullness of `Φ` nor
invertibility of arrows.

When `D` is also a topological groupoid, `Φ` is full and essentially surjective, and the source of
`C` is a local diffeomorphism, pullback along `Φ` is a linear equivalence on invariant forms
(`CategoryTheory.Functor.invariantFormsEquiv`). Local inverses of `D`'s target and `Φ.obj` lift
objects smoothly to `C`, and any two local lifts are joined near a point by a smooth family of
arrows in `C` via fullness and the local-diffeomorphism property of source maps. The equivalence
commutes with the exterior derivative and wedge products, and depends only on the smooth
natural-transformation class of `Φ`.

## References

* A. Adem, J. Leida and Y. Ruan, *Orbifolds and stringy topology*, Chapter 2.
* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Sections 2–3.
-/

public noncomputable section

open Bundle CategoryTheory Filter Set Topology
open scoped Manifold ContDiff

namespace CategoryTheory.Functor

open TauCeti

private theorem eventuallyEq_of_isLocalDiffeomorph {M N P EM HM EN HN : Type*} [TopologicalSpace M]
    [NormedAddCommGroup EM] [NormedSpace ℝ EM] [TopologicalSpace HM]
    [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
    [TopologicalSpace N] [TopologicalSpace P] [ChartedSpace HM N] [ChartedSpace HN P]
    {IM : ModelWithCorners ℝ EM HM} {IN : ModelWithCorners ℝ EN HN}
    {f : N → P} (hf : IsLocalDiffeomorph IM IN ∞ f) {g₁ g₂ : M → N} {y₀ : M}
    (hg₁ : ContinuousAt g₁ y₀) (hg₂ : ContinuousAt g₂ y₀)
    (h0 : g₁ y₀ = g₂ y₀) (hf12 : ∀ᶠ z in 𝓝 y₀, f (g₁ z) = f (g₂ z)) : g₁ =ᶠ[𝓝 y₀] g₂ := by
  have ht₁ := hg₁.preimage_mem_nhds ((hf (g₁ y₀)).localInverse.open_target.mem_nhds
    (hf (g₁ y₀)).localInverse_mem_target)
  have ht₂ := hg₂.preimage_mem_nhds ((hf (g₁ y₀)).localInverse.open_target.mem_nhds
    (h0 ▸ (hf (g₁ y₀)).localInverse_mem_target))
  filter_upwards [ht₁, ht₂, hf12] with z hz₁ hz₂ hfz
  rw [← (hf (g₁ y₀)).localInverse_left_inv hz₁, hfz, (hf (g₁ y₀)).localInverse_left_inv hz₂]

variable {E H A K E' H' A' K' C D : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup A] [NormedSpace ℝ A] [TopologicalSpace K]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  [NormedAddCommGroup A'] [NormedSpace ℝ A'] [TopologicalSpace K']
  [Category C] [Category D] [TopologicalSpace C] [TopologicalSpace D]
  [TopologicalSpace (Quiver.Total D)]
  [ChartedSpace H C] [ChartedSpace H' D] [ChartedSpace K' (Quiver.Total D)]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ A K}
  {I' : ModelWithCorners ℝ E' H'} {J' : ModelWithCorners ℝ A' K'}

section Injective

variable [TopologicalSpace (Quiver.Total C)] [ChartedSpace K (Quiver.Total C)]
  [IsManifold I ∞ C] [IsManifold J ∞ (Quiver.Total C)]
  [IsManifold I' ∞ D] [IsManifold J' ∞ (Quiver.Total D)]
  {hs : ContMDiff J I ∞ (Quiver.Total.left : Quiver.Total C → C)}
  {ht : ContMDiff J I ∞ (Quiver.Total.right : Quiver.Total C → C)}
  {hs' : ContMDiff J' I' ∞ (Quiver.Total.left : Quiver.Total D → D)}
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {k : ℕ}

/-- Pullback of invariant forms along an essentially surjective functor is injective whenever the
object map and the target map of the codomain are smooth local diffeomorphisms. -/
theorem invariantFormsPullback_injective (Φ : C ⥤ D) [Φ.EssSurj]
    (hΦ : IsLocalDiffeomorph I I' ∞ Φ.obj) (hΦ₁ : ContMDiff J J' ∞ Φ.toPrefunctor.mapTotal)
    (ht' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.right : Quiver.Total D → D)) :
    Function.Injective (Φ.toPrefunctor.invariantFormsPullback (hs := hs) (ht := ht) (hs' := hs')
      (ht' := ht'.contMDiff) (V := V) (k := k) hΦ.contMDiff hΦ₁) := by
  rw [injective_iff_map_eq_zero]
  intro φ hφ
  refine Subtype.ext <| Subtype.ext <| funext fun y ↦ ?_
  let a : Quiver.Total D := ⟨Φ.obj (Φ.objPreimage y), y, (Φ.objObjPreimageIso y).hom⟩
  have hΦx : mpullback (F := V) (k := k) I I' Φ.obj φ.1.1 (Φ.objPreimage y) = 0 := by
    have h0 := congrArg Subtype.val hφ
    rw [Prefunctor.coe_invariantFormsPullback, Submodule.coe_zero] at h0
    have h0x := congrArg (fun η : SmoothForm I C V k ↦ η.1 (Φ.objPreimage y)) h0
    rwa [SmoothForm.coe_mpullback, Submodule.coe_zero, Pi.zero_apply] at h0x
  have hleft : (φ.1.1 : RoughForm I' D V k) a.left = 0 :=
    ((hΦ (Φ.objPreimage y)).mpullback_apply_eq_zero_iff (by simp)).mp hΦx
  have hinv := congrArg (fun η : SmoothForm J' (Quiver.Total D) V k ↦ η.1 a)
    (TauCeti.Quiver.mem_invariantForms_iff.mp φ.2)
  simp only [SmoothForm.coe_mpullback] at hinv
  exact ((ht' a).mpullback_apply_eq_zero_iff (by simp)).mp
    (hinv.symm.trans (mpullback_apply_eq_zero hleft))

end Injective

section LocalLifts

private structure IsLocalLiftAt (Φ : C ⥤ D) (y₀ : D) (ℓ : D → C) (τ : D → Quiver.Total D) :
    Prop where
  contMDiffAt : ContMDiffAt I' I ∞ ℓ y₀
  continuousAt : ContinuousAt τ y₀
  eventually_left : ∀ᶠ z in 𝓝 y₀, (τ z).left = Φ.obj (ℓ z)
  eventually_right : ∀ᶠ z in 𝓝 y₀, (τ z).right = z

private def arrowLocalLift (Φ : C ⥤ D)
    (ht' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.right : Quiver.Total D → D))
    (hΦ : IsLocalDiffeomorph I I' ∞ Φ.obj) (x : C) (a : Quiver.Total D) : D → C :=
  (hΦ x).localInverse ∘ Quiver.Total.left ∘ (ht' a).localInverse

private def arrowLocalLiftOpen (Φ : C ⥤ D)
    (ht' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.right : Quiver.Total D → D))
    (hΦ : IsLocalDiffeomorph I I' ∞ Φ.obj) (x : C) (a : Quiver.Total D) : Set D :=
  (ht' a).localInverse.source ∩
    (Quiver.Total.left ∘ (ht' a).localInverse) ⁻¹' (hΦ x).localInverse.source

private theorem isOpen_arrowLocalLiftOpen (Φ : C ⥤ D)
    (hs' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.left : Quiver.Total D → D))
    (ht' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.right : Quiver.Total D → D))
    (hΦ : IsLocalDiffeomorph I I' ∞ Φ.obj) (x : C) (a : Quiver.Total D) :
    IsOpen (arrowLocalLiftOpen Φ ht' hΦ x a) :=
  (hs'.contMDiff.continuous.comp_continuousOn
    (ht' a).contMDiffOn_localInverse.continuousOn).isOpen_inter_preimage
    (ht' a).localInverse_open_source (hΦ x).localInverse_open_source

private theorem mem_arrowLocalLiftOpen (Φ : C ⥤ D)
    (ht' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.right : Quiver.Total D → D))
    (hΦ : IsLocalDiffeomorph I I' ∞ Φ.obj) (x : C) (a : Quiver.Total D)
    (ha : a.left = Φ.obj x) : a.right ∈ arrowLocalLiftOpen Φ ht' hΦ x a := by
  refine ⟨(ht' a).localInverse_mem_source, ?_⟩
  change ((ht' a).localInverse a.right).left ∈ (hΦ x).localInverse.source
  rw [(ht' a).localInverse_left_inv (ht' a).localInverse_mem_target, ha]
  exact (hΦ x).localInverse_mem_source

private theorem isLocalLiftAt_arrowLocalLift (Φ : C ⥤ D)
    (hs' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.left : Quiver.Total D → D))
    (ht' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.right : Quiver.Total D → D))
    (hΦ : IsLocalDiffeomorph I I' ∞ Φ.obj) (x : C) (a : Quiver.Total D)
    {y : D} (hy : y ∈ arrowLocalLiftOpen Φ ht' hΦ x a) :
    IsLocalLiftAt (I := I) (I' := I') Φ y (arrowLocalLift Φ ht' hΦ x a) (ht' a).localInverse := by
  have hopen := isOpen_arrowLocalLiftOpen Φ hs' ht' hΦ x a
  have hτ : ContMDiffAt I' J' ∞ (ht' a).localInverse y :=
    (ht' a).contMDiffOn_localInverse.contMDiffAt ((ht' a).localInverse_open_source.mem_nhds hy.1)
  have hℓ : ContMDiffAt I' I ∞ (arrowLocalLift Φ ht' hΦ x a) y :=
    ((hΦ x).contMDiffOn_localInverse.contMDiffAt
      ((hΦ x).localInverse_open_source.mem_nhds hy.2)).comp y (hs'.contMDiff.contMDiffAt.comp y hτ)
  exact ⟨hℓ, hτ.continuousAt,
    eventually_of_mem (hopen.mem_nhds hy) fun _ hz ↦ ((hΦ x).localInverse_right_inv hz.2).symm,
    eventually_of_mem (hopen.mem_nhds hy) fun _ hz ↦ (ht' a).localInverse_right_inv hz.1⟩

end LocalLifts

section Descent

variable [IsGroupoid D] [TopologicalSpace (Quiver.Total C)] [TauCeti.IsTopologicalGroupoid D]
  [ChartedSpace K (Quiver.Total C)]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {k : ℕ}

private theorem exists_smooth_connecting_arrow (Φ : C ⥤ D) [Φ.Full]
    (hs : IsLocalDiffeomorph J I ∞ (Quiver.Total.left : Quiver.Total C → C))
    (ht : ContMDiff J I ∞ (Quiver.Total.right : Quiver.Total C → C))
    (hs' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.left : Quiver.Total D → D))
    (hΦ : IsLocalDiffeomorph I I' ∞ Φ.obj) (hΦ₁ : ContMDiff J J' ∞ Φ.toPrefunctor.mapTotal)
    {y₀ : D} {ℓ₁ ℓ₂ : D → C} {τ₁ τ₂ : D → Quiver.Total D}
    (h₁ : IsLocalLiftAt (I := I) (I' := I') Φ y₀ ℓ₁ τ₁)
    (h₂ : IsLocalLiftAt (I := I) (I' := I') Φ y₀ ℓ₂ τ₂) :
    ∃ σ : D → Quiver.Total C, ContMDiffAt I' J ∞ σ y₀ ∧
      (Quiver.Total.left ∘ σ =ᶠ[𝓝 y₀] ℓ₁) ∧ (Quiver.Total.right ∘ σ =ᶠ[𝓝 y₀] ℓ₂) := by
  obtain ⟨U, hUsub, hUo, hy₀U⟩ := mem_nhds_iff.mp
    (h₁.eventually_left.and (h₂.eventually_left.and (h₁.eventually_right.and h₂.eventually_right)))
  let pairU : U → {p : Quiver.Total D × Quiver.Total D // p.1.right = p.2.left} := fun z ↦
    ⟨(τ₁ z, ⟨(τ₂ z).right, (τ₂ z).left, CategoryTheory.inv (τ₂ z).hom⟩),
      (hUsub z.2).2.2.1.trans (hUsub z.2).2.2.2.symm⟩
  let δU : U → Quiver.Total D := fun z ↦ (pairU z).1.1.comp (pairU z).1.2 (pairU z).2
  let y₀' : U := ⟨y₀, hy₀U⟩
  have hpairU : ContinuousAt pairU y₀' := by
    rw [ContinuousAt, tendsto_subtype_rng]
    exact (h₁.continuousAt.comp continuous_subtype_val.continuousAt).prodMk
      (IsTopologicalGroupoid.continuous_inverse.continuousAt.comp
        (h₂.continuousAt.comp continuous_subtype_val.continuousAt))
  have hδU_cont : ContinuousAt δU y₀' :=
    IsTopologicalGroupoid.continuous_comp.continuousAt.comp hpairU
  have hδl : (δU y₀').left = Φ.obj (ℓ₁ y₀) := (Quiver.Total.comp_left _ _ _).trans (hUsub hy₀U).1
  have hδr : (δU y₀').right = Φ.obj (ℓ₂ y₀) :=
    (Quiver.Total.comp_right _ _ _).trans (hUsub hy₀U).2.1
  let b₀ : Quiver.Total C := ⟨ℓ₁ y₀, ℓ₂ y₀, Φ.preimage (Quiver.homOfEq (δU y₀').hom hδl hδr)⟩
  let σ : D → Quiver.Total C := (hs b₀).localInverse ∘ ℓ₁
  have hσ : ContMDiffAt I' J ∞ σ y₀ := (hs b₀).contMDiffAt_localInverse.comp y₀ h₁.contMDiffAt
  have hσ_left : Quiver.Total.left ∘ σ =ᶠ[𝓝 y₀] ℓ₁ :=
    h₁.contMDiffAt.continuousAt.tendsto.eventually (hs b₀).localInverse_eventuallyEq_right
  have hσ0 : σ y₀ = b₀ := (hs b₀).localInverse_left_inv (hs b₀).localInverse_mem_target
  have hmap0 : Φ.toPrefunctor.mapTotal (σ y₀) = δU y₀' := by
    rw [hσ0]
    change ⟨_, _, Φ.map (Φ.preimage (Quiver.homOfEq (δU y₀').hom hδl hδr))⟩ = δU y₀'
    rw [Φ.map_preimage, Quiver.Total.mk_homOfEq]
  have hmapU : (fun z : U ↦ Φ.toPrefunctor.mapTotal (σ z)) =ᶠ[𝓝 y₀'] δU :=
    eventuallyEq_of_isLocalDiffeomorph hs'
      (ContinuousAt.comp (g := Φ.toPrefunctor.mapTotal ∘ σ) (f := (Subtype.val : U → D))
        (hΦ₁.contMDiffAt.comp y₀ hσ).continuousAt continuous_subtype_val.continuousAt)
      hδU_cont hmap0 ((hσ_left.comp_tendsto continuous_subtype_val.continuousAt.tendsto).mono
        fun z hz ↦ by
          change Φ.obj ((Quiver.Total.left ∘ σ) z) = (δU z).left
          change (Quiver.Total.left ∘ σ) z = ℓ₁ z at hz
          rw [hz, Quiver.Total.comp_left, (hUsub z.2).1])
  have hΦright : ∀ᶠ z in 𝓝 y₀, Φ.obj (σ z).right = Φ.obj (ℓ₂ z) := by
    have hU' : ∀ᶠ z : U in 𝓝 y₀', Φ.obj (σ z).right = Φ.obj (ℓ₂ z) :=
      hmapU.mono fun z hz ↦ (congrArg Quiver.Total.right hz).trans
        ((Quiver.Total.comp_right _ _ _).trans (hUsub z.2).2.1)
    obtain ⟨V', hVy₀, hVsub⟩ := Filter.mem_comap.mp (nhds_induced (Subtype.val : U → D) y₀' ▸ hU')
    filter_upwards [hVy₀, hUo.mem_nhds hy₀U] with z hzV hzU using
      hVsub (show (⟨z, hzU⟩ : U) ∈ Subtype.val ⁻¹' V' from hzV)
  exact ⟨σ, hσ, hσ_left, eventuallyEq_of_isLocalDiffeomorph hΦ
    (ht.contMDiffAt.comp y₀ hσ).continuousAt h₂.contMDiffAt.continuousAt
    (congrArg Quiver.Total.right hσ0) hΦright⟩

omit [TopologicalSpace (Quiver.Total C)] in
private theorem isLocalLiftAt_comp_target_localInverse (Φ : C ⥤ D)
    (hs' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.left : Quiver.Total D → D))
    (ht' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.right : Quiver.Total D → D))
    (hΦ : IsLocalDiffeomorph I I' ∞ Φ.obj) (x₁ : C) (a₁ a : Quiver.Total D)
    (ha₁ : a₁.left = Φ.obj x₁) (ha₁r : a₁.right = a.left) :
    ∃ τ₂ : D → Quiver.Total D, IsLocalLiftAt (I := I) (I' := I') Φ a.right
      (arrowLocalLift Φ ht' hΦ x₁ a₁ ∘ Quiver.Total.left ∘ (ht' a).localInverse) τ₂ := by
  classical
  have hmem₁ : a.left ∈ arrowLocalLiftOpen Φ ht' hΦ x₁ a₁ :=
    ha₁r ▸ mem_arrowLocalLiftOpen Φ ht' hΦ x₁ a₁ ha₁
  have hlift₁ := isLocalLiftAt_arrowLocalLift (I := I) (I' := I') Φ hs' ht' hΦ x₁ a₁ hmem₁
  have hta_eq : ((ht' a).localInverse a.right).left = a.left := by
    rw [(ht' a).localInverse_left_inv (ht' a).localInverse_mem_target]
  have hsub : ContMDiffAt I' I' ∞ (Quiver.Total.left ∘ (ht' a).localInverse) a.right :=
    hs'.contMDiff.contMDiffAt.comp a.right (ht' a).contMDiffAt_localInverse
  obtain ⟨W, hWsub, hWo, haW⟩ := mem_nhds_iff.mp
    ((hsub.continuousAt.tendsto.eventually
      (hta_eq ▸ (isOpen_arrowLocalLiftOpen Φ hs' ht' hΦ x₁ a₁).mem_nhds hmem₁)).and
      ((ht' a).localInverse_open_source.mem_nhds (ht' a).localInverse_mem_source))
  let pairW : W → {p : Quiver.Total D × Quiver.Total D // p.1.right = p.2.left} := fun w ↦
    ⟨((ht' a₁).localInverse ((ht' a).localInverse w).left, (ht' a).localInverse w),
      (ht' a₁).localInverse_right_inv (hWsub w.2).1.1⟩
  let τW : D → Quiver.Total D := fun z ↦
    if hz : z ∈ W then (pairW ⟨z, hz⟩).1.1.comp (pairW ⟨z, hz⟩).1.2 (pairW ⟨z, hz⟩).2 else a
  have hτW_sub : ContinuousAt (τW ∘ (Subtype.val : W → D)) ⟨a.right, haW⟩ := by
    have heq : τW ∘ (Subtype.val : W → D) =
        fun w : W ↦ (pairW w).1.1.comp (pairW w).1.2 (pairW w).2 :=
      funext fun w ↦ by simp only [Function.comp_apply, τW, w.2, ↓reduceDIte]
    rw [heq]
    have hta_w : ContinuousAt (fun w : W ↦ (ht' a).localInverse w) ⟨a.right, haW⟩ :=
      ContinuousAt.comp (g := (ht' a).localInverse) (f := (Subtype.val : W → D))
        (ht' a).contMDiffAt_localInverse.continuousAt continuous_subtype_val.continuousAt
    have hta₁_at : ContinuousAt (ht' a₁).localInverse ((ht' a).localInverse a.right).left :=
      (ht' a₁).contMDiffOn_localInverse.continuousOn.continuousAt
        (hta_eq.symm ▸ (ht' a₁).localInverse_open_source.mem_nhds hmem₁.1)
    have hpairW : ContinuousAt pairW ⟨a.right, haW⟩ := by
      rw [ContinuousAt, tendsto_subtype_rng]
      exact (ContinuousAt.comp (f := fun w : W ↦ ((ht' a).localInverse w).left)
        hta₁_at (hs'.contMDiff.continuous.continuousAt.comp hta_w)).prodMk hta_w
    exact IsTopologicalGroupoid.continuous_comp.continuousAt.comp hpairW
  refine ⟨τW, (hta_eq.symm ▸ hlift₁.contMDiffAt).comp a.right hsub,
    hWo.isOpenEmbedding_subtypeVal.continuousAt_iff.mp hτW_sub, ?_, ?_⟩
  · filter_upwards [hWo.mem_nhds haW] with z hz
    simp only [τW, hz, ↓reduceDIte, pairW, Quiver.Total.comp_left]
    exact ((hΦ x₁).localInverse_right_inv (hWsub hz).1.2).symm
  · filter_upwards [hWo.mem_nhds haW] with z hz
    simp only [τW, hz, ↓reduceDIte, pairW, Quiver.Total.comp_right]
    exact (ht' a).localInverse_right_inv (hWsub hz).2

variable [IsManifold I ∞ C] [IsManifold J ∞ (Quiver.Total C)]

section PrivateDescent

variable {Φ : C ⥤ D} (hs : IsLocalDiffeomorph J I ∞ (Quiver.Total.left : Quiver.Total C → C))
  {ht : ContMDiff J I ∞ (Quiver.Total.right : Quiver.Total C → C)}
  {hs' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.left : Quiver.Total D → D)}
  {ht' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.right : Quiver.Total D → D)}
  {hΦ : IsLocalDiffeomorph I I' ∞ Φ.obj} {hΦ₁ : ContMDiff J J' ∞ Φ.toPrefunctor.mapTotal}

private theorem mpullback_apply_eq_of_isLocalLiftAt [Φ.Full]
    (hs' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.left : Quiver.Total D → D))
    (hΦ : IsLocalDiffeomorph I I' ∞ Φ.obj) (hΦ₁ : ContMDiff J J' ∞ Φ.toPrefunctor.mapTotal)
    {α : SmoothForm I C V k} (hα : α ∈ TauCeti.Quiver.invariantForms I J hs.contMDiff ht V k)
    {y₀ : D} {ℓ₁ ℓ₂ : D → C} {τ₁ τ₂ : D → Quiver.Total D}
    (h₁ : IsLocalLiftAt (I := I) (I' := I') Φ y₀ ℓ₁ τ₁)
    (h₂ : IsLocalLiftAt (I := I) (I' := I') Φ y₀ ℓ₂ τ₂) :
    mpullback (F := V) (k := k) I' I ℓ₁ α.1 y₀ = mpullback (F := V) (k := k) I' I ℓ₂ α.1 y₀ := by
  obtain ⟨σ, hσ, hleft, hright⟩ := exists_smooth_connecting_arrow Φ hs ht hs' hΦ hΦ₁ h₁ h₂
  have hσd : MDifferentiableAt I' J σ y₀ := hσ.mdifferentiableAt (by simp)
  have hinv := congrArg (fun η : SmoothForm J (Quiver.Total C) V k ↦
    mpullback (F := V) (k := k) I' J σ η.1 y₀) (TauCeti.Quiver.mem_invariantForms_iff.mp hα)
  simp only [SmoothForm.coe_mpullback] at hinv
  rw [← hleft.mpullback_eq, mpullback_comp_at hσd (hs.mdifferentiable (by simp) (σ y₀)), hinv,
    ← mpullback_comp_at hσd (ht.contMDiffAt.mdifferentiableAt (by simp)), hright.mpullback_eq]

private def descendedRoughForm (Φ : C ⥤ D) [Φ.EssSurj]
    (ht' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.right : Quiver.Total D → D))
    (hΦ : IsLocalDiffeomorph I I' ∞ Φ.obj) (α : RoughForm I C V k) : RoughForm I' D V k :=
  fun y ↦ mpullback (F := V) (k := k) I' I
    (arrowLocalLift Φ ht' hΦ (Φ.objPreimage y)
      ⟨Φ.obj (Φ.objPreimage y), y, (Φ.objObjPreimageIso y).hom⟩) α y

include hs' hΦ₁

private theorem eventually_descendedRoughForm_eq [Φ.Full] [Φ.EssSurj]
    {α : SmoothForm I C V k} (hα : α ∈ TauCeti.Quiver.invariantForms I J hs.contMDiff ht V k)
    (x : C) (a : Quiver.Total D) (ha : a.left = Φ.obj x) :
    ∀ᶠ z in 𝓝 a.right, descendedRoughForm Φ ht' hΦ α.1 z =
      mpullback (F := V) (k := k) I' I (arrowLocalLift Φ ht' hΦ x a) α.1 z :=
  eventually_of_mem ((isOpen_arrowLocalLiftOpen Φ hs' ht' hΦ x a).mem_nhds
    (mem_arrowLocalLiftOpen Φ ht' hΦ x a ha)) fun y hy ↦
    mpullback_apply_eq_of_isLocalLiftAt hs hs' hΦ hΦ₁ hα
      (isLocalLiftAt_arrowLocalLift Φ hs' ht' hΦ (Φ.objPreimage y)
        ⟨Φ.obj (Φ.objPreimage y), y, (Φ.objObjPreimageIso y).hom⟩
        (mem_arrowLocalLiftOpen Φ ht' hΦ (Φ.objPreimage y) _ rfl))
      (isLocalLiftAt_arrowLocalLift Φ hs' ht' hΦ x a hy)

private theorem isSmoothForm_descendedRoughForm [IsManifold I' ∞ D] [Φ.Full] [Φ.EssSurj]
    {α : SmoothForm I C V k} (hα : α ∈ TauCeti.Quiver.invariantForms I J hs.contMDiff ht V k) :
    IsSmoothForm I' ∞ (descendedRoughForm Φ ht' hΦ α.1) := by
  rw [isSmoothForm_def]
  intro y
  let x := Φ.objPreimage y
  let a : Quiver.Total D := ⟨Φ.obj x, y, (Φ.objObjPreimageIso y).hom⟩
  have hℓ := (isLocalLiftAt_arrowLocalLift (I := I) (I' := I') Φ hs' ht' hΦ x a
    (mem_arrowLocalLiftOpen Φ ht' hΦ x a rfl)).contMDiffAt
  exact ((α.contMDiff (arrowLocalLift Φ ht' hΦ x a y)).mpullback_form hℓ
    (by simp)).congr_of_eventuallyEq
    ((eventually_descendedRoughForm_eq (hs' := hs') (ht' := ht') (hΦ := hΦ) (hΦ₁ := hΦ₁)
      hs hα x a rfl).mono fun z hz ↦ by dsimp only; rw [hz])

private theorem mpullback_descendedRoughForm [Φ.Full] [Φ.EssSurj]
    {α : SmoothForm I C V k} (hα : α ∈ TauCeti.Quiver.invariantForms I J hs.contMDiff ht V k) :
    mpullback (F := V) (k := k) I I' Φ.obj (descendedRoughForm Φ ht' hΦ α.1) = α.1 := by
  funext x
  have hpt : descendedRoughForm Φ ht' hΦ α.1 (Φ.obj x) =
      mpullback (F := V) (k := k) I' I (hΦ x).localInverse α.1 (Φ.obj x) :=
    mpullback_apply_eq_of_isLocalLiftAt hs hs' hΦ hΦ₁ hα
      (isLocalLiftAt_arrowLocalLift Φ hs' ht' hΦ (Φ.objPreimage (Φ.obj x))
        ⟨Φ.obj (Φ.objPreimage (Φ.obj x)), Φ.obj x, (Φ.objObjPreimageIso (Φ.obj x)).hom⟩
        (mem_arrowLocalLiftOpen Φ ht' hΦ (Φ.objPreimage (Φ.obj x)) _ rfl))
      ⟨(hΦ x).contMDiffAt_localInverse, IsTopologicalGroupoid.continuous_unit.continuousAt,
        (hΦ x).localInverse_eventuallyEq_right.symm, Eventually.of_forall fun _ ↦ rfl⟩
  have heq : mpullback (F := V) (k := k) I I' Φ.obj (descendedRoughForm Φ ht' hΦ α.1) x =
      mpullback (F := V) (k := k) I I' Φ.obj
        (mpullback (F := V) (k := k) I' I (hΦ x).localInverse α.1) x := by
    ext v; rw [mpullback_apply, hpt, ← mpullback_apply]
  rw [heq, ← mpullback_comp_at (hΦ.mdifferentiable (by simp) x)
      ((hΦ x).mdifferentiableAt_localInverse (by simp)),
    (hΦ x).localInverse_eventuallyEq_left.mpullback_eq, mpullback_id]

private theorem mpullback_left_eq_right_descendedRoughForm [Φ.Full] [Φ.EssSurj]
    {α : SmoothForm I C V k} (hα : α ∈ TauCeti.Quiver.invariantForms I J hs.contMDiff ht V k) :
    mpullback (F := V) (k := k) J' I' Quiver.Total.left (descendedRoughForm Φ ht' hΦ α.1) =
      mpullback (F := V) (k := k) J' I' Quiver.Total.right (descendedRoughForm Φ ht' hΦ α.1) := by
  funext a
  let x₁ := Φ.objPreimage a.left
  let a₁ : Quiver.Total D := ⟨Φ.obj x₁, a.left, (Φ.objObjPreimageIso a.left).hom⟩
  have hl : mpullback (F := V) (k := k) J' I' Quiver.Total.left
        (descendedRoughForm Φ ht' hΦ α.1) a =
      mpullback (F := V) (k := k) J' I
        (arrowLocalLift Φ ht' hΦ x₁ a₁ ∘ Quiver.Total.left) α.1 a := by
    have hpt_l : mpullback (F := V) (k := k) J' I' Quiver.Total.left
          (descendedRoughForm Φ ht' hΦ α.1) a =
        mpullback (F := V) (k := k) J' I' Quiver.Total.left
          (mpullback (F := V) (k := k) I' I (arrowLocalLift Φ ht' hΦ x₁ a₁) α.1) a := by
      ext v; rw [mpullback_apply, descendedRoughForm, ← mpullback_apply]
    rw [hpt_l, ← mpullback_comp_at (hs'.mdifferentiable (by simp) a)
      ((isLocalLiftAt_arrowLocalLift Φ hs' ht' hΦ x₁ a₁
        (mem_arrowLocalLiftOpen Φ ht' hΦ x₁ a₁ rfl)).contMDiffAt.mdifferentiableAt (by simp))]
  obtain ⟨τ₂, hlift₂⟩ := isLocalLiftAt_comp_target_localInverse (I := I) (I' := I')
    Φ hs' ht' hΦ x₁ a₁ a rfl rfl
  have hcomp_eq : descendedRoughForm Φ ht' hΦ α.1 a.right =
      mpullback (F := V) (k := k) I' I
        (arrowLocalLift Φ ht' hΦ x₁ a₁ ∘ Quiver.Total.left ∘ (ht' a).localInverse) α.1 a.right :=
    mpullback_apply_eq_of_isLocalLiftAt hs hs' hΦ hΦ₁ hα
      (isLocalLiftAt_arrowLocalLift Φ hs' ht' hΦ (Φ.objPreimage a.right)
        ⟨Φ.obj (Φ.objPreimage a.right), a.right, (Φ.objObjPreimageIso a.right).hom⟩
        (mem_arrowLocalLiftOpen Φ ht' hΦ (Φ.objPreimage a.right) _ rfl)) hlift₂
  have hr : mpullback (F := V) (k := k) J' I' Quiver.Total.right
        (descendedRoughForm Φ ht' hΦ α.1) a =
      mpullback (F := V) (k := k) J' I' Quiver.Total.right
        (mpullback (F := V) (k := k) I' I
          (arrowLocalLift Φ ht' hΦ x₁ a₁ ∘ Quiver.Total.left ∘ (ht' a).localInverse) α.1) a := by
    ext v; rw [mpullback_apply, hcomp_eq, ← mpullback_apply]
  have hev_a : (arrowLocalLift Φ ht' hΦ x₁ a₁ ∘ Quiver.Total.left ∘ (ht' a).localInverse) ∘
      Quiver.Total.right =ᶠ[𝓝 a] arrowLocalLift Φ ht' hΦ x₁ a₁ ∘ Quiver.Total.left := by
    filter_upwards [(ht' a).localInverse.open_target.mem_nhds
      (ht' a).localInverse_mem_target] with b hb
    simp only [Function.comp_apply, (ht' a).localInverse_left_inv hb]
  rw [hl, hr, ← mpullback_comp_at (ht'.mdifferentiable (by simp) a)
    (hlift₂.contMDiffAt.mdifferentiableAt (by simp)), hev_a.mpullback_eq]

end PrivateDescent

variable [IsManifold I' ∞ D] [IsManifold J' ∞ (Quiver.Total D)]

/-- Pullback of invariant forms along a full, essentially surjective étale refinement into a
topological smooth groupoid is surjective. -/
theorem invariantFormsPullback_surjective (Φ : C ⥤ D) [Φ.Full] [Φ.EssSurj]
    (hs : IsLocalDiffeomorph J I ∞ (Quiver.Total.left : Quiver.Total C → C))
    (ht : ContMDiff J I ∞ (Quiver.Total.right : Quiver.Total C → C))
    (hs' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.left : Quiver.Total D → D))
    (ht' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.right : Quiver.Total D → D))
    (hΦ : IsLocalDiffeomorph I I' ∞ Φ.obj) (hΦ₁ : ContMDiff J J' ∞ Φ.toPrefunctor.mapTotal) :
    Function.Surjective (Φ.toPrefunctor.invariantFormsPullback (hs := hs.contMDiff) (ht := ht)
      (hs' := hs'.contMDiff) (ht' := ht'.contMDiff) (V := V) (k := k) hΦ.contMDiff hΦ₁) := by
  intro α
  refine ⟨⟨⟨descendedRoughForm Φ ht' hΦ α.1.1,
    (isSmoothForm_descendedRoughForm (hs' := hs') (ht' := ht') (hΦ := hΦ) (hΦ₁ := hΦ₁)
      hs α.2).mem_smoothBundleForms⟩, ?_⟩, Subtype.ext (Subtype.ext ?_)⟩
  · rw [TauCeti.Quiver.mem_invariantForms_iff]; apply Subtype.ext
    rw [SmoothForm.coe_mpullback, SmoothForm.coe_mpullback]
    exact mpullback_left_eq_right_descendedRoughForm (hs' := hs') (ht' := ht')
      (hΦ := hΦ) (hΦ₁ := hΦ₁) hs α.2
  · rw [Prefunctor.coe_invariantFormsPullback, SmoothForm.coe_mpullback]
    exact mpullback_descendedRoughForm (hs' := hs') (ht' := ht') (hΦ := hΦ) (hΦ₁ := hΦ₁) hs α.2

/-- **Étale-refinement descent of invariant forms.** Pullback along a full, essentially surjective
functor with locally diffeomorphic object map, between smooth presentations where the source of `C`
and both source and target of the topological groupoid `D` are smooth local diffeomorphisms, is a
linear equivalence on invariant forms. -/
def invariantFormsEquiv (Φ : C ⥤ D) [Φ.Full] [Φ.EssSurj]
    (hs : IsLocalDiffeomorph J I ∞ (Quiver.Total.left : Quiver.Total C → C))
    (ht : ContMDiff J I ∞ (Quiver.Total.right : Quiver.Total C → C))
    (hs' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.left : Quiver.Total D → D))
    (ht' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.right : Quiver.Total D → D))
    (hΦ : IsLocalDiffeomorph I I' ∞ Φ.obj) (hΦ₁ : ContMDiff J J' ∞ Φ.toPrefunctor.mapTotal) :
    TauCeti.Quiver.invariantForms I' J' hs'.contMDiff ht'.contMDiff V k ≃ₗ[ℝ]
      TauCeti.Quiver.invariantForms I J hs.contMDiff ht V k :=
  LinearEquiv.ofBijective (Φ.toPrefunctor.invariantFormsPullback hΦ.contMDiff hΦ₁)
    ⟨Φ.invariantFormsPullback_injective hΦ hΦ₁ ht',
      Φ.invariantFormsPullback_surjective hs ht hs' ht' hΦ hΦ₁⟩

/-- Applying the étale-refinement equivalence of invariant forms computes pullback along `Φ`. -/
@[simp]
theorem invariantFormsEquiv_apply (Φ : C ⥤ D) [Φ.Full] [Φ.EssSurj]
    (hs : IsLocalDiffeomorph J I ∞ (Quiver.Total.left : Quiver.Total C → C))
    (ht : ContMDiff J I ∞ (Quiver.Total.right : Quiver.Total C → C))
    (hs' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.left : Quiver.Total D → D))
    (ht' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.right : Quiver.Total D → D))
    (hΦ : IsLocalDiffeomorph I I' ∞ Φ.obj) (hΦ₁ : ContMDiff J J' ∞ Φ.toPrefunctor.mapTotal)
    (φ : TauCeti.Quiver.invariantForms I' J' hs'.contMDiff ht'.contMDiff V k) :
    Φ.invariantFormsEquiv hs ht hs' ht' hΦ hΦ₁ φ =
      Φ.toPrefunctor.invariantFormsPullback hΦ.contMDiff hΦ₁ φ := (rfl)

/-- Pulling the descended invariant form back along `Φ` recovers the original invariant form. -/
@[simp]
theorem mpullback_invariantFormsEquiv_symm (Φ : C ⥤ D) [Φ.Full] [Φ.EssSurj]
    (hs : IsLocalDiffeomorph J I ∞ (Quiver.Total.left : Quiver.Total C → C))
    (ht : ContMDiff J I ∞ (Quiver.Total.right : Quiver.Total C → C))
    (hs' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.left : Quiver.Total D → D))
    (ht' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.right : Quiver.Total D → D))
    (hΦ : IsLocalDiffeomorph I I' ∞ Φ.obj) (hΦ₁ : ContMDiff J J' ∞ Φ.toPrefunctor.mapTotal)
    (α : TauCeti.Quiver.invariantForms I J hs.contMDiff ht V k) :
    SmoothForm.mpullback Φ.obj hΦ.contMDiff
      ((Φ.invariantFormsEquiv hs ht hs' ht' hΦ hΦ₁).symm α).1 = α.1 := by
  have h := congrArg Subtype.val ((Φ.invariantFormsEquiv hs ht hs' ht' hΦ hΦ₁).apply_symm_apply α)
  rwa [invariantFormsEquiv_apply, Prefunctor.coe_invariantFormsPullback] at h

/-- Descent of invariant forms along an étale refinement commutes with exterior differentiation. -/
theorem invariantFormsEquiv_symm_mextDerivₗ (Φ : C ⥤ D) [Φ.Full] [Φ.EssSurj]
    (hs : IsLocalDiffeomorph J I ∞ (Quiver.Total.left : Quiver.Total C → C))
    (ht : ContMDiff J I ∞ (Quiver.Total.right : Quiver.Total C → C))
    (hs' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.left : Quiver.Total D → D))
    (ht' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.right : Quiver.Total D → D))
    (hΦ : IsLocalDiffeomorph I I' ∞ Φ.obj) (hΦ₁ : ContMDiff J J' ∞ Φ.toPrefunctor.mapTotal)
    (α : TauCeti.Quiver.invariantForms I J hs.contMDiff ht V k) :
    (Φ.invariantFormsEquiv hs ht hs' ht' hΦ hΦ₁).symm
        (TauCeti.Quiver.invariantForms.mextDerivₗ I J hs.contMDiff ht V k α) =
      TauCeti.Quiver.invariantForms.mextDerivₗ I' J' hs'.contMDiff ht'.contMDiff V k
        ((Φ.invariantFormsEquiv hs ht hs' ht' hΦ hΦ₁).symm α) := by
  rw [LinearEquiv.symm_apply_eq, invariantFormsEquiv_apply,
    ← Φ.toPrefunctor.mextDerivₗ_invariantFormsPullback hΦ.contMDiff hΦ₁,
    ← Φ.invariantFormsEquiv_apply hs ht hs' ht' hΦ hΦ₁, LinearEquiv.apply_symm_apply]

/-- Descent of invariant forms along an étale refinement commutes with paired wedge products. -/
theorem invariantFormsEquiv_symm_wedgeWith {V₁ V₂ V₃ : Type*}
    [NormedAddCommGroup V₁] [NormedSpace ℝ V₁] [NormedAddCommGroup V₂] [NormedSpace ℝ V₂]
    [NormedAddCommGroup V₃] [NormedSpace ℝ V₃] (μ : V₁ →L[ℝ] V₂ →L[ℝ] V₃) {l : ℕ}
    (Φ : C ⥤ D) [Φ.Full] [Φ.EssSurj]
    (hs : IsLocalDiffeomorph J I ∞ (Quiver.Total.left : Quiver.Total C → C))
    (ht : ContMDiff J I ∞ (Quiver.Total.right : Quiver.Total C → C))
    (hs' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.left : Quiver.Total D → D))
    (ht' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.right : Quiver.Total D → D))
    (hΦ : IsLocalDiffeomorph I I' ∞ Φ.obj) (hΦ₁ : ContMDiff J J' ∞ Φ.toPrefunctor.mapTotal)
    (α : TauCeti.Quiver.invariantForms I J hs.contMDiff ht V₁ k)
    (β : TauCeti.Quiver.invariantForms I J hs.contMDiff ht V₂ l) :
    (((Φ.invariantFormsEquiv (V := V₃) (k := k + l) hs ht hs' ht' hΦ hΦ₁).symm
        ⟨SmoothForm.wedgeWith μ α.1 β.1,
          TauCeti.Quiver.wedgeWith_mem_invariantForms μ α.2 β.2⟩).1 :
        SmoothForm I' D V₃ (k + l)) =
      SmoothForm.wedgeWith μ ((Φ.invariantFormsEquiv hs ht hs' ht' hΦ hΦ₁).symm α).1
        ((Φ.invariantFormsEquiv hs ht hs' ht' hΦ hΦ₁).symm β).1 := by
  let e₁ := (Φ.invariantFormsEquiv hs ht hs' ht' hΦ hΦ₁).symm α
  let e₂ := (Φ.invariantFormsEquiv hs ht hs' ht' hΦ hΦ₁).symm β
  have heq : (Φ.invariantFormsEquiv (V := V₃) (k := k + l) hs ht hs' ht' hΦ hΦ₁).symm
      ⟨SmoothForm.wedgeWith μ α.1 β.1, TauCeti.Quiver.wedgeWith_mem_invariantForms μ α.2 β.2⟩ =
      ⟨SmoothForm.wedgeWith μ e₁.1 e₂.1,
        TauCeti.Quiver.wedgeWith_mem_invariantForms μ e₁.2 e₂.2⟩ := by
    rw [LinearEquiv.symm_apply_eq]; apply Subtype.ext
    rw [invariantFormsEquiv_apply, Prefunctor.coe_invariantFormsPullback]
    change α.1.wedgeWith μ β.1 = SmoothForm.mpullback Φ.obj hΦ.contMDiff _
    rw [SmoothForm.mpullback_wedgeWith, mpullback_invariantFormsEquiv_symm,
      mpullback_invariantFormsEquiv_symm]
  exact congrArg Subtype.val heq

/-- Descent of real-valued invariant forms along an étale refinement commutes with wedge
products. -/
theorem invariantFormsEquiv_symm_wedge {l : ℕ} (Φ : C ⥤ D) [Φ.Full] [Φ.EssSurj]
    (hs : IsLocalDiffeomorph J I ∞ (Quiver.Total.left : Quiver.Total C → C))
    (ht : ContMDiff J I ∞ (Quiver.Total.right : Quiver.Total C → C))
    (hs' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.left : Quiver.Total D → D))
    (ht' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.right : Quiver.Total D → D))
    (hΦ : IsLocalDiffeomorph I I' ∞ Φ.obj) (hΦ₁ : ContMDiff J J' ∞ Φ.toPrefunctor.mapTotal)
    (α : TauCeti.Quiver.invariantForms I J hs.contMDiff ht ℝ k)
    (β : TauCeti.Quiver.invariantForms I J hs.contMDiff ht ℝ l) :
    (((Φ.invariantFormsEquiv (V := ℝ) (k := k + l) hs ht hs' ht' hΦ hΦ₁).symm
        ⟨SmoothForm.wedge α.1 β.1, TauCeti.Quiver.wedge_mem_invariantForms α.2 β.2⟩).1 :
        SmoothForm I' D ℝ (k + l)) =
      SmoothForm.wedge ((Φ.invariantFormsEquiv hs ht hs' ht' hΦ hΦ₁).symm α).1
        ((Φ.invariantFormsEquiv hs ht hs' ht' hΦ hΦ₁).symm β).1 := by
  simp only [SmoothForm.wedge_def]
  exact Φ.invariantFormsEquiv_symm_wedgeWith _ hs ht hs' ht' hΦ hΦ₁ α β

/-- Smoothly naturally related étale refinements induce the same equivalence on invariant forms. -/
theorem invariantFormsEquiv_eq_of_natTrans {Ψ : C ⥤ D} [Ψ.Full] [Ψ.EssSurj]
    (Φ : C ⥤ D) [Φ.Full] [Φ.EssSurj] (η : Φ ⟶ Ψ)
    (hs : IsLocalDiffeomorph J I ∞ (Quiver.Total.left : Quiver.Total C → C))
    (ht : ContMDiff J I ∞ (Quiver.Total.right : Quiver.Total C → C))
    (hs' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.left : Quiver.Total D → D))
    (ht' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.right : Quiver.Total D → D))
    (hΦ : IsLocalDiffeomorph I I' ∞ Φ.obj) (hΨ : IsLocalDiffeomorph I I' ∞ Ψ.obj)
    (hΦ₁ : ContMDiff J J' ∞ Φ.toPrefunctor.mapTotal)
    (hΨ₁ : ContMDiff J J' ∞ Ψ.toPrefunctor.mapTotal)
    (hη : ContMDiff I J' ∞ fun x ↦ (⟨Φ.obj x, Ψ.obj x, η.app x⟩ : Quiver.Total D)) :
    Φ.invariantFormsEquiv (V := V) (k := k) hs ht hs' ht' hΦ hΦ₁ =
      Ψ.invariantFormsEquiv hs ht hs' ht' hΨ hΨ₁ :=
  LinearEquiv.toLinearMap_injective
    (η.invariantFormsPullback_eq hΦ.contMDiff hΨ.contMDiff hΦ₁ hΨ₁ hη)

end Descent

end CategoryTheory.Functor
