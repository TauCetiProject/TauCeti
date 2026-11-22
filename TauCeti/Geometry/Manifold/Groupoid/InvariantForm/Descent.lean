/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Category.InvariantForm
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.LocalDiffeomorph
public import TauCeti.Topology.CategoryTheory.Groupoid.Basic
import TauCeti.Topology.SeparatedMap

/-!
# Descent of invariant forms along étale refinements

Étale Lie groupoids representing the same orbifold are linked by spans of étale refinements
(equivalences of presentations). This file proves that pulling invariant differential forms back
along such a refinement is an isomorphism of differential graded algebras, showing that the
invariant-form DGA depends only on the orbifold up to étale atlas refinement and supplying the
descent foundation for orbifold de Rham cohomology and coarse-support descent.

For any essentially surjective smooth functor `Φ : C ⥤ D` between smooth categories whose object
map `Φ.obj` and target map `Quiver.Total.right : Quiver.Total D → D` have pointwise surjective
differentials (in particular, submersions or local diffeomorphisms), pullback of invariant forms
along `Φ` is injective (`CategoryTheory.Functor.invariantFormsPullback_injective`); this requires
neither fullness of `Φ` nor invertibility of arrows.

When `D` is a topological smooth groupoid whose source and target are smooth local diffeomorphisms,
the source of `C` is a smooth local diffeomorphism, and `Φ` is full and essentially surjective with
locally diffeomorphic object map, pullback along `Φ` is a linear equivalence on invariant forms
(`CategoryTheory.Functor.invariantFormsEquiv`). The equivalence is functorial in identity and
composition, commutes with exterior differentiation and wedge products, and depends only on the
smooth natural-transformation class of `Φ` (`CategoryTheory.NatTrans.invariantFormsEquiv_eq`).

## References

* A. Adem, J. Leida and Y. Ruan, *Orbifolds and stringy topology*, Chapter 2.
* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Sections 2–3.
-/

public noncomputable section

open Bundle CategoryTheory Filter Set Topology
open scoped Manifold ContDiff

section DescentFile

open TauCeti
open TauCeti.Quiver (invariantForms mem_invariantForms_iff wedgeWith_mem_invariantForms
  wedge_mem_invariantForms)

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

namespace CategoryTheory.Functor

section Injective

variable [TopologicalSpace (Quiver.Total C)] [ChartedSpace K (Quiver.Total C)]
  [IsManifold I ∞ C] [IsManifold J ∞ (Quiver.Total C)]
  [IsManifold I' ∞ D] [IsManifold J' ∞ (Quiver.Total D)]
  {hs : ContMDiff J I ∞ (Quiver.Total.left : Quiver.Total C → C)}
  {ht : ContMDiff J I ∞ (Quiver.Total.right : Quiver.Total C → C)}
  {hs' : ContMDiff J' I' ∞ (Quiver.Total.left : Quiver.Total D → D)}
  {ht' : ContMDiff J' I' ∞ (Quiver.Total.right : Quiver.Total D → D)}
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {k : ℕ}

/-- Pullback of invariant forms along an essentially surjective smooth functor is injective whenever
the object map and the target map of the codomain have pointwise surjective differentials. -/
theorem invariantFormsPullback_injective (Φ : C ⥤ D) [Φ.EssSurj]
    (hΦ : ContMDiff I I' ∞ Φ.obj) (hΦ₁ : ContMDiff J J' ∞ Φ.toPrefunctor.mapTotal)
    (hdΦ : ∀ x, Function.Surjective (mfderiv I I' Φ.obj x))
    (hdt' : ∀ a, Function.Surjective (mfderiv J' I' (Quiver.Total.right : Quiver.Total D → D) a)) :
    Function.Injective (Φ.toPrefunctor.invariantFormsPullback (hs := hs) (ht := ht) (hs' := hs')
      (ht' := ht') (V := V) (k := k) hΦ hΦ₁) := by
  rw [injective_iff_map_eq_zero]
  intro φ hφ
  refine Subtype.ext <| Subtype.ext <| funext fun y ↦ ?_
  let a : Quiver.Total D := ⟨Φ.obj (Φ.objPreimage y), y, (Φ.objObjPreimageIso y).hom⟩
  have hΦx : mpullback (F := V) (k := k) I I' Φ.obj φ.val.val (Φ.objPreimage y) = 0 := by
    have h0 := congrArg Subtype.val hφ
    rw [Prefunctor.coe_invariantFormsPullback, Submodule.coe_zero] at h0
    have h0x := congrArg (fun η : SmoothForm I C V k ↦ η.val (Φ.objPreimage y)) h0
    rwa [SmoothForm.coe_mpullback, Submodule.coe_zero, Pi.zero_apply] at h0x
  have hleft : (φ.val.val : RoughForm I' D V k) a.left = 0 :=
    (mpullback_apply_eq_mpullback_apply_iff (η := (0 : RoughForm I' D V k))
      (hdΦ (Φ.objPreimage y))).mp (hΦx.trans (by rw [mpullback_zero, Pi.zero_apply]))
  have hinv := congrArg (fun η : SmoothForm J' (Quiver.Total D) V k ↦ η.val a)
    (mem_invariantForms_iff.mp φ.property)
  simp only [SmoothForm.coe_mpullback] at hinv
  exact (mpullback_apply_eq_mpullback_apply_iff (η := (0 : RoughForm I' D V k)) (hdt' a)).mp
    (hinv.symm.trans ((mpullback_apply_eq_zero hleft).trans
      (by rw [mpullback_zero, Pi.zero_apply])))

end Injective

section LocalLifts

private structure IsLocalLiftAt (Φ : C ⥤ D) (y₀ : D) (ℓ : D → C) (τ : D → Quiver.Total D) :
    Prop where
  contMDiffAt : ContMDiffAt I' I ∞ ℓ y₀
  continuousAt : ContinuousAt τ y₀
  eventually_left : ∀ᶠ z in 𝓝 y₀, (τ z).left = Φ.obj (ℓ z)
  eventually_right : ∀ᶠ z in 𝓝 y₀, (τ z).right = z

variable (Φ : C ⥤ D)
  (ht' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.right : Quiver.Total D → D))
  (hΦ : IsLocalDiffeomorph I I' ∞ Φ.obj) (x : C) (a : Quiver.Total D)

private def arrowLocalLift : D → C :=
  (hΦ x).localInverse ∘ Quiver.Total.left ∘ (ht' a).localInverse

private def arrowLocalLiftOpen : Set D :=
  (ht' a).localInverse.source ∩
    (Quiver.Total.left ∘ (ht' a).localInverse) ⁻¹' (hΦ x).localInverse.source

private theorem isOpen_arrowLocalLiftOpen
    (hs' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.left : Quiver.Total D → D)) :
    IsOpen (arrowLocalLiftOpen Φ ht' hΦ x a) :=
  (hs'.contMDiff.continuous.comp_continuousOn
    (ht' a).contMDiffOn_localInverse.continuousOn).isOpen_inter_preimage
    (ht' a).localInverse_open_source (hΦ x).localInverse_open_source

private theorem mem_arrowLocalLiftOpen (ha : a.left = Φ.obj x) :
    a.right ∈ arrowLocalLiftOpen Φ ht' hΦ x a := by
  refine ⟨(ht' a).localInverse_mem_source, ?_⟩
  simp only [mem_preimage, Function.comp_apply]
  rw [(ht' a).localInverse_left_inv (ht' a).localInverse_mem_target, ha]
  exact (hΦ x).localInverse_mem_source

private theorem isLocalLiftAt_arrowLocalLift
    (hs' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.left : Quiver.Total D → D))
    {y : D} (hy : y ∈ arrowLocalLiftOpen Φ ht' hΦ x a) :
    IsLocalLiftAt (I := I) (I' := I') Φ y (arrowLocalLift Φ ht' hΦ x a) (ht' a).localInverse := by
  have hopen := isOpen_arrowLocalLiftOpen Φ ht' hΦ x a hs'
  have hτ : ContMDiffAt I' J' ∞ (ht' a).localInverse y :=
    (ht' a).contMDiffOn_localInverse.contMDiffAt ((ht' a).localInverse_open_source.mem_nhds hy.1)
  have hℓ : ContMDiffAt I' I ∞ (arrowLocalLift Φ ht' hΦ x a) y :=
    ((hΦ x).contMDiffOn_localInverse.contMDiffAt
      ((hΦ x).localInverse_open_source.mem_nhds hy.2)).comp y (hs'.contMDiff.contMDiffAt.comp y hτ)
  exact ⟨hℓ, hτ.continuousAt,
    eventually_of_mem (hopen.mem_nhds hy) fun _ hz ↦ ((hΦ x).localInverse_right_inv hz.2).symm,
    eventually_of_mem (hopen.mem_nhds hy) fun _ hz ↦ (ht' a).localInverse_right_inv hz.1⟩

end LocalLifts

end CategoryTheory.Functor

section Descent

variable [IsGroupoid D] [TopologicalSpace (Quiver.Total C)] [TauCeti.IsTopologicalGroupoid D]
  [ChartedSpace K (Quiver.Total C)]

namespace CategoryTheory.Functor

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
  -- Step 1: Compose `τ₁` with `τ₂⁻¹` in `D` to connect `Φ (ℓ₁ z)` to `Φ (ℓ₂ z)` near `y₀`.
  have hmatch : ∀ᶠ z in 𝓝 y₀,
      (τ₁ z).right = (IsTopologicalGroupoid.inverseHomeomorph D (τ₂ z)).left := by
    filter_upwards [h₁.eventually_right, h₂.eventually_right] with z h1 h2
    simpa only [IsTopologicalGroupoid.inverseHomeomorph_apply] using h1.trans h2.symm
  obtain ⟨δ, hδ_cont, hδ_eq⟩ := IsTopologicalGroupoid.exists_continuousAt_comp h₁.continuousAt
    ((IsTopologicalGroupoid.inverseHomeomorph D).continuous.continuousAt.comp h₂.continuousAt)
    hmatch
  have hδ_left : ∀ᶠ z in 𝓝 y₀, (δ z).left = Φ.obj (ℓ₁ z) := by
    filter_upwards [hδ_eq, hmatch, h₁.eventually_left] with z hz hm hl
    rw [hz hm, Quiver.Total.comp_left, hl]
  have hδ_right : ∀ᶠ z in 𝓝 y₀, (δ z).right = Φ.obj (ℓ₂ z) := by
    filter_upwards [hδ_eq, hmatch, h₂.eventually_left] with z hz hm hl
    rw [hz hm, Quiver.Total.comp_right, Function.comp_apply,
      IsTopologicalGroupoid.inverseHomeomorph_apply]
    exact hl
  -- Step 2: Lift `δ y₀` by fullness and extend it smoothly via a local section of `C`'s source.
  let b₀ : Quiver.Total C := ⟨ℓ₁ y₀, ℓ₂ y₀,
    Φ.preimage (Quiver.homOfEq (δ y₀).hom hδ_left.self_of_nhds hδ_right.self_of_nhds)⟩
  let σ : D → Quiver.Total C := (hs b₀).localInverse ∘ ℓ₁
  have hσ : ContMDiffAt I' J ∞ σ y₀ := (hs b₀).contMDiffAt_localInverse.comp y₀ h₁.contMDiffAt
  have hσ_left : Quiver.Total.left ∘ σ =ᶠ[𝓝 y₀] ℓ₁ :=
    h₁.contMDiffAt.continuousAt.tendsto.eventually (hs b₀).localInverse_eventuallyEq_right
  have hσ0 : σ y₀ = b₀ := (hs b₀).localInverse_left_inv (hs b₀).localInverse_mem_target
  have hmap0 : Φ.toPrefunctor.mapTotal (σ y₀) = δ y₀ := by
    rw [hσ0, Prefunctor.mapTotal_mk, Functor.toPrefunctor_map, Φ.map_preimage,
      Quiver.Total.mk_homOfEq]
  -- Step 3: Compare `Φ (σ z)` with `δ z` via local injectivity of `D`'s source, then cancel `Φ`.
  have hmap : Φ.toPrefunctor.mapTotal ∘ σ =ᶠ[𝓝 y₀] δ :=
    hs'.isLocalHomeomorph.isLocallyInjective.eventuallyEq_of_comp
      (hΦ₁.contMDiffAt.comp y₀ hσ).continuousAt hδ_cont hmap0 (by
        filter_upwards [hσ_left, hδ_left] with z hz hδz
        simp only [Function.comp_apply, Prefunctor.mapTotal_left, Functor.toPrefunctor_obj]
        rw [← Function.comp_apply (f := Quiver.Total.left) (g := σ), hz, hδz])
  have hΦright : ∀ᶠ z in 𝓝 y₀, Φ.obj (σ z).right = Φ.obj (ℓ₂ z) := by
    filter_upwards [hmap, hδ_right] with z hz hδz
    simpa only [Function.comp_apply, Prefunctor.mapTotal_right, Functor.toPrefunctor_obj] using
      (congrArg Quiver.Total.right hz).trans hδz
  exact ⟨σ, hσ, hσ_left, hΦ.isLocalHomeomorph.isLocallyInjective.eventuallyEq_of_comp
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
  have hmem₁ : a.left ∈ arrowLocalLiftOpen Φ ht' hΦ x₁ a₁ :=
    ha₁r ▸ mem_arrowLocalLiftOpen Φ ht' hΦ x₁ a₁ ha₁
  have hlift₁ := isLocalLiftAt_arrowLocalLift (I := I) (I' := I') Φ ht' hΦ x₁ a₁ hs' hmem₁
  have hta_eq : (Quiver.Total.left ∘ (ht' a).localInverse) a.right = a.left := by
    simp only [Function.comp_apply]
    rw [(ht' a).localInverse_left_inv (ht' a).localInverse_mem_target]
  have hsub : ContMDiffAt I' I' ∞ (Quiver.Total.left ∘ (ht' a).localInverse) a.right :=
    hs'.contMDiff.contMDiffAt.comp a.right (ht' a).contMDiffAt_localInverse
  have hmatch : ∀ᶠ z in 𝓝 a.right,
      ((ht' a₁).localInverse ((ht' a).localInverse z).left).right = ((ht' a).localInverse z).left :=
    hsub.continuousAt.tendsto.eventually (hta_eq.symm ▸ hlift₁.eventually_right)
  have hleft₁ : ∀ᶠ z in 𝓝 a.right,
      ((ht' a₁).localInverse ((ht' a).localInverse z).left).left =
        Φ.obj ((arrowLocalLift Φ ht' hΦ x₁ a₁ ∘ Quiver.Total.left ∘ (ht' a).localInverse) z) :=
    hsub.continuousAt.tendsto.eventually (hta_eq.symm ▸ hlift₁.eventually_left)
  obtain ⟨τ₂, hτ₂_cont, hτ₂_eq⟩ := IsTopologicalGroupoid.exists_continuousAt_comp
    ((hta_eq.symm ▸ hlift₁.continuousAt).comp hsub.continuousAt)
    (ht' a).contMDiffAt_localInverse.continuousAt hmatch
  refine ⟨τ₂, (hta_eq.symm ▸ hlift₁.contMDiffAt).comp a.right hsub, hτ₂_cont, ?_, ?_⟩
  · filter_upwards [hτ₂_eq, hmatch, hleft₁] with z hz hm hl
    rw [hz hm, Quiver.Total.comp_left]; exact hl
  · filter_upwards [hτ₂_eq, hmatch, (ht' a).localInverse_eventuallyEq_right] with z hz hm hr
    rw [hz hm, Quiver.Total.comp_right]; exact hr

variable [IsManifold I ∞ C] [IsManifold J ∞ (Quiver.Total C)]

section PrivateDescent

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {k : ℕ}
  {Φ : C ⥤ D} (hs : IsLocalDiffeomorph J I ∞ (Quiver.Total.left : Quiver.Total C → C))
  {ht : ContMDiff J I ∞ (Quiver.Total.right : Quiver.Total C → C)}
  {hs' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.left : Quiver.Total D → D)}
  {ht' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.right : Quiver.Total D → D)}
  {hΦ : IsLocalDiffeomorph I I' ∞ Φ.obj} {hΦ₁ : ContMDiff J J' ∞ Φ.toPrefunctor.mapTotal}

include hs' hΦ hΦ₁ in
private theorem mpullback_apply_eq_of_isLocalLiftAt [Φ.Full]
    {α : SmoothForm I C V k} (hα : α ∈ invariantForms I J hs.contMDiff ht V k)
    {y₀ : D} {ℓ₁ ℓ₂ : D → C} {τ₁ τ₂ : D → Quiver.Total D}
    (h₁ : IsLocalLiftAt (I := I) (I' := I') Φ y₀ ℓ₁ τ₁)
    (h₂ : IsLocalLiftAt (I := I) (I' := I') Φ y₀ ℓ₂ τ₂) :
    mpullback (F := V) (k := k) I' I ℓ₁ α.val y₀ =
      mpullback (F := V) (k := k) I' I ℓ₂ α.val y₀ := by
  obtain ⟨σ, hσ, hleft, hright⟩ := exists_smooth_connecting_arrow Φ hs ht hs' hΦ hΦ₁ h₁ h₂
  have hσd : MDifferentiableAt I' J σ y₀ := hσ.mdifferentiableAt (by simp)
  have hinv := congrArg (fun η : SmoothForm J (Quiver.Total C) V k ↦
    mpullback (F := V) (k := k) I' J σ η.val y₀) (mem_invariantForms_iff.mp hα)
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
    {α : SmoothForm I C V k} (hα : α ∈ invariantForms I J hs.contMDiff ht V k)
    (x : C) (a : Quiver.Total D) (ha : a.left = Φ.obj x) :
    ∀ᶠ z in 𝓝 a.right, descendedRoughForm Φ ht' hΦ α.val z =
      mpullback (F := V) (k := k) I' I (arrowLocalLift Φ ht' hΦ x a) α.val z :=
  eventually_of_mem ((isOpen_arrowLocalLiftOpen Φ ht' hΦ x a hs').mem_nhds
    (mem_arrowLocalLiftOpen Φ ht' hΦ x a ha)) fun y hy ↦
    mpullback_apply_eq_of_isLocalLiftAt (hs' := hs') (hΦ := hΦ) (hΦ₁ := hΦ₁) hs hα
      (isLocalLiftAt_arrowLocalLift Φ ht' hΦ (Φ.objPreimage y)
        ⟨Φ.obj (Φ.objPreimage y), y, (Φ.objObjPreimageIso y).hom⟩ hs'
        (mem_arrowLocalLiftOpen Φ ht' hΦ (Φ.objPreimage y) _ rfl))
      (isLocalLiftAt_arrowLocalLift Φ ht' hΦ x a hs' hy)

private theorem isSmoothForm_descendedRoughForm [IsManifold I' ∞ D] [Φ.Full] [Φ.EssSurj]
    {α : SmoothForm I C V k} (hα : α ∈ invariantForms I J hs.contMDiff ht V k) :
    IsSmoothForm I' ∞ (descendedRoughForm Φ ht' hΦ α.val) := by
  rw [isSmoothForm_def]; intro y
  let x := Φ.objPreimage y
  let a : Quiver.Total D := ⟨Φ.obj x, y, (Φ.objObjPreimageIso y).hom⟩
  have hℓ := (isLocalLiftAt_arrowLocalLift (I := I) (I' := I') Φ ht' hΦ x a hs'
    (mem_arrowLocalLiftOpen Φ ht' hΦ x a rfl)).contMDiffAt
  exact ((α.contMDiff (arrowLocalLift Φ ht' hΦ x a y)).mpullback_form hℓ
    (by simp)).congr_of_eventuallyEq
    ((eventually_descendedRoughForm_eq (hs' := hs') (ht' := ht') (hΦ := hΦ) (hΦ₁ := hΦ₁)
      hs hα x a rfl).mono fun z hz ↦ by dsimp only; rw [hz])

private theorem mpullback_descendedRoughForm [Φ.Full] [Φ.EssSurj]
    {α : SmoothForm I C V k} (hα : α ∈ invariantForms I J hs.contMDiff ht V k) :
    mpullback (F := V) (k := k) I I' Φ.obj (descendedRoughForm Φ ht' hΦ α.val) = α.val := by
  funext x
  have hpt : descendedRoughForm Φ ht' hΦ α.val (Φ.obj x) =
      mpullback (F := V) (k := k) I' I (hΦ x).localInverse α.val (Φ.obj x) :=
    mpullback_apply_eq_of_isLocalLiftAt (hs' := hs') (hΦ := hΦ) (hΦ₁ := hΦ₁) hs hα
      (isLocalLiftAt_arrowLocalLift Φ ht' hΦ (Φ.objPreimage (Φ.obj x))
        ⟨Φ.obj (Φ.objPreimage (Φ.obj x)), Φ.obj x, (Φ.objObjPreimageIso (Φ.obj x)).hom⟩ hs'
        (mem_arrowLocalLiftOpen Φ ht' hΦ (Φ.objPreimage (Φ.obj x)) _ rfl))
      ⟨(hΦ x).contMDiffAt_localInverse, IsTopologicalGroupoid.continuous_unit.continuousAt,
        (hΦ x).localInverse_eventuallyEq_right.symm, Eventually.of_forall fun _ ↦ rfl⟩
  have heq : mpullback (F := V) (k := k) I I' Φ.obj (descendedRoughForm Φ ht' hΦ α.val) x =
      mpullback (F := V) (k := k) I I' Φ.obj
        (mpullback (F := V) (k := k) I' I (hΦ x).localInverse α.val) x := by
    ext v; rw [mpullback_apply, hpt, ← mpullback_apply]
  rw [heq, ← mpullback_comp_at (hΦ.mdifferentiable (by simp) x)
      ((hΦ x).mdifferentiableAt_localInverse (by simp)),
    (hΦ x).localInverse_eventuallyEq_left.mpullback_eq, mpullback_id]

private theorem mpullback_left_eq_right_descendedRoughForm [Φ.Full] [Φ.EssSurj]
    {α : SmoothForm I C V k} (hα : α ∈ invariantForms I J hs.contMDiff ht V k) :
    mpullback (F := V) (k := k) J' I' Quiver.Total.left (descendedRoughForm Φ ht' hΦ α.val) =
      mpullback (F := V) (k := k) J' I' Quiver.Total.right (descendedRoughForm Φ ht' hΦ α.val) := by
  funext a
  let x₁ := Φ.objPreimage a.left
  let a₁ : Quiver.Total D := ⟨Φ.obj x₁, a.left, (Φ.objObjPreimageIso a.left).hom⟩
  have hl : mpullback (F := V) (k := k) J' I' Quiver.Total.left
        (descendedRoughForm Φ ht' hΦ α.val) a =
      mpullback (F := V) (k := k) J' I
        (arrowLocalLift Φ ht' hΦ x₁ a₁ ∘ Quiver.Total.left) α.val a := by
    have hpt_l : mpullback (F := V) (k := k) J' I' Quiver.Total.left
          (descendedRoughForm Φ ht' hΦ α.val) a =
        mpullback (F := V) (k := k) J' I' Quiver.Total.left
          (mpullback (F := V) (k := k) I' I (arrowLocalLift Φ ht' hΦ x₁ a₁) α.val) a := by
      ext v; rw [mpullback_apply, descendedRoughForm, ← mpullback_apply]
    rw [hpt_l, ← mpullback_comp_at (hs'.mdifferentiable (by simp) a)
      ((isLocalLiftAt_arrowLocalLift Φ ht' hΦ x₁ a₁ hs'
        (mem_arrowLocalLiftOpen Φ ht' hΦ x₁ a₁ rfl)).contMDiffAt.mdifferentiableAt (by simp))]
  obtain ⟨τ₂, hlift₂⟩ := isLocalLiftAt_comp_target_localInverse (I := I) (I' := I')
    Φ hs' ht' hΦ x₁ a₁ a rfl rfl
  have hcomp_eq : descendedRoughForm Φ ht' hΦ α.val a.right =
      mpullback (F := V) (k := k) I' I
        (arrowLocalLift Φ ht' hΦ x₁ a₁ ∘ Quiver.Total.left ∘ (ht' a).localInverse) α.val a.right :=
    mpullback_apply_eq_of_isLocalLiftAt (hs' := hs') (hΦ := hΦ) (hΦ₁ := hΦ₁) hs hα
      (isLocalLiftAt_arrowLocalLift Φ ht' hΦ (Φ.objPreimage a.right)
        ⟨Φ.obj (Φ.objPreimage a.right), a.right, (Φ.objObjPreimageIso a.right).hom⟩ hs'
        (mem_arrowLocalLiftOpen Φ ht' hΦ (Φ.objPreimage a.right) _ rfl)) hlift₂
  have hr : mpullback (F := V) (k := k) J' I' Quiver.Total.right
        (descendedRoughForm Φ ht' hΦ α.val) a =
      mpullback (F := V) (k := k) J' I' Quiver.Total.right
        (mpullback (F := V) (k := k) I' I
          (arrowLocalLift Φ ht' hΦ x₁ a₁ ∘ Quiver.Total.left ∘ (ht' a).localInverse) α.val) a := by
    ext v; rw [mpullback_apply, hcomp_eq, ← mpullback_apply]
  have hev_a : (arrowLocalLift Φ ht' hΦ x₁ a₁ ∘ Quiver.Total.left ∘ (ht' a).localInverse) ∘
      Quiver.Total.right =ᶠ[𝓝 a] arrowLocalLift Φ ht' hΦ x₁ a₁ ∘ Quiver.Total.left :=
    (ht' a).localInverse_eventuallyEq_left.fun_comp
      (arrowLocalLift Φ ht' hΦ x₁ a₁ ∘ Quiver.Total.left)
  rw [hl, hr, ← mpullback_comp_at (ht'.mdifferentiable (by simp) a)
    (hlift₂.contMDiffAt.mdifferentiableAt (by simp)), hev_a.mpullback_eq]

end PrivateDescent

variable [IsManifold I' ∞ D] [IsManifold J' ∞ (Quiver.Total D)]

section EquivAPI

variable (Φ : C ⥤ D) [Φ.Full] [Φ.EssSurj]
  (hs : IsLocalDiffeomorph J I ∞ (Quiver.Total.left : Quiver.Total C → C))
  (ht : ContMDiff J I ∞ (Quiver.Total.right : Quiver.Total C → C))
  (hs' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.left : Quiver.Total D → D))
  (ht' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.right : Quiver.Total D → D))
  (hΦ : IsLocalDiffeomorph I I' ∞ Φ.obj) (hΦ₁ : ContMDiff J J' ∞ Φ.toPrefunctor.mapTotal)

section SingleCoeff

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {k : ℕ}

/-- Pullback of invariant forms along a full, essentially surjective étale refinement into a
topological smooth groupoid is surjective. -/
theorem invariantFormsPullback_surjective :
    Function.Surjective (Φ.toPrefunctor.invariantFormsPullback (hs := hs.contMDiff) (ht := ht)
      (hs' := hs'.contMDiff) (ht' := ht'.contMDiff) (V := V) (k := k) hΦ.contMDiff hΦ₁) := by
  intro α
  refine ⟨⟨⟨descendedRoughForm Φ ht' hΦ α.val.val,
    (isSmoothForm_descendedRoughForm (hs' := hs') (ht' := ht') (hΦ := hΦ) (hΦ₁ := hΦ₁)
      hs α.property).mem_smoothBundleForms⟩, ?_⟩, Subtype.ext (Subtype.ext ?_)⟩
  · rw [mem_invariantForms_iff]; apply Subtype.ext
    rw [SmoothForm.coe_mpullback, SmoothForm.coe_mpullback]
    exact mpullback_left_eq_right_descendedRoughForm (hs' := hs') (ht' := ht')
      (hΦ := hΦ) (hΦ₁ := hΦ₁) hs α.property
  · rw [Prefunctor.coe_invariantFormsPullback, SmoothForm.coe_mpullback]
    exact mpullback_descendedRoughForm (hs' := hs') (ht' := ht')
      (hΦ := hΦ) (hΦ₁ := hΦ₁) hs α.property

/-- **Étale-refinement descent of invariant forms.** Pullback along a full, essentially surjective
functor with locally diffeomorphic object map, between smooth presentations where the source of `C`
and both source and target of the topological groupoid `D` are smooth local diffeomorphisms, is a
linear equivalence on invariant forms. -/
def invariantFormsEquiv :
    invariantForms I' J' hs'.contMDiff ht'.contMDiff V k ≃ₗ[ℝ]
      invariantForms I J hs.contMDiff ht V k :=
  LinearEquiv.ofBijective (Φ.toPrefunctor.invariantFormsPullback hΦ.contMDiff hΦ₁)
    ⟨Φ.invariantFormsPullback_injective hΦ.contMDiff hΦ₁
        (fun x ↦ (hΦ.isInvertible_mfderiv (by simp) x).surjective)
        (fun a ↦ (ht'.isInvertible_mfderiv (by simp) a).surjective),
      Φ.invariantFormsPullback_surjective hs ht hs' ht' hΦ hΦ₁⟩

/-- Applying the étale-refinement equivalence of invariant forms computes pullback along `Φ`. -/
@[simp]
theorem invariantFormsEquiv_apply
    (φ : invariantForms I' J' hs'.contMDiff ht'.contMDiff V k) :
    Φ.invariantFormsEquiv hs ht hs' ht' hΦ hΦ₁ φ =
      Φ.toPrefunctor.invariantFormsPullback hΦ.contMDiff hΦ₁ φ := (rfl)

/-- Pulling the descended invariant form back along `Φ` recovers the original invariant form. -/
@[simp]
theorem mpullback_invariantFormsEquiv_symm (α : invariantForms I J hs.contMDiff ht V k) :
    SmoothForm.mpullback Φ.obj hΦ.contMDiff
      ((Φ.invariantFormsEquiv hs ht hs' ht' hΦ hΦ₁).symm α).val = α.val := by
  have h := congrArg Subtype.val ((Φ.invariantFormsEquiv hs ht hs' ht' hΦ hΦ₁).apply_symm_apply α)
  rwa [invariantFormsEquiv_apply, Prefunctor.coe_invariantFormsPullback] at h

/-- Descent of invariant forms along an étale refinement commutes with exterior differentiation. -/
theorem invariantFormsEquiv_symm_mextDerivₗ (α : invariantForms I J hs.contMDiff ht V k) :
    (Φ.invariantFormsEquiv hs ht hs' ht' hΦ hΦ₁).symm
        (invariantForms.mextDerivₗ I J hs.contMDiff ht V k α) =
      invariantForms.mextDerivₗ I' J' hs'.contMDiff ht'.contMDiff V k
        ((Φ.invariantFormsEquiv hs ht hs' ht' hΦ hΦ₁).symm α) := by
  rw [LinearEquiv.symm_apply_eq, invariantFormsEquiv_apply,
    ← Φ.toPrefunctor.mextDerivₗ_invariantFormsPullback hΦ.contMDiff hΦ₁,
    ← Φ.invariantFormsEquiv_apply hs ht hs' ht' hΦ hΦ₁, LinearEquiv.apply_symm_apply]

end SingleCoeff

/-- Descent of invariant forms along an étale refinement commutes with paired wedge products. -/
theorem invariantFormsEquiv_symm_wedgeWith {V₁ V₂ V₃ : Type*}
    [NormedAddCommGroup V₁] [NormedSpace ℝ V₁] [NormedAddCommGroup V₂] [NormedSpace ℝ V₂]
    [NormedAddCommGroup V₃] [NormedSpace ℝ V₃] {k l : ℕ} (μ : V₁ →L[ℝ] V₂ →L[ℝ] V₃)
    (α : invariantForms I J hs.contMDiff ht V₁ k) (β : invariantForms I J hs.contMDiff ht V₂ l) :
    (((Φ.invariantFormsEquiv (V := V₃) (k := k + l) hs ht hs' ht' hΦ hΦ₁).symm
        ⟨SmoothForm.wedgeWith μ α.val β.val,
          wedgeWith_mem_invariantForms μ α.property β.property⟩).val :
        SmoothForm I' D V₃ (k + l)) =
      SmoothForm.wedgeWith μ ((Φ.invariantFormsEquiv hs ht hs' ht' hΦ hΦ₁).symm α).val
        ((Φ.invariantFormsEquiv hs ht hs' ht' hΦ hΦ₁).symm β).val := by
  let e₁ := (Φ.invariantFormsEquiv hs ht hs' ht' hΦ hΦ₁).symm α
  let e₂ := (Φ.invariantFormsEquiv hs ht hs' ht' hΦ hΦ₁).symm β
  have heq : (Φ.invariantFormsEquiv (V := V₃) (k := k + l) hs ht hs' ht' hΦ hΦ₁).symm
      ⟨SmoothForm.wedgeWith μ α.val β.val,
        wedgeWith_mem_invariantForms μ α.property β.property⟩ =
      ⟨SmoothForm.wedgeWith μ e₁.val e₂.val,
        wedgeWith_mem_invariantForms μ e₁.property e₂.property⟩ := by
    rw [LinearEquiv.symm_apply_eq]; apply Subtype.ext
    rw [invariantFormsEquiv_apply, Prefunctor.coe_invariantFormsPullback,
      SmoothForm.mpullback_wedgeWith]
    exact congrArg₂ (fun x y ↦ SmoothForm.wedgeWith μ x y)
      (Φ.mpullback_invariantFormsEquiv_symm hs ht hs' ht' hΦ hΦ₁ α).symm
      (Φ.mpullback_invariantFormsEquiv_symm hs ht hs' ht' hΦ hΦ₁ β).symm
  exact congrArg Subtype.val heq

/-- Descent of real-valued invariant forms along an étale refinement commutes with wedge
products. -/
theorem invariantFormsEquiv_symm_wedge {k l : ℕ}
    (α : invariantForms I J hs.contMDiff ht ℝ k) (β : invariantForms I J hs.contMDiff ht ℝ l) :
    (((Φ.invariantFormsEquiv (V := ℝ) (k := k + l) hs ht hs' ht' hΦ hΦ₁).symm
        ⟨SmoothForm.wedge α.val β.val, wedge_mem_invariantForms α.property β.property⟩).val :
        SmoothForm I' D ℝ (k + l)) =
      SmoothForm.wedge ((Φ.invariantFormsEquiv hs ht hs' ht' hΦ hΦ₁).symm α).val
        ((Φ.invariantFormsEquiv hs ht hs' ht' hΦ hΦ₁).symm β).val := by
  simp only [SmoothForm.wedge_def]
  exact Φ.invariantFormsEquiv_symm_wedgeWith hs ht hs' ht' hΦ hΦ₁ _ α β

end EquivAPI

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {k : ℕ}

/-- The identity refinement induces the identity equivalence on invariant forms. -/
@[simp]
theorem invariantFormsEquiv_id [IsGroupoid C] [TauCeti.IsTopologicalGroupoid C]
    (hs : IsLocalDiffeomorph J I ∞ (Quiver.Total.left : Quiver.Total C → C))
    (ht : IsLocalDiffeomorph J I ∞ (Quiver.Total.right : Quiver.Total C → C))
    (h : IsLocalDiffeomorph I I ∞ (𝟭 C).obj)
    (h₁ : ContMDiff J J ∞ (𝟭 C).toPrefunctor.mapTotal) :
    (𝟭 C).invariantFormsEquiv (V := V) (k := k) hs ht.contMDiff hs ht h h₁ =
      LinearEquiv.refl ℝ _ :=
  LinearEquiv.toLinearMap_injective Prefunctor.invariantFormsPullback_id

/-- Composing étale refinements reverses composition of their invariant-form equivalences. -/
theorem invariantFormsEquiv_comp {E'' H'' A'' K'' B : Type*}
    [NormedAddCommGroup E''] [NormedSpace ℝ E''] [TopologicalSpace H'']
    [NormedAddCommGroup A''] [NormedSpace ℝ A''] [TopologicalSpace K'']
    [Category B] [IsGroupoid B] [TopologicalSpace B] [TopologicalSpace (Quiver.Total B)]
    [TauCeti.IsTopologicalGroupoid B] [ChartedSpace H'' B] [ChartedSpace K'' (Quiver.Total B)]
    {I'' : ModelWithCorners ℝ E'' H''} {J'' : ModelWithCorners ℝ A'' K''}
    [IsManifold I'' ∞ B] [IsManifold J'' ∞ (Quiver.Total B)]
    (Φ : C ⥤ D) (Ψ : D ⥤ B) [Φ.Full] [Φ.EssSurj] [Ψ.Full] [Ψ.EssSurj]
    (hs : IsLocalDiffeomorph J I ∞ (Quiver.Total.left : Quiver.Total C → C))
    (ht : ContMDiff J I ∞ (Quiver.Total.right : Quiver.Total C → C))
    (hs' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.left : Quiver.Total D → D))
    (ht' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.right : Quiver.Total D → D))
    (hs'' : IsLocalDiffeomorph J'' I'' ∞ (Quiver.Total.left : Quiver.Total B → B))
    (ht'' : IsLocalDiffeomorph J'' I'' ∞ (Quiver.Total.right : Quiver.Total B → B))
    (hΦ : IsLocalDiffeomorph I I' ∞ Φ.obj) (hΦ₁ : ContMDiff J J' ∞ Φ.toPrefunctor.mapTotal)
    (hΨ : IsLocalDiffeomorph I' I'' ∞ Ψ.obj) (hΨ₁ : ContMDiff J' J'' ∞ Ψ.toPrefunctor.mapTotal) :
    (Φ ⋙ Ψ).invariantFormsEquiv (V := V) (k := k) hs ht hs'' ht''
        (fun x ↦ (hΦ x).comp I'' B (hΨ (Φ.obj x)))
        (Prefunctor.mapTotal_comp Φ.toPrefunctor Ψ.toPrefunctor ▸ hΨ₁.comp hΦ₁) =
      (Ψ.invariantFormsEquiv hs' ht'.contMDiff hs'' ht'' hΨ hΨ₁).trans
        (Φ.invariantFormsEquiv hs ht hs' ht' hΦ hΦ₁) :=
  LinearEquiv.toLinearMap_injective
    (Prefunctor.invariantFormsPullback_comp Φ.toPrefunctor Ψ.toPrefunctor
      hΦ.contMDiff hΦ₁ hΨ.contMDiff hΨ₁)

end CategoryTheory.Functor

namespace CategoryTheory.NatTrans

variable [IsManifold I ∞ C] [IsManifold J ∞ (Quiver.Total C)]
  [IsManifold I' ∞ D] [IsManifold J' ∞ (Quiver.Total D)]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {k : ℕ}

/-- Smoothly naturally related étale refinements induce the same equivalence on invariant forms. -/
theorem invariantFormsEquiv_eq {Φ Ψ : C ⥤ D} [Φ.Full] [Φ.EssSurj] [Ψ.Full] [Ψ.EssSurj] (η : Φ ⟶ Ψ)
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

end CategoryTheory.NatTrans

end Descent

end DescentFile
