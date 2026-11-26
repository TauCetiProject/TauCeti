/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Pullback
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Geometry.Manifold.VectorBundle.TotalSpace.Basic

/-!
# Pulling back commutes with the Hom bundle

For a continuous map `f : B' → B` and vector bundles `E₁`, `E₂` over `B`, continuous linear maps
between the fibres of the pullbacks `f *ᵖ E₁` and `f *ᵖ E₂` are exactly the fibres of the pullback
of the Hom bundle `fun b ↦ E₁ b →L[𝕜] E₂ b` (`Bundle.Pullback.homEquiv`). When `f` is `C^n`, this
fibrewise identification is a `C^n` diffeomorphism of total spaces
(`Bundle.Pullback.homDiffeomorph`): in the preferred trivializations both sides have the same
coordinates, by `ContinuousLinearMap.inCoordinates_pullback_of_mem`.
-/

public noncomputable section

open Bundle Filter Topology
open scoped Manifold

namespace Bundle.Pullback

variable {𝕜 B B' F₁ F₂ EB HB EB' HB' K : Type*} [NontriviallyNormedField 𝕜] {n : WithTop ℕ∞}
  [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  [NormedAddCommGroup EB'] [NormedSpace 𝕜 EB'] [TopologicalSpace HB']
  {IB' : ModelWithCorners 𝕜 EB' HB'} [TopologicalSpace B'] [ChartedSpace HB' B']
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {E₁ : B → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [∀ x, TopologicalSpace (E₁ x)] [TopologicalSpace (TotalSpace F₁ E₁)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  {E₂ : B → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [∀ x, TopologicalSpace (E₂ x)] [TopologicalSpace (TotalSpace F₂ E₂)]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]
  [FunLike K B' B] [ContinuousMapClass K B' B]

/-- Continuous linear maps between fibres of pullbacks are fibres of the pulled-back Hom bundle. -/
def homEquiv (f : K) (x : B') :
    (((f : B' → B) *ᵖ E₁) x →L[𝕜] ((f : B' → B) *ᵖ E₂) x) ≃L[𝕜]
      ((f : B' → B) *ᵖ (fun b ↦ E₁ b →L[𝕜] E₂ b)) x :=
  ContinuousLinearEquiv.refl 𝕜 _

omit [TopologicalSpace B] [TopologicalSpace B'] [ContinuousMapClass K B' B] in
/-- The pullback Hom identification keeps the underlying continuous linear map. -/
@[simp]
theorem homEquiv_apply (f : K) (x : B')
    (ℓ : ((f : B' → B) *ᵖ E₁) x →L[𝕜] ((f : B' → B) *ᵖ E₂) x) :
    homEquiv f x ℓ = ℓ :=
  (rfl)

omit [TopologicalSpace B] [TopologicalSpace B'] [ContinuousMapClass K B' B] in
/-- The inverse pullback Hom identification keeps the underlying continuous linear map. -/
@[simp]
theorem homEquiv_symm_apply (f : K) (x : B')
    (ℓ : ((f : B' → B) *ᵖ (fun b ↦ E₁ b →L[𝕜] E₂ b)) x) :
    (homEquiv (E₁ := E₁) (E₂ := E₂) f x).symm ℓ = ℓ :=
  (rfl)

omit [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)] in
/-- Near each point, Hom-bundle coordinates between pullbacks are the original Hom-bundle
coordinates at the image points. -/
private theorem eventually_inCoordinates_pullback_eq (f : K)
    (hf : Continuous f) (x₀ : B') :
    ∀ᶠ y in 𝓝 x₀, ∀ ℓ : E₁ (f y) →L[𝕜] E₂ (f y),
      ContinuousLinearMap.inCoordinates F₁ ((f : B' → B) *ᵖ E₁) F₂ ((f : B' → B) *ᵖ E₂)
          x₀ y x₀ y ℓ =
        ContinuousLinearMap.inCoordinates F₁ E₁ F₂ E₂ (f x₀) (f y) (f x₀) (f y) ℓ := by
  filter_upwards [hf.continuousAt.preimage_mem_nhds
      ((trivializationAt F₁ E₁ (f x₀)).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt F₁ E₁ (f x₀))),
    hf.continuousAt.preimage_mem_nhds
      ((trivializationAt F₂ E₂ (f x₀)).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt F₂ E₂ (f x₀)))] with y h₁ h₂ ℓ
  exact ContinuousLinearMap.inCoordinates_pullback_of_mem f f x₀ y ℓ h₁ h₂

/-- The pullback Hom identification is `C^n` on total spaces when `f` is. -/
theorem contMDiff_homEquiv (f : K) (hf : ContMDiff IB' IB n f) :
    ContMDiff (IB'.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) (IB'.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun p : TotalSpace (F₁ →L[𝕜] F₂)
          (fun x ↦ ((f : B' → B) *ᵖ E₁) x →L[𝕜] ((f : B' → B) *ᵖ E₂) x) ↦
        TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := (f : B' → B) *ᵖ (fun b ↦ E₁ b →L[𝕜] E₂ b))
          p.proj (homEquiv f p.proj p.snd)) := by
  refine (contMDiff_iff f hf).2 ⟨contMDiff_proj _, ?_⟩
  refine Bundle.contMDiff_totalSpace_of_eventuallyEq (h := id)
    (hf.comp (contMDiff_proj _)) contMDiff_id fun p ↦ ?_
  filter_upwards [(FiberBundle.continuous_proj (F₁ →L[𝕜] F₂)
    (fun x ↦ ((f : B' → B) *ᵖ E₁) x →L[𝕜] ((f : B' → B) *ᵖ E₂) x)).continuousAt.eventually
    (eventually_inCoordinates_pullback_eq (𝕜 := 𝕜) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂) f
      hf.continuous p.proj)] with q hq
  simp only [hom_trivializationAt_apply, homEquiv_apply, id]
  exact (hq q.snd).symm

/-- The inverse pullback Hom identification is `C^n` on total spaces when `f` is. -/
theorem contMDiff_homEquiv_symm (f : K) (hf : ContMDiff IB' IB n f) :
    ContMDiff (IB'.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) (IB'.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun p : TotalSpace (F₁ →L[𝕜] F₂) ((f : B' → B) *ᵖ (fun b ↦ E₁ b →L[𝕜] E₂ b)) ↦
        TotalSpace.mk' (F₁ →L[𝕜] F₂)
          (E := fun x ↦ ((f : B' → B) *ᵖ E₁) x →L[𝕜] ((f : B' → B) *ᵖ E₂) x)
          p.proj ((homEquiv f p.proj).symm p.snd)) := by
  refine Bundle.contMDiff_totalSpace_of_eventuallyEq (h := Pullback.lift f)
    (contMDiff_proj _) (contMDiff_lift f hf) fun p ↦ ?_
  filter_upwards [(FiberBundle.continuous_proj (F₁ →L[𝕜] F₂)
    ((f : B' → B) *ᵖ (fun b ↦ E₁ b →L[𝕜] E₂ b))).continuousAt.eventually
    (eventually_inCoordinates_pullback_eq (𝕜 := 𝕜) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂) f
      hf.continuous p.proj)] with q hq
  simp only [hom_trivializationAt_apply, Pullback.lift_proj, Pullback.lift_snd, homEquiv_symm_apply]
  exact hq q.snd

/-- For `C^n` `f`, the Hom bundle of two pullbacks and the pullback of the Hom bundle have
`C^n` diffeomorphic total spaces, by the identity on every fibre. -/
def homDiffeomorph (f : K) (hf : ContMDiff IB' IB n f) :
    TotalSpace (F₁ →L[𝕜] F₂)
        (fun x ↦ ((f : B' → B) *ᵖ E₁) x →L[𝕜] ((f : B' → B) *ᵖ E₂) x)
      ≃ₘ^n⟮IB'.prod 𝓘(𝕜, F₁ →L[𝕜] F₂), IB'.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)⟯
      TotalSpace (F₁ →L[𝕜] F₂) ((f : B' → B) *ᵖ (fun b ↦ E₁ b →L[𝕜] E₂ b)) where
  toFun p := ⟨p.proj, homEquiv f p.proj p.snd⟩
  invFun p := ⟨p.proj, (homEquiv f p.proj).symm p.snd⟩
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun := contMDiff_homEquiv f hf
  contMDiff_invFun := contMDiff_homEquiv_symm f hf

/-- The pullback Hom diffeomorphism acts by `homEquiv` over the same base point. -/
@[simp]
theorem homDiffeomorph_apply (f : K) (hf : ContMDiff IB' IB n f)
    (p : TotalSpace (F₁ →L[𝕜] F₂)
      (fun x ↦ ((f : B' → B) *ᵖ E₁) x →L[𝕜] ((f : B' → B) *ᵖ E₂) x)) :
    homDiffeomorph f hf p = ⟨p.proj, homEquiv f p.proj p.snd⟩ :=
  (rfl)

/-- The inverse pullback Hom diffeomorphism acts by the inverse of `homEquiv`. -/
@[simp]
theorem homDiffeomorph_symm_apply (f : K) (hf : ContMDiff IB' IB n f)
    (p : TotalSpace (F₁ →L[𝕜] F₂) ((f : B' → B) *ᵖ (fun b ↦ E₁ b →L[𝕜] E₂ b))) :
    (homDiffeomorph f hf).symm p = ⟨p.proj, (homEquiv f p.proj).symm p.snd⟩ :=
  (rfl)

end Bundle.Pullback
