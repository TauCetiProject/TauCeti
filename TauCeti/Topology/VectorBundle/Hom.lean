/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.VectorBundle.Hom
public import Mathlib.Topology.VectorBundle.FiniteDimensional
public import TauCeti.Topology.VectorBundle.Coordinates
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Continuous bundle homomorphisms and their inverses

For a bundle with finite-dimensional model source, continuity of a fibrewise linear map
on total spaces is equivalent to continuity as a section of Mathlib's Hom bundle.
Consequently a continuous fibrewise linear equivalence gives a homeomorphism of total
spaces: continuity of the inverse need not be supplied separately.

We also prove local continuity of inversion for Hom-bundle sections with a Banach model
source. This local result does not require finite rank or invertibility away from the
point under consideration. The inverse is Mathlib's `ContinuousLinearMap.inverse`,
which is zero at noninvertible maps.

The coordinate argument uses `ContinuousLinearMap.inCoordinates_inverse` and parallels
the smooth inverse argument in `TauCeti.Geometry.Manifold.VectorBundle.Hom`.
For the classical finite-rank bundle-isomorphism criterion see Hatcher,
*Vector Bundles and K-Theory*, §1.1.
-/

public section

open Bundle FiberBundle Set
open scoped Topology

section

variable {𝕜 B F₁ F₂ M : Type*} [NontriviallyNormedField 𝕜]
  [TopologicalSpace B] [TopologicalSpace M]
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {E₁ : B → Type*} {E₂ : B → Type*}
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [∀ x, TopologicalSpace (E₁ x)] [TopologicalSpace (TotalSpace F₁ E₁)]
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [∀ x, TopologicalSpace (E₂ x)] [TopologicalSpace (TotalSpace F₂ E₂)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]

namespace TauCeti

/-- For a finite-dimensional model source, a fibrewise continuous linear map is continuous
on total spaces exactly when it is continuous as a section of the Hom bundle. The target
need not have finite rank. -/
theorem continuous_hom_bundle_iff [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F₁]
    (ϕ : ∀ x, E₁ x →L[𝕜] E₂ x) :
    Continuous (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) x (ϕ x)) ↔
      Continuous (fun p : TotalSpace F₁ E₁ ↦ TotalSpace.mk' F₂ p.proj (ϕ p.proj p.2)) := by
  constructor
  · intro hϕ
    exact (hϕ.comp (continuous_proj F₁ E₁)).clm_bundle_apply continuous_id
  · intro hϕ
    refine continuous_iff_continuousAt.mpr fun x ↦ ?_
    rw [continuousAt_hom_bundle]
    refine ⟨continuousAt_id, continuousAt_clm_apply.mpr fun v ↦ ?_⟩
    let e₁ := trivializationAt F₁ E₁ x
    let e₂ := trivializationAt F₂ E₂ x
    have h₁ : x ∈ e₁.baseSet := mem_baseSet_trivializationAt F₁ E₁ x
    have h₂ : x ∈ e₂.baseSet := mem_baseSet_trivializationAt F₂ E₂ x
    have hs : ContinuousAt (fun y ↦ TotalSpace.mk' F₁ y (e₁.symm y v)) x :=
      (e₁.continuousOn_symm.continuousAt
        ((e₁.open_baseSet.prod isOpen_univ).mem_nhds ⟨h₁, mem_univ v⟩)).comp
          (continuousAt_id.prodMk continuousAt_const)
    have ht := (e₂.continuousAt (e₂.mem_source.mpr h₂)).comp (hϕ.continuousAt.comp hs)
    refine ht.snd.congr_of_eventuallyEq ?_
    filter_upwards [e₁.open_baseSet.mem_nhds h₁, e₂.open_baseSet.mem_nhds h₂] with y hy₁ hy₂
    simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply]
    rw [(trivializationAt F₁ E₁ x).symmL_apply hy₁,
      Trivialization.continuousLinearMapAt_apply_of_mem 𝕜 _ hy₂]
    rfl

end TauCeti

section Inverse

variable [CompleteSpace F₁]
  [∀ x, IsTopologicalAddGroup (E₁ x)] [∀ x, ContinuousSMul 𝕜 (E₁ x)]
  {b : M → B} {ϕ : ∀ m, E₁ (b m) →L[𝕜] E₂ (b m)} {s : Set M} {x : M}

/-- Inversion of a continuous Hom-bundle section is continuous within a set at any point
where the fibre map is invertible. Only the model source must be complete. -/
theorem ContinuousWithinAt.clm_bundle_inverse
    (hϕ : ContinuousWithinAt
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun y ↦ E₁ y →L[𝕜] E₂ y)
        (b m) (ϕ m)) s x)
    (hx : (ϕ x).IsInvertible) :
    ContinuousWithinAt
      (fun m ↦ TotalSpace.mk' (F₂ →L[𝕜] F₁) (E := fun y ↦ E₂ y →L[𝕜] E₁ y)
        (b m) (ϕ m).inverse) s x := by
  simp only [continuousWithinAt_hom_bundle] at hϕ ⊢
  refine ⟨hϕ.1, ?_⟩
  have h₁ := mem_baseSet_trivializationAt F₁ E₁ (b x)
  have h₂ := mem_baseSet_trivializationAt F₂ E₂ (b x)
  have hinv : (ContinuousLinearMap.inCoordinates F₁ E₁ F₂ E₂ (b x) (b x) (b x) (b x)
      (ϕ x)).IsInvertible := by
    rw [ContinuousLinearMap.inCoordinates_eq h₁ h₂]
    exact ContinuousLinearMap.isInvertible_equiv.comp
      (hx.comp ContinuousLinearMap.isInvertible_equiv)
  have hev : ∀ᶠ m in 𝓝[s] x, b m ∈ (trivializationAt F₁ E₁ (b x)).baseSet ∧
      b m ∈ (trivializationAt F₂ E₂ (b x)).baseSet :=
    hϕ.1.preimage_mem_nhdsWithin <| Filter.inter_mem
      ((trivializationAt F₁ E₁ (b x)).open_baseSet.mem_nhds h₁)
      ((trivializationAt F₂ E₂ (b x)).open_baseSet.mem_nhds h₂)
  have hcomp := (hinv.contDiffAt_map_inverse (n := 0)).continuousAt.comp_continuousWithinAt
    (f := fun m : M ↦ ContinuousLinearMap.inCoordinates F₁ E₁ F₂ E₂
      (b x) (b m) (b x) (b m) (ϕ m)) hϕ.2
  refine hcomp.congr_of_eventuallyEq ?_
    (ContinuousLinearMap.inCoordinates_inverse (ϕ x) h₁ h₂)
  filter_upwards [hev] with m hm
  exact ContinuousLinearMap.inCoordinates_inverse (ϕ m) hm.1 hm.2

/-- Inversion of a continuous Hom-bundle section is continuous at a point where its fibre
map is invertible. -/
theorem ContinuousAt.clm_bundle_inverse
    (hϕ : ContinuousAt (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂)
      (E := fun y ↦ E₁ y →L[𝕜] E₂ y) (b m) (ϕ m)) x)
    (hx : (ϕ x).IsInvertible) :
    ContinuousAt (fun m ↦ TotalSpace.mk' (F₂ →L[𝕜] F₁)
      (E := fun y ↦ E₂ y →L[𝕜] E₁ y) (b m) (ϕ m).inverse) x := by
  rw [← continuousWithinAt_univ] at hϕ ⊢
  exact hϕ.clm_bundle_inverse hx

/-- Inversion preserves continuity on a set of fibrewise invertible Hom-bundle maps. -/
theorem ContinuousOn.clm_bundle_inverse
    (hϕ : ContinuousOn (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂)
      (E := fun y ↦ E₁ y →L[𝕜] E₂ y) (b m) (ϕ m)) s)
    (hs : ∀ x ∈ s, (ϕ x).IsInvertible) :
    ContinuousOn (fun m ↦ TotalSpace.mk' (F₂ →L[𝕜] F₁)
      (E := fun y ↦ E₂ y →L[𝕜] E₁ y) (b m) (ϕ m).inverse) s :=
  fun x hx ↦ (hϕ x hx).clm_bundle_inverse (hs x hx)

/-- Inversion preserves continuity of a fibrewise invertible Hom-bundle section. -/
theorem Continuous.clm_bundle_inverse
    (hϕ : Continuous (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂)
      (E := fun y ↦ E₁ y →L[𝕜] E₂ y) (b m) (ϕ m)))
    (hinv : ∀ x, (ϕ x).IsInvertible) :
    Continuous (fun m ↦ TotalSpace.mk' (F₂ →L[𝕜] F₁)
      (E := fun y ↦ E₂ y →L[𝕜] E₁ y) (b m) (ϕ m).inverse) :=
  continuous_iff_continuousAt.mpr fun x ↦ hϕ.continuousAt.clm_bundle_inverse (hinv x)

end Inverse

namespace TauCeti

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F₁]
  [∀ x, IsTopologicalAddGroup (E₁ x)] [∀ x, ContinuousSMul 𝕜 (E₁ x)]

/-- A continuous fibrewise linear equivalence with finite-dimensional model source has a
continuous inverse on total spaces. No compactness or separation of the base is needed. -/
theorem continuous_bundle_symm (e : ∀ x, E₁ x ≃L[𝕜] E₂ x)
    (he : Continuous (fun p : TotalSpace F₁ E₁ ↦ TotalSpace.mk' F₂ p.proj (e p.proj p.2))) :
    Continuous (fun p : TotalSpace F₂ E₂ ↦ TotalSpace.mk' F₁ p.proj ((e p.proj).symm p.2)) := by
  let := FiniteDimensional.complete 𝕜 F₁
  have h := (continuous_hom_bundle_iff (fun x ↦ (e x).toContinuousLinearMap)).mpr he
  have hi := h.clm_bundle_inverse (fun x ↦ ContinuousLinearMap.isInvertible_equiv)
  have ha := (hi.comp (continuous_proj F₂ E₂)).clm_bundle_apply continuous_id
  simpa only [ContinuousLinearMap.inverse_equiv, ContinuousLinearEquiv.coe_coe] using ha

/-- The homeomorphism of total spaces induced by a continuous family of fibrewise linear
equivalences. Continuity of the inverse follows from finite dimensionality. -/
def bundleHomeomorph (e : ∀ x, E₁ x ≃L[𝕜] E₂ x)
    (he : Continuous (fun p : TotalSpace F₁ E₁ ↦ TotalSpace.mk' F₂ p.proj (e p.proj p.2))) :
    TotalSpace F₁ E₁ ≃ₜ TotalSpace F₂ E₂ where
  toFun p := ⟨p.proj, e p.proj p.2⟩
  invFun p := ⟨p.proj, (e p.proj).symm p.2⟩
  left_inv p := by simp
  right_inv p := by simp
  continuous_toFun := he
  continuous_invFun := continuous_bundle_symm e he

@[simp]
theorem bundleHomeomorph_apply (e : ∀ x, E₁ x ≃L[𝕜] E₂ x)
    (he : Continuous (fun p : TotalSpace F₁ E₁ ↦ TotalSpace.mk' F₂ p.proj (e p.proj p.2)))
    (p : TotalSpace F₁ E₁) : bundleHomeomorph e he p = ⟨p.proj, e p.proj p.2⟩ :=
  (rfl)

@[simp]
theorem bundleHomeomorph_symm_apply (e : ∀ x, E₁ x ≃L[𝕜] E₂ x)
    (he : Continuous (fun p : TotalSpace F₁ E₁ ↦ TotalSpace.mk' F₂ p.proj (e p.proj p.2)))
    (p : TotalSpace F₂ E₂) : (bundleHomeomorph e he).symm p = ⟨p.proj, (e p.proj).symm p.2⟩ :=
  (rfl)

/-- A continuous fibrewise bijective linear map between vector bundles with a
finite-dimensional model source is induced by a homeomorphism of total spaces. -/
theorem exists_bundleHomeomorph_of_bijective (ϕ : ∀ x, E₁ x →L[𝕜] E₂ x)
    (hϕ : Continuous (fun p : TotalSpace F₁ E₁ ↦ TotalSpace.mk' F₂ p.proj (ϕ p.proj p.2)))
    (hbij : ∀ x, Function.Bijective (ϕ x)) :
    ∃ h : TotalSpace F₁ E₁ ≃ₜ TotalSpace F₂ E₂,
      ∀ (x : B) (v : E₁ x), h ⟨x, v⟩ = ⟨x, ϕ x v⟩ := by
  let e (x : B) : E₁ x ≃L[𝕜] E₂ x := by
    let := FiberBundle.t2Space F₁ E₁ x
    let := FiberBundle.t2Space F₂ E₂ x
    let := VectorBundle.finiteDimensional 𝕜 F₁ E₁ x
    exact (LinearEquiv.ofBijective (ϕ x).toLinearMap (hbij x)).toContinuousLinearEquiv
  have he : Continuous (fun p : TotalSpace F₁ E₁ ↦ TotalSpace.mk' F₂ p.proj (e p.proj p.2)) := hϕ
  exact ⟨bundleHomeomorph e he, fun _ _ ↦ rfl⟩

end TauCeti

end
