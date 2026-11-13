/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.EquivariantBilinear
public import Mathlib.Geometry.Manifold.VectorBundle.Basic

/-!
# Smooth bilinear operations on associated bundles

The bilinear operation descended from an equivariant continuous bilinear map preserves smooth
families in the native associated total spaces. In particular it acts on smooth sections.
The model spaces can be different, as for Clifford multiplication of a covector and a spinor.

These statements compare the existing bundle charts and require neither a fibre metric nor
finite rank. Smoothness of the associated bundles themselves is supplied separately by smooth
principal transitions and smooth actions.

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, §10.7.
-/

public section

open Bundle Filter Set TauCeti TauCeti.AssociatedBundle
open scoped Manifold Topology ContDiff

variable {n : ℕ∞ω} {𝕜 B G F₁ F₂ F₃ M : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
  [TopologicalSpace B] [ChartedSpace HB B] [Group G] [TopologicalSpace G]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [DistribMulAction G F₁] [SMulCommClass G 𝕜 F₁] [ContinuousSMul G F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  [DistribMulAction G F₂] [SMulCommClass G 𝕜 F₂] [ContinuousSMul G F₂]
  [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃]
  [DistribMulAction G F₃] [SMulCommClass G 𝕜 F₃] [ContinuousSMul G F₃]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners 𝕜 EM HM}
  [TopologicalSpace M] [ChartedSpace HM M]
  (β : F₁ →L[𝕜] F₂ →L[𝕜] F₃)
  (hβ : ∀ (g : G) v w, β (g • v) (g • w) = g • β v w)
  {f : M → B} {v : ∀ x, AssociatedBundle G P F₁ (f x)}
  {w : ∀ x, AssociatedBundle G P F₂ (f x)} {s : Set M} {x₀ : M}

/-- A descended bilinear operation preserves families `C^n` within a set at a point. -/
theorem ContMDiffWithinAt.associatedBundleBilinearMap
    (hv : ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F₁)) n
      (fun x ↦ (⟨f x, v x⟩ : TotalSpace F₁ (AssociatedBundle G P F₁))) s x₀)
    (hw : ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F₂)) n
      (fun x ↦ (⟨f x, w x⟩ : TotalSpace F₂ (AssociatedBundle G P F₂))) s x₀) :
    ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F₃)) n
      (fun x ↦ (⟨f x, bilinearMap β hβ (f x) (v x) (w x)⟩ :
        TotalSpace F₃ (AssociatedBundle G P F₃))) s x₀ := by
  rw [contMDiffWithinAt_totalSpace_iff] at hv hw ⊢
  refine ⟨hv.1, ?_⟩
  have h := β.isBoundedBilinearMap.contDiff.comp_contMDiffWithinAt (hv.2.prodMk_space hw.2)
  have h₀ := mem_baseSet_trivializationAt G P (f x₀)
  refine h.congr_of_eventuallyEq ?_ (trivializationAt_bilinearMap β hβ h₀ _ _)
  filter_upwards [hv.1.continuousWithinAt
    ((trivializationAt G P (f x₀)).open_baseSet.mem_nhds h₀)] with x hx
  exact trivializationAt_bilinearMap β hβ hx _ _

/-- A descended bilinear operation preserves families `C^n` at a point. -/
theorem ContMDiffAt.associatedBundleBilinearMap
    (hv : ContMDiffAt IM (IB.prod 𝓘(𝕜, F₁)) n
      (fun x ↦ (⟨f x, v x⟩ : TotalSpace F₁ (AssociatedBundle G P F₁))) x₀)
    (hw : ContMDiffAt IM (IB.prod 𝓘(𝕜, F₂)) n
      (fun x ↦ (⟨f x, w x⟩ : TotalSpace F₂ (AssociatedBundle G P F₂))) x₀) :
    ContMDiffAt IM (IB.prod 𝓘(𝕜, F₃)) n
      (fun x ↦ (⟨f x, bilinearMap β hβ (f x) (v x) (w x)⟩ :
        TotalSpace F₃ (AssociatedBundle G P F₃))) x₀ :=
  ContMDiffWithinAt.associatedBundleBilinearMap β hβ hv hw

/-- A descended bilinear operation preserves families `C^n` on a set. -/
theorem ContMDiffOn.associatedBundleBilinearMap
    (hv : ContMDiffOn IM (IB.prod 𝓘(𝕜, F₁)) n
      (fun x ↦ (⟨f x, v x⟩ : TotalSpace F₁ (AssociatedBundle G P F₁))) s)
    (hw : ContMDiffOn IM (IB.prod 𝓘(𝕜, F₂)) n
      (fun x ↦ (⟨f x, w x⟩ : TotalSpace F₂ (AssociatedBundle G P F₂))) s) :
    ContMDiffOn IM (IB.prod 𝓘(𝕜, F₃)) n
      (fun x ↦ (⟨f x, bilinearMap β hβ (f x) (v x) (w x)⟩ :
        TotalSpace F₃ (AssociatedBundle G P F₃))) s :=
  fun x hx ↦ (hv x hx).associatedBundleBilinearMap β hβ (hw x hx)

/-- A descended bilinear operation preserves `C^n` families, including smooth sections. -/
theorem ContMDiff.associatedBundleBilinearMap
    (hv : ContMDiff IM (IB.prod 𝓘(𝕜, F₁)) n
      (fun x ↦ (⟨f x, v x⟩ : TotalSpace F₁ (AssociatedBundle G P F₁))))
    (hw : ContMDiff IM (IB.prod 𝓘(𝕜, F₂)) n
      (fun x ↦ (⟨f x, w x⟩ : TotalSpace F₂ (AssociatedBundle G P F₂)))) :
    ContMDiff IM (IB.prod 𝓘(𝕜, F₃)) n
      (fun x ↦ (⟨f x, bilinearMap β hβ (f x) (v x) (w x)⟩ :
        TotalSpace F₃ (AssociatedBundle G P F₃))) :=
  fun x ↦ (hv x).associatedBundleBilinearMap β hβ (hw x)
