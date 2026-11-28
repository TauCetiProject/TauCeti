/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Quotient.BundleMap
public import TauCeti.Geometry.Manifold.VectorBundle.Dual
import TauCeti.Geometry.Manifold.VectorBundle.Bilinear.SmulRight

/-!
# Compatibility of quotient bundle descent with dual bundles

For vector bundles over `M ⧸ G`, quotient descent preserves `C^m` regularity (`m ≤ n`) for dual
evaluation (`ContMDiff.orbitRelQuotientLift_dual_apply`) and fibrewise transpose maps
(`ContMDiff.section_dual_precomp_orbitRelQuotientRec`,
`TauCeti.contMDiff_totalSpaceMap_dual_precomp_orbitRelQuotientRec_iff`,
`TauCeti.exists_bundleDiffeomorph_dual_precomp_orbitRelQuotientRec_iff`).

## References
* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapters 10, 11, and 21.
-/

public section

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti

section Manifold

variable {G M 𝕜 E H : Type*} [Group G] [MulAction G M] [TopologicalSpace M]
  [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [ChartedSpace H M] {m n : ℕ∞ω}
  [ProperlyDiscontinuousSMul G M] [ContinuousConstSMul G M] [IsCancelSMul G M]
  [T2Space M] [LocallyCompactSpace M] [IsManifold I n M] [ContMDiffConstSMul I n G M]

/-- If an invariant dual-bundle section `α` and an invariant vector-bundle section `t` are `C^m`
upstairs (`m ≤ n`), the scalar descent of `x ↦ α x (t x)` is `C^m` on `M ⧸ G`. -/
theorem _root_.ContMDiff.orbitRelQuotientLift_dual_apply {F : Type*} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] {V : MulAction.orbitRel.Quotient G M → Type*}
    [∀ q, AddCommGroup (V q)] [∀ q, Module 𝕜 (V q)] [∀ q, TopologicalSpace (V q)]
    [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle 𝕜 F V]
    {α : ∀ x : M, StrongDual 𝕜 (V (Quotient.mk (MulAction.orbitRel G M) x))}
    {t : ∀ x : M, V (Quotient.mk (MulAction.orbitRel G M) x)}
    (hα_smooth : ContMDiff I (I.prod 𝓘(𝕜, StrongDual 𝕜 F)) m (fun x ↦ TotalSpace.mk'
      (StrongDual 𝕜 F) (E := fun q ↦ StrongDual 𝕜 (V q))
      (Quotient.mk (MulAction.orbitRel G M) x) (α x)))
    (ht_smooth : ContMDiff I (I.prod 𝓘(𝕜, F)) m
      (fun x ↦ TotalSpace.mk' F (Quotient.mk (MulAction.orbitRel G M) x) (t x)))
    (hα : ∀ (g : G) (x : M), α (g • x) ≍ α x) (ht : ∀ (g : G) (x : M), t (g • x) ≍ t x)
    (hm : m ≤ n) :
    ContMDiff I 𝓘(𝕜) m (MulAction.orbitRelQuotientLift (fun x ↦ α x (t x))
      (MulAction.apply₂_smul_eq (fun _ (f : StrongDual 𝕜 _) v ↦ f v) hα ht)) :=
  (contMDiff_orbitRelQuotientLift_iff hm).2 fun x ↦
    (hα_smooth x).clm_bundle_apply_scalar (ht_smooth x)

section Hom

variable {F₁ F₂ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] {V₁ V₂ : MulAction.orbitRel.Quotient G M → Type*}
  [∀ q, AddCommGroup (V₁ q)] [∀ q, Module 𝕜 (V₁ q)] [∀ q, TopologicalSpace (V₁ q)]
  [TopologicalSpace (TotalSpace F₁ V₁)] [FiberBundle F₁ V₁] [VectorBundle 𝕜 F₁ V₁]
  [∀ q, AddCommGroup (V₂ q)] [∀ q, Module 𝕜 (V₂ q)] [∀ q, TopologicalSpace (V₂ q)]
  [∀ q, IsTopologicalAddGroup (V₂ q)] [∀ q, ContinuousSMul 𝕜 (V₂ q)]
  [TopologicalSpace (TotalSpace F₂ V₂)] [FiberBundle F₂ V₂] [VectorBundle 𝕜 F₂ V₂]
  {φ : ∀ x : M, V₁ (Quotient.mk (MulAction.orbitRel G M) x) →L[𝕜]
    V₂ (Quotient.mk (MulAction.orbitRel G M) x)}

/-- If an invariant Hom-bundle family `φ` is `C^m` upstairs (`m ≤ n`), the descent of its fibrewise
dual (transpose) family is a `C^m` section of the dual Hom bundle on `M ⧸ G`. -/
theorem _root_.ContMDiff.section_dual_precomp_orbitRelQuotientRec
    (hφ_smooth : ContMDiff I (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) m (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂)
      (E := fun q ↦ V₁ q →L[𝕜] V₂ q) (Quotient.mk (MulAction.orbitRel G M) x) (φ x)))
    (hφ : ∀ (g : G) (x : M), φ (g • x) ≍ φ x) (hm : m ≤ n) :
    ContMDiff I (I.prod 𝓘(𝕜, StrongDual 𝕜 F₂ →L[𝕜] StrongDual 𝕜 F₁)) m (fun q ↦ TotalSpace.mk'
      (StrongDual 𝕜 F₂ →L[𝕜] StrongDual 𝕜 F₁) (E := fun q ↦ StrongDual 𝕜 (V₂ q) →L[𝕜]
        StrongDual 𝕜 (V₁ q)) q (MulAction.orbitRelQuotientRec
        (V := fun q ↦ StrongDual 𝕜 (V₂ q) →L[𝕜] StrongDual 𝕜 (V₁ q))
        (fun x ↦ ContinuousLinearMap.precomp 𝕜 (φ x))
        (MulAction.apply_smul_heq (fun _ A ↦ ContinuousLinearMap.precomp 𝕜 A) hφ) q)) :=
  (contMDiff_section_orbitRelQuotientRec_iff hm).2 hφ_smooth.clm_bundle_dual_precomp

section FiniteRank

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F₁] [FiniteDimensional 𝕜 F₂]
  {hφ : ∀ (g : G) (x : M), φ (g • x) ≍ φ x}

/-- In finite dimensions over a complete field, the descended dual linear family induces a `C^m`
map of dual total spaces (`m ≤ n`) iff `φ` is a `C^m` section of the pulled-back Hom bundle. -/
theorem contMDiff_totalSpaceMap_dual_precomp_orbitRelQuotientRec_iff (hm : m ≤ n) :
    ContMDiff (I.prod 𝓘(𝕜, StrongDual 𝕜 F₂)) (I.prod 𝓘(𝕜, StrongDual 𝕜 F₁)) m
        (fun p : TotalSpace (StrongDual 𝕜 F₂) (fun q ↦ StrongDual 𝕜 (V₂ q)) ↦ TotalSpace.mk'
          (StrongDual 𝕜 F₁) (E := fun q ↦ StrongDual 𝕜 (V₁ q)) p.proj
          (MulAction.orbitRelQuotientRec
            (V := fun q ↦ StrongDual 𝕜 (V₂ q) →L[𝕜] StrongDual 𝕜 (V₁ q))
            (fun x ↦ ContinuousLinearMap.precomp 𝕜 (φ x)) (MulAction.apply_smul_heq
              (fun _ A ↦ ContinuousLinearMap.precomp 𝕜 A) hφ) p.proj p.snd)) ↔
      ContMDiff I (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) m (fun x ↦ (TotalSpace.mk' (F₁ →L[𝕜] F₂) x (φ x) :
        TotalSpace (F₁ →L[𝕜] F₂) (⇑(⟨Quotient.mk _, continuous_quotient_mk'⟩ :
          C(M, MulAction.orbitRel.Quotient G M)) *ᵖ (fun q ↦ V₁ q →L[𝕜] V₂ q)))) := by
  conv_lhs =>
    enter [4, p]
    rw [← MulAction.apply_orbitRelQuotientRec (fun _ A ↦ ContinuousLinearMap.precomp 𝕜 A) hφ]
  rw [contMDiff_totalSpaceMap_dual_precomp_iff, contMDiff_totalSpaceMap_orbitRelQuotientRec_iff hm]

/-- In finite dimensions over a complete field, the descended dual linear family underlies a `C^m`
diffeomorphism of dual total spaces (`m ≤ n`) iff `φ` is a `C^m` section of the pulled-back Hom
bundle and every upstairs fibre map `φ x` is bijective. -/
theorem exists_bundleDiffeomorph_dual_precomp_orbitRelQuotientRec_iff (hm : m ≤ n) :
    (∃ Φ : TotalSpace (StrongDual 𝕜 F₂) (fun q ↦ StrongDual 𝕜 (V₂ q)) ≃ₘ^m⟮
        I.prod 𝓘(𝕜, StrongDual 𝕜 F₂), I.prod 𝓘(𝕜, StrongDual 𝕜 F₁)⟯
        TotalSpace (StrongDual 𝕜 F₁) (fun q ↦ StrongDual 𝕜 (V₁ q)),
        ⇑Φ = fun p ↦ TotalSpace.mk' (StrongDual 𝕜 F₁) (E := fun q ↦ StrongDual 𝕜 (V₁ q)) p.proj
          (MulAction.orbitRelQuotientRec
            (V := fun q ↦ StrongDual 𝕜 (V₂ q) →L[𝕜] StrongDual 𝕜 (V₁ q))
            (fun x ↦ ContinuousLinearMap.precomp 𝕜 (φ x)) (MulAction.apply_smul_heq
              (fun _ A ↦ ContinuousLinearMap.precomp 𝕜 A) hφ) p.proj p.snd)) ↔
      ContMDiff I (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) m (fun x ↦ (TotalSpace.mk' (F₁ →L[𝕜] F₂) x (φ x) :
          TotalSpace (F₁ →L[𝕜] F₂) (⇑(⟨Quotient.mk _, continuous_quotient_mk'⟩ :
            C(M, MulAction.orbitRel.Quotient G M)) *ᵖ (fun q ↦ V₁ q →L[𝕜] V₂ q)))) ∧
        ∀ x, Function.Bijective (φ x) := by
  conv_lhs =>
    enter [1, Φ, 2, p]
    rw [← MulAction.apply_orbitRelQuotientRec (fun _ A ↦ ContinuousLinearMap.precomp 𝕜 A) hφ]
  rw [exists_bundleDiffeomorph_dual_precomp_iff,
    exists_bundleDiffeomorph_orbitRelQuotientRec_iff hm]

end FiniteRank

end Hom

end Manifold

end TauCeti
