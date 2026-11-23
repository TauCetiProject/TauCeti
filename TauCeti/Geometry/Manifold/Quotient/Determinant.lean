/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Quotient.BundleMap
public import TauCeti.Geometry.Manifold.VectorBundle.Determinant

/-!
# Compatibility of quotient bundle descent with determinants

For vector bundles over `M ⧸ G`, quotient descent preserves `C^m` regularity (`m ≤ n`) of
endomorphism determinants (`ContMDiff.orbitRelQuotientLift_det`,
`TauCeti.exists_bundleDiffeomorph_orbitRelQuotientRec_iff_contMDiff_and_det_ne_zero`).

## References
* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapters 14 and 21.
-/

public section

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti

section Manifold

variable {G M 𝕜 E H : Type*} [Group G] [MulAction G M] [TopologicalSpace M]
  [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [ChartedSpace H M] {m n : ℕ∞ω} [ProperlyDiscontinuousSMul G M]
  [ContinuousConstSMul G M] [IsCancelSMul G M] [T2Space M] [LocallyCompactSpace M]
  [IsManifold I n M] [ContMDiffConstSMul I n G M] [CompleteSpace 𝕜] {F : Type*}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {V : MulAction.orbitRel.Quotient G M → Type*}
  [∀ q, AddCommGroup (V q)] [∀ q, Module 𝕜 (V q)] [∀ q, TopologicalSpace (V q)]
  [∀ q, IsTopologicalAddGroup (V q)] [∀ q, ContinuousSMul 𝕜 (V q)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle 𝕜 F V]
  {φ : ∀ x : M, V (Quotient.mk (MulAction.orbitRel G M) x) →L[𝕜]
    V (Quotient.mk (MulAction.orbitRel G M) x)}

/-- Over a complete field, if an invariant endomorphism family `φ` is `C^m` upstairs (`m ≤ n`), the
scalar descent of `x ↦ (φ x).det` is a `C^m` function on `M ⧸ G`. -/
theorem _root_.ContMDiff.orbitRelQuotientLift_det
    (hφ_smooth : ContMDiff I (I.prod 𝓘(𝕜, F →L[𝕜] F)) m (fun x ↦ TotalSpace.mk' (F →L[𝕜] F)
      (E := fun q ↦ V q →L[𝕜] V q) (Quotient.mk (MulAction.orbitRel G M) x) (φ x)))
    (hφ : ∀ (g : G) (x : M), φ (g • x) ≍ φ x) (hm : m ≤ n) :
    ContMDiff I 𝓘(𝕜) m (MulAction.orbitRelQuotientLift (fun x ↦ (φ x).det)
      (MulAction.apply_smul_eq (fun _ (A : _ →L[𝕜] _) ↦ A.det) hφ)) :=
  (contMDiff_orbitRelQuotientLift_iff hm).2 hφ_smooth.clm_bundle_det

/-- For a finite-rank vector bundle over `M ⧸ G`, `MulAction.orbitRelQuotientRec φ hφ` underlies a
`C^m` automorphism of `TotalSpace F V` (`m ≤ n`) iff `φ` is a `C^m` section of the pulled-back
endomorphism bundle and `(φ x).det ≠ 0` for every `x : M`. -/
theorem exists_bundleDiffeomorph_orbitRelQuotientRec_iff_contMDiff_and_det_ne_zero
    [FiniteDimensional 𝕜 F] {hφ : ∀ (g : G) (x : M), φ (g • x) ≍ φ x} (hm : m ≤ n) :
    (∃ Φ : TotalSpace F V ≃ₘ^m⟮I.prod 𝓘(𝕜, F), I.prod 𝓘(𝕜, F)⟯ TotalSpace F V,
        ⇑Φ = fun p ↦ TotalSpace.mk' F p.proj
          (MulAction.orbitRelQuotientRec (V := fun q ↦ V q →L[𝕜] V q) φ hφ p.proj p.snd)) ↔
      ContMDiff I (I.prod 𝓘(𝕜, F →L[𝕜] F)) m (fun x ↦ (TotalSpace.mk' (F →L[𝕜] F) x (φ x) :
          TotalSpace (F →L[𝕜] F) (⇑(⟨Quotient.mk _, continuous_quotient_mk'⟩ :
            C(M, MulAction.orbitRel.Quotient G M)) *ᵖ (fun q ↦ V q →L[𝕜] V q)))) ∧
        ∀ x : M, (φ x).det ≠ 0 := by
  rw [exists_bundleDiffeomorph_iff_contMDiff_and_det_ne_zero,
    contMDiff_totalSpaceMap_orbitRelQuotientRec_iff hm]
  exact and_congr_right fun _ ↦
    Quotient.mk_surjective.forall.trans (by simp only [MulAction.orbitRelQuotientRec_mk])

end Manifold

end TauCeti
