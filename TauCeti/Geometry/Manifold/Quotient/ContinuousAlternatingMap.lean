/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Quotient.Section
public import TauCeti.Geometry.Manifold.VectorBundle.ContinuousAlternatingMap

/-!
# Compatibility of quotient bundle descent with alternating-map bundles

Let `q : M → M ⧸ G` be the orbit projection of a free properly discontinuous action by `C^n` maps
on a `C^n` manifold `M`. For vector bundles over `M ⧸ G`, quotient descent preserves `C^m`
regularity (`m ≤ n`) of alternating-map domain pullbacks
(`ContMDiff.section_compContinuousLinearMap_orbitRelQuotientRec`).
-/

public section

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti

section Manifold

variable {G M 𝕜 E H ι F₁ F₂ F₃ : Type*} [Group G] [MulAction G M] [TopologicalSpace M]
  [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [ChartedSpace H M] {m n : ℕ∞ω} [ProperlyDiscontinuousSMul G M]
  [ContinuousConstSMul G M] [IsCancelSMul G M] [T2Space M] [LocallyCompactSpace M]
  [IsManifold I n M] [ContMDiffConstSMul I n G M] [Fintype ι] [NormedAddCommGroup F₁]
  [NormedSpace 𝕜 F₁] [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [NormedAddCommGroup F₃]
  [NormedSpace 𝕜 F₃]
  {V₁ V₂ V₃ : MulAction.orbitRel.Quotient G M → Type*}
  [∀ q, AddCommGroup (V₁ q)] [∀ q, Module 𝕜 (V₁ q)] [∀ q, TopologicalSpace (V₁ q)]
  [TopologicalSpace (TotalSpace F₁ V₁)] [FiberBundle F₁ V₁] [VectorBundle 𝕜 F₁ V₁]
  [∀ q, AddCommGroup (V₂ q)] [∀ q, Module 𝕜 (V₂ q)] [∀ q, TopologicalSpace (V₂ q)]
  [∀ q, IsTopologicalAddGroup (V₂ q)] [∀ q, ContinuousSMul 𝕜 (V₂ q)]
  [TopologicalSpace (TotalSpace F₂ V₂)] [FiberBundle F₂ V₂] [VectorBundle 𝕜 F₂ V₂]
  [∀ q, AddCommGroup (V₃ q)] [∀ q, Module 𝕜 (V₃ q)] [∀ q, TopologicalSpace (V₃ q)]
  [∀ q, IsTopologicalAddGroup (V₃ q)] [∀ q, ContinuousSMul 𝕜 (V₃ q)]
  [TopologicalSpace (TotalSpace F₃ V₃)] [FiberBundle F₃ V₃] [VectorBundle 𝕜 F₃ V₃]

/-- If an invariant alternating-map family `α` and an invariant linear family `A` are `C^m`
upstairs (`m ≤ n`), the descent of `x ↦ (α x).compContinuousLinearMap (A x)` is a `C^m` section of
the alternating-map bundle over `M ⧸ G`. -/
theorem _root_.ContMDiff.section_compContinuousLinearMap_orbitRelQuotientRec
    {α : ∀ x : M, V₂ (Quotient.mk (MulAction.orbitRel G M) x) [⋀^ι]→L[𝕜]
      V₃ (Quotient.mk (MulAction.orbitRel G M) x)}
    {A : ∀ x : M, V₁ (Quotient.mk (MulAction.orbitRel G M) x) →L[𝕜]
      V₂ (Quotient.mk (MulAction.orbitRel G M) x)}
    (hα_smooth : ContMDiff I (I.prod 𝓘(𝕜, F₂ [⋀^ι]→L[𝕜] F₃)) m (fun x ↦ TotalSpace.mk'
      (F₂ [⋀^ι]→L[𝕜] F₃) (E := fun q ↦ V₂ q [⋀^ι]→L[𝕜] V₃ q)
      (Quotient.mk (MulAction.orbitRel G M) x) (α x)))
    (hA_smooth : ContMDiff I (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) m (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂)
      (E := fun q ↦ V₁ q →L[𝕜] V₂ q) (Quotient.mk (MulAction.orbitRel G M) x) (A x)))
    (hα : ∀ (g : G) (x : M), α (g • x) ≍ α x) (hA : ∀ (g : G) (x : M), A (g • x) ≍ A x)
    (hm : m ≤ n) (hfact : m = ω → ((Fintype.card ι).factorial : 𝕜) ≠ 0 := by
      intro h; first | exact NeZero.ne _ | cases h) :
    ContMDiff I (I.prod 𝓘(𝕜, F₁ [⋀^ι]→L[𝕜] F₃)) m (fun q ↦ TotalSpace.mk' (F₁ [⋀^ι]→L[𝕜] F₃)
      (E := fun q ↦ V₁ q [⋀^ι]→L[𝕜] V₃ q) q (MulAction.orbitRelQuotientRec
        (V := fun q ↦ V₁ q [⋀^ι]→L[𝕜] V₃ q) (fun x ↦ (α x).compContinuousLinearMap (A x))
        (MulAction.apply₂_smul_heq (fun _ (f : _ [⋀^ι]→L[𝕜] _) (T : _ →L[𝕜] _) ↦
          f.compContinuousLinearMap T) hα hA) q)) :=
  (contMDiff_section_orbitRelQuotientRec_iff hm).2
    (hα_smooth.continuousAlternatingMap_bundle_compContinuousLinearMap hA_smooth hfact)

end Manifold

end TauCeti
