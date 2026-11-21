/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Quotient.BundleMap
public import TauCeti.Geometry.Manifold.VectorBundle.ContinuousAlternatingMap
public import TauCeti.Geometry.Manifold.VectorBundle.Determinant
public import TauCeti.Topology.VectorBundle.OrbitRelQuotient

/-!
# Compatibility of quotient bundle descent with determinants and top-degree forms

Let `q : M → M ⧸ G` be the orbit projection of a free properly discontinuous action by `C^n` maps
on a `C^n` manifold `M`. For vector bundles over `M ⧸ G`, quotient descent preserves `C^m`
regularity (`m ≤ n`) of endomorphism determinants (`ContMDiff.orbitRelQuotientLift_det`,
`TauCeti.exists_bundleDiffeomorph_orbitRelQuotientRec_iff_det_ne_zero`) and alternating-form
pullbacks (`ContMDiff.section_compContinuousLinearMap_orbitRelQuotientRec`), building on the
pointwise compatibility in `TauCeti.Topology.VectorBundle.OrbitRelQuotient`.

Over `ℂ` at regularity `∞`, these results express compatibility of holomorphic quotient descent
with endomorphism determinants and the determinant line bundle `⋀^r V^*`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapters 14 and 21.
* Daniel Huybrechts, *Complex Geometry: An Introduction*, Section 2.2.
-/

public section

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti

section Manifold

variable {G M 𝕜 : Type*} [Group G] [MulAction G M] [TopologicalSpace M]
  [NontriviallyNormedField 𝕜]
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [ChartedSpace H M] {m n : ℕ∞ω}
  [ProperlyDiscontinuousSMul G M] [ContinuousConstSMul G M] [IsCancelSMul G M]
  [T2Space M] [LocallyCompactSpace M] [IsManifold I n M] [ContMDiffConstSMul I n G M]

section DetSmooth

variable [CompleteSpace 𝕜]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : MulAction.orbitRel.Quotient G M → Type*}
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

/-- For a finite-rank vector bundle over `M ⧸ G`, the descended endomorphism family
`MulAction.orbitRelQuotientRec φ hφ` underlies a `C^m` automorphism of `TotalSpace F V` (`m ≤ n`)
if and only if `φ` is a `C^m` section of the pulled-back endomorphism bundle and `(φ x).det ≠ 0`
for every `x : M`. -/
theorem exists_bundleDiffeomorph_orbitRelQuotientRec_iff_det_ne_zero [FiniteDimensional 𝕜 F]
    {hφ : ∀ (g : G) (x : M), φ (g • x) ≍ φ x} (hm : m ≤ n) :
    (∃ Φ : TotalSpace F V ≃ₘ^m⟮I.prod 𝓘(𝕜, F), I.prod 𝓘(𝕜, F)⟯ TotalSpace F V,
        ⇑Φ = fun p ↦ TotalSpace.mk' F p.proj
          (MulAction.orbitRelQuotientRec (V := fun q ↦ V q →L[𝕜] V q) φ hφ p.proj p.snd)) ↔
      ContMDiff I (I.prod 𝓘(𝕜, F →L[𝕜] F)) m (fun x ↦ (TotalSpace.mk' (F →L[𝕜] F) x (φ x) :
          TotalSpace (F →L[𝕜] F) (⇑(⟨Quotient.mk _, continuous_quotient_mk'⟩ :
            C(M, MulAction.orbitRel.Quotient G M)) *ᵖ (fun q ↦ V q →L[𝕜] V q)))) ∧
        ∀ x : M, (φ x).det ≠ 0 := by
  rw [exists_bundleDiffeomorph_iff_det_ne_zero, contMDiff_totalSpaceMap_orbitRelQuotientRec_iff hm]
  exact and_congr_right fun _ ↦
    Quotient.mk_surjective.forall.trans (by simp only [MulAction.orbitRelQuotientRec_mk])

end DetSmooth

section AlternatingSmooth

variable {ι : Type*} [Fintype ι] {F₁ F₂ F₃ : Type*}
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃]
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
    (hα_smooth : ContMDiff I (I.prod 𝓘(𝕜, F₂ [⋀^ι]→L[𝕜] F₃)) m (fun x ↦
      TotalSpace.mk' (F₂ [⋀^ι]→L[𝕜] F₃) (E := fun q ↦ V₂ q [⋀^ι]→L[𝕜] V₃ q)
        (Quotient.mk (MulAction.orbitRel G M) x) (α x)))
    (hA_smooth : ContMDiff I (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) m (fun x ↦
      TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun q ↦ V₁ q →L[𝕜] V₂ q)
        (Quotient.mk (MulAction.orbitRel G M) x) (A x)))
    (hα : ∀ (g : G) (x : M), α (g • x) ≍ α x) (hA : ∀ (g : G) (x : M), A (g • x) ≍ A x)
    (hm : m ≤ n) (hfact : m = ω → ((Fintype.card ι).factorial : 𝕜) ≠ 0 := by
      intro h; first | exact NeZero.ne _ | cases h) :
    ContMDiff I (I.prod 𝓘(𝕜, F₁ [⋀^ι]→L[𝕜] F₃)) m (fun q ↦ TotalSpace.mk' (F₁ [⋀^ι]→L[𝕜] F₃)
      (E := fun q ↦ V₁ q [⋀^ι]→L[𝕜] V₃ q) q (MulAction.orbitRelQuotientRec
        (V := fun q ↦ V₁ q [⋀^ι]→L[𝕜] V₃ q) (fun x ↦ (α x).compContinuousLinearMap (A x))
        (MulAction.apply₂_smul_heq (fun _ (f : _ [⋀^ι]→L[𝕜] _) (T : _ →L[𝕜] _) ↦
          f.compContinuousLinearMap T) hα hA) q)) :=
  (contMDiff_section_orbitRelQuotientRec_iff hm).2
    (hα_smooth.continuousAlternatingMap_comp_clm hA_smooth hfact)

end AlternatingSmooth

end Manifold

end TauCeti
