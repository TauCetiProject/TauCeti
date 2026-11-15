/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Quotient.BundleMap
public import TauCeti.Geometry.Manifold.VectorBundle.Dual

/-!
# Compatibility of quotient bundle descent with dual bundles

Let `q : M → M ⧸ G` be the orbit projection of a free properly discontinuous action by `C^n` maps
on a `C^n` manifold `M`. For vector bundles over `M ⧸ G`, quotient descent commutes with the two
fundamental dual-bundle operations:

* **Dual evaluation pairing:** evaluating the descended covector section
  `MulAction.orbitRelQuotientRec α hα` on the descended vector section
  `MulAction.orbitRelQuotientRec t ht` agrees with the scalar descent
  `MulAction.orbitRelQuotientLift` of the upstairs pairing `x ↦ α x (t x)`
  (`TauCeti.orbitRelQuotientRec_dual_apply`), and is `C^m` for `m ≤ n` whenever both sections are
  `C^m` upstairs (`TauCeti.ContMDiff.orbitRelQuotientLift_dual_apply`).
* **Fibrewise precomposition and dual (transpose) bundle maps:** precomposing into a third bundle,
  and in particular taking the fibrewise dual `ContinuousLinearMap.precomp 𝕜`, commutes with
  `MulAction.orbitRelQuotientRec` (`TauCeti.precomp_orbitRelQuotientRec`,
  `TauCeti.dualMap_orbitRelQuotientRec`) and preserves `C^m` Hom-section regularity without finite
  rank (`TauCeti.ContMDiff.section_dualMap_orbitRelQuotientRec`). When `𝕜` is complete and both
  model fibres are finite-dimensional, `C^m` regularity and `C^m` bundle-diffeomorphism
  realizability of the descended dual total-space map are equivalent to the corresponding upstairs
  criteria on the primal linear family
  (`TauCeti.contMDiff_totalSpaceMap_dualMap_orbitRelQuotientRec_iff`,
  `TauCeti.exists_bundleDiffeomorph_dualMap_orbitRelQuotientRec_iff`).

Over `ℂ` at regularity `∞`, these results express compatibility of holomorphic quotient descent
with holomorphic dual bundles.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapters 10, 11, and 21.
* Daniel Huybrechts, *Complex Geometry: An Introduction*, Section 2.2.
-/

public section

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti

section Algebraic

variable {G M 𝕜 : Type*} [Group G] [MulAction G M] [NontriviallyNormedField 𝕜]

/-- Pairing a descended dual-bundle section with a descended vector-bundle section over `M ⧸ G`
agrees with the scalar descent `MulAction.orbitRelQuotientLift` of their upstairs pairing. -/
theorem orbitRelQuotientRec_dual_apply {V : MulAction.orbitRel.Quotient G M → Type*}
    [∀ q, AddCommGroup (V q)] [∀ q, Module 𝕜 (V q)] [∀ q, TopologicalSpace (V q)]
    {α : ∀ x : M, StrongDual 𝕜 (V (Quotient.mk (MulAction.orbitRel G M) x))}
    {t : ∀ x : M, V (Quotient.mk (MulAction.orbitRel G M) x)}
    (hα : ∀ (g : G) (x : M), α (g • x) ≍ α x)
    (ht : ∀ (g : G) (x : M), t (g • x) ≍ t x)
    (q : MulAction.orbitRel.Quotient G M) :
    MulAction.orbitRelQuotientRec (V := fun q ↦ StrongDual 𝕜 (V q)) α hα q
        (MulAction.orbitRelQuotientRec t ht q) =
      MulAction.orbitRelQuotientLift (fun x ↦ α x (t x))
        (MulAction.apply₂_eq_of_heq (fun _ (f : StrongDual 𝕜 _) v ↦ f v) hα ht) q :=
  MulAction.apply₂_orbitRelQuotientRec_eq_orbitRelQuotientLift
    (fun _ (f : StrongDual 𝕜 _) v ↦ f v) hα ht q

/-- Fibrewise precomposition into any third bundle `V₃` over `M ⧸ G` commutes with
`MulAction.orbitRelQuotientRec`. -/
theorem precomp_orbitRelQuotientRec {V₁ V₂ : MulAction.orbitRel.Quotient G M → Type*}
    (V₃ : MulAction.orbitRel.Quotient G M → Type*)
    [∀ q, AddCommGroup (V₁ q)] [∀ q, Module 𝕜 (V₁ q)] [∀ q, TopologicalSpace (V₁ q)]
    [∀ q, AddCommGroup (V₂ q)] [∀ q, Module 𝕜 (V₂ q)] [∀ q, TopologicalSpace (V₂ q)]
    [∀ q, AddCommGroup (V₃ q)] [∀ q, Module 𝕜 (V₃ q)] [∀ q, TopologicalSpace (V₃ q)]
    [∀ q, IsTopologicalAddGroup (V₃ q)] [∀ q, ContinuousSMul 𝕜 (V₃ q)]
    {φ : ∀ x : M, V₁ (Quotient.mk (MulAction.orbitRel G M) x) →L[𝕜]
      V₂ (Quotient.mk (MulAction.orbitRel G M) x)}
    (hφ : ∀ (g : G) (x : M), φ (g • x) ≍ φ x)
    (q : MulAction.orbitRel.Quotient G M) :
    ContinuousLinearMap.precomp (V₃ q)
        (MulAction.orbitRelQuotientRec (V := fun q ↦ V₁ q →L[𝕜] V₂ q) φ hφ q) =
      MulAction.orbitRelQuotientRec
        (V := fun q ↦ (V₂ q →L[𝕜] V₃ q) →L[𝕜] V₁ q →L[𝕜] V₃ q)
        (fun x ↦ ContinuousLinearMap.precomp (V₃ (Quotient.mk (MulAction.orbitRel G M) x)) (φ x))
        (MulAction.apply_heq_of_heq (fun q A ↦ ContinuousLinearMap.precomp (V₃ q) A) hφ) q :=
  MulAction.apply_orbitRelQuotientRec (fun q A ↦ ContinuousLinearMap.precomp (V₃ q) A) hφ q

/-- Fibrewise dual (transpose) `ContinuousLinearMap.precomp 𝕜` commutes with
`MulAction.orbitRelQuotientRec`. -/
theorem dualMap_orbitRelQuotientRec {V₁ V₂ : MulAction.orbitRel.Quotient G M → Type*}
    [∀ q, AddCommGroup (V₁ q)] [∀ q, Module 𝕜 (V₁ q)] [∀ q, TopologicalSpace (V₁ q)]
    [∀ q, AddCommGroup (V₂ q)] [∀ q, Module 𝕜 (V₂ q)] [∀ q, TopologicalSpace (V₂ q)]
    {φ : ∀ x : M, V₁ (Quotient.mk (MulAction.orbitRel G M) x) →L[𝕜]
      V₂ (Quotient.mk (MulAction.orbitRel G M) x)}
    (hφ : ∀ (g : G) (x : M), φ (g • x) ≍ φ x)
    (q : MulAction.orbitRel.Quotient G M) :
    ContinuousLinearMap.precomp 𝕜
        (MulAction.orbitRelQuotientRec (V := fun q ↦ V₁ q →L[𝕜] V₂ q) φ hφ q) =
      MulAction.orbitRelQuotientRec
        (V := fun q ↦ StrongDual 𝕜 (V₂ q) →L[𝕜] StrongDual 𝕜 (V₁ q))
        (fun x ↦ ContinuousLinearMap.precomp 𝕜 (φ x))
        (MulAction.apply_heq_of_heq (fun _ A ↦ ContinuousLinearMap.precomp 𝕜 A) hφ) q :=
  MulAction.apply_orbitRelQuotientRec (fun _ A ↦ ContinuousLinearMap.precomp 𝕜 A) hφ q

end Algebraic

section Manifold

variable {G M 𝕜 : Type*} [Group G] [MulAction G M] [TopologicalSpace M]
  [NontriviallyNormedField 𝕜]
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [ChartedSpace H M] {m n : ℕ∞ω}
  [ProperlyDiscontinuousSMul G M] [ContinuousConstSMul G M] [IsCancelSMul G M]
  [T2Space M] [LocallyCompactSpace M] [IsManifold I n M] [ContMDiffConstSMul I n G M]

/-- If an invariant dual-bundle section `α` and an invariant vector-bundle section `t` are `C^m`
upstairs (`m ≤ n`), the scalar descent of their pairing `x ↦ α x (t x)` is `C^m` on `M ⧸ G`. -/
theorem ContMDiff.orbitRelQuotientLift_dual_apply {F : Type*} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] {V : MulAction.orbitRel.Quotient G M → Type*}
    [∀ q, AddCommGroup (V q)] [∀ q, Module 𝕜 (V q)] [∀ q, TopologicalSpace (V q)]
    [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle 𝕜 F V]
    {α : ∀ x : M, StrongDual 𝕜 (V (Quotient.mk (MulAction.orbitRel G M) x))}
    {t : ∀ x : M, V (Quotient.mk (MulAction.orbitRel G M) x)}
    (hα : ∀ (g : G) (x : M), α (g • x) ≍ α x)
    (ht : ∀ (g : G) (x : M), t (g • x) ≍ t x)
    (hm : m ≤ n)
    (hα_smooth : ContMDiff I (I.prod 𝓘(𝕜, StrongDual 𝕜 F)) m
      (fun x ↦ TotalSpace.mk' (StrongDual 𝕜 F) (E := fun q ↦ StrongDual 𝕜 (V q))
        (Quotient.mk (MulAction.orbitRel G M) x) (α x)))
    (ht_smooth : ContMDiff I (I.prod 𝓘(𝕜, F)) m
      (fun x ↦ TotalSpace.mk' F (Quotient.mk (MulAction.orbitRel G M) x) (t x))) :
    ContMDiff I 𝓘(𝕜) m
      (MulAction.orbitRelQuotientLift (fun x ↦ α x (t x))
        (MulAction.apply₂_eq_of_heq (fun _ (f : StrongDual 𝕜 _) v ↦ f v) hα ht)) :=
  (contMDiff_orbitRelQuotientLift_iff hm).2 (hα_smooth.dual_bundle_apply ht_smooth)

/-- If an invariant Hom-bundle family `φ` is `C^m` upstairs (`m ≤ n`), the descent of its fibrewise
dual (transpose) family is a `C^m` section of the dual Hom bundle on `M ⧸ G`. Neither finite rank
nor completeness of `𝕜` is required. -/
theorem ContMDiff.section_dualMap_orbitRelQuotientRec {F₁ F₂ : Type*}
    [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
    [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
    {V₁ V₂ : MulAction.orbitRel.Quotient G M → Type*}
    [∀ q, AddCommGroup (V₁ q)] [∀ q, Module 𝕜 (V₁ q)] [∀ q, TopologicalSpace (V₁ q)]
    [TopologicalSpace (TotalSpace F₁ V₁)] [FiberBundle F₁ V₁] [VectorBundle 𝕜 F₁ V₁]
    [∀ q, AddCommGroup (V₂ q)] [∀ q, Module 𝕜 (V₂ q)] [∀ q, TopologicalSpace (V₂ q)]
    [∀ q, IsTopologicalAddGroup (V₂ q)] [∀ q, ContinuousSMul 𝕜 (V₂ q)]
    [TopologicalSpace (TotalSpace F₂ V₂)] [FiberBundle F₂ V₂] [VectorBundle 𝕜 F₂ V₂]
    {φ : ∀ x : M, V₁ (Quotient.mk (MulAction.orbitRel G M) x) →L[𝕜]
      V₂ (Quotient.mk (MulAction.orbitRel G M) x)}
    (hφ : ∀ (g : G) (x : M), φ (g • x) ≍ φ x)
    (hm : m ≤ n)
    (hφ_smooth : ContMDiff I (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) m
      (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun q ↦ V₁ q →L[𝕜] V₂ q)
        (Quotient.mk (MulAction.orbitRel G M) x) (φ x))) :
    ContMDiff I (I.prod 𝓘(𝕜, StrongDual 𝕜 F₂ →L[𝕜] StrongDual 𝕜 F₁)) m
      (fun q ↦ TotalSpace.mk' (StrongDual 𝕜 F₂ →L[𝕜] StrongDual 𝕜 F₁)
        (E := fun q ↦ StrongDual 𝕜 (V₂ q) →L[𝕜] StrongDual 𝕜 (V₁ q)) q
        (MulAction.orbitRelQuotientRec
          (V := fun q ↦ StrongDual 𝕜 (V₂ q) →L[𝕜] StrongDual 𝕜 (V₁ q))
          (fun x ↦ ContinuousLinearMap.precomp 𝕜 (φ x))
          (MulAction.apply_heq_of_heq (fun _ A ↦ ContinuousLinearMap.precomp 𝕜 A) hφ) q)) :=
  (contMDiff_section_orbitRelQuotientRec_iff hm).2 hφ_smooth.clm_bundle_dualMap

section FiniteRank

variable [CompleteSpace 𝕜]
  {F₁ F₂ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]
  {V₁ V₂ : MulAction.orbitRel.Quotient G M → Type*}
  [∀ q, AddCommGroup (V₁ q)] [∀ q, Module 𝕜 (V₁ q)] [∀ q, TopologicalSpace (V₁ q)]
  [TopologicalSpace (TotalSpace F₁ V₁)] [FiberBundle F₁ V₁] [VectorBundle 𝕜 F₁ V₁]
  [∀ q, AddCommGroup (V₂ q)] [∀ q, Module 𝕜 (V₂ q)] [∀ q, TopologicalSpace (V₂ q)]
  [∀ q, IsTopologicalAddGroup (V₂ q)] [∀ q, ContinuousSMul 𝕜 (V₂ q)]
  [TopologicalSpace (TotalSpace F₂ V₂)] [FiberBundle F₂ V₂] [VectorBundle 𝕜 F₂ V₂]
  {φ : ∀ x : M, V₁ (Quotient.mk (MulAction.orbitRel G M) x) →L[𝕜]
    V₂ (Quotient.mk (MulAction.orbitRel G M) x)}
  {hφ : ∀ (g : G) (x : M), φ (g • x) ≍ φ x}

/-- In finite dimensions over a complete field, the descended dual linear family induces a `C^m`
map of dual total spaces (`m ≤ n`) if and only if the primal family `φ` is a `C^m` section of the
pulled-back Hom bundle. -/
theorem contMDiff_totalSpaceMap_dualMap_orbitRelQuotientRec_iff (hm : m ≤ n) :
    ContMDiff (I.prod 𝓘(𝕜, StrongDual 𝕜 F₂)) (I.prod 𝓘(𝕜, StrongDual 𝕜 F₁)) m
        (fun p : TotalSpace (StrongDual 𝕜 F₂) (fun q ↦ StrongDual 𝕜 (V₂ q)) ↦
          TotalSpace.mk' (StrongDual 𝕜 F₁) (E := fun q ↦ StrongDual 𝕜 (V₁ q)) p.proj
            (MulAction.orbitRelQuotientRec
              (V := fun q ↦ StrongDual 𝕜 (V₂ q) →L[𝕜] StrongDual 𝕜 (V₁ q))
              (fun x ↦ ContinuousLinearMap.precomp 𝕜 (φ x))
              (MulAction.apply_heq_of_heq (fun _ A ↦ ContinuousLinearMap.precomp 𝕜 A) hφ)
              p.proj p.2)) ↔
      ContMDiff I (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) m
        (fun x ↦ (TotalSpace.mk' (F₁ →L[𝕜] F₂) x (φ x) :
          TotalSpace (F₁ →L[𝕜] F₂)
            (⇑(⟨Quotient.mk _, continuous_quotient_mk'⟩ :
              C(M, MulAction.orbitRel.Quotient G M)) *ᵖ (fun q ↦ V₁ q →L[𝕜] V₂ q)))) := by
  conv_lhs => enter [4, p]; rw [← dualMap_orbitRelQuotientRec hφ]
  rw [contMDiff_totalSpaceMap_dualMap_iff, contMDiff_totalSpaceMap_orbitRelQuotientRec_iff hm]

/-- In finite dimensions over a complete field, the descended dual linear family underlies a `C^m`
diffeomorphism of dual total spaces (`m ≤ n`) if and only if the primal family `φ` is a `C^m`
section of the pulled-back Hom bundle and every upstairs fibre map `φ x` is bijective. -/
theorem exists_bundleDiffeomorph_dualMap_orbitRelQuotientRec_iff
    [∀ q, IsTopologicalAddGroup (V₁ q)] [∀ q, ContinuousSMul 𝕜 (V₁ q)] (hm : m ≤ n) :
    (∃ Φ : TotalSpace (StrongDual 𝕜 F₂) (fun q ↦ StrongDual 𝕜 (V₂ q)) ≃ₘ^m⟮
        I.prod 𝓘(𝕜, StrongDual 𝕜 F₂), I.prod 𝓘(𝕜, StrongDual 𝕜 F₁)⟯
        TotalSpace (StrongDual 𝕜 F₁) (fun q ↦ StrongDual 𝕜 (V₁ q)),
        ⇑Φ = fun p ↦ TotalSpace.mk' (StrongDual 𝕜 F₁) (E := fun q ↦ StrongDual 𝕜 (V₁ q)) p.proj
          (MulAction.orbitRelQuotientRec
            (V := fun q ↦ StrongDual 𝕜 (V₂ q) →L[𝕜] StrongDual 𝕜 (V₁ q))
            (fun x ↦ ContinuousLinearMap.precomp 𝕜 (φ x))
            (MulAction.apply_heq_of_heq (fun _ A ↦ ContinuousLinearMap.precomp 𝕜 A) hφ)
            p.proj p.2)) ↔
      ContMDiff I (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) m
          (fun x ↦ (TotalSpace.mk' (F₁ →L[𝕜] F₂) x (φ x) :
            TotalSpace (F₁ →L[𝕜] F₂)
              (⇑(⟨Quotient.mk _, continuous_quotient_mk'⟩ :
                C(M, MulAction.orbitRel.Quotient G M)) *ᵖ (fun q ↦ V₁ q →L[𝕜] V₂ q)))) ∧
        ∀ x, Function.Bijective (φ x) := by
  conv_lhs => enter [1, Φ, 2, p]; rw [← dualMap_orbitRelQuotientRec hφ]
  rw [exists_bundleDiffeomorph_dualMap_iff, exists_bundleDiffeomorph_orbitRelQuotientRec_iff hm]

end FiniteRank

end Manifold

end TauCeti
