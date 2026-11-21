/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Quotient.BundleMap
public import TauCeti.Geometry.Manifold.VectorBundle.TensorProduct
public import TauCeti.LinearAlgebra.TensorProduct.OrbitRelQuotient
public import TauCeti.Topology.VectorBundle.TensorProduct.OrbitRelQuotient

/-!
# Compatibility of quotient bundle descent with tensor products

Let `q : M → M ⧸ G` be the orbit projection of a free properly discontinuous action by `C^n` maps
on a `C^n` manifold `M`. For finite-rank vector bundles over `M ⧸ G` whose tensor-product fibres
carry the `𝕜`-module topology, quotient descent preserves `C^m` regularity (`m ≤ n`) for
tensor-product operations, building on the algebraic and topological identities in
`TauCeti.LinearAlgebra.TensorProduct.OrbitRelQuotient` and
`TauCeti.Topology.VectorBundle.TensorProduct.OrbitRelQuotient`:

* **Pure tensors:** the descent of the upstairs pure tensor `x ↦ t₁ x ⊗ₜ[𝕜] t₂ x` is `C^m`
  whenever `t₁` and `t₂` are `C^m` upstairs (`ContMDiff.section_tmul_orbitRelQuotientRec`).
* **Universal property (`bundleTensorLift`):** the descended total-space map out of `V₁ ⊗ V₂` into
  any normed-fibre target bundle `V₃` is `C^m` if and only if the invariant bilinear family `Φ` is
  `C^m` upstairs (`TauCeti.contMDiff_totalSpaceMap_bundleTensorLift_orbitRelQuotientRec_iff`).
* **Functoriality (`bundleTensorMap`) and dual-tensor-Hom:** forming fibrewise tensor products of
  invariant `C^m` linear bundle maps induces `C^m` total-space maps and diffeomorphisms on `M ⧸ G`
  (`ContMDiff.totalSpaceMap_bundleTensorMap_orbitRelQuotientRec`,
  `TauCeti.exists_bundleDiffeomorph_bundleTensorMap_orbitRelQuotientRec`), and descending an
  invariant section of `StrongDual 𝕜 V₁ ⊗ V₂` through `bundleDualTensorHom` is `C^m` as a
  Hom-bundle section if and only if the section is `C^m` upstairs
  (`TauCeti.contMDiff_section_bundleDualTensorHom_orbitRelQuotientRec_iff`).

Over `ℂ` at regularity `∞`, these results express compatibility of holomorphic quotient descent
with holomorphic tensor products.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapters 10, 12, and 21.
* Daniel Huybrechts, *Complex Geometry: An Introduction*, Section 2.2.
-/

public section

noncomputable section

open Bundle
open scoped Manifold ContDiff TensorProduct

namespace TauCeti

section Manifold

variable {G M 𝕜 : Type*} [Group G] [MulAction G M] [TopologicalSpace M]
  [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [ChartedSpace H M] {m n : ℕ∞ω}
  [ProperlyDiscontinuousSMul G M] [ContinuousConstSMul G M] [IsCancelSMul G M]
  [T2Space M] [LocallyCompactSpace M] [IsManifold I n M] [ContMDiffConstSMul I n G M]
  {F₁ F₂ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]
  {V₁ V₂ : MulAction.orbitRel.Quotient G M → Type*}
  [∀ q, AddCommGroup (V₁ q)] [∀ q, Module 𝕜 (V₁ q)] [∀ q, TopologicalSpace (V₁ q)]
  [TopologicalSpace (TotalSpace F₁ V₁)] [FiberBundle F₁ V₁] [VectorBundle 𝕜 F₁ V₁]
  [∀ q, AddCommGroup (V₂ q)] [∀ q, Module 𝕜 (V₂ q)] [∀ q, TopologicalSpace (V₂ q)]
  [TopologicalSpace (TotalSpace F₂ V₂)] [FiberBundle F₂ V₂] [VectorBundle 𝕜 F₂ V₂]

/-- If two invariant sections `t₁` and `t₂` upstairs are `C^m` (`m ≤ n`), the descent of their
pointwise pure tensor `x ↦ t₁ x ⊗ₜ[𝕜] t₂ x` is a `C^m` section of `V₁ ⊗ V₂` over `M ⧸ G`. -/
theorem _root_.ContMDiff.section_tmul_orbitRelQuotientRec
    [∀ q, IsTopologicalAddGroup (V₁ q)] [∀ q, ContinuousSMul 𝕜 (V₁ q)]
    [∀ q, IsTopologicalAddGroup (V₂ q)] [∀ q, ContinuousSMul 𝕜 (V₂ q)]
    [∀ q, TopologicalSpace (V₁ q ⊗[𝕜] V₂ q)] [∀ q, IsModuleTopology 𝕜 (V₁ q ⊗[𝕜] V₂ q)]
    {t₁ : ∀ x : M, V₁ (Quotient.mk (MulAction.orbitRel G M) x)}
    {t₂ : ∀ x : M, V₂ (Quotient.mk (MulAction.orbitRel G M) x)}
    (ht₁_smooth : ContMDiff I (I.prod 𝓘(𝕜, F₁)) m
      (fun x ↦ TotalSpace.mk' F₁ (Quotient.mk (MulAction.orbitRel G M) x) (t₁ x)))
    (ht₂_smooth : ContMDiff I (I.prod 𝓘(𝕜, F₂)) m
      (fun x ↦ TotalSpace.mk' F₂ (Quotient.mk (MulAction.orbitRel G M) x) (t₂ x)))
    (ht₁ : ∀ (g : G) (x : M), t₁ (g • x) ≍ t₁ x)
    (ht₂ : ∀ (g : G) (x : M), t₂ (g • x) ≍ t₂ x) (hm : m ≤ n) :
    ContMDiff I (I.prod 𝓘(𝕜, ProjectiveTensor 𝕜 F₁ F₂)) m
      (fun q ↦ TotalSpace.mk' (ProjectiveTensor 𝕜 F₁ F₂) (E := fun q ↦ V₁ q ⊗[𝕜] V₂ q) q
        (MulAction.orbitRelQuotientRec (V := fun q ↦ V₁ q ⊗[𝕜] V₂ q) (fun x ↦ t₁ x ⊗ₜ[𝕜] t₂ x)
          (MulAction.apply₂_smul_heq (fun _ v w ↦ v ⊗ₜ[𝕜] w) ht₁ ht₂) q)) :=
  (contMDiff_section_orbitRelQuotientRec_iff hm).2 (ht₁_smooth.tmul_section ht₂_smooth)

/-- **Quotient `C^m` universal property of `V₁ ⊗ V₂`.** Into any normed-fibre target bundle `V₃`
over `M ⧸ G`, the descended linear bundle map `orbitRelQuotientRec (bundleTensorLift Φ) ...`
induces a `C^m` map of total spaces (`m ≤ n`) if and only if the invariant bilinear family `Φ` is
`C^m` upstairs. -/
theorem contMDiff_totalSpaceMap_bundleTensorLift_orbitRelQuotientRec_iff
    {F₃ : Type*} [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃]
    {V₃ : MulAction.orbitRel.Quotient G M → Type*}
    [∀ q, AddCommGroup (V₃ q)] [∀ q, Module 𝕜 (V₃ q)] [∀ q, TopologicalSpace (V₃ q)]
    [∀ q, IsTopologicalAddGroup (V₃ q)] [∀ q, ContinuousSMul 𝕜 (V₃ q)]
    [TopologicalSpace (TotalSpace F₃ V₃)] [FiberBundle F₃ V₃] [VectorBundle 𝕜 F₃ V₃]
    [∀ q, TopologicalSpace (V₁ q ⊗[𝕜] V₂ q)] [∀ q, IsModuleTopology 𝕜 (V₁ q ⊗[𝕜] V₂ q)]
    {Φ : ∀ x : M, V₁ (Quotient.mk (MulAction.orbitRel G M) x) →L[𝕜]
      V₂ (Quotient.mk (MulAction.orbitRel G M) x) →L[𝕜]
      V₃ (Quotient.mk (MulAction.orbitRel G M) x)}
    (hΦ : ∀ (g : G) (x : M), Φ (g • x) ≍ Φ x) (hm : m ≤ n) :
    ContMDiff (I.prod 𝓘(𝕜, ProjectiveTensor 𝕜 F₁ F₂)) (I.prod 𝓘(𝕜, F₃)) m (fun p :
        TotalSpace (ProjectiveTensor 𝕜 F₁ F₂) (fun q ↦ V₁ q ⊗[𝕜] V₂ q) ↦
        TotalSpace.mk' F₃ p.proj (MulAction.orbitRelQuotientRec
          (V := fun q ↦ V₁ q ⊗[𝕜] V₂ q →L[𝕜] V₃ q)
          (bundleTensorLift Φ) (bundleTensorLift_smul_heq hΦ) p.proj p.snd)) ↔
      ContMDiff I (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂ →L[𝕜] F₃)) m (fun x ↦
        TotalSpace.mk' (F₁ →L[𝕜] F₂ →L[𝕜] F₃) (E := fun q ↦ V₁ q →L[𝕜] V₂ q →L[𝕜] V₃ q)
          (Quotient.mk (MulAction.orbitRel G M) x) (Φ x)) := by
  conv_lhs => enter [4, p]; rw [← bundleTensorLift_orbitRelQuotientRec hΦ]
  rw [← contMDiff_hom_bundle_iff (IB := I) (bundleTensorLift
      (MulAction.orbitRelQuotientRec (V := fun q ↦ V₁ q →L[𝕜] V₂ q →L[𝕜] V₃ q) Φ hΦ)),
    contMDiff_bundleTensorLift_iff, contMDiff_section_orbitRelQuotientRec_iff hm]

section MapManifold

variable {F₁' F₂' : Type*}
  [NormedAddCommGroup F₁'] [NormedSpace 𝕜 F₁'] [FiniteDimensional 𝕜 F₁']
  [NormedAddCommGroup F₂'] [NormedSpace 𝕜 F₂'] [FiniteDimensional 𝕜 F₂']
  {V₁' V₂' : MulAction.orbitRel.Quotient G M → Type*}
  [∀ q, AddCommGroup (V₁' q)] [∀ q, Module 𝕜 (V₁' q)] [∀ q, TopologicalSpace (V₁' q)]
  [∀ q, IsTopologicalAddGroup (V₁' q)] [∀ q, ContinuousSMul 𝕜 (V₁' q)]
  [TopologicalSpace (TotalSpace F₁' V₁')] [FiberBundle F₁' V₁'] [VectorBundle 𝕜 F₁' V₁']
  [∀ q, AddCommGroup (V₂' q)] [∀ q, Module 𝕜 (V₂' q)] [∀ q, TopologicalSpace (V₂' q)]
  [∀ q, IsTopologicalAddGroup (V₂' q)] [∀ q, ContinuousSMul 𝕜 (V₂' q)]
  [TopologicalSpace (TotalSpace F₂' V₂')] [FiberBundle F₂' V₂'] [VectorBundle 𝕜 F₂' V₂']
  [∀ q, TopologicalSpace (V₁ q ⊗[𝕜] V₂ q)] [∀ q, IsModuleTopology 𝕜 (V₁ q ⊗[𝕜] V₂ q)]
  [∀ q, TopologicalSpace (V₁' q ⊗[𝕜] V₂' q)] [∀ q, IsModuleTopology 𝕜 (V₁' q ⊗[𝕜] V₂' q)]
  {φ₁ : ∀ x : M, V₁ (Quotient.mk (MulAction.orbitRel G M) x) →L[𝕜]
    V₁' (Quotient.mk (MulAction.orbitRel G M) x)}
  {φ₂ : ∀ x : M, V₂ (Quotient.mk (MulAction.orbitRel G M) x) →L[𝕜]
    V₂' (Quotient.mk (MulAction.orbitRel G M) x)}

/-- If two invariant linear families `φ₁` and `φ₂` are `C^m` upstairs (`m ≤ n`), the descent of
`bundleTensorMap φ₁ φ₂` induces a `C^m` map of tensor-product total spaces over `M ⧸ G`. -/
theorem _root_.ContMDiff.totalSpaceMap_bundleTensorMap_orbitRelQuotientRec
    (hφ₁_smooth : ContMDiff I (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₁')) m (fun x ↦ TotalSpace.mk'
      (F₁ →L[𝕜] F₁') (E := fun q ↦ V₁ q →L[𝕜] V₁' q)
      (Quotient.mk (MulAction.orbitRel G M) x) (φ₁ x)))
    (hφ₂_smooth : ContMDiff I (I.prod 𝓘(𝕜, F₂ →L[𝕜] F₂')) m (fun x ↦ TotalSpace.mk'
      (F₂ →L[𝕜] F₂') (E := fun q ↦ V₂ q →L[𝕜] V₂' q)
      (Quotient.mk (MulAction.orbitRel G M) x) (φ₂ x)))
    (hφ₁ : ∀ (g : G) (x : M), φ₁ (g • x) ≍ φ₁ x)
    (hφ₂ : ∀ (g : G) (x : M), φ₂ (g • x) ≍ φ₂ x) (hm : m ≤ n) :
    ContMDiff (I.prod 𝓘(𝕜, ProjectiveTensor 𝕜 F₁ F₂))
      (I.prod 𝓘(𝕜, ProjectiveTensor 𝕜 F₁' F₂')) m
      (fun p : TotalSpace (ProjectiveTensor 𝕜 F₁ F₂) (fun q ↦ V₁ q ⊗[𝕜] V₂ q) ↦
        TotalSpace.mk' (ProjectiveTensor 𝕜 F₁' F₂') (E := fun q ↦ V₁' q ⊗[𝕜] V₂' q) p.proj
          (MulAction.orbitRelQuotientRec (V := fun q ↦ V₁ q ⊗[𝕜] V₂ q →L[𝕜] V₁' q ⊗[𝕜] V₂' q)
            (bundleTensorMap φ₁ φ₂) (bundleTensorMap_smul_heq hφ₁ hφ₂) p.proj p.snd)) := by
  let _ : ∀ q, IsTopologicalAddGroup (V₁' q ⊗[𝕜] V₂' q) := fun _ ↦ inferInstance
  let _ : ∀ q, ContinuousSMul 𝕜 (V₁' q ⊗[𝕜] V₂' q) := fun _ ↦ inferInstance
  refine ((contMDiff_hom_bundle_iff (IB := I) (bundleTensorMap
    (MulAction.orbitRelQuotientRec (V := fun q ↦ V₁ q →L[𝕜] V₁' q) φ₁ hφ₁)
    (MulAction.orbitRelQuotientRec (V := fun q ↦ V₂ q →L[𝕜] V₂' q) φ₂ hφ₂))).1
    (contMDiff_bundleTensorMap ((contMDiff_section_orbitRelQuotientRec_iff hm).2 hφ₁_smooth)
      ((contMDiff_section_orbitRelQuotientRec_iff hm).2 hφ₂_smooth))).congr fun p ↦ ?_
  rw [bundleTensorMap_orbitRelQuotientRec]

/-- If two invariant `C^m` linear families `φ₁` and `φ₂` (`m ≤ n`) are fibrewise bijective
upstairs, the descent of `bundleTensorMap φ₁ φ₂` underlies a `C^m` diffeomorphism of
tensor-product total spaces over `M ⧸ G`. -/
theorem exists_bundleDiffeomorph_bundleTensorMap_orbitRelQuotientRec
    (hφ₁ : ∀ (g : G) (x : M), φ₁ (g • x) ≍ φ₁ x)
    (hφ₂ : ∀ (g : G) (x : M), φ₂ (g • x) ≍ φ₂ x) (hm : m ≤ n)
    (hφ₁_smooth : ContMDiff I (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₁')) m (fun x ↦ TotalSpace.mk'
      (F₁ →L[𝕜] F₁') (E := fun q ↦ V₁ q →L[𝕜] V₁' q)
      (Quotient.mk (MulAction.orbitRel G M) x) (φ₁ x)))
    (hφ₂_smooth : ContMDiff I (I.prod 𝓘(𝕜, F₂ →L[𝕜] F₂')) m (fun x ↦ TotalSpace.mk'
      (F₂ →L[𝕜] F₂') (E := fun q ↦ V₂ q →L[𝕜] V₂' q)
      (Quotient.mk (MulAction.orbitRel G M) x) (φ₂ x)))
    (hbij₁ : ∀ x : M, Function.Bijective (φ₁ x)) (hbij₂ : ∀ x : M, Function.Bijective (φ₂ x)) :
    ∃ Φ : TotalSpace (ProjectiveTensor 𝕜 F₁ F₂) (fun q ↦ V₁ q ⊗[𝕜] V₂ q) ≃ₘ^m⟮
        I.prod 𝓘(𝕜, ProjectiveTensor 𝕜 F₁ F₂), I.prod 𝓘(𝕜, ProjectiveTensor 𝕜 F₁' F₂')⟯
        TotalSpace (ProjectiveTensor 𝕜 F₁' F₂') (fun q ↦ V₁' q ⊗[𝕜] V₂' q),
      ⇑Φ = fun p ↦ TotalSpace.mk' (ProjectiveTensor 𝕜 F₁' F₂') (E := fun q ↦ V₁' q ⊗[𝕜] V₂' q)
        p.proj (MulAction.orbitRelQuotientRec
          (V := fun q ↦ V₁ q ⊗[𝕜] V₂ q →L[𝕜] V₁' q ⊗[𝕜] V₂' q)
          (bundleTensorMap φ₁ φ₂) (bundleTensorMap_smul_heq hφ₁ hφ₂) p.proj p.snd) := by
  rw [exists_bundleDiffeomorph_iff]
  refine ⟨hφ₁_smooth.totalSpaceMap_bundleTensorMap_orbitRelQuotientRec hφ₂_smooth hφ₁ hφ₂ hm,
    fun q ↦ ?_⟩
  induction q using Quotient.inductionOn with | h x =>
  rw [MulAction.orbitRelQuotientRec_mk]
  let e₁ := LinearEquiv.ofBijective (φ₁ x).toLinearMap (hbij₁ x)
  let e₂ := LinearEquiv.ofBijective (φ₂ x).toLinearMap (hbij₂ x)
  convert (_root_.TensorProduct.congr e₁ e₂).bijective
  exact funext fun t ↦ LinearMap.congr_fun (_root_.TensorProduct.ext' fun v w ↦ by
    simp [e₁, e₂, bundleTensorMap_tmul]) t

end MapManifold

/-- Under `bundleDualTensorHom`, the descent of an invariant section `τ` of `StrongDual 𝕜 V₁ ⊗ V₂`
is `C^m` (`m ≤ n`) as a Hom-bundle section on `M ⧸ G` if and only if `τ` is `C^m` upstairs. -/
theorem contMDiff_section_bundleDualTensorHom_orbitRelQuotientRec_iff
    [∀ q, IsTopologicalAddGroup (V₂ q)] [∀ q, ContinuousSMul 𝕜 (V₂ q)]
    [∀ q, TopologicalSpace (StrongDual 𝕜 (V₁ q) ⊗[𝕜] V₂ q)]
    [∀ q, IsModuleTopology 𝕜 (StrongDual 𝕜 (V₁ q) ⊗[𝕜] V₂ q)]
    {τ : ∀ x : M, StrongDual 𝕜 (V₁ (Quotient.mk (MulAction.orbitRel G M) x)) ⊗[𝕜]
      V₂ (Quotient.mk (MulAction.orbitRel G M) x)}
    (hτ : ∀ (g : G) (x : M), τ (g • x) ≍ τ x) (hm : m ≤ n) :
    ContMDiff I (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) m
        (fun q ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun q ↦ V₁ q →L[𝕜] V₂ q) q
          (MulAction.orbitRelQuotientRec (V := fun q ↦ V₁ q →L[𝕜] V₂ q) (fun x ↦
            bundleDualTensorHom (E₁ := V₁) (E₂ := V₂) (Quotient.mk (MulAction.orbitRel G M) x)
              (τ x)) (MulAction.apply_smul_heq (fun q t ↦
            bundleDualTensorHom (E₁ := V₁) (E₂ := V₂) q t) hτ) q)) ↔
      ContMDiff I (I.prod 𝓘(𝕜, ProjectiveTensor 𝕜 (StrongDual 𝕜 F₁) F₂)) m (fun x ↦
        TotalSpace.mk' (ProjectiveTensor 𝕜 (StrongDual 𝕜 F₁) F₂)
          (E := fun q ↦ StrongDual 𝕜 (V₁ q) ⊗[𝕜] V₂ q)
          (Quotient.mk (MulAction.orbitRel G M) x) (τ x)) := by
  let Φ := bundleDualTensorHomDiffeomorph I m F₁ V₁ F₂ V₂
  rw [← contMDiff_section_orbitRelQuotientRec_iff (ht := hτ) hm]
  simp only [← bundleDualTensorHom_orbitRelQuotientRec (hτ := hτ)]
  exact ⟨fun h ↦ (Φ.symm.contMDiff.comp h).congr fun q ↦ by
      simp only [Function.comp_apply, Φ, bundleDualTensorHomDiffeomorph_symm_apply]
      rw [← bundleDualTensorHomEquiv_toContinuousLinearMap (F₁ := F₁) (F₂ := F₂),
        ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply],
    fun h ↦ (Φ.contMDiff.comp h).congr fun q ↦ by
      simp [Φ, ← ContinuousLinearEquiv.coe_coe, bundleDualTensorHomEquiv_toContinuousLinearMap]⟩

end Manifold

end TauCeti
