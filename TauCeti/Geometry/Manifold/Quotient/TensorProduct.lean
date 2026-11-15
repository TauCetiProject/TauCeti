/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Quotient.BundleMap
public import TauCeti.Geometry.Manifold.VectorBundle.TensorProduct

/-!
# Compatibility of quotient bundle descent with tensor products

Let `q : M → M ⧸ G` be the orbit projection of a free properly discontinuous action by `C^n` maps
on a `C^n` manifold `M`. For finite-rank vector bundles over `M ⧸ G` whose tensor-product fibres
carry the `𝕜`-module topology, quotient descent commutes with tensor-product operations:

* **Pure tensors:** the fibrewise pure tensor of two descended sections is the descent of the
  upstairs pure tensor (`TauCeti.tmul_orbitRelQuotientRec`) and preserves `C^m` section regularity
  for `m ≤ n` (`TauCeti.ContMDiff.section_tmul_orbitRelQuotientRec`).
* **Universal property (`bundleTensorLift`):** lifting an invariant bilinear family `Φ` into any
  normed-fibre target bundle `V₃` (not necessarily of finite rank) commutes with
  `MulAction.orbitRelQuotientRec` (`TauCeti.bundleTensorLift_orbitRelQuotientRec`), and the
  descended total-space map out of `V₁ ⊗ V₂` is `C^m` if and only if `Φ` is `C^m` upstairs
  (`TauCeti.contMDiff_totalSpaceMap_bundleTensorLift_orbitRelQuotientRec_iff`).
* **Functoriality (`bundleTensorMap`) and dual-tensor-Hom:** forming fibrewise tensor products of
  linear bundle maps and applying `bundleDualTensorHom` commute with
  `MulAction.orbitRelQuotientRec` (`TauCeti.bundleTensorMap_orbitRelQuotientRec`,
  `TauCeti.bundleDualTensorHom_orbitRelQuotientRec`), inducing `C^m` total-space maps and
  diffeomorphisms on `M ⧸ G` from invariant `C^m` data upstairs
  (`TauCeti.ContMDiff.totalSpaceMap_bundleTensorMap_orbitRelQuotientRec`,
  `TauCeti.exists_bundleDiffeomorph_bundleTensorMap_orbitRelQuotientRec`,
  `TauCeti.contMDiff_section_bundleDualTensorHom_orbitRelQuotientRec_iff`).

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

section Algebraic

variable {G M : Type*} [Group G] [MulAction G M]

section CommRing

variable {𝕜 : Type*} [CommRing 𝕜]
  {V₁ V₂ : MulAction.orbitRel.Quotient G M → Type*}
  [∀ q, AddCommGroup (V₁ q)] [∀ q, Module 𝕜 (V₁ q)]
  [∀ q, AddCommGroup (V₂ q)] [∀ q, Module 𝕜 (V₂ q)]

/-- Fibrewise pure tensor `⊗ₜ[𝕜]` commutes with `MulAction.orbitRelQuotientRec`. -/
theorem tmul_orbitRelQuotientRec
    {t₁ : ∀ x : M, V₁ (Quotient.mk (MulAction.orbitRel G M) x)}
    {t₂ : ∀ x : M, V₂ (Quotient.mk (MulAction.orbitRel G M) x)}
    (ht₁ : ∀ (g : G) (x : M), t₁ (g • x) ≍ t₁ x)
    (ht₂ : ∀ (g : G) (x : M), t₂ (g • x) ≍ t₂ x)
    (q : MulAction.orbitRel.Quotient G M) :
    MulAction.orbitRelQuotientRec t₁ ht₁ q ⊗ₜ[𝕜] MulAction.orbitRelQuotientRec t₂ ht₂ q =
      MulAction.orbitRelQuotientRec (V := fun q ↦ V₁ q ⊗[𝕜] V₂ q)
        (fun x ↦ t₁ x ⊗ₜ[𝕜] t₂ x)
        (MulAction.apply₂_heq_of_heq (fun _ v w ↦ v ⊗ₜ[𝕜] w) ht₁ ht₂) q :=
  MulAction.apply₂_orbitRelQuotientRec (fun _ v w ↦ v ⊗ₜ[𝕜] w) ht₁ ht₂ q

section Map

variable [TopologicalSpace 𝕜]
  {V₁' V₂' : MulAction.orbitRel.Quotient G M → Type*}
  [∀ q, AddCommGroup (V₁' q)] [∀ q, Module 𝕜 (V₁' q)]
  [∀ q, AddCommGroup (V₂' q)] [∀ q, Module 𝕜 (V₂' q)]
  [∀ q, TopologicalSpace (V₁ q)] [∀ q, TopologicalSpace (V₁' q)]
  [∀ q, TopologicalSpace (V₂ q)] [∀ q, TopologicalSpace (V₂' q)]
  [∀ q, TopologicalSpace (V₁ q ⊗[𝕜] V₂ q)] [∀ q, IsModuleTopology 𝕜 (V₁ q ⊗[𝕜] V₂ q)]
  [∀ q, TopologicalSpace (V₁' q ⊗[𝕜] V₂' q)] [∀ q, IsModuleTopology 𝕜 (V₁' q ⊗[𝕜] V₂' q)]

/-- If two linear families `φ₁` and `φ₂` upstairs are `G`-invariant, so is their fibrewise tensor
product `bundleTensorMap φ₁ φ₂`. -/
theorem bundleTensorMap_smul_heq
    {φ₁ : ∀ x : M, V₁ (Quotient.mk (MulAction.orbitRel G M) x) →L[𝕜]
      V₁' (Quotient.mk (MulAction.orbitRel G M) x)}
    {φ₂ : ∀ x : M, V₂ (Quotient.mk (MulAction.orbitRel G M) x) →L[𝕜]
      V₂' (Quotient.mk (MulAction.orbitRel G M) x)}
    (hφ₁ : ∀ (g : G) (x : M), φ₁ (g • x) ≍ φ₁ x)
    (hφ₂ : ∀ (g : G) (x : M), φ₂ (g • x) ≍ φ₂ x) (g : G) (x : M) :
    bundleTensorMap φ₁ φ₂ (g • x) ≍ bundleTensorMap φ₁ φ₂ x := by
  let B : ∀ q, (V₁ q →L[𝕜] V₁' q) → (V₂ q →L[𝕜] V₂' q) → (V₁ q ⊗[𝕜] V₂ q →L[𝕜] V₁' q ⊗[𝕜] V₂' q) :=
    fun q A₁ A₂ ↦ bundleTensorMap (B := Unit)
      (E₁ := fun _ ↦ V₁ q) (E₁' := fun _ ↦ V₁' q)
      (E₂ := fun _ ↦ V₂ q) (E₂' := fun _ ↦ V₂' q)
      (fun _ ↦ A₁) (fun _ ↦ A₂) ()
  have hB (y : M) : bundleTensorMap φ₁ φ₂ y =
      B (Quotient.mk (MulAction.orbitRel G M) y) (φ₁ y) (φ₂ y) :=
    ContinuousLinearMap.ext <| LinearMap.congr_fun <|
      _root_.TensorProduct.ext' fun v w ↦ by simp [B]
  rw [hB (g • x), hB x]
  exact MulAction.apply₂_heq_of_heq B hφ₁ hφ₂ g x

/-- Fibrewise tensor product `bundleTensorMap` commutes with `MulAction.orbitRelQuotientRec`. -/
theorem bundleTensorMap_orbitRelQuotientRec
    {φ₁ : ∀ x : M, V₁ (Quotient.mk (MulAction.orbitRel G M) x) →L[𝕜]
      V₁' (Quotient.mk (MulAction.orbitRel G M) x)}
    {φ₂ : ∀ x : M, V₂ (Quotient.mk (MulAction.orbitRel G M) x) →L[𝕜]
      V₂' (Quotient.mk (MulAction.orbitRel G M) x)}
    (hφ₁ : ∀ (g : G) (x : M), φ₁ (g • x) ≍ φ₁ x)
    (hφ₂ : ∀ (g : G) (x : M), φ₂ (g • x) ≍ φ₂ x)
    (q : MulAction.orbitRel.Quotient G M) :
    bundleTensorMap
        (MulAction.orbitRelQuotientRec (V := fun q ↦ V₁ q →L[𝕜] V₁' q) φ₁ hφ₁)
        (MulAction.orbitRelQuotientRec (V := fun q ↦ V₂ q →L[𝕜] V₂' q) φ₂ hφ₂) q =
      MulAction.orbitRelQuotientRec
        (V := fun q ↦ V₁ q ⊗[𝕜] V₂ q →L[𝕜] V₁' q ⊗[𝕜] V₂' q)
        (bundleTensorMap φ₁ φ₂) (bundleTensorMap_smul_heq hφ₁ hφ₂) q := by
  induction q using Quotient.inductionOn with | h x =>
  exact ContinuousLinearMap.ext <| LinearMap.congr_fun <|
    _root_.TensorProduct.ext' fun _ _ ↦ by simp

end Map

end CommRing

section NormedField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {V₁ V₂ V₃ : MulAction.orbitRel.Quotient G M → Type*}
  [∀ q, AddCommGroup (V₁ q)] [∀ q, Module 𝕜 (V₁ q)] [∀ q, TopologicalSpace (V₁ q)]
  [∀ q, AddCommGroup (V₂ q)] [∀ q, Module 𝕜 (V₂ q)] [∀ q, TopologicalSpace (V₂ q)]
  [∀ q, AddCommGroup (V₃ q)] [∀ q, Module 𝕜 (V₃ q)] [∀ q, TopologicalSpace (V₃ q)]
  [∀ q, IsTopologicalAddGroup (V₃ q)] [∀ q, ContinuousSMul 𝕜 (V₃ q)]

section Lift

variable [∀ q, TopologicalSpace (V₁ q ⊗[𝕜] V₂ q)] [∀ q, IsModuleTopology 𝕜 (V₁ q ⊗[𝕜] V₂ q)]

/-- If a bilinear family `Φ` upstairs is `G`-invariant, so is its tensor-product lift
`bundleTensorLift Φ`. -/
theorem bundleTensorLift_smul_heq
    {Φ : ∀ x : M, V₁ (Quotient.mk (MulAction.orbitRel G M) x) →L[𝕜]
      V₂ (Quotient.mk (MulAction.orbitRel G M) x) →L[𝕜]
      V₃ (Quotient.mk (MulAction.orbitRel G M) x)}
    (hΦ : ∀ (g : G) (x : M), Φ (g • x) ≍ Φ x) (g : G) (x : M) :
    bundleTensorLift Φ (g • x) ≍ bundleTensorLift Φ x := by
  let F : ∀ q, (V₁ q →L[𝕜] V₂ q →L[𝕜] V₃ q) → (V₁ q ⊗[𝕜] V₂ q →L[𝕜] V₃ q) :=
    fun q B ↦ bundleTensorLift (B := Unit)
      (E₁ := fun _ ↦ V₁ q) (E₂ := fun _ ↦ V₂ q) (E₃ := fun _ ↦ V₃ q) (fun _ ↦ B) ()
  have hF (y : M) : bundleTensorLift Φ y = F (Quotient.mk (MulAction.orbitRel G M) y) (Φ y) :=
    (eq_bundleTensorLift_iff.2 fun v w ↦ by simp [F]).symm
  rw [hF (g • x), hF x]
  exact MulAction.apply_heq_of_heq F hΦ g x

/-- The tensor-product universal property `bundleTensorLift` commutes with
`MulAction.orbitRelQuotientRec`. -/
theorem bundleTensorLift_orbitRelQuotientRec
    {Φ : ∀ x : M, V₁ (Quotient.mk (MulAction.orbitRel G M) x) →L[𝕜]
      V₂ (Quotient.mk (MulAction.orbitRel G M) x) →L[𝕜]
      V₃ (Quotient.mk (MulAction.orbitRel G M) x)}
    (hΦ : ∀ (g : G) (x : M), Φ (g • x) ≍ Φ x) (q : MulAction.orbitRel.Quotient G M) :
    bundleTensorLift
        (MulAction.orbitRelQuotientRec (V := fun q ↦ V₁ q →L[𝕜] V₂ q →L[𝕜] V₃ q) Φ hΦ) q =
      MulAction.orbitRelQuotientRec (V := fun q ↦ V₁ q ⊗[𝕜] V₂ q →L[𝕜] V₃ q)
        (bundleTensorLift Φ) (bundleTensorLift_smul_heq hΦ) q := by
  induction q using Quotient.inductionOn with | h x =>
  exact (eq_bundleTensorLift_iff.2 fun _ _ ↦ by simp).symm

end Lift

section DualTensorHom

variable [∀ q, IsTopologicalAddGroup (V₂ q)] [∀ q, ContinuousSMul 𝕜 (V₂ q)]
  [∀ q, TopologicalSpace (StrongDual 𝕜 (V₁ q) ⊗[𝕜] V₂ q)]
  [∀ q, IsModuleTopology 𝕜 (StrongDual 𝕜 (V₁ q) ⊗[𝕜] V₂ q)]

/-- Applying `bundleDualTensorHom` over `M ⧸ G` to the descent of an invariant section `τ` agrees
with the descent of `x ↦ bundleDualTensorHom ⟦x⟧ (τ x)`. -/
theorem bundleDualTensorHom_orbitRelQuotientRec
    {τ : ∀ x : M, StrongDual 𝕜 (V₁ (Quotient.mk (MulAction.orbitRel G M) x)) ⊗[𝕜]
      V₂ (Quotient.mk (MulAction.orbitRel G M) x)}
    (hτ : ∀ (g : G) (x : M), τ (g • x) ≍ τ x) (q : MulAction.orbitRel.Quotient G M) :
    bundleDualTensorHom (E₁ := V₁) (E₂ := V₂) q
        (MulAction.orbitRelQuotientRec (V := fun q ↦ StrongDual 𝕜 (V₁ q) ⊗[𝕜] V₂ q) τ hτ q) =
      MulAction.orbitRelQuotientRec (V := fun q ↦ V₁ q →L[𝕜] V₂ q)
        (fun x ↦ bundleDualTensorHom (E₁ := V₁) (E₂ := V₂)
          (Quotient.mk (MulAction.orbitRel G M) x) (τ x))
        (MulAction.apply_heq_of_heq
          (fun q t ↦ bundleDualTensorHom (E₁ := V₁) (E₂ := V₂) q t) hτ) q :=
  MulAction.apply_orbitRelQuotientRec
    (fun q t ↦ bundleDualTensorHom (E₁ := V₁) (E₂ := V₂) q t) hτ q

end DualTensorHom

end NormedField

end Algebraic

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
theorem ContMDiff.section_tmul_orbitRelQuotientRec
    [∀ q, IsTopologicalAddGroup (V₁ q)] [∀ q, ContinuousSMul 𝕜 (V₁ q)]
    [∀ q, IsTopologicalAddGroup (V₂ q)] [∀ q, ContinuousSMul 𝕜 (V₂ q)]
    [∀ q, TopologicalSpace (V₁ q ⊗[𝕜] V₂ q)] [∀ q, IsModuleTopology 𝕜 (V₁ q ⊗[𝕜] V₂ q)]
    {t₁ : ∀ x : M, V₁ (Quotient.mk (MulAction.orbitRel G M) x)}
    {t₂ : ∀ x : M, V₂ (Quotient.mk (MulAction.orbitRel G M) x)}
    (ht₁ : ∀ (g : G) (x : M), t₁ (g • x) ≍ t₁ x)
    (ht₂ : ∀ (g : G) (x : M), t₂ (g • x) ≍ t₂ x) (hm : m ≤ n)
    (ht₁_smooth : ContMDiff I (I.prod 𝓘(𝕜, F₁)) m
      (fun x ↦ TotalSpace.mk' F₁ (Quotient.mk (MulAction.orbitRel G M) x) (t₁ x)))
    (ht₂_smooth : ContMDiff I (I.prod 𝓘(𝕜, F₂)) m
      (fun x ↦ TotalSpace.mk' F₂ (Quotient.mk (MulAction.orbitRel G M) x) (t₂ x))) :
    ContMDiff I (I.prod 𝓘(𝕜, ProjectiveTensor 𝕜 F₁ F₂)) m
      (fun q ↦ TotalSpace.mk' (ProjectiveTensor 𝕜 F₁ F₂) (E := fun q ↦ V₁ q ⊗[𝕜] V₂ q) q
        (MulAction.orbitRelQuotientRec (V := fun q ↦ V₁ q ⊗[𝕜] V₂ q) (fun x ↦ t₁ x ⊗ₜ[𝕜] t₂ x)
          (MulAction.apply₂_heq_of_heq (fun _ v w ↦ v ⊗ₜ[𝕜] w) ht₁ ht₂) q)) :=
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
    ContMDiff (I.prod 𝓘(𝕜, ProjectiveTensor 𝕜 F₁ F₂)) (I.prod 𝓘(𝕜, F₃)) m
        (fun p : TotalSpace (ProjectiveTensor 𝕜 F₁ F₂) (fun q ↦ V₁ q ⊗[𝕜] V₂ q) ↦
          TotalSpace.mk' F₃ p.proj
            (MulAction.orbitRelQuotientRec (V := fun q ↦ V₁ q ⊗[𝕜] V₂ q →L[𝕜] V₃ q)
              (bundleTensorLift Φ) (bundleTensorLift_smul_heq hΦ) p.proj p.2)) ↔
      ContMDiff I (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂ →L[𝕜] F₃)) m
        (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂ →L[𝕜] F₃)
          (E := fun q ↦ V₁ q →L[𝕜] V₂ q →L[𝕜] V₃ q)
          (Quotient.mk (MulAction.orbitRel G M) x) (Φ x)) := by
  conv_lhs => enter [4, p]; rw [← bundleTensorLift_orbitRelQuotientRec hΦ]
  rw [← contMDiff_hom_bundle_iff (IB := I)
      (bundleTensorLift
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

/-- If two invariant linear families `φ₁` and `φ₂` are `C^m` upstairs (`m ≤ n`), the descent of
`bundleTensorMap φ₁ φ₂` induces a `C^m` map of tensor-product total spaces over `M ⧸ G`. -/
theorem ContMDiff.totalSpaceMap_bundleTensorMap_orbitRelQuotientRec
    {φ₁ : ∀ x : M, V₁ (Quotient.mk (MulAction.orbitRel G M) x) →L[𝕜]
      V₁' (Quotient.mk (MulAction.orbitRel G M) x)}
    {φ₂ : ∀ x : M, V₂ (Quotient.mk (MulAction.orbitRel G M) x) →L[𝕜]
      V₂' (Quotient.mk (MulAction.orbitRel G M) x)}
    (hφ₁ : ∀ (g : G) (x : M), φ₁ (g • x) ≍ φ₁ x)
    (hφ₂ : ∀ (g : G) (x : M), φ₂ (g • x) ≍ φ₂ x) (hm : m ≤ n)
    (hφ₁_smooth : ContMDiff I (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₁')) m
      (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₁') (E := fun q ↦ V₁ q →L[𝕜] V₁' q)
        (Quotient.mk (MulAction.orbitRel G M) x) (φ₁ x)))
    (hφ₂_smooth : ContMDiff I (I.prod 𝓘(𝕜, F₂ →L[𝕜] F₂')) m
      (fun x ↦ TotalSpace.mk' (F₂ →L[𝕜] F₂') (E := fun q ↦ V₂ q →L[𝕜] V₂' q)
        (Quotient.mk (MulAction.orbitRel G M) x) (φ₂ x))) :
    ContMDiff (I.prod 𝓘(𝕜, ProjectiveTensor 𝕜 F₁ F₂))
      (I.prod 𝓘(𝕜, ProjectiveTensor 𝕜 F₁' F₂')) m
      (fun p : TotalSpace (ProjectiveTensor 𝕜 F₁ F₂) (fun q ↦ V₁ q ⊗[𝕜] V₂ q) ↦
        TotalSpace.mk' (ProjectiveTensor 𝕜 F₁' F₂') (E := fun q ↦ V₁' q ⊗[𝕜] V₂' q) p.proj
          (MulAction.orbitRelQuotientRec
            (V := fun q ↦ V₁ q ⊗[𝕜] V₂ q →L[𝕜] V₁' q ⊗[𝕜] V₂' q)
            (bundleTensorMap φ₁ φ₂) (bundleTensorMap_smul_heq hφ₁ hφ₂) p.proj p.2)) := by
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
    {φ₁ : ∀ x : M, V₁ (Quotient.mk (MulAction.orbitRel G M) x) →L[𝕜]
      V₁' (Quotient.mk (MulAction.orbitRel G M) x)}
    {φ₂ : ∀ x : M, V₂ (Quotient.mk (MulAction.orbitRel G M) x) →L[𝕜]
      V₂' (Quotient.mk (MulAction.orbitRel G M) x)}
    (hφ₁ : ∀ (g : G) (x : M), φ₁ (g • x) ≍ φ₁ x)
    (hφ₂ : ∀ (g : G) (x : M), φ₂ (g • x) ≍ φ₂ x) (hm : m ≤ n)
    (hφ₁_smooth : ContMDiff I (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₁')) m
      (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₁') (E := fun q ↦ V₁ q →L[𝕜] V₁' q)
        (Quotient.mk (MulAction.orbitRel G M) x) (φ₁ x)))
    (hφ₂_smooth : ContMDiff I (I.prod 𝓘(𝕜, F₂ →L[𝕜] F₂')) m
      (fun x ↦ TotalSpace.mk' (F₂ →L[𝕜] F₂') (E := fun q ↦ V₂ q →L[𝕜] V₂' q)
        (Quotient.mk (MulAction.orbitRel G M) x) (φ₂ x)))
    (hbij₁ : ∀ x : M, Function.Bijective (φ₁ x))
    (hbij₂ : ∀ x : M, Function.Bijective (φ₂ x)) :
    ∃ Φ : TotalSpace (ProjectiveTensor 𝕜 F₁ F₂) (fun q ↦ V₁ q ⊗[𝕜] V₂ q) ≃ₘ^m⟮
        I.prod 𝓘(𝕜, ProjectiveTensor 𝕜 F₁ F₂), I.prod 𝓘(𝕜, ProjectiveTensor 𝕜 F₁' F₂')⟯
        TotalSpace (ProjectiveTensor 𝕜 F₁' F₂') (fun q ↦ V₁' q ⊗[𝕜] V₂' q),
      ⇑Φ = fun p ↦ TotalSpace.mk' (ProjectiveTensor 𝕜 F₁' F₂')
        (E := fun q ↦ V₁' q ⊗[𝕜] V₂' q) p.proj
        (MulAction.orbitRelQuotientRec
          (V := fun q ↦ V₁ q ⊗[𝕜] V₂ q →L[𝕜] V₁' q ⊗[𝕜] V₂' q)
          (bundleTensorMap φ₁ φ₂) (bundleTensorMap_smul_heq hφ₁ hφ₂) p.proj p.2) := by
  let _ : ∀ q, IsTopologicalAddGroup (V₁ q ⊗[𝕜] V₂ q) := fun _ ↦ inferInstance
  let _ : ∀ q, ContinuousSMul 𝕜 (V₁ q ⊗[𝕜] V₂ q) := fun _ ↦ inferInstance
  let _ : ∀ q, IsTopologicalAddGroup (V₁' q ⊗[𝕜] V₂' q) := fun _ ↦ inferInstance
  let _ : ∀ q, ContinuousSMul 𝕜 (V₁' q ⊗[𝕜] V₂' q) := fun _ ↦ inferInstance
  rw [exists_bundleDiffeomorph_iff]
  refine ⟨ContMDiff.totalSpaceMap_bundleTensorMap_orbitRelQuotientRec
    hφ₁ hφ₂ hm hφ₁_smooth hφ₂_smooth, fun q ↦ ?_⟩
  induction q using Quotient.inductionOn with | h x =>
  rw [MulAction.orbitRelQuotientRec_mk]
  let e₁ := LinearEquiv.ofBijective (φ₁ x).toLinearMap (hbij₁ x)
  let e₂ := LinearEquiv.ofBijective (φ₂ x).toLinearMap (hbij₂ x)
  convert (_root_.TensorProduct.congr e₁ e₂).bijective
  ext t : 1
  exact LinearMap.congr_fun (_root_.TensorProduct.ext' fun v w ↦ by
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
          (MulAction.orbitRelQuotientRec (V := fun q ↦ V₁ q →L[𝕜] V₂ q)
            (fun x ↦ bundleDualTensorHom (E₁ := V₁) (E₂ := V₂)
              (Quotient.mk (MulAction.orbitRel G M) x) (τ x))
            (MulAction.apply_heq_of_heq
              (fun q t ↦ bundleDualTensorHom (E₁ := V₁) (E₂ := V₂) q t) hτ) q)) ↔
      ContMDiff I (I.prod 𝓘(𝕜, ProjectiveTensor 𝕜 (StrongDual 𝕜 F₁) F₂)) m
        (fun x ↦ TotalSpace.mk' (ProjectiveTensor 𝕜 (StrongDual 𝕜 F₁) F₂)
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
