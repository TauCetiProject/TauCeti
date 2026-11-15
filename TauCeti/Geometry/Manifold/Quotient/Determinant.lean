/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Quotient.BundleMap
public import TauCeti.Geometry.Manifold.VectorBundle.Determinant

/-!
# Compatibility of quotient bundle descent with determinants and top-degree forms

Let `q : M → M ⧸ G` be the orbit projection of a free properly discontinuous action by `C^n` maps
on a `C^n` manifold `M`. For vector bundles over `M ⧸ G`, quotient descent commutes with
endomorphism determinants and alternating-form pullbacks:

* **Endomorphism determinant:** the fibrewise determinant `ContinuousLinearMap.det` of the
  descended endomorphism section `MulAction.orbitRelQuotientRec φ hφ` equals the scalar descent
  `MulAction.orbitRelQuotientLift` of `x ↦ (φ x).det` (`TauCeti.det_orbitRelQuotientRec`), and is
  `C^m` for `m ≤ n` whenever `φ` is `C^m` upstairs over a complete field
  (`TauCeti.ContMDiff.orbitRelQuotientLift_det`). In finite rank, the descended endomorphism family
  underlies a `C^m` bundle automorphism of `TotalSpace F V` if and only if `φ` is a `C^m` section
  of the pulled-back endomorphism bundle and `(φ x).det ≠ 0` everywhere upstairs
  (`TauCeti.exists_bundleDiffeomorph_orbitRelQuotientRec_iff_det_ne_zero`).
* **Alternating-form pullback and determinant line action:** fibrewise domain pullback
  `ContinuousAlternatingMap.compContinuousLinearMap` commutes with `MulAction.orbitRelQuotientRec`
  (`TauCeti.compContinuousLinearMap_orbitRelQuotientRec`) and preserves `C^m` regularity for
  `m ≤ n` (`TauCeti.ContMDiff.section_compContinuousLinearMap_orbitRelQuotientRec`). On the
  top-degree alternating line bundle (`Fintype.card ι = Module.finrank 𝕜 F`), pulling back a
  descended top form along a descended endomorphism equals scalar multiplication by the descended
  determinant (`TauCeti.bundleTopForm_compContinuousLinearMap_orbitRelQuotientRec_eq_det_smul`).

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

section Algebraic

variable {G M : Type*} [Group G] [MulAction G M]

/-- Fibrewise determinant `ContinuousLinearMap.det` commutes with quotient descent: the determinant
of `MulAction.orbitRelQuotientRec φ hφ` at `q` equals the scalar descent of `x ↦ (φ x).det`. -/
theorem det_orbitRelQuotientRec {𝕜 : Type*} [CommRing 𝕜]
    {V : MulAction.orbitRel.Quotient G M → Type*}
    [∀ q, AddCommGroup (V q)] [∀ q, Module 𝕜 (V q)] [∀ q, TopologicalSpace (V q)]
    {φ : ∀ x : M, V (Quotient.mk (MulAction.orbitRel G M) x) →L[𝕜]
      V (Quotient.mk (MulAction.orbitRel G M) x)}
    (hφ : ∀ (g : G) (x : M), φ (g • x) ≍ φ x)
    (q : MulAction.orbitRel.Quotient G M) :
    (MulAction.orbitRelQuotientRec (V := fun q ↦ V q →L[𝕜] V q) φ hφ q).det =
      MulAction.orbitRelQuotientLift (fun x ↦ (φ x).det)
        (MulAction.apply_eq_of_heq (fun _ (A : _ →L[𝕜] _) ↦ A.det) hφ) q :=
  MulAction.apply_orbitRelQuotientRec_eq_orbitRelQuotientLift
    (fun _ (A : _ →L[𝕜] _) ↦ A.det) hφ q

/-- Fibrewise domain pullback `ContinuousAlternatingMap.compContinuousLinearMap` of alternating
maps commutes with `MulAction.orbitRelQuotientRec`. -/
theorem compContinuousLinearMap_orbitRelQuotientRec {𝕜 ι : Type*} [CommRing 𝕜]
    {V₁ V₂ V₃ : MulAction.orbitRel.Quotient G M → Type*}
    [∀ q, AddCommGroup (V₁ q)] [∀ q, Module 𝕜 (V₁ q)] [∀ q, TopologicalSpace (V₁ q)]
    [∀ q, AddCommGroup (V₂ q)] [∀ q, Module 𝕜 (V₂ q)] [∀ q, TopologicalSpace (V₂ q)]
    [∀ q, AddCommGroup (V₃ q)] [∀ q, Module 𝕜 (V₃ q)] [∀ q, TopologicalSpace (V₃ q)]
    {α : ∀ x : M, V₂ (Quotient.mk (MulAction.orbitRel G M) x) [⋀^ι]→L[𝕜]
      V₃ (Quotient.mk (MulAction.orbitRel G M) x)}
    {A : ∀ x : M, V₁ (Quotient.mk (MulAction.orbitRel G M) x) →L[𝕜]
      V₂ (Quotient.mk (MulAction.orbitRel G M) x)}
    (hα : ∀ (g : G) (x : M), α (g • x) ≍ α x)
    (hA : ∀ (g : G) (x : M), A (g • x) ≍ A x)
    (q : MulAction.orbitRel.Quotient G M) :
    ContinuousAlternatingMap.compContinuousLinearMap
        (MulAction.orbitRelQuotientRec (V := fun q ↦ V₂ q [⋀^ι]→L[𝕜] V₃ q) α hα q)
        (MulAction.orbitRelQuotientRec (V := fun q ↦ V₁ q →L[𝕜] V₂ q) A hA q) =
      MulAction.orbitRelQuotientRec (V := fun q ↦ V₁ q [⋀^ι]→L[𝕜] V₃ q)
        (fun x ↦ (α x).compContinuousLinearMap (A x))
        (MulAction.apply₂_heq_of_heq
          (fun _ (f : _ [⋀^ι]→L[𝕜] _) (T : _ →L[𝕜] _) ↦ f.compContinuousLinearMap T) hα hA) q :=
  MulAction.apply₂_orbitRelQuotientRec
    (fun _ (f : _ [⋀^ι]→L[𝕜] _) (T : _ →L[𝕜] _) ↦ f.compContinuousLinearMap T) hα hA q

end Algebraic

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
  {hφ : ∀ (g : G) (x : M), φ (g • x) ≍ φ x}

/-- Over a complete field, if an invariant endomorphism family `φ` is `C^m` upstairs (`m ≤ n`), the
scalar descent of `x ↦ (φ x).det` is a `C^m` function on `M ⧸ G`. -/
theorem ContMDiff.orbitRelQuotientLift_det (hm : m ≤ n)
    (hφ_smooth : ContMDiff I (I.prod 𝓘(𝕜, F →L[𝕜] F)) m
      (fun x ↦ TotalSpace.mk' (F →L[𝕜] F) (E := fun q ↦ V q →L[𝕜] V q)
        (Quotient.mk (MulAction.orbitRel G M) x) (φ x))) :
    ContMDiff I 𝓘(𝕜) m
      (MulAction.orbitRelQuotientLift (fun x ↦ (φ x).det)
        (MulAction.apply_eq_of_heq (fun _ (A : _ →L[𝕜] _) ↦ A.det) hφ)) :=
  (contMDiff_orbitRelQuotientLift_iff hm).2 hφ_smooth.clm_bundle_det

/-- For a finite-rank vector bundle over `M ⧸ G`, the descended endomorphism family
`MulAction.orbitRelQuotientRec φ hφ` underlies a `C^m` automorphism of `TotalSpace F V` (`m ≤ n`)
if and only if `φ` is a `C^m` section of the pulled-back endomorphism bundle and `(φ x).det ≠ 0`
for every `x : M`. -/
theorem exists_bundleDiffeomorph_orbitRelQuotientRec_iff_det_ne_zero [FiniteDimensional 𝕜 F]
    (hm : m ≤ n) :
    (∃ Φ : TotalSpace F V ≃ₘ^m⟮I.prod 𝓘(𝕜, F), I.prod 𝓘(𝕜, F)⟯ TotalSpace F V,
        ⇑Φ = fun p ↦ TotalSpace.mk' F p.proj
          (MulAction.orbitRelQuotientRec (V := fun q ↦ V q →L[𝕜] V q) φ hφ p.proj p.2)) ↔
      ContMDiff I (I.prod 𝓘(𝕜, F →L[𝕜] F)) m
          (fun x ↦ (TotalSpace.mk' (F →L[𝕜] F) x (φ x) :
            TotalSpace (F →L[𝕜] F)
              (⇑(⟨Quotient.mk _, continuous_quotient_mk'⟩ :
                C(M, MulAction.orbitRel.Quotient G M)) *ᵖ (fun q ↦ V q →L[𝕜] V q)))) ∧
        ∀ x : M, (φ x).det ≠ 0 := by
  rw [exists_bundleDiffeomorph_iff_det_ne_zero,
    contMDiff_totalSpaceMap_orbitRelQuotientRec_iff hm]
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
theorem ContMDiff.section_compContinuousLinearMap_orbitRelQuotientRec
    {α : ∀ x : M, V₂ (Quotient.mk (MulAction.orbitRel G M) x) [⋀^ι]→L[𝕜]
      V₃ (Quotient.mk (MulAction.orbitRel G M) x)}
    {A : ∀ x : M, V₁ (Quotient.mk (MulAction.orbitRel G M) x) →L[𝕜]
      V₂ (Quotient.mk (MulAction.orbitRel G M) x)}
    (hα : ∀ (g : G) (x : M), α (g • x) ≍ α x) (hA : ∀ (g : G) (x : M), A (g • x) ≍ A x)
    (hm : m ≤ n)
    (hα_smooth : ContMDiff I (I.prod 𝓘(𝕜, F₂ [⋀^ι]→L[𝕜] F₃)) m
      (fun x ↦ TotalSpace.mk' (F₂ [⋀^ι]→L[𝕜] F₃) (E := fun q ↦ V₂ q [⋀^ι]→L[𝕜] V₃ q)
        (Quotient.mk (MulAction.orbitRel G M) x) (α x)))
    (hA_smooth : ContMDiff I (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) m
      (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun q ↦ V₁ q →L[𝕜] V₂ q)
        (Quotient.mk (MulAction.orbitRel G M) x) (A x)))
    (hfact : m = ω → ((Fintype.card ι).factorial : 𝕜) ≠ 0 := by
      intro h; first | exact NeZero.ne _ | cases h) :
    ContMDiff I (I.prod 𝓘(𝕜, F₁ [⋀^ι]→L[𝕜] F₃)) m
      (fun q ↦ TotalSpace.mk' (F₁ [⋀^ι]→L[𝕜] F₃) (E := fun q ↦ V₁ q [⋀^ι]→L[𝕜] V₃ q) q
        (MulAction.orbitRelQuotientRec (V := fun q ↦ V₁ q [⋀^ι]→L[𝕜] V₃ q)
          (fun x ↦ (α x).compContinuousLinearMap (A x))
          (MulAction.apply₂_heq_of_heq
            (fun _ (f : _ [⋀^ι]→L[𝕜] _) (T : _ →L[𝕜] _) ↦ f.compContinuousLinearMap T) hα hA) q)) :=
  (contMDiff_section_orbitRelQuotientRec_iff hm).2
    (hα_smooth.continuousAlternatingMap_comp_clm hA_smooth hfact)

end AlternatingSmooth

end Manifold

section TopFormQuotient

variable {G M 𝕜 ι F : Type*} [Group G] [MulAction G M] [TopologicalSpace M]
  [NontriviallyNormedField 𝕜] [Fintype ι] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [FiniteDimensional 𝕜 F] {V : MulAction.orbitRel.Quotient G M → Type*}
  [∀ q, AddCommGroup (V q)] [∀ q, Module 𝕜 (V q)] [∀ q, TopologicalSpace (V q)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- On the top-degree scalar alternating line bundle (`Fintype.card ι = Module.finrank 𝕜 F`) over
`M ⧸ G`, pulling back a descended top form along a descended endomorphism multiplies the form by
the descended scalar determinant `MulAction.orbitRelQuotientLift (fun x ↦ (φ x).det) ...`. -/
theorem bundleTopForm_compContinuousLinearMap_orbitRelQuotientRec_eq_det_smul
    (hrank : Fintype.card ι = Module.finrank 𝕜 F)
    {α : ∀ x : M, V (Quotient.mk (MulAction.orbitRel G M) x) [⋀^ι]→L[𝕜] 𝕜}
    {φ : ∀ x : M, V (Quotient.mk (MulAction.orbitRel G M) x) →L[𝕜]
      V (Quotient.mk (MulAction.orbitRel G M) x)}
    (hα : ∀ (g : G) (x : M), α (g • x) ≍ α x) (hφ : ∀ (g : G) (x : M), φ (g • x) ≍ φ x)
    (q : MulAction.orbitRel.Quotient G M) :
    ContinuousAlternatingMap.compContinuousLinearMap
        (MulAction.orbitRelQuotientRec (V := fun q ↦ V q [⋀^ι]→L[𝕜] 𝕜) α hα q)
        (MulAction.orbitRelQuotientRec (V := fun q ↦ V q →L[𝕜] V q) φ hφ q) =
      MulAction.orbitRelQuotientLift (fun x ↦ (φ x).det)
        (MulAction.apply_eq_of_heq (fun _ (A : _ →L[𝕜] _) ↦ A.det) hφ) q •
        MulAction.orbitRelQuotientRec (V := fun q ↦ V q [⋀^ι]→L[𝕜] 𝕜) α hα q := by
  rw [bundleTopForm_compContinuousLinearMap_eq_det_smul hrank, det_orbitRelQuotientRec]

end TopFormQuotient

end TauCeti
