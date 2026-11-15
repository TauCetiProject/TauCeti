/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Quotient.Section
public import TauCeti.Geometry.Manifold.VectorBundle.Hom

/-!
# Descending linear bundle maps through an orbit projection

Let `q : M → M/G` be the orbit projection of a free properly discontinuous action by `C^n`
maps. For vector bundles `V` and `W` over `M/G`, an invariant family of continuous linear maps
`φ x : V (q x) →L[𝕜] W (q x)` descends through the existing dependent recursor
`TauCeti.MulAction.orbitRelQuotientRec`. No quotient bundle or new total-space carrier is needed.

For finite-dimensional model source fibre, the descended map of total spaces is `C^m`, for
`m ≤ n`, exactly when the invariant family is a `C^m` section of the pullback of the Hom bundle.
The descent is unique among fibrewise continuous linear maps with the prescribed pullback.
It underlies a `C^m` diffeomorphism exactly when, in addition, every upstairs fibre map is
bijective. The target fibre need not be finite-dimensional. Over `ℂ` at regularity `∞`, these
are holomorphic bundle-map descent and the corresponding bundle-equivalence criterion.

These results concern bundles already defined on the quotient and their pullbacks. They do not
construct the quotient of an arbitrary equivariant vector bundle.

The proofs combine the section descent in `TauCeti.Geometry.Manifold.Quotient.Section` with
`TauCeti.contMDiff_hom_bundle_iff` and `TauCeti.exists_bundleDiffeomorph_iff`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 21.
* Daniel Huybrechts, *Complex Geometry: An Introduction*, Section 2.2.
-/

public section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti

variable {G M : Type*} [Group G] [MulAction G M] [TopologicalSpace M]
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [ChartedSpace H M] {m n : ℕ∞ω}
  [ProperlyDiscontinuousSMul G M] [ContinuousConstSMul G M] [IsCancelSMul G M]
  [T2Space M] [LocallyCompactSpace M] [IsManifold I n M] [ContMDiffConstSMul I n G M]
  {F₁ F₂ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {V W : MulAction.orbitRel.Quotient G M → Type*}
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)]
  [TopologicalSpace (TotalSpace F₁ V)] [FiberBundle F₁ V] [VectorBundle 𝕜 F₁ V]
  [∀ x, AddCommGroup (W x)] [∀ x, Module 𝕜 (W x)] [∀ x, TopologicalSpace (W x)]
  [∀ x, IsTopologicalAddGroup (W x)] [∀ x, ContinuousSMul 𝕜 (W x)]
  [TopologicalSpace (TotalSpace F₂ W)] [FiberBundle F₂ W] [VectorBundle 𝕜 F₂ W]
  {φ : ∀ x : M, V (Quotient.mk (MulAction.orbitRel G M) x) →L[𝕜]
    W (Quotient.mk (MulAction.orbitRel G M) x)}
  {hφ : ∀ (g : G) (x : M), φ (g • x) ≍ φ x}

/-- The total-space map descended from an invariant linear family is `C^m` exactly when the
family is a `C^m` section of the pulled-back Hom bundle. No smoothness assumption on the bundle
transition functions is needed for this comparison of the two regularity predicates. -/
theorem contMDiff_totalSpaceMap_orbitRelQuotientRec_iff (hm : m ≤ n) :
    ContMDiff (I.prod 𝓘(𝕜, F₁)) (I.prod 𝓘(𝕜, F₂)) m
        (fun p : TotalSpace F₁ V ↦ TotalSpace.mk' F₂ p.proj
          (MulAction.orbitRelQuotientRec (V := fun q ↦ V q →L[𝕜] W q) φ hφ p.proj p.2)) ↔
      ContMDiff I (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) m
        (fun x ↦ (TotalSpace.mk' (F₁ →L[𝕜] F₂) x (φ x) :
          TotalSpace (F₁ →L[𝕜] F₂)
            (⇑(⟨Quotient.mk _, continuous_quotient_mk'⟩ :
              C(M, MulAction.orbitRel.Quotient G M)) *ᵖ (fun q ↦ V q →L[𝕜] W q)))) := by
  rw [← contMDiff_hom_bundle_iff]
  exact (contMDiff_pullback_section_iff_orbitRelQuotientRec
    (V := fun q ↦ V q →L[𝕜] W q) (t := φ) (ht := hφ) hm).symm

include hφ in
/-- An invariant linear family is a `C^m` section of the pulled-back Hom bundle exactly when
it is the pullback of a unique family inducing a `C^m` map of total spaces downstairs. -/
theorem existsUnique_contMDiff_bundleMap_iff (hm : m ≤ n) :
    (∃! ψ : ∀ q, V q →L[𝕜] W q,
      ContMDiff (I.prod 𝓘(𝕜, F₁)) (I.prod 𝓘(𝕜, F₂)) m
          (fun p : TotalSpace F₁ V ↦ TotalSpace.mk' F₂ p.proj (ψ p.proj p.2)) ∧
        ∀ x : M, ψ (Quotient.mk (MulAction.orbitRel G M) x) = φ x) ↔
      ContMDiff I (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) m
        (fun x ↦ (TotalSpace.mk' (F₁ →L[𝕜] F₂) x (φ x) :
          TotalSpace (F₁ →L[𝕜] F₂)
            (⇑(⟨Quotient.mk _, continuous_quotient_mk'⟩ :
              C(M, MulAction.orbitRel.Quotient G M)) *ᵖ (fun q ↦ V q →L[𝕜] W q)))) := by
  constructor
  · rintro ⟨ψ, ⟨hψ, hpull⟩, _⟩
    have heq := (MulAction.eq_orbitRelQuotientRec_iff (ht := hφ)).2 hpull
    subst ψ
    exact (contMDiff_totalSpaceMap_orbitRelQuotientRec_iff hm).1 hψ
  · intro h
    refine ⟨MulAction.orbitRelQuotientRec (V := fun q ↦ V q →L[𝕜] W q) φ hφ,
      ⟨(contMDiff_totalSpaceMap_orbitRelQuotientRec_iff hm).2 h,
        MulAction.orbitRelQuotientRec_mk⟩, ?_⟩
    intro ψ hψ
    exact MulAction.eq_orbitRelQuotientRec_iff.2 hψ.2

/-- The descended linear family underlies a `C^m` diffeomorphism of total spaces exactly when
its pulled-back Hom section is `C^m` and all its fibre maps upstairs are bijective. Smoothness of
the inverse downstairs follows automatically. -/
theorem exists_bundleDiffeomorph_orbitRelQuotientRec_iff (hm : m ≤ n) :
    (∃ Φ : TotalSpace F₁ V ≃ₘ^m⟮I.prod 𝓘(𝕜, F₁), I.prod 𝓘(𝕜, F₂)⟯ TotalSpace F₂ W,
      ⇑Φ = fun p ↦ TotalSpace.mk' F₂ p.proj
        (MulAction.orbitRelQuotientRec (V := fun q ↦ V q →L[𝕜] W q) φ hφ p.proj p.2)) ↔
      ContMDiff I (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) m
          (fun x ↦ (TotalSpace.mk' (F₁ →L[𝕜] F₂) x (φ x) :
            TotalSpace (F₁ →L[𝕜] F₂)
              (⇑(⟨Quotient.mk _, continuous_quotient_mk'⟩ :
                C(M, MulAction.orbitRel.Quotient G M)) *ᵖ (fun q ↦ V q →L[𝕜] W q)))) ∧
        ∀ x, Function.Bijective (φ x) := by
  rw [exists_bundleDiffeomorph_iff, contMDiff_totalSpaceMap_orbitRelQuotientRec_iff hm]
  apply and_congr_right
  intro _
  exact Quotient.mk_surjective.forall.trans (by simp only [MulAction.orbitRelQuotientRec_mk])

end TauCeti
