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
`TauCeti.contMDiff_hom_bundle_iff` and `TauCeti.exists_bundleDiffeomorph_iff`. Pulling back an
invariant linear family along an equivariant `C^m` map commutes with descent along
`Pullback.lift`, inducing `C^m` maps and diffeomorphisms of the pulled-back total spaces over the
source orbit space (`TauCeti.lift_totalSpaceMap_pullbackOrbitSection_orbitRelQuotientRec`,
`TauCeti.ContMDiff.totalSpaceMap_pullbackOrbitSection_orbitRelQuotientRec`,
`TauCeti.exists_bundleDiffeomorph_pullbackOrbitSection_orbitRelQuotientRec`).

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 21.
* Daniel Huybrechts, *Complex Geometry: An Introduction*, Section 2.2.
-/

public section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti

section AlgebraicPullback

variable {G M G' M' 𝕜 F₁ F₂ : Type*} [Group G] [MulAction G M] [Group G'] [MulAction G' M']
  [Semiring 𝕜] {V W : MulAction.orbitRel.Quotient G M → Type*}
  [∀ q, AddCommMonoid (V q)] [∀ q, Module 𝕜 (V q)] [∀ q, TopologicalSpace (V q)]
  [∀ q, AddCommMonoid (W q)] [∀ q, Module 𝕜 (W q)] [∀ q, TopologicalSpace (W q)]
  {σ : G' → G} (ψ : M' →ₑ[σ] M)
  {φ : ∀ x : M, V (Quotient.mk (MulAction.orbitRel G M) x) →L[𝕜]
    W (Quotient.mk (MulAction.orbitRel G M) x)}
  (hφ : ∀ (g : G) (x : M), φ (g • x) ≍ φ x)

/-- On total spaces, the `G'`-descent of the equivariant pullback of `φ` intertwines with the
`G`-descent of `φ` along `Pullback.lift ψ.orbitRelQuotientMap`. -/
theorem lift_totalSpaceMap_pullbackOrbitSection_orbitRelQuotientRec
    (p : TotalSpace F₁ (ψ.orbitRelQuotientMap *ᵖ V)) :
    Pullback.lift ψ.orbitRelQuotientMap
        (TotalSpace.mk' F₂ (E := ψ.orbitRelQuotientMap *ᵖ W) p.proj
          (MulAction.orbitRelQuotientRec
            (V := fun q' ↦ (ψ.orbitRelQuotientMap *ᵖ V) q' →L[𝕜] (ψ.orbitRelQuotientMap *ᵖ W) q')
            (ψ.pullbackOrbitSection (V := fun q ↦ V q →L[𝕜] W q) φ)
            (ψ.pullbackOrbitSection_smul_heq (V := fun q ↦ V q →L[𝕜] W q) hφ) p.proj p.2)) =
      TotalSpace.mk' F₂ (ψ.orbitRelQuotientMap p.proj)
        (MulAction.orbitRelQuotientRec (V := fun q ↦ V q →L[𝕜] W q) φ hφ
          (ψ.orbitRelQuotientMap p.proj) p.2) :=
  congrArg
    (fun T : V (ψ.orbitRelQuotientMap p.proj) →L[𝕜] W (ψ.orbitRelQuotientMap p.proj) ↦
      TotalSpace.mk' F₂ (ψ.orbitRelQuotientMap p.proj) (T p.2))
    (ψ.orbitRelQuotientRec_pullbackOrbitSection (V := fun q ↦ V q →L[𝕜] W q) hφ p.proj)

end AlgebraicPullback

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

variable [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]

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

section EquivariantPullback

variable {G' M' E' H' : Type*} [Group G'] [MulAction G' M'] [TopologicalSpace M']
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} [ChartedSpace H' M']
  [ProperlyDiscontinuousSMul G' M'] [ContinuousConstSMul G' M'] [IsCancelSMul G' M']
  [T2Space M'] [LocallyCompactSpace M'] [IsManifold I' n M'] [ContMDiffConstSMul I' n G' M']
  {σ : G' → G}

omit [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)] in
/-- Pulling back a `G`-invariant `C^m` linear bundle-map family along a `C^m` equivariant map
`ψ : M' →ₑ[σ] M` (`m ≤ n`) yields a `G'`-invariant family whose descent induces a `C^m` map of
pulled-back total spaces over `M' ⧸ G'`. -/
theorem ContMDiff.totalSpaceMap_pullbackOrbitSection_orbitRelQuotientRec {ψ : M' →ₑ[σ] M}
    (hm : m ≤ n) (hψ : ContMDiff I' I m ψ)
    (hφ_smooth : ContMDiff I (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) m
      (fun x ↦ (TotalSpace.mk' (F₁ →L[𝕜] F₂) x (φ x) :
        TotalSpace (F₁ →L[𝕜] F₂)
          (⇑(⟨Quotient.mk _, continuous_quotient_mk'⟩ :
            C(M, MulAction.orbitRel.Quotient G M)) *ᵖ (fun q ↦ V q →L[𝕜] W q))))) :
    let f : C(MulAction.orbitRel.Quotient G' M', MulAction.orbitRel.Quotient G M) :=
      ⟨ψ.orbitRelQuotientMap, (contMDiff_orbitRelQuotientMap hm hψ).continuous⟩
    ContMDiff (I'.prod 𝓘(𝕜, F₁)) (I'.prod 𝓘(𝕜, F₂)) m
      (fun p : TotalSpace F₁ (⇑f *ᵖ V) ↦ TotalSpace.mk' F₂ (E := ⇑f *ᵖ W) p.proj
        (MulAction.orbitRelQuotientRec
          (V := fun q' ↦ (⇑f *ᵖ V) q' →L[𝕜] (⇑f *ᵖ W) q')
          (ψ.pullbackOrbitSection (V := fun q ↦ V q →L[𝕜] W q) φ)
          (ψ.pullbackOrbitSection_smul_heq (V := fun q ↦ V q →L[𝕜] W q) hφ) p.proj p.2)) := by
  intro f
  have hdown := (contMDiff_totalSpaceMap_orbitRelQuotientRec_iff (hφ := hφ) hm).2 hφ_smooth
  refine (Bundle.Pullback.contMDiff_fiberwise
    (fun q v ↦ MulAction.orbitRelQuotientRec (V := fun q ↦ V q →L[𝕜] W q) φ hφ q v)
    hdown f (contMDiff_orbitRelQuotientMap hm hψ)).congr fun p ↦
      congrArg (fun T : V (f p.proj) →L[𝕜] W (f p.proj) ↦ TotalSpace.mk' F₂ (E := ⇑f *ᵖ W) p.proj
        (T p.2)) (ψ.orbitRelQuotientRec_pullbackOrbitSection (V := fun q ↦ V q →L[𝕜] W q) hφ p.proj)

/-- If a `G`-invariant linear family `φ` satisfies the upstairs `C^m` bundle-diffeomorphism
criterion over `M`, its equivariant pullback along a `C^m` map `ψ : M' →ₑ[σ] M` (`m ≤ n`) descends
to a `C^m` diffeomorphism of pulled-back total spaces over `M' ⧸ G'`. -/
theorem exists_bundleDiffeomorph_pullbackOrbitSection_orbitRelQuotientRec {ψ : M' →ₑ[σ] M}
    (hm : m ≤ n) (hψ : ContMDiff I' I m ψ)
    (hφ_smooth : ContMDiff I (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) m
      (fun x ↦ (TotalSpace.mk' (F₁ →L[𝕜] F₂) x (φ x) :
        TotalSpace (F₁ →L[𝕜] F₂)
          (⇑(⟨Quotient.mk _, continuous_quotient_mk'⟩ :
            C(M, MulAction.orbitRel.Quotient G M)) *ᵖ (fun q ↦ V q →L[𝕜] W q)))))
    (hbij : ∀ x : M, Function.Bijective (φ x)) :
    let f : C(MulAction.orbitRel.Quotient G' M', MulAction.orbitRel.Quotient G M) :=
      ⟨ψ.orbitRelQuotientMap, (contMDiff_orbitRelQuotientMap hm hψ).continuous⟩
    ∃ Φ : TotalSpace F₁ (⇑f *ᵖ V) ≃ₘ^m⟮I'.prod 𝓘(𝕜, F₁), I'.prod 𝓘(𝕜, F₂)⟯ TotalSpace F₂ (⇑f *ᵖ W),
      ⇑Φ = fun p ↦ TotalSpace.mk' F₂ (E := ⇑f *ᵖ W) p.proj
        (MulAction.orbitRelQuotientRec
          (V := fun q' ↦ (⇑f *ᵖ V) q' →L[𝕜] (⇑f *ᵖ W) q')
          (ψ.pullbackOrbitSection (V := fun q ↦ V q →L[𝕜] W q) φ)
          (ψ.pullbackOrbitSection_smul_heq (V := fun q ↦ V q →L[𝕜] W q) hφ) p.proj p.2) := by
  intro f
  let _ : ∀ q', IsTopologicalAddGroup ((⇑f *ᵖ V) q') :=
    fun q' ↦ ‹∀ q, IsTopologicalAddGroup (V q)› (f q')
  let _ : ∀ q', ContinuousSMul 𝕜 ((⇑f *ᵖ V) q') := fun q' ↦ ‹∀ q, ContinuousSMul 𝕜 (V q)› (f q')
  let _ : ∀ q', IsTopologicalAddGroup ((⇑f *ᵖ W) q') :=
    fun q' ↦ ‹∀ q, IsTopologicalAddGroup (W q)› (f q')
  let _ : ∀ q', ContinuousSMul 𝕜 ((⇑f *ᵖ W) q') := fun q' ↦ ‹∀ q, ContinuousSMul 𝕜 (W q)› (f q')
  rw [exists_bundleDiffeomorph_iff (IB := I') (fun q' ↦ MulAction.orbitRelQuotientRec
    (V := fun q' ↦ (⇑f *ᵖ V) q' →L[𝕜] (⇑f *ᵖ W) q')
    (ψ.pullbackOrbitSection (V := fun q ↦ V q →L[𝕜] W q) φ)
    (ψ.pullbackOrbitSection_smul_heq (V := fun q ↦ V q →L[𝕜] W q) hφ) q')]
  refine ⟨ContMDiff.totalSpaceMap_pullbackOrbitSection_orbitRelQuotientRec
    (hφ := hφ) hm hψ hφ_smooth, fun q' ↦ ?_⟩
  have hbij_q : ∀ q, Function.Bijective
      (MulAction.orbitRelQuotientRec (V := fun q ↦ V q →L[𝕜] W q) φ hφ q) :=
    Quotient.mk_surjective.forall.2 fun x ↦ by
      simpa only [MulAction.orbitRelQuotientRec_mk] using hbij x
  exact (congrArg (fun T : V (f q') →L[𝕜] W (f q') ↦ Function.Bijective (T : V (f q') → W (f q')))
    (ψ.orbitRelQuotientRec_pullbackOrbitSection (V := fun q ↦ V q →L[𝕜] W q) hφ q')).mpr
    (hbij_q (f q'))

end EquivariantPullback

end TauCeti
