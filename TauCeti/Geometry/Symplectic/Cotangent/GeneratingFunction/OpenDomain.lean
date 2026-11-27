/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Opens
public import TauCeti.Geometry.Symplectic.Cotangent.GeneratingFunction.GeneratedMap
import TauCeti.Geometry.Manifold.ChartedSpace
import TauCeti.Geometry.Manifold.ContMDiffMap.Extension
import TauCeti.Geometry.Manifold.DifferentialForm.Opens
import TauCeti.Geometry.Manifold.MFDeriv.Opens

/-!
# Generating functions on open domains

A generating function need only be smooth on an open subset of the product of its two base
manifolds. The source and target covectors and the mixed Hessian depend only on its germ.
Consequently, a smooth extension of this germ gives a local canonical transformation whose
entire branch stays inside the original domain.

`TauCeti.CotangentBundle.exists_partialDiffeomorph_of_isInvertible_mixedHessian` constructs this
transformation `Φ`, its smooth branch `β`, the two covector identities, and the exact Liouville
primitive `λ - Φ^* λ = d(S ∘ β)`. The branch is unique among continuous local right inverses of the
source projection through the specified point. The construction uses the globally smooth
generated-map API and a smooth bump extension; no regularity outside the given open domain is
needed.

The bump extension needs Hausdorff base manifolds, but the generated relation is local in the base
as well: restricting `S` to a product `U × V` of open subsets does not change its mixed Hessian
(`TauCeti.mixedHessian_comp_prodMap_subtype_val`), and the cotangent inclusions `T*U → T*M`,
`T*V → T*N` carry the source and target projections of the restriction to those of `S`
(`TauCeti.CotangentBundle.openInclusion_generatingSource`,
`TauCeti.CotangentBundle.openInclusion_generatingTarget`). Chart domains are Hausdorff, so the
construction is carried out over the chart domains at the base point and read in the ambient
cotangent bundles (`TauCeti.CotangentBundle.exists_partialDiffeomorph_openInclusion_eq`). The
cotangent inclusion pulls the Liouville form back to the Liouville form
(`TauCeti.CotangentBundle.mpullback_openInclusion_liouvilleForm`) and has surjective differential,
so the exact primitive survives this transfer; and a competing branch in the ambient bundles is
read over the chart domains, where the branch is unique. Thus neither the transformation, nor its
primitive, nor the uniqueness of its branch needs a Hausdorff hypothesis.

`TauCeti.CotangentBundle.exists_diffeomorph_opens_of_isInvertible_mixedHessian` states the result
as a diffeomorphism `φ : U → V` between open sets `U ⊆ T*M` and `V ⊆ T*N` which pulls the
canonical symplectic form of `T*N`, restricted to `V`, back to that of `T*M`, restricted to `U`.
It sends `(q₀, d_q S (x))` to `(Q₀, -d_Q S (x))`, and its graph lies in the relation
`p = d_q S (q, Q)`, `P = -d_Q S (q, Q)` with `(q, Q)` in the domain of `S`. It is an exact
symplectomorphism: for the branch `b (q, p) = (q, Q)`, `λ_M - φ^* λ_N = d(S ∘ b)` on `U`. It is
unique as a germ (`TauCeti.CotangentBundle.eventually_apply_eq_of_isInvertible_mixedHessian`): any
two maps defined near `(q₀, d_q S (x))`, continuous there, which send it to `(Q₀, -d_Q S (x))` and
satisfy the generated relation agree on a neighbourhood of it.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Section 4.2.
* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, second edition, Section 48.
-/

public section

noncomputable section

open Bundle Filter Manifold Set TopologicalSpace
open scoped Manifold ContDiff Topology

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F H' : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {S : M × N → ℝ} {x : M × N}

namespace TauCeti.CotangentBundle

/-! ### Restricting generating functions to open subsets -/

/-- The cotangent inclusion of an open subset `U ⊆ M` carries the source projection of the
restriction of `S` to `U × V` to the source projection of `S`. -/
theorem openInclusion_generatingSource {U : Opens M} {V : Opens N} (S : M × N → ℝ) (y : U × V) :
    openInclusion U (generatingSource I (S ∘ Prod.map Subtype.val Subtype.val) y) =
      generatingSource I S (Prod.map Subtype.val Subtype.val y) := by
  rw [openInclusion_def, generatingSource_eq_mk, generatingSource_eq_mk]
  refine CotangentBundle.ext rfl fun v ↦ ?_
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    Manifold.tangentSpaceOpenEquiv_symm_apply]
  exact congrArg (· v) (Manifold.mvfderiv_comp_subtype_val (J := I) (fun q ↦ S (q, (y.2 : N))) y.1)

/-- The cotangent inclusion of an open subset `V ⊆ N` carries the target projection of the
restriction of `S` to `U × V` to the target projection of `S`. -/
theorem openInclusion_generatingTarget {U : Opens M} {V : Opens N} (S : M × N → ℝ) (y : U × V) :
    openInclusion V (generatingTarget J (S ∘ Prod.map Subtype.val Subtype.val) y) =
      generatingTarget J S (Prod.map Subtype.val Subtype.val y) := by
  rw [openInclusion_def, generatingTarget_eq_mk, generatingTarget_eq_mk]
  refine CotangentBundle.ext rfl fun v ↦ ?_
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    Manifold.tangentSpaceOpenEquiv_symm_apply]
  exact congrArg (fun L ↦ (-L) v)
    (Manifold.mvfderiv_comp_subtype_val (J := J) (fun Q ↦ S ((y.1 : M), Q)) y.2)

variable [IsManifold I ∞ M] [IsManifold J ∞ N]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [BoundarylessManifold I M] [BoundarylessManifold J N]

section T2

variable [T2Space M] [T2Space N]

/-- Local generation on an open domain, for Hausdorff base manifolds: the case of
`TauCeti.CotangentBundle.exists_partialDiffeomorph_of_isInvertible_mixedHessian` in which a smooth
bump extension of the germ of `S` at `x` exists. -/
private theorem exists_partialDiffeomorph_of_isInvertible_mixedHessian_of_t2Space
    {W : Set (M × N)} (hW : IsOpen W) (hxW : x ∈ W)
    (hS : ContMDiffOn (I.prod J) 𝓘(ℝ) ∞ S W)
    (hx : (mixedHessian I J S x).IsInvertible) :
    ∃ Φ : PartialDiffeomorph (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (J.prod 𝓘(ℝ, F →L[ℝ] ℝ))
        (CotangentBundle I M) (CotangentBundle J N) ∞,
      ∃ β : CotangentBundle I M → M × N,
        generatingSource I S x ∈ Φ.source ∧
        β (generatingSource I S x) = x ∧
        ContMDiffOn (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (I.prod J) ∞ β Φ.source ∧
        (∀ z ∈ Φ.source, β z ∈ W ∧ generatingSource I S (β z) = z ∧
          Φ z = generatingTarget J S (β z)) ∧
        (∀ z ∈ Φ.source,
          mpullback (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) Φ
            (symplecticForm J N).val z = (symplecticForm I M).val z) ∧
        (∀ z ∈ Φ.source, (liouvilleForm I M).val z -
          mpullback (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) Φ
            (liouvilleForm J N).val z =
          mextDeriv (RoughForm.ofFunction (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (S ∘ β)) z) ∧
        (∀ γ : CotangentBundle I M → M × N,
          ContinuousAt γ (generatingSource I S x) → γ (generatingSource I S x) = x →
          (∀ᶠ z in 𝓝 (generatingSource I S x), generatingSource I S (γ z) = z) →
          γ =ᶠ[𝓝 (generatingSource I S x)] β) := by
  -- Extend only the germ at `x`, then shrink to a region where all differential data agree.
  obtain ⟨T, hT⟩ := hS.exists_contMDiffMap_eventuallyEq (hW.mem_nhds hxW)
  have hTx : (mixedHessian I J (T : M × N → ℝ) x).IsInvertible :=
    (hT.mixedHessian_eq (I := I) (J := J)).symm ▸ hx
  let β := generatingBranch T.contMDiff hTx
  let Ψ := generatedMap T.contMDiff hTx
  have hsrc : generatingSource I (T : M × N → ℝ) x = generatingSource I S x :=
    hT.generatingSource_eq
  obtain ⟨O, hOsub, hOo, hxO⟩ := mem_nhds_iff.mp (inter_mem (hW.mem_nhds hxW)
    hT.eventuallyEq_nhds)
  have hO : ∀ y ∈ O, y ∈ W ∧ (T : M × N → ℝ) =ᶠ[𝓝 y] S := hOsub
  -- Restrict the canonical transformation so its entire branch stays in the original domain.
  let A := Ψ.source ∩ β ⁻¹' O
  have hβc : ContinuousOn β Ψ.source :=
    β.contMDiffOn.continuousOn.mono (generatedMap_source_subset T.contMDiff hTx)
  have hAo : IsOpen A := hβc.isOpen_inter_preimage Ψ.open_source hOo
  let Φ := Ψ.restrOpen A hAo
  have hΦsource : Φ.source = Ψ.source ∩ A := Ψ.restrOpen_source hAo
  have hΦcoe : ⇑Φ = Ψ := Ψ.coe_restrOpen hAo
  have hΦ : Φ.source ⊆ Ψ.source := by rw [hΦsource]; exact inter_subset_left
  have hβO : ∀ z ∈ Φ.source, β z ∈ O := by
    rw [hΦsource]
    exact fun _ hz ↦ hz.2.2
  have hβx : β (generatingSource I S x) = x := by
    rw [← hsrc]
    exact generatingBranch_generatingSource T.contMDiff hTx
  have hxΦ : generatingSource I S x ∈ Φ.source := by
    have hxΨ : generatingSource I S x ∈ Ψ.source := hsrc ▸ mem_generatedMap_source T.contMDiff hTx
    rw [hΦsource]
    exact ⟨hxΨ, hxΨ, by simpa only [mem_preimage, hβx] using hxO⟩
  refine ⟨Φ, β, hxΦ, hβx, β.contMDiffOn.mono
    ((hΦ).trans (generatedMap_source_subset T.contMDiff hTx)), ?_, ?_, ?_, ?_⟩
  · intro z hz
    have heq := (hO _ (hβO z hz)).2
    rw [hΦcoe]
    exact ⟨(hO _ (hβO z hz)).1,
      (heq.generatingSource_eq (I := I)) ▸ generatingSource_generatingBranch T.contMDiff hTx
        (generatedMap_source_subset T.contMDiff hTx (hΦ hz)),
      (generatedMap_apply T.contMDiff hTx (hΦ hz)).trans (heq.generatingTarget_eq (J := J))⟩
  · intro z hz
    rw [hΦcoe]
    exact mpullback_generatedMap_symplecticForm T.contMDiff hTx (hΦ hz)
  · intro z hz
    -- The primitive is local too: differentiating along the branch removes the extension.
    have heq : ((T : M × N → ℝ) ∘ β) =ᶠ[𝓝 z] S ∘ β := by
      have hc := (β.contMDiffOn _ (generatedMap_source_subset T.contMDiff hTx (hΦ hz))).contMDiffAt
        (β.open_source.mem_nhds (generatedMap_source_subset T.contMDiff hTx (hΦ hz)))
      filter_upwards [hc.continuousAt.eventually (hOo.mem_nhds (hβO z hz))] with p hp
      exact (hO _ hp).2.self_of_nhds
    have hd : mextDeriv (RoughForm.ofFunction (I.prod 𝓘(ℝ, E →L[ℝ] ℝ))
        ((T : M × N → ℝ) ∘ β)) z =
        mextDeriv (RoughForm.ofFunction (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (S ∘ β)) z := by
      rw [mextDeriv_ofFunction, mextDeriv_ofFunction,
        heq.mvfderiv_eq (I := I.prod 𝓘(ℝ, E →L[ℝ] ℝ))]
    rw [hΦcoe, ← hd]
    exact liouvilleForm_sub_mpullback_generatedMap T.contMDiff hTx (hΦ hz)
  · intro γ hγ hγx hγsrc
    -- Any competing branch through `x` stays in the agreement region near the source point.
    have hnear : ∀ᶠ z in 𝓝 (generatingSource I S x), γ z ∈ O :=
      hγ.eventually (by rw [hγx]; exact hOo.mem_nhds hxO)
    rw [← hsrc]
    apply eventuallyEq_generatingBranch T.contMDiff hTx
    · rwa [hsrc]
    · rwa [hsrc]
    · rw [hsrc]
      filter_upwards [hnear, hγsrc] with z hz hzsrc
      exact ((hO _ hz).2.generatingSource_eq (I := I)).trans hzsrc

end T2

omit [FiniteDimensional ℝ E] [BoundarylessManifold I M] in
/-- A continuous local right inverse `γ` of the source projection of `S` through a point `y` of
`U × V`, for open sets `U ⊆ M` and `V ⊆ N`, is read over `U × V` as a continuous local right
inverse of the source projection of the restriction of `S` to `U × V`. So if the branch `β` of the
restriction is unique, `γ` agrees near the source point with every `b` corresponding to `β`. -/
private theorem eventuallyEq_of_comp_openInclusion {U : Opens M} {V : Opens N} (y : U × V)
    {β : CotangentBundle I U → U × V} {b : CotangentBundle I M → M × N}
    (huniq : ∀ γ₀ : CotangentBundle I U → U × V,
      ContinuousAt γ₀ (generatingSource I (S ∘ Prod.map Subtype.val Subtype.val) y) →
      γ₀ (generatingSource I (S ∘ Prod.map Subtype.val Subtype.val) y) = y →
      (∀ᶠ a in 𝓝 (generatingSource I (S ∘ Prod.map Subtype.val Subtype.val) y),
        generatingSource I (S ∘ Prod.map Subtype.val Subtype.val) (γ₀ a) = a) →
      γ₀ =ᶠ[𝓝 (generatingSource I (S ∘ Prod.map Subtype.val Subtype.val) y)] β)
    (hb : ∀ᶠ a in 𝓝 (generatingSource I (S ∘ Prod.map Subtype.val Subtype.val) y),
      b (openInclusion U a) = Prod.map Subtype.val Subtype.val (β a))
    {γ : CotangentBundle I M → M × N}
    (hγ : ContinuousAt γ (generatingSource I S (Prod.map Subtype.val Subtype.val y)))
    (hγy : γ (generatingSource I S (Prod.map Subtype.val Subtype.val y)) =
      Prod.map Subtype.val Subtype.val y)
    (hγsrc : ∀ᶠ z in 𝓝 (generatingSource I S (Prod.map Subtype.val Subtype.val y)),
      generatingSource I S (γ z) = z) :
    γ =ᶠ[𝓝 (generatingSource I S (Prod.map Subtype.val Subtype.val y))] b := by
  classical
  let ι := openInclusion (I := I) U
  have hιy : ι (generatingSource I (S ∘ Prod.map Subtype.val Subtype.val) y) =
      generatingSource I S (Prod.map Subtype.val Subtype.val y) :=
    openInclusion_generatingSource S y
  have hιc : Continuous ι := (contMDiff_openInclusion U).continuous
  have hγι := hγ.comp_of_eq hιc.continuousAt hιy
  -- Near the source point, `γ ∘ ι` takes values over `U × V`, where it lifts.
  have hmem : ∀ᶠ a in 𝓝 (generatingSource I (S ∘ Prod.map Subtype.val Subtype.val) y),
      γ (ι a) ∈ (U : Set M) ×ˢ (V : Set N) :=
    hγι.preimage_mem_nhds (by
      rw [Function.comp_apply, hιy, hγy]
      exact (U.isOpen.prod V.isOpen).mem_nhds ⟨y.1.property, y.2.property⟩)
  let γ₀ : CotangentBundle I U → U × V := fun a ↦
    if h : γ (ι a) ∈ (U : Set M) ×ˢ (V : Set N) then (⟨_, h.1⟩, ⟨_, h.2⟩) else y
  have hγ₀ : ∀ᶠ a in 𝓝 (generatingSource I (S ∘ Prod.map Subtype.val Subtype.val) y),
      Prod.map Subtype.val Subtype.val (γ₀ a) = γ (ι a) := by
    filter_upwards [hmem] with a ha
    simp only [γ₀, ha, ↓reduceDIte, Prod.map_apply]
  have hγ₀c : ContinuousAt γ₀ (generatingSource I (S ∘ Prod.map Subtype.val Subtype.val) y) := by
    rw [(Topology.IsInducing.subtypeVal.prodMap Topology.IsInducing.subtypeVal).continuousAt_iff]
    exact hγι.congr (hγ₀.mono fun _ h ↦ h.symm)
  have hγ₀y : γ₀ (generatingSource I (S ∘ Prod.map Subtype.val Subtype.val) y) = y := by
    have h := hγ₀.self_of_nhds
    rw [hιy, hγy] at h
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))
  -- The source projections correspond under the injective cotangent inclusion.
  have hγ₀src : ∀ᶠ a in 𝓝 (generatingSource I (S ∘ Prod.map Subtype.val Subtype.val) y),
      generatingSource I (S ∘ Prod.map Subtype.val Subtype.val) (γ₀ a) = a := by
    have h := hιc.continuousAt (x := generatingSource I (S ∘ Prod.map Subtype.val Subtype.val) y)
    rw [ContinuousAt, hιy] at h
    filter_upwards [hγ₀, h.eventually hγsrc] with a h₁ h₂
    apply (isOpenEmbedding_openInclusion (I := I) U).injective
    rw [openInclusion_generatingSource, h₁, h₂]
  have h : ∀ᶠ a in 𝓝 (generatingSource I (S ∘ Prod.map Subtype.val Subtype.val) y),
      γ (ι a) = b (ι a) := by
    filter_upwards [hγ₀, huniq γ₀ hγ₀c hγ₀y hγ₀src, hb] with a h₁ h₂ h₃
    rw [← h₁, h₂, h₃]
  rw [← hιy, ← (isOpenEmbedding_openInclusion (I := I) U).map_nhds_eq]
  exact eventually_map.2 h

/-- **Local generation on an open domain.** If `S` is smooth on an open `W` and its mixed Hessian
is invertible at `x ∈ W`, there is a partial canonical transformation `Φ` through the generated
covectors, together with a smooth local inverse `β` of the source projection taking values in `W`.
On its whole source `Φ` satisfies the generated relation, preserves the canonical two-form, and has
exact Liouville primitive `S ∘ β`: `λ - Φ^* λ = d(S ∘ β)`. The branch through `x` is unique as a
germ among continuous local right inverses of the source projection.

No Hausdorff hypothesis on `M` or `N` is needed: the construction takes place over the chart
domains at `x`, and its result is read in the ambient cotangent bundles. -/
theorem exists_partialDiffeomorph_of_isInvertible_mixedHessian
    {W : Set (M × N)} (hW : IsOpen W) (hxW : x ∈ W)
    (hS : ContMDiffOn (I.prod J) 𝓘(ℝ) ∞ S W)
    (hx : (mixedHessian I J S x).IsInvertible) :
    ∃ Φ : PartialDiffeomorph (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (J.prod 𝓘(ℝ, F →L[ℝ] ℝ))
        (CotangentBundle I M) (CotangentBundle J N) ∞,
      ∃ β : CotangentBundle I M → M × N,
        generatingSource I S x ∈ Φ.source ∧
        β (generatingSource I S x) = x ∧
        ContMDiffOn (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (I.prod J) ∞ β Φ.source ∧
        (∀ z ∈ Φ.source, β z ∈ W ∧ generatingSource I S (β z) = z ∧
          Φ z = generatingTarget J S (β z)) ∧
        (∀ z ∈ Φ.source,
          mpullback (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) Φ
            (symplecticForm J N).val z = (symplecticForm I M).val z) ∧
        (∀ z ∈ Φ.source, (liouvilleForm I M).val z -
          mpullback (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) Φ
            (liouvilleForm J N).val z =
          mextDeriv (RoughForm.ofFunction (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (S ∘ β)) z) ∧
        (∀ γ : CotangentBundle I M → M × N,
          ContinuousAt γ (generatingSource I S x) → γ (generatingSource I S x) = x →
          (∀ᶠ z in 𝓝 (generatingSource I S x), generatingSource I S (γ z) = z) →
          γ =ᶠ[𝓝 (generatingSource I S x)] β) := by
  -- Restrict `S` to a product of Hausdorff open neighbourhoods of the coordinates of `x`.
  have : T2Space H := I.isClosedEmbedding.isEmbedding.t2Space
  have : T2Space H' := J.isClosedEmbedding.isEmbedding.t2Space
  obtain ⟨U₀, hxU₀, _⟩ := ChartedSpace.exists_opens_mem_t2Space H x.1
  obtain ⟨V₀, hxV₀, _⟩ := ChartedSpace.exists_opens_mem_t2Space H' x.2
  let y : U₀ × V₀ := (⟨x.1, hxU₀⟩, ⟨x.2, hxV₀⟩)
  have : Nonempty U₀ := ⟨y.1⟩
  obtain ⟨Φ, β, hyΦ, hβy, -, hβ, hΦ, hprim, huniq⟩ :=
    exists_partialDiffeomorph_of_isInvertible_mixedHessian_of_t2Space
      (hW.preimage (continuous_subtypeVal.prodMap continuous_subtypeVal))
      ((mem_preimage (a := y)).2 hxW)
      (hS.comp (contMDiff_subtypeVal.prodMap contMDiff_subtypeVal).contMDiffOn
        (mapsTo_preimage _ _))
      (by rwa [mixedHessian_comp_prodMap_subtype_val])
  -- Read the resulting canonical transformation in the ambient cotangent bundles.
  obtain ⟨Ψ, hΨsrc, hΨ, hΨω⟩ := exists_partialDiffeomorph_openInclusion_eq Φ hΦ
  let ι := openInclusion (I := I) U₀
  let b : CotangentBundle I M → M × N := fun z ↦ (z.proj, (Ψ z).proj)
  have hιy : ι (generatingSource I (S ∘ Prod.map Subtype.val Subtype.val) y) =
      generatingSource I S x := openInclusion_generatingSource S y
  have hιΨ {a} (ha : a ∈ Φ.source) : ι a ∈ Ψ.source := hΨsrc ▸ mem_image_of_mem _ ha
  -- Over the chart domains, the ambient branch is the branch of the restriction.
  have hb {a} (ha : a ∈ Φ.source) : b (ι a) = Prod.map Subtype.val Subtype.val (β a) := by
    obtain ⟨-, hsrc, htgt⟩ := hβ a ha
    simp only [b, ι, hΨ a ha, proj_openInclusion,
      eq_proj_of_generatingSource_eq_of_generatingTarget_eq hsrc htgt.symm, Prod.map_apply']
  refine ⟨Ψ, b, hιy ▸ hιΨ hyΦ, by rw [← hιy, hb hyΦ, hβy]; rfl, ?_, fun z hz ↦ ?_, hΨω,
    fun z hz ↦ ?_, fun γ hγ hγx hγsrc ↦ ?_⟩
  · exact (contMDiff_proj _).contMDiffOn.prodMk
      ((contMDiff_proj _).comp_contMDiffOn Ψ.contMDiffOn)
  · rw [hΨsrc] at hz
    obtain ⟨a, ha, rfl⟩ := hz
    obtain ⟨hβW, hsrc, htgt⟩ := hβ a ha
    rw [hb ha]
    exact ⟨hβW, by rw [← openInclusion_generatingSource, hsrc],
      by rw [hΨ a ha, htgt, openInclusion_generatingTarget]⟩
  · -- The primitive transfers through the cotangent inclusions.
    rw [hΨsrc] at hz
    obtain ⟨a, ha, rfl⟩ := hz
    have hΨd := Ψ.mdifferentiableAt (by simp) (hιΨ ha)
    have hbW : b (ι a) ∈ W := by rw [hb ha]; exact (hβ a ha).1
    refine liouvilleForm_sub_mpullback_apply_openInclusion (Φ.mdifferentiableAt (by simp) ha) hΨd
      (eventually_of_mem (Φ.open_source.mem_nhds ha) fun a' ha' ↦ hΨ a' ha')
      (((hS.contMDiffAt (hW.mem_nhds hbW)).mdifferentiableAt (by simp)).comp _
        (((contMDiff_proj _).mdifferentiableAt one_ne_zero).prodMk
          (((contMDiff_proj _).mdifferentiableAt one_ne_zero).comp _ hΨd)))
      (eventually_of_mem (Φ.open_source.mem_nhds ha) fun a' ha' ↦ congrArg S (hb ha'))
      (hprim a ha)
  · -- Uniqueness: read a competing branch over the chart domains, where the branch is unique.
    exact eventuallyEq_of_comp_openInclusion y huniq
      (eventually_of_mem (Φ.open_source.mem_nhds hyΦ) fun a ha ↦ hb ha) hγ hγx hγsrc

/-- **Generating functions give symplectomorphisms between open sets.** Let `S` be smooth on an
open set `W ⊆ M × N` whose mixed Hessian `d_Q (d_q S)` is invertible at `x ∈ W`. Then there are
open sets `U ⊆ T*M` and `V ⊆ T*N` and a diffeomorphism `φ : U → V` pulling the canonical
symplectic form of `T*N`, restricted to `V`, back to that of `T*M`, restricted to `U`. It sends
`(q₀, d_q S (x))` to `(Q₀, -d_Q S (x))`, and every `z = (q, p) ∈ U` with `φ z = (Q, P)` satisfies
`(q, Q) ∈ W`, `p = d_q S (q, Q)` and `P = -d_Q S (q, Q)`. The symplectomorphism is exact: with the
branch `b (z) = (q, Q)`, the Liouville forms satisfy `λ_M - φ^* λ_N = d(S ∘ b)` on `U`.

No Hausdorff hypothesis on `M` or `N` is needed: the construction takes place over the chart
domains at `x`. By `TauCeti.CotangentBundle.eventually_apply_eq_of_isInvertible_mixedHessian`, any
two such maps agree near `(q₀, d_q S (x))`. -/
theorem exists_diffeomorph_opens_of_isInvertible_mixedHessian
    {W : Set (M × N)} (hW : IsOpen W) (hxW : x ∈ W)
    (hS : ContMDiffOn (I.prod J) 𝓘(ℝ) ∞ S W)
    (hx : (mixedHessian I J S x).IsInvertible) :
    ∃ (U : Opens (CotangentBundle I M)) (V : Opens (CotangentBundle J N))
      (φ : U ≃ₘ⟮I.prod 𝓘(ℝ, E →L[ℝ] ℝ), J.prod 𝓘(ℝ, F →L[ℝ] ℝ)⟯ V),
      (∃ h : generatingSource I S x ∈ U,
        (φ ⟨_, h⟩ : CotangentBundle J N) = generatingTarget J S x) ∧
      (∀ z : U, ((z : CotangentBundle I M).proj, (φ z : CotangentBundle J N).proj) ∈ W ∧
        generatingSource I S ((z : CotangentBundle I M).proj, (φ z : CotangentBundle J N).proj) =
          z ∧
        generatingTarget J S ((z : CotangentBundle I M).proj, (φ z : CotangentBundle J N).proj) =
          φ z) ∧
      SmoothForm.mpullback φ φ.contMDiff
          (SmoothForm.mpullback (Subtype.val : V → CotangentBundle J N) contMDiff_subtypeVal
            (symplecticForm J N)) =
        SmoothForm.mpullback (Subtype.val : U → CotangentBundle I M) contMDiff_subtypeVal
          (symplecticForm I M) ∧
      ∀ z : U, (SmoothForm.mpullback (Subtype.val : U → CotangentBundle I M) contMDiff_subtypeVal
          (liouvilleForm I M)).val z -
        (SmoothForm.mpullback φ φ.contMDiff
          (SmoothForm.mpullback (Subtype.val : V → CotangentBundle J N) contMDiff_subtypeVal
            (liouvilleForm J N))).val z =
        mextDeriv (RoughForm.ofFunction (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) fun z : U ↦
          S ((z : CotangentBundle I M).proj, (φ z : CotangentBundle J N).proj)) z := by
  obtain ⟨Ψ, β, hx₀, hβx, hβs, hβ, hΨω, hprim, -⟩ :=
    exists_partialDiffeomorph_of_isInvertible_mixedHessian hW hxW hS hx
  -- On the source of `Ψ`, the branch is read off from the base points.
  have hβeq {z} (hz : z ∈ Ψ.source) : β z = (z.proj, (Ψ z).proj) :=
    eq_proj_of_generatingSource_eq_of_generatingTarget_eq (hβ z hz).2.1 (hβ z hz).2.2.symm
  refine ⟨⟨Ψ.source, Ψ.open_source⟩, ⟨Ψ.target, Ψ.open_target⟩, Ψ.toDiffeomorphSourceTarget,
    ⟨hx₀, (Ψ.toDiffeomorphSourceTarget_apply_coe _).trans ?_⟩, fun z ↦ ?_, ?_, fun z ↦ ?_⟩
  · rw [(hβ _ hx₀).2.2, hβx]
  · obtain ⟨hW', hsrc, htgt⟩ := hβ z z.property
    rw [Ψ.toDiffeomorphSourceTarget_apply_coe, ← hβeq z.property]
    exact ⟨hW', hsrc, htgt.symm⟩
  -- The forms: through the inclusions, `φ` is `Ψ`, which preserves the canonical forms.
  · apply Subtype.ext
    funext z
    simp only [SmoothForm.coe_mpullback]
    rw [mpullback_toDiffeomorphSourceTarget_apply Ψ (by simp), mpullback_subtype_val_apply]
    exact hΨω z z.property
  · have hβd : MDifferentiableAt (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 𝓘(ℝ) (S ∘ β) z :=
      ((hS.contMDiffAt (hW.mem_nhds (hβ z z.property).1)).mdifferentiableAt (by simp)).comp _
        ((hβs z z.property).contMDiffAt
          (Ψ.open_source.mem_nhds z.property) |>.mdifferentiableAt (by simp))
    have hfun : (S ∘ β) ∘ (Subtype.val : (⟨Ψ.source, Ψ.open_source⟩ : Opens _) → _) =
        fun z : (⟨Ψ.source, Ψ.open_source⟩ : Opens (CotangentBundle I M)) ↦
          S ((z : CotangentBundle I M).proj,
            (Ψ.toDiffeomorphSourceTarget z : CotangentBundle J N).proj) :=
      funext fun z ↦ by
        rw [Function.comp_apply, Function.comp_apply, hβeq z.property,
          Ψ.toDiffeomorphSourceTarget_apply_coe]
    simp only [SmoothForm.coe_mpullback]
    rw [mpullback_toDiffeomorphSourceTarget_apply Ψ (by simp), mpullback_subtype_val_apply, ← hfun,
      ← mpullback_mextDeriv_ofFunction_apply (contMDiff_subtypeVal.mdifferentiableAt one_ne_zero)
        hβd,
      mpullback_subtype_val_apply]
    exact hprim z z.property

/-- **Uniqueness of the symplectomorphism generated by `S`.** Let `S` be smooth on an open set
`W ⊆ M × N` whose mixed Hessian is invertible at `x ∈ W`. Any two maps `φ₁`, `φ₂` defined on open
sets of `T*M`, continuous at `(q₀, d_q S (x))` and sending it to `(Q₀, -d_Q S (x))`, and satisfying
the generated relation `p = d_q S (q, Q)`, `P = -d_Q S (q, Q)` for `φᵢ (q, p) = (Q, P)`, agree on a
neighbourhood of `(q₀, d_q S (x))`. In particular this applies to the symplectomorphisms of
`TauCeti.CotangentBundle.exists_diffeomorph_opens_of_isInvertible_mixedHessian`. -/
theorem eventually_apply_eq_of_isInvertible_mixedHessian
    {W : Set (M × N)} (hW : IsOpen W) (hxW : x ∈ W)
    (hS : ContMDiffOn (I.prod J) 𝓘(ℝ) ∞ S W)
    (hx : (mixedHessian I J S x).IsInvertible)
    {U₁ U₂ : Opens (CotangentBundle I M)}
    {φ₁ : U₁ → CotangentBundle J N} {φ₂ : U₂ → CotangentBundle J N}
    (h₁ : generatingSource I S x ∈ U₁) (h₂ : generatingSource I S x ∈ U₂)
    (hφ₁ : ContinuousAt φ₁ ⟨_, h₁⟩) (hφ₂ : ContinuousAt φ₂ ⟨_, h₂⟩)
    (hφ₁x : φ₁ ⟨_, h₁⟩ = generatingTarget J S x) (hφ₂x : φ₂ ⟨_, h₂⟩ = generatingTarget J S x)
    (hrel₁ : ∀ z : U₁,
      generatingSource I S ((z : CotangentBundle I M).proj, (φ₁ z).proj) = z ∧
        generatingTarget J S ((z : CotangentBundle I M).proj, (φ₁ z).proj) = φ₁ z)
    (hrel₂ : ∀ z : U₂,
      generatingSource I S ((z : CotangentBundle I M).proj, (φ₂ z).proj) = z ∧
        generatingTarget J S ((z : CotangentBundle I M).proj, (φ₂ z).proj) = φ₂ z) :
    ∀ᶠ z in 𝓝 (generatingSource I S x),
      ∀ (hz₁ : z ∈ U₁) (hz₂ : z ∈ U₂), φ₁ ⟨z, hz₁⟩ = φ₂ ⟨z, hz₂⟩ := by
  obtain ⟨-, β, -, -, -, -, -, -, huniq⟩ :=
    exists_partialDiffeomorph_of_isInvertible_mixedHessian hW hxW hS hx
  -- Each map determines a continuous local right inverse of the source projection.
  have key (U : Opens (CotangentBundle I M)) (φ : U → CotangentBundle J N)
      (h : generatingSource I S x ∈ U) (hφ : ContinuousAt φ ⟨_, h⟩)
      (hφx : φ ⟨_, h⟩ = generatingTarget J S x)
      (hrel : ∀ z : U,
        generatingSource I S ((z : CotangentBundle I M).proj, (φ z).proj) = z) :
      ∀ᶠ z in 𝓝 (generatingSource I S x),
        ∀ hz : z ∈ U, (z.proj, (φ ⟨z, hz⟩).proj) = β z := by
    classical
    let γ : CotangentBundle I M → M × N := fun z ↦
      if hz : z ∈ U then (z.proj, (φ ⟨z, hz⟩).proj) else x
    have hγU (z) (hz : z ∈ U) : γ z = (z.proj, (φ ⟨z, hz⟩).proj) :=
      dite_eq_left_of_eq_true (eq_true hz)
    have hU : (U : Set (CotangentBundle I M)) ∈ 𝓝 (generatingSource I S x) := U.isOpen.mem_nhds h
    have hγ : ContinuousAt γ (generatingSource I S x) := by
      refine ((continuousWithinAt_iff_continuousAt_domRestrict _ h).2 ?_).continuousAt hU
      have hc : ContinuousAt (fun z : U ↦ ((z : CotangentBundle I M).proj, (φ z).proj)) ⟨_, h⟩ :=
        ((FiberBundle.continuous_proj _ _).comp continuous_subtypeVal).continuousAt.prodMk
          ((FiberBundle.continuous_proj _ _).continuousAt.comp hφ)
      convert hc using 1
      funext z
      exact hγU z z.property
    have hγx : γ (generatingSource I S x) = x := by
      rw [hγU _ h]
      exact (eq_proj_of_generatingSource_eq_of_generatingTarget_eq rfl hφx.symm).symm
    have hγsrc : ∀ᶠ z in 𝓝 (generatingSource I S x), generatingSource I S (γ z) = z := by
      filter_upwards [hU] with z hz
      rw [hγU z hz]
      exact hrel ⟨z, hz⟩
    filter_upwards [huniq γ hγ hγx hγsrc] with z hz hzU
    rw [← hz, hγU z hzU]
  filter_upwards [key U₁ φ₁ h₁ hφ₁ hφ₁x fun z ↦ (hrel₁ z).1,
    key U₂ φ₂ h₂ hφ₂ hφ₂x fun z ↦ (hrel₂ z).1] with z k₁ k₂ hz₁ hz₂
  rw [← (hrel₁ ⟨z, hz₁⟩).2, ← (hrel₂ ⟨z, hz₂⟩).2]
  exact congrArg (generatingTarget J S) ((k₁ hz₁).trans (k₂ hz₂).symm)

end TauCeti.CotangentBundle
