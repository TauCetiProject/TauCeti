/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Opens
public import TauCeti.Geometry.Symplectic.Cotangent.GeneratingFunction.GeneratedMap
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
transformation, its smooth branch, the two covector identities, and the exact Liouville primitive.
The branch is unique among continuous local right inverses through the specified point.
The construction uses the globally smooth generated-map API and a smooth bump extension;
no regularity outside the given open domain is needed. The bump extension needs Hausdorff base
manifolds.

The generated relation is local in the base as well: restricting `S` to a product `U × V` of open
subsets does not change its mixed Hessian (`TauCeti.mixedHessian_comp_prodMap_subtype_val`), and
the cotangent inclusions `T*U → T*M`, `T*V → T*N` carry the source and target projections of the
restriction to those of `S` (`TauCeti.CotangentBundle.openInclusion_generatingSource`,
`TauCeti.CotangentBundle.openInclusion_generatingTarget`). Chart domains are Hausdorff, so applying
the construction over the chart domains at the base point and reading the result in the ambient
cotangent bundles (`TauCeti.CotangentBundle.exists_partialDiffeomorph_openInclusion_eq`) removes
the Hausdorff hypothesis.
`TauCeti.CotangentBundle.exists_diffeomorph_opens_of_isInvertible_mixedHessian` states the result
as a diffeomorphism `φ : U → V` between open sets `U ⊆ T*M` and `V ⊆ T*N` which pulls the
canonical symplectic form of `T*N`, restricted to `V`, back to that of `T*M`, restricted to `U`.
It sends `(q₀, d_q S (x))` to `(Q₀, -d_Q S (x))`, and its graph lies in the relation
`p = d_q S (q, Q)`, `P = -d_Q S (q, Q)` with `(q, Q)` in the domain of `S`.

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

/-- **Local generation on an open domain.** If `S` is smooth on an open `W` and its mixed Hessian
is invertible at `x ∈ W`, there is a partial canonical transformation through the generated
covectors, together with a smooth local inverse of the source projection taking values in `W`.
On its whole source the transformation satisfies the generated relation, preserves the canonical
two-form, and has exact Liouville primitive `S ∘ β`. The branch through `x` is unique as a germ.
-/
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

/-- **Generating functions give symplectomorphisms between open sets.** Let `S` be smooth on an
open set `W ⊆ M × N` whose mixed Hessian `d_Q (d_q S)` is invertible at `x ∈ W`. Then there are
open sets `U ⊆ T*M` and `V ⊆ T*N` and a diffeomorphism `φ : U → V` pulling the canonical
symplectic form of `T*N`, restricted to `V`, back to that of `T*M`, restricted to `U`. It sends
`(q₀, d_q S (x))` to `(Q₀, -d_Q S (x))`, and every `z = (q, p) ∈ U` with `φ z = (Q, P)` satisfies
`(q, Q) ∈ W`, `p = d_q S (q, Q)` and `P = -d_Q S (q, Q)`.

No Hausdorff hypothesis on `M` or `N` is needed: the construction takes place over the chart
domains at `x`. -/
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
          (symplecticForm I M) := by
  -- Restrict `S` to the product of the chart domains at `x`, which are Hausdorff.
  let U₀ : Opens M := ⟨(chartAt H x.1).source, (chartAt H x.1).open_source⟩
  let V₀ : Opens N := ⟨(chartAt H' x.2).source, (chartAt H' x.2).open_source⟩
  have : T2Space H := I.isClosedEmbedding.isEmbedding.t2Space
  have : T2Space H' := J.isClosedEmbedding.isEmbedding.t2Space
  have : T2Space U₀ := (chartAt H x.1).toHomeomorphSourceTarget.isEmbedding.t2Space
  have : T2Space V₀ := (chartAt H' x.2).toHomeomorphSourceTarget.isEmbedding.t2Space
  let y : U₀ × V₀ := (⟨x.1, mem_chart_source H x.1⟩, ⟨x.2, mem_chart_source H' x.2⟩)
  have : Nonempty U₀ := ⟨y.1⟩
  obtain ⟨Φ, β, hyΦ, hβy, -, hβ, hΦ, -, -⟩ := exists_partialDiffeomorph_of_isInvertible_mixedHessian
    (hW.preimage (continuous_subtypeVal.prodMap continuous_subtypeVal))
    ((mem_preimage (a := y)).2 hxW)
    (hS.comp (contMDiff_subtypeVal.prodMap contMDiff_subtypeVal).contMDiffOn
      (mapsTo_preimage _ _))
    (by rwa [mixedHessian_comp_prodMap_subtype_val])
  -- Read the resulting canonical transformation in the ambient cotangent bundles.
  obtain ⟨Ψ, hΨsrc, hΨ, hΨω⟩ := exists_partialDiffeomorph_openInclusion_eq Φ hΦ
  have hrel (z) (hz : z ∈ Ψ.source) :
      ∃ w ∈ W, generatingSource I S w = z ∧ generatingTarget J S w = Ψ z := by
    rw [hΨsrc] at hz
    obtain ⟨z, hz, rfl⟩ := hz
    obtain ⟨hβW, hsrc, htgt⟩ := hβ z hz
    exact ⟨_, hβW, by rw [← openInclusion_generatingSource, hsrc],
      by rw [hΨ z hz, htgt, openInclusion_generatingTarget]⟩
  have hy : Prod.map Subtype.val Subtype.val y = x := rfl
  have hx₀ : generatingSource I S x ∈ Ψ.source := by
    rw [hΨsrc, ← hy]
    exact ⟨_, hyΦ, openInclusion_generatingSource S y⟩
  have hΨx : Ψ (generatingSource I S x) = generatingTarget J S x := by
    rw [← hy, ← openInclusion_generatingSource S y, hΨ _ hyΦ, (hβ _ hyΦ).2.2, hβy,
      openInclusion_generatingTarget]
  refine ⟨⟨Ψ.source, Ψ.open_source⟩, ⟨Ψ.target, Ψ.open_target⟩, Ψ.toDiffeomorphSourceTarget,
    ⟨hx₀, (Ψ.toDiffeomorphSourceTarget_apply_coe _).trans hΨx⟩, fun z ↦ ?_, ?_⟩
  · obtain ⟨w, hwW, hws, hwt⟩ := hrel z z.property
    rw [Ψ.toDiffeomorphSourceTarget_apply_coe, ← hwt, ← hws, proj_generatingSource,
      proj_generatingTarget]
    exact ⟨hwW, rfl, rfl⟩
  -- The forms: through the inclusions, `φ` is `Ψ`, which preserves the canonical forms.
  apply Subtype.ext
  funext z
  simp only [SmoothForm.coe_mpullback]
  rw [mpullback_toDiffeomorphSourceTarget_apply Ψ (by simp), mpullback_subtype_val_apply]
  exact hΨω z z.property

end TauCeti.CotangentBundle
