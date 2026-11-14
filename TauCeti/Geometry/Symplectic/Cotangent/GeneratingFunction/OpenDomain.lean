/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.GeneratingFunction.GeneratedMap
import TauCeti.Geometry.Manifold.ContMDiffMap.Extension

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
no regularity outside the given open domain is needed.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Section 4.2.
* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, second edition, Section 48.
-/

public section

noncomputable section

open Bundle Filter Manifold Set
open scoped Manifold ContDiff Topology

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F H' : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {S : M × N → ℝ} {x : M × N}

namespace TauCeti.CotangentBundle

variable [IsManifold I ∞ M] [IsManifold J ∞ N]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [BoundarylessManifold I M] [BoundarylessManifold J N] [T2Space M] [T2Space N]

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
            (symplecticForm J N).1 z = (symplecticForm I M).1 z) ∧
        (∀ z ∈ Φ.source, (liouvilleForm I M).1 z -
          mpullback (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) Φ
            (liouvilleForm J N).1 z =
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

end TauCeti.CotangentBundle
