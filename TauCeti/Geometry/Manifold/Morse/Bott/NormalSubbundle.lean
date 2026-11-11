/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.Splitting
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Subbundle
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import TauCeti.Geometry.Manifold.Morse.Bott.Index
import TauCeti.Geometry.Manifold.Morse.Bott.NegativeNormal
import TauCeti.Geometry.Manifold.VectorBundle.Hom
import TauCeti.LinearAlgebra.Projection
import TauCeti.Topology.VectorBundle.Hom
import TauCeti.Topology.VectorBundle.Trivialization

/-!
# The negative and positive normal bundles of a Morse–Bott submanifold

Let `i : S → M` be a nondegenerate critical submanifold of a function `f` on a boundaryless
manifold, and let `g` be a `C^k` fibre metric on its normal bundle `ν`. At each point `s` the
normal space splits into the negative normal space `ν⁻ s`, spanned by the normal vectors `v` with
`Hess v = μ g v` for some `μ < 0`, and the positive normal space `ν⁺ s`, defined with `μ > 0`
(`TauCeti.SmoothEmbedding.IsCriticalSubmanifold.negativeNormalSpace` and
`TauCeti.SmoothEmbedding.IsCriticalSubmanifold.positiveNormalSpace`). Their dimensions are the
Morse indices of `f` and of `-f` at `i s`.

This file shows that, when `f` is `C^{k+2}` along `S`, the embedding is `C^{k+1}` and these
indices are constant, the spaces `ν⁻ s` and `ν⁺ s` have `C^k` local frames near every point of `S`
(`IsNondegenerateCriticalSubmanifold.hasLocalContMDiffSubbundleFrames_negativeNormalSpace` and
`IsNondegenerateCriticalSubmanifold.hasLocalContMDiffSubbundleFrames_positiveNormalSpace`, in the
namespace `TauCeti.SmoothEmbedding`). By the smooth local frame criterion
`TauCeti.HasLocalContMDiffSubbundleFrames.contMDiffVectorBundle` they are therefore `C^k`
subbundles of the normal bundle, the **negative and positive normal bundles** `ν⁻` and `ν⁺`; the
rank of `ν⁻` is the index of the submanifold. The indices are locally constant along a Morse–Bott
submanifold, so on a connected one the hypothesis holds automatically (the `_of_preconnectedSpace`
versions). The negative normal bundle is the bundle whose disc bundle is attached when the
critical level of the submanifold is crossed.

The subbundles depend on the metric `g`, but their ranks do not. No eigenbasis of the normal
Hessian is chosen. In the preferred normal-bundle trivialization at `s₀`, with fibre model `P`, the
metric becomes a `C^k` family `G` of bilinear forms on `P`
(`Bundle.Trivialization.contMDiffOn_compl₁₂_symmₗ`). The projections onto the negative relative
spectral subspaces of the normal Hessian with respect to `G`, along the positive ones, are then a
`C^k` family of operators on `P` whose ranges and kernels read the negative and positive normal
spaces in the trivialization
(`IsNondegenerateCriticalSubmanifold.exists_contMDiffOn_negativeNormalProjection`), and a `C^k`
family of operators of constant rank has `C^k` local frames of its ranges
(`Bundle.Trivialization.exists_isSubbundleFrameOn_map_symmₗ`).

Up to isomorphism, the splitting does not depend on the metric. For two fibre metrics `g₀` and
`g₁`, write `π₀` and `π₁` for the projections onto their negative normal spaces along their
positive ones. The normal Hessian is negative definite on the negative normal space of either
metric and positive definite on the positive normal space of the other, so these meet only in `0`
(`IsCriticalSubmanifold.disjoint_negativeNormalSpace_positiveNormalSpace'`). Hence the operator
`π₁ π₀ + (1 - π₁) (1 - π₀)` is injective
(`LinearMap.IsIdempotentElem.injective_mul_add_one_sub_mul_one_sub`); it carries the negative and
positive normal spaces of `g₀` onto those of `g₁`, and in a trivialization it is the same
expression in the continuous families of projections of the fibre model, so it depends
continuously on the base point. The result is a homeomorphism of the total space of the normal
bundle, linear on the fibres, carrying the splitting for `g₀` onto the splitting for `g₁`
(`exists_homeomorph_totalSpace_map_negativeNormalSpace_eq_and_map_positiveNormalSpace_eq`, in the
namespace `TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold`).
It restricts to isomorphisms between the negative normal bundles of the two metrics, and between
their positive normal bundles
(`IsNondegenerateCriticalSubmanifold.exists_homeomorph_totalSpace_negativeNormalSpace` and
`IsNondegenerateCriticalSubmanifold.exists_homeomorph_totalSpace_positiveNormalSpace`). So the
negative normal bundle, whose disc bundle is attached at the critical level, is determined by `f`
up to isomorphism, although its fibres depend on the metric.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* A. Banyaga and D. E. Hurtubise, *Lectures on Morse Homology*, Kluwer, 2004, Section 3.5.
-/

public section

open Bundle Function Set Module
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' S : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S]
  {f : M → ℝ} {n : ℕ∞ω} {i : SmoothEmbedding J I n S M} (hn : n ≠ 0)
  [I.Boundaryless] [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
  {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {k : ℕ∞ω} [IsManifold I (k + 2) M] [IsManifold J (k + 1) S]

/-- In the preferred normal-bundle trivialization at `s₀`, the negative and positive normal
spaces relative to a `C^k` fibre metric are the images of the range and of the kernel of a `C^k`
family of projections of the fibre model. -/
private theorem exists_contMDiffOn_negativeNormalSpace_eq_map
    (h : i.IsNondegenerateCriticalSubmanifold f) (hk : k + 1 ≤ n)
    (hf : ∀ s, ContMDiffAt I 𝓘(ℝ) (k + 2) f (i s))
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g : haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
      haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
      letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J k P fun s ↦ i.NormalSpace s hn) (s₀ : S) :
    haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
    haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
    haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    let e := trivializationAt P (fun s ↦ i.NormalSpace s hn) s₀
    ∃ p : S → P →L[ℝ] P, ContMDiffOn J 𝓘(ℝ, P →L[ℝ] P) k p e.baseSet ∧
      ∀ s ∈ e.baseSet, IsIdempotentElem (p s) ∧
        h.negativeNormalSpace hn g.toRiemannianMetric s = (p s).range.map (e.symmₗ ℝ s) ∧
        h.positiveNormalSpace hn g.toRiemannianMetric s = (p s).ker.map (e.symmₗ ℝ s) ∧
        finrank ℝ (p s).range = manifoldMorseIndex I f (i s) ∧
        finrank ℝ (p s).ker = manifoldMorseIndex I (-f) (i s) := by
  have : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
  have : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
  have : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  have : IsManifold I (k + 1) M := .of_le (n := k + 2) (by gcongr; exact one_le_two)
  let := i.normalSpaceContMDiffVectorBundle hn hk hdim
  set e := trivializationAt P (fun s ↦ i.NormalSpace s hn) s₀
  -- The metric read in the trivialization.
  set G : S → P →L[ℝ] P →L[ℝ] ℝ := fun s ↦
    ((g.inner s).toLinearMap₁₂.compl₁₂ (e.symmₗ ℝ s) (e.symmₗ ℝ s)).toContinuousBilinearMap
  have hG : ContMDiffOn J 𝓘(ℝ, P →L[ℝ] P →L[ℝ] ℝ) k G e.baseSet :=
    e.contMDiffOn_compl₁₂_symmₗ g.contMDiff.contMDiffOn
  obtain ⟨p, hp, hps⟩ := h.exists_contMDiffOn_negativeNormalProjection hn (le_self_add.trans hk)
    hf hdim s₀ hG (fun s _ u v ↦ by simpa [G] using g.symm s _ _) fun s hs u hu ↦ by
      simpa [G] using g.pos s _ ((map_ne_zero_iff _ (e.symmₗ_injective ℝ hs)).mpr hu)
  -- The normal-bundle trivialization at `s₀` is the bundle chart `e` at `s₀`.
  simp only [← normalSpaceFiberBundle_trivializationAt] at hp hps
  refine ⟨p, hp.mono fun s hs ↦ ⟨hs, hs⟩, fun s hs ↦ ?_⟩
  obtain ⟨hidem, hrange, hker, -, -, -, -, hrank, hnull⟩ := hps s ⟨hs, hs⟩
  -- Pulled back along the inverse trivialization, the metric is `G s`.
  set L := (e.linearEquivAt ℝ s hs).symm
  have hgL : (g.toRiemannianMetric.inner s).toBilinForm.compl₁₂ (L : P →ₗ[ℝ] i.NormalSpace s hn)
      (L : P →ₗ[ℝ] i.NormalSpace s hn) = (G s).toBilinForm := by
    ext u v
    simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, L,
      Trivialization.linearEquivAt_symm_apply, ContinuousLinearMap.toBilinForm_apply, G,
      LinearMap.toContinuousBilinearMap_apply, ContinuousLinearMap.toLinearMap₁₂_apply,
      e.symmₗ_apply hs]
    -- The underlying metric of `g` has the inner products of `g`, by definition.
    rfl
  have hL : (L : P →ₗ[ℝ] i.NormalSpace s hn) = e.symmₗ ℝ s := e.coe_linearEquivAt_symm ℝ hs
  refine ⟨hidem, ?_, ?_, hrank, hnull⟩
  · rw [IsCriticalSubmanifold.negativeNormalSpace_def, ← hL,
      ← LinearMap.BilinForm.map_relativeSpectralSubspace_compl₁₂ L, hgL, hL, hrange]
  · rw [IsCriticalSubmanifold.positiveNormalSpace_def, ← hL,
      ← LinearMap.BilinForm.map_relativeSpectralSubspace_compl₁₂ L, hgL, hL, hker]

/-- **The negative normal bundle of a Morse–Bott submanifold.** Let `i` be a nondegenerate
critical submanifold of `f`, with `f` of class `C^{k+2}` along it and `i` of class `C^{k+1}`, and
let `g` be a `C^k` fibre metric on the normal bundle, with fibre model `P`. If the Morse index of
`f` is `r` at every point of the submanifold, then the negative normal spaces relative to `g` have
`C^k` local frames of size `r` near every point: with the subspace topology they form a `C^k`
subbundle of rank `r` of the normal bundle
(`TauCeti.HasLocalContMDiffSubbundleFrames.contMDiffVectorBundle`). -/
theorem hasLocalContMDiffSubbundleFrames_negativeNormalSpace
    (h : i.IsNondegenerateCriticalSubmanifold f) (hk : k + 1 ≤ n)
    (hf : ∀ s, ContMDiffAt I 𝓘(ℝ) (k + 2) f (i s))
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g : haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
      haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
      letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J k P fun s ↦ i.NormalSpace s hn) {r : ℕ}
    (hr : ∀ s, manifoldMorseIndex I f (i s) = r) :
    haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
    haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
    haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    HasLocalContMDiffSubbundleFrames J k P (Fin r)
      (h.negativeNormalSpace hn g.toRiemannianMetric) := by
  have : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
  have : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
  have : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  have : IsManifold I (k + 1) M := .of_le (n := k + 2) (by gcongr; exact one_le_two)
  let := i.normalSpaceContMDiffVectorBundle hn hk hdim
  refine hasLocalContMDiffSubbundleFrames_iff.mpr fun s₀ ↦ ?_
  obtain ⟨p, hp, hps⟩ := exists_contMDiffOn_negativeNormalSpace_eq_map hn h hk hf hdim g s₀
  obtain ⟨U, hUe, hU, hs₀U, X, hX, hXk⟩ :=
    (trivializationAt P (fun s ↦ i.NormalSpace s hn) s₀).exists_isSubbundleFrameOn_map_symmₗ
      (trivializationAt P (fun s ↦ i.NormalSpace s hn) s₀).open_baseSet subset_rfl hp
      (fun s hs ↦ (hps s hs).2.2.2.1.trans (hr s))
      (mem_baseSet_trivializationAt P (fun s ↦ i.NormalSpace s hn) s₀)
  exact ⟨U, hU, hs₀U, X, ⟨hX.continuousOn, hX.linearIndependent,
    fun hy ↦ (hX.span_eq hy).trans (hps _ (hUe hy)).2.1.symm⟩, hXk⟩

/-- **The positive normal bundle of a Morse–Bott submanifold.** Let `i` be a nondegenerate
critical submanifold of `f`, with `f` of class `C^{k+2}` along it and `i` of class `C^{k+1}`, and
let `g` be a `C^k` fibre metric on the normal bundle, with fibre model `P`. If the Morse index of
`-f` is `r` at every point of the submanifold, then the positive normal spaces relative to `g`
have `C^k` local frames of size `r` near every point: with the subspace topology they form a `C^k`
subbundle of rank `r` of the normal bundle
(`TauCeti.HasLocalContMDiffSubbundleFrames.contMDiffVectorBundle`). -/
theorem hasLocalContMDiffSubbundleFrames_positiveNormalSpace
    (h : i.IsNondegenerateCriticalSubmanifold f) (hk : k + 1 ≤ n)
    (hf : ∀ s, ContMDiffAt I 𝓘(ℝ) (k + 2) f (i s))
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g : haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
      haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
      letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J k P fun s ↦ i.NormalSpace s hn) {r : ℕ}
    (hr : ∀ s, manifoldMorseIndex I (-f) (i s) = r) :
    haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
    haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
    haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    HasLocalContMDiffSubbundleFrames J k P (Fin r)
      (h.positiveNormalSpace hn g.toRiemannianMetric) := by
  have : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
  have : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
  have : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  have : IsManifold I (k + 1) M := .of_le (n := k + 2) (by gcongr; exact one_le_two)
  let := i.normalSpaceContMDiffVectorBundle hn hk hdim
  refine hasLocalContMDiffSubbundleFrames_iff.mpr fun s₀ ↦ ?_
  obtain ⟨p, hp, hps⟩ := exists_contMDiffOn_negativeNormalSpace_eq_map hn h hk hf hdim g s₀
  -- The kernel of a projection `p` is the range of the complementary projection `1 - p`.
  have hker (s : S) (hs : s ∈ (trivializationAt P (fun s ↦ i.NormalSpace s hn) s₀).baseSet) :
      (1 - p s).range = (p s).ker := by
    have hP : IsIdempotentElem (p s : P →ₗ[ℝ] P) := congr(($((hps s hs).1) : P →ₗ[ℝ] P))
    rw [LinearMap.IsIdempotentElem.ker_eq_range_one_sub hP,
      ContinuousLinearMap.toLinearMap_sub, ContinuousLinearMap.toLinearMap_one]
  obtain ⟨U, hUe, hU, hs₀U, X, hX, hXk⟩ :=
    (trivializationAt P (fun s ↦ i.NormalSpace s hn) s₀).exists_isSubbundleFrameOn_map_symmₗ
      (trivializationAt P (fun s ↦ i.NormalSpace s hn) s₀).open_baseSet subset_rfl
      (A := fun s ↦ 1 - p s) ((contDiff_const.sub contDiff_id :
        ContDiff ℝ k fun A : P →L[ℝ] P ↦ 1 - A).contMDiff.comp_contMDiffOn hp)
      (fun s hs ↦ (hker s hs ▸ (hps s hs).2.2.2.2).trans (hr s))
      (mem_baseSet_trivializationAt P (fun s ↦ i.NormalSpace s hn) s₀)
  exact ⟨U, hU, hs₀U, X, ⟨hX.continuousOn, hX.linearIndependent, fun hy ↦
    (hX.span_eq hy).trans (by rw [hker _ (hUe hy), (hps _ (hUe hy)).2.2.1])⟩, hXk⟩

/-- **The negative normal bundle of a connected Morse–Bott submanifold.** On a connected
critical submanifold the Morse index is constant, so the negative normal spaces relative to a
`C^k` fibre metric form a `C^k` subbundle of the normal bundle whose rank is the index at any
point `s₀`. -/
theorem hasLocalContMDiffSubbundleFrames_negativeNormalSpace_of_preconnectedSpace
    [PreconnectedSpace S] (h : i.IsNondegenerateCriticalSubmanifold f) (hk : k + 1 ≤ n)
    (hf : ∀ s, ContMDiffAt I 𝓘(ℝ) (k + 2) f (i s))
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g : haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
      haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
      letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J k P fun s ↦ i.NormalSpace s hn) (s₀ : S) :
    haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
    haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
    haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    HasLocalContMDiffSubbundleFrames J k P (Fin (manifoldMorseIndex I f (i s₀)))
      (h.negativeNormalSpace hn g.toRiemannianMetric) :=
  haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
  h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn hk hf hdim g fun s ↦
    (h.isLocallyConstant_manifoldMorseIndex hn).apply_eq_of_preconnectedSpace s s₀

/-- **The positive normal bundle of a connected Morse–Bott submanifold.** On a connected
critical submanifold the Morse index of `-f` is constant, so the positive normal spaces relative to
a `C^k` fibre metric form a `C^k` subbundle of the normal bundle whose rank is the index of `-f`
at any point `s₀`. -/
theorem hasLocalContMDiffSubbundleFrames_positiveNormalSpace_of_preconnectedSpace
    [PreconnectedSpace S] (h : i.IsNondegenerateCriticalSubmanifold f) (hk : k + 1 ≤ n)
    (hf : ∀ s, ContMDiffAt I 𝓘(ℝ) (k + 2) f (i s))
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g : haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
      haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
      letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J k P fun s ↦ i.NormalSpace s hn) (s₀ : S) :
    haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
    haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
    haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    HasLocalContMDiffSubbundleFrames J k P (Fin (manifoldMorseIndex I (-f) (i s₀)))
      (h.positiveNormalSpace hn g.toRiemannianMetric) :=
  haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
  h.hasLocalContMDiffSubbundleFrames_positiveNormalSpace hn hk hf hdim g fun s ↦
    (h.neg.isLocallyConstant_manifoldMorseIndex hn).apply_eq_of_preconnectedSpace s s₀

/-! ### Independence of the metric -/

section MetricIndependence

variable [IsManifold I 2 M]

/-- The projection of the normal space onto the negative normal space relative to `g`, along the
positive normal space. -/
private def negativeNormalProj (h : i.IsNondegenerateCriticalSubmanifold f)
    (g : RiemannianMetric fun s ↦ i.NormalSpace s hn) (s : S) :
    Module.End ℝ (i.NormalSpace s hn) :=
  (h.negativeNormalSpace hn g s).projection (h.positiveNormalSpace hn g s)
    (h.isCompl_negativeNormalSpace_positiveNormalSpace hn g s)

/-- The operator comparing the splittings of the normal space relative to two fibre metrics `g₀`
and `g₁`: on the negative normal space of `g₀` it is the projection onto the negative normal space
of `g₁`, and on the positive normal space of `g₀` the projection onto the positive normal space of
`g₁`. -/
private def metricChange (h : i.IsNondegenerateCriticalSubmanifold f)
    (g₀ g₁ : RiemannianMetric fun s ↦ i.NormalSpace s hn) (s : S) :
    Module.End ℝ (i.NormalSpace s hn) :=
  negativeNormalProj hn h g₁ s * negativeNormalProj hn h g₀ s +
    (1 - negativeNormalProj hn h g₁ s) * (1 - negativeNormalProj hn h g₀ s)

variable (h : i.IsNondegenerateCriticalSubmanifold f)
  (g₀ g₁ : RiemannianMetric fun s ↦ i.NormalSpace s hn) (s : S)

omit [FiniteDimensional ℝ E'] in
/-- The comparison operator is injective: the negative normal space of each metric meets the
positive normal space of the other only in `0`. -/
private theorem injective_metricChange : Function.Injective ⇑(metricChange hn h g₀ g₁ s) := by
  refine LinearMap.IsIdempotentElem.injective_mul_add_one_sub_mul_one_sub
    (Submodule.isIdempotentElem_projection _) (Submodule.isIdempotentElem_projection _) ?_ ?_
  · rw [negativeNormalProj, negativeNormalProj, Submodule.range_projection,
      Submodule.ker_projection]
    exact h.disjoint_negativeNormalSpace_positiveNormalSpace' hn g₀ g₁
  · rw [negativeNormalProj, negativeNormalProj, Submodule.range_projection,
      Submodule.ker_projection]
    exact (h.disjoint_negativeNormalSpace_positiveNormalSpace' hn g₁ g₀).symm

omit [FiniteDimensional ℝ E'] in
/-- The comparison operator carries the negative normal space of `g₀` into that of `g₁`. -/
private theorem metricChange_mem_negativeNormalSpace {v : i.NormalSpace s hn}
    (hv : v ∈ h.negativeNormalSpace hn g₀ s) :
    metricChange hn h g₀ g₁ s v ∈ h.negativeNormalSpace hn g₁ s := by
  have hv₀ : negativeNormalProj hn h g₀ s v = v := Submodule.projection_apply_of_mem_left _ hv
  have : metricChange hn h g₀ g₁ s v = negativeNormalProj hn h g₁ s v := by
    simp [metricChange, hv₀]
  rw [this]
  exact Submodule.projection_apply_mem _ _

omit [FiniteDimensional ℝ E'] in
/-- The comparison operator carries the positive normal space of `g₀` into that of `g₁`. -/
private theorem metricChange_mem_positiveNormalSpace {v : i.NormalSpace s hn}
    (hv : v ∈ h.positiveNormalSpace hn g₀ s) :
    metricChange hn h g₀ g₁ s v ∈ h.positiveNormalSpace hn g₁ s := by
  have hv₀ : negativeNormalProj hn h g₀ s v = 0 :=
    (Submodule.projection_apply_eq_zero_iff _).mpr hv
  have : metricChange hn h g₀ g₁ s v = v - negativeNormalProj hn h g₁ s v := by
    simp [metricChange, hv₀]
  rw [this]
  exact Submodule.sub_projection_mem _ _

omit [FiniteDimensional ℝ E'] [FiniteDimensional ℝ P] in
/-- Read in a linear trivialization `e` of the normal bundle in which the negative and positive
normal spaces of `g` are the images of the range and the kernel of an idempotent `p` of the fibre
model, the projection onto the negative normal space along the positive one is `p`. -/
private theorem negativeNormalProj_coord
    [TopologicalSpace (TotalSpace P fun s ↦ i.NormalSpace s hn)]
    (e : Trivialization P (π P fun s ↦ i.NormalSpace s hn)) [e.IsLinear ℝ] {s : S}
    (hs : s ∈ e.baseSet) {p : P →L[ℝ] P} (hp : IsIdempotentElem p)
    (hneg : h.negativeNormalSpace hn g₀ s = p.range.map (e.symmₗ ℝ s))
    (hpos : h.positiveNormalSpace hn g₀ s = p.ker.map (e.symmₗ ℝ s)) (v : i.NormalSpace s hn) :
    (e ⟨s, negativeNormalProj hn h g₀ s v⟩).2 = p (e ⟨s, v⟩).2 := by
  set w := (e ⟨s, v⟩).2
  have hpp : p (p w) = p w := congr($hp.eq w)
  -- Split `v` along the range and the kernel of `p`, read in the trivialization.
  have hv : v = e.symmₗ ℝ s (p w) + e.symmₗ ℝ s (w - p w) := by
    rw [← map_add, add_sub_cancel, e.symmₗ_apply hs, e.symm_apply_apply_mk hs]
  have h₁ : e.symmₗ ℝ s (p w) ∈ h.negativeNormalSpace hn g₀ s :=
    hneg ▸ Submodule.mem_map_of_mem (LinearMap.mem_range_self (p : P →ₗ[ℝ] P) w)
  have h₂ : e.symmₗ ℝ s (w - p w) ∈ h.positiveNormalSpace hn g₀ s :=
    hpos ▸ Submodule.mem_map_of_mem (by simp [hpp])
  rw [hv, map_add, negativeNormalProj, Submodule.projection_apply_of_mem_left _ h₁,
    (Submodule.projection_apply_eq_zero_iff _).mpr h₂, add_zero, e.symmₗ_apply hs,
    e.apply_mk_symm hs]

end MetricIndependence

/-- The comparison operator of two continuous fibre metrics is continuous on the total space of
the normal bundle. In the trivialization at `s₀`, the projections onto the negative normal spaces
are the continuous families of idempotents of the fibre model supplied by
`exists_contMDiffOn_negativeNormalSpace_eq_map`, and the comparison operator is the same
expression in them. -/
private theorem continuous_totalSpace_metricChange
    (h : i.IsNondegenerateCriticalSubmanifold f) (hk : k + 1 ≤ n)
    (hf : ∀ s, ContMDiffAt I 𝓘(ℝ) (k + 2) f (i s))
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g₀ g₁ : haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
      haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
      letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J k P fun s ↦ i.NormalSpace s hn) :
    haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
    haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
    haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    Continuous fun v : TotalSpace P (fun s ↦ i.NormalSpace s hn) ↦
      TotalSpace.mk' P (E := fun s ↦ i.NormalSpace s hn) v.proj
        (metricChange hn h g₀.toRiemannianMetric g₁.toRiemannianMetric v.proj v.2) := by
  have : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
  have : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
  have : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  set G₀ := g₀.toRiemannianMetric
  set G₁ := g₁.toRiemannianMetric
  refine continuous_iff_continuousAt.mpr fun v₀ ↦ ?_
  set e := trivializationAt P (fun s ↦ i.NormalSpace s hn) v₀.proj
  obtain ⟨p₀, hp₀, hps₀⟩ := exists_contMDiffOn_negativeNormalSpace_eq_map hn h hk hf hdim g₀ v₀.proj
  obtain ⟨p₁, hp₁, hps₁⟩ := exists_contMDiffOn_negativeNormalSpace_eq_map hn h hk hf hdim g₁ v₀.proj
  set t : S → P →L[ℝ] P := fun s ↦ p₁ s * p₀ s + (1 - p₁ s) * (1 - p₀ s)
  have ht : ContinuousOn t e.baseSet :=
    (hp₁.continuousOn.mul hp₀.continuousOn).add
      ((continuousOn_const.sub hp₁.continuousOn).mul (continuousOn_const.sub hp₀.continuousOn))
  -- In the trivialization, the comparison operator reads as `t`.
  have hcoord (v : TotalSpace P (fun s ↦ i.NormalSpace s hn)) (hv : v.proj ∈ e.baseSet) :
      (e (TotalSpace.mk' P (E := fun s ↦ i.NormalSpace s hn) v.proj
        (metricChange hn h G₀ G₁ v.proj v.2))).2 = t v.proj (e v).2 := by
    obtain ⟨hidem₀, hneg₀, hpos₀, -⟩ := hps₀ v.proj hv
    obtain ⟨hidem₁, hneg₁, hpos₁, -⟩ := hps₁ v.proj hv
    have h₀ (x : i.NormalSpace v.proj hn) :=
      negativeNormalProj_coord hn h G₀ e hv hidem₀ hneg₀ hpos₀ x
    have h₁ (x : i.NormalSpace v.proj hn) :=
      negativeNormalProj_coord hn h G₁ e hv hidem₁ hneg₁ hpos₁ x
    have hlin (x : i.NormalSpace v.proj hn) : (e ⟨v.proj, x⟩).2 = e.linearMapAt ℝ v.proj x := by
      rw [e.coe_linearMapAt_of_mem hv]
    simp only [hlin] at h₀ h₁
    rw [hlin, hlin]
    simp [t, metricChange, h₀, h₁, map_sub]
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨FiberBundle.continuous_proj P _ |>.continuousAt, ?_⟩
  have hsrc : e.source ∈ 𝓝 v₀ :=
    e.open_source.mem_nhds FiberBundle.mem_trivializationAt_proj_source
  refine ContinuousAt.congr ?_ (Filter.eventuallyEq_of_mem hsrc fun v hv ↦
    (hcoord v (e.mem_source.mp hv)).symm)
  exact ((ht.continuousAt (e.open_baseSet.mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt' _))).comp
      (FiberBundle.continuous_proj P _).continuousAt).clm_apply
    (e.continuousOn.continuousAt hsrc).snd

/-- **The splitting of the normal bundle does not depend on the metric, up to isomorphism.** Let
`i` be a nondegenerate critical submanifold of `f`, with `f` of class `C^{k+2}` along it and `i` of
class `C^{k+1}`, and let `g₀` and `g₁` be two `C^k` fibre metrics on the normal bundle, with fibre
model `P`. There is a homeomorphism `Φ` of the total space of the normal bundle, covering the
identity of `S` and acting on each normal space by a linear isomorphism `φ s`, which carries the
negative and the positive normal spaces relative to `g₀` onto those relative to `g₁`. The negative
and positive normal spaces themselves depend on the metric.

On the negative normal space of `g₀`, `φ s` is the projection onto the negative normal space of
`g₁` along its positive normal space, and on the positive normal space of `g₀` it is the
complementary projection. -/
theorem exists_homeomorph_totalSpace_map_negativeNormalSpace_eq_and_map_positiveNormalSpace_eq
    (h : i.IsNondegenerateCriticalSubmanifold f) (hk : k + 1 ≤ n)
    (hf : ∀ s, ContMDiffAt I 𝓘(ℝ) (k + 2) f (i s))
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g₀ g₁ : haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
      haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
      letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J k P fun s ↦ i.NormalSpace s hn) :
    haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
    haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
    haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    ∃ (φ : ∀ s, i.NormalSpace s hn ≃L[ℝ] i.NormalSpace s hn)
      (Φ : TotalSpace P (fun s ↦ i.NormalSpace s hn) ≃ₜ TotalSpace P fun s ↦ i.NormalSpace s hn),
      (∀ s v, Φ ⟨s, v⟩ = ⟨s, φ s v⟩) ∧ ∀ s,
        (h.negativeNormalSpace hn g₀.toRiemannianMetric s).map
            (φ s : i.NormalSpace s hn →ₗ[ℝ] i.NormalSpace s hn) =
          h.negativeNormalSpace hn g₁.toRiemannianMetric s ∧
        (h.positiveNormalSpace hn g₀.toRiemannianMetric s).map
            (φ s : i.NormalSpace s hn →ₗ[ℝ] i.NormalSpace s hn) =
          h.positiveNormalSpace hn g₁.toRiemannianMetric s := by
  have : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
  have : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
  have : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  set G₀ := g₀.toRiemannianMetric
  set G₁ := g₁.toRiemannianMetric
  let φ (s : S) : i.NormalSpace s hn ≃L[ℝ] i.NormalSpace s hn :=
    (LinearEquiv.ofInjectiveEndo _ (injective_metricChange hn h G₀ G₁ s)).toContinuousLinearEquiv
  have hcont : Continuous fun v : TotalSpace P (fun s ↦ i.NormalSpace s hn) ↦
      TotalSpace.mk' P (E := fun s ↦ i.NormalSpace s hn) v.proj (φ v.proj v.2) :=
    continuous_totalSpace_metricChange hn h hk hf hdim g₀ g₁
  refine ⟨φ, bundleHomeomorph φ hcont, fun _ _ ↦ bundleHomeomorph_apply φ hcont _, fun s ↦ ⟨?_, ?_⟩⟩
  · refine Submodule.eq_of_le_of_finrank_eq (Submodule.map_le_iff_le_comap.mpr fun v hv ↦
      metricChange_mem_negativeNormalSpace hn h G₀ G₁ s hv) ?_
    -- `φ s` and its underlying linear equivalence have the same underlying linear map.
    rw [show (φ s : i.NormalSpace s hn →ₗ[ℝ] i.NormalSpace s hn) = (φ s).toLinearEquiv from rfl,
      LinearEquiv.finrank_map_eq, h.finrank_negativeNormalSpace, h.finrank_negativeNormalSpace]
  · refine Submodule.eq_of_le_of_finrank_eq (Submodule.map_le_iff_le_comap.mpr fun v hv ↦
      metricChange_mem_positiveNormalSpace hn h G₀ G₁ s hv) ?_
    -- `φ s` and its underlying linear equivalence have the same underlying linear map.
    rw [show (φ s : i.NormalSpace s hn →ₗ[ℝ] i.NormalSpace s hn) = (φ s).toLinearEquiv from rfl,
      LinearEquiv.finrank_map_eq, h.finrank_positiveNormalSpace, h.finrank_positiveNormalSpace]

/-- **The negative normal bundle does not depend on the metric, up to isomorphism.** Let `i` be a
nondegenerate critical submanifold of `f`, with `f` of class `C^{k+2}` along it and `i` of class
`C^{k+1}`, and let `g₀` and `g₁` be two `C^k` fibre metrics on the normal bundle, with fibre model
`P`. The total spaces of the negative normal spaces relative to `g₀` and to `g₁`, each with the
topology of a subspace of the total space of the normal bundle, are homeomorphic by a map covering
the identity of `S` and acting on each fibre by a linear isomorphism. When the Morse index of
`f` is constant along the submanifold, these are the negative normal bundles
(`hasLocalContMDiffSubbundleFrames_negativeNormalSpace`), so the two are isomorphic topological
vector bundles. -/
theorem exists_homeomorph_totalSpace_negativeNormalSpace
    (h : i.IsNondegenerateCriticalSubmanifold f) (hk : k + 1 ≤ n)
    (hf : ∀ s, ContMDiffAt I 𝓘(ℝ) (k + 2) f (i s))
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g₀ g₁ : haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
      haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
      letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J k P fun s ↦ i.NormalSpace s hn) (F' : Type*) :
    haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
    haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
    haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    letI := subbundleTopology P (F' := F') (h.negativeNormalSpace hn g₀.toRiemannianMetric)
    letI := subbundleTopology P (F' := F') (h.negativeNormalSpace hn g₁.toRiemannianMetric)
    ∃ (φ : ∀ s, h.negativeNormalSpace hn g₀.toRiemannianMetric s ≃ₗ[ℝ]
        h.negativeNormalSpace hn g₁.toRiemannianMetric s)
      (Φ : TotalSpace F' (fun s ↦ h.negativeNormalSpace hn g₀.toRiemannianMetric s) ≃ₜ
        TotalSpace F' fun s ↦ h.negativeNormalSpace hn g₁.toRiemannianMetric s),
      ∀ s v, Φ ⟨s, v⟩ = ⟨s, φ s v⟩ := by
  have : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
  have : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
  have : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  obtain ⟨φ, Φ, hΦ, hmap⟩ :=
    h.exists_homeomorph_totalSpace_map_negativeNormalSpace_eq_and_map_positiveNormalSpace_eq hn hk
      hf hdim g₀ g₁
  obtain ⟨ψ, Ψ, -, hΨ⟩ := exists_homeomorph_totalSpace_subbundle_of_map_eq P F'
    (fun s ↦ (φ s).toLinearEquiv) Φ hΦ fun s ↦ (hmap s).1
  exact ⟨ψ, Ψ, hΨ⟩

/-- **The positive normal bundle does not depend on the metric, up to isomorphism.** Let `i` be a
nondegenerate critical submanifold of `f`, with `f` of class `C^{k+2}` along it and `i` of class
`C^{k+1}`, and let `g₀` and `g₁` be two `C^k` fibre metrics on the normal bundle, with fibre model
`P`. The total spaces of the positive normal spaces relative to `g₀` and to `g₁`, each with the
topology of a subspace of the total space of the normal bundle, are homeomorphic by a map covering
the identity of `S` and acting on each fibre by a linear isomorphism. When the Morse index of
`-f` is constant along the submanifold, these are the positive normal bundles
(`hasLocalContMDiffSubbundleFrames_positiveNormalSpace`), so the two are isomorphic topological
vector bundles. -/
theorem exists_homeomorph_totalSpace_positiveNormalSpace
    (h : i.IsNondegenerateCriticalSubmanifold f) (hk : k + 1 ≤ n)
    (hf : ∀ s, ContMDiffAt I 𝓘(ℝ) (k + 2) f (i s))
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g₀ g₁ : haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
      haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
      letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J k P fun s ↦ i.NormalSpace s hn) (F' : Type*) :
    haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
    haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
    haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    letI := subbundleTopology P (F' := F') (h.positiveNormalSpace hn g₀.toRiemannianMetric)
    letI := subbundleTopology P (F' := F') (h.positiveNormalSpace hn g₁.toRiemannianMetric)
    ∃ (φ : ∀ s, h.positiveNormalSpace hn g₀.toRiemannianMetric s ≃ₗ[ℝ]
        h.positiveNormalSpace hn g₁.toRiemannianMetric s)
      (Φ : TotalSpace F' (fun s ↦ h.positiveNormalSpace hn g₀.toRiemannianMetric s) ≃ₜ
        TotalSpace F' fun s ↦ h.positiveNormalSpace hn g₁.toRiemannianMetric s),
      ∀ s v, Φ ⟨s, v⟩ = ⟨s, φ s v⟩ := by
  have : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
  have : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
  have : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  obtain ⟨φ, Φ, hΦ, hmap⟩ :=
    h.exists_homeomorph_totalSpace_map_negativeNormalSpace_eq_and_map_positiveNormalSpace_eq hn hk
      hf hdim g₀ g₁
  obtain ⟨ψ, Ψ, -, hΨ⟩ := exists_homeomorph_totalSpace_subbundle_of_map_eq P F'
    (fun s ↦ (φ s).toLinearEquiv) Φ hΦ fun s ↦ (hmap s).2
  exact ⟨ψ, Ψ, hΨ⟩

end TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold
