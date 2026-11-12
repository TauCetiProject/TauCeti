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

Although the subbundles depend on the metric, their isomorphism classes do not. For two `C^k`
fibre metrics `g` and `g'`, projecting along the positive normal bundle relative to `g'` is a
`C^k` diffeomorphism from the total space of the negative normal bundle relative to `g` onto that
relative to `g'`, linear on each fibre
(`IsNondegenerateCriticalSubmanifold.exists_bundleDiffeomorph_negativeNormalSpace`), and similarly
for the positive normal bundles
(`IsNondegenerateCriticalSubmanifold.exists_bundleDiffeomorph_positiveNormalSpace`). Read in a
trivialization, the projection onto the negative normal spaces along the positive ones is the
`C^k` family of projections above, so it is a `C^k` map of the total space of the normal bundle to
itself. On each fibre it restricts to the linear isomorphism
`IsNondegenerateCriticalSubmanifold.negativeNormalSpaceEquiv`, since the negative normal space for
`g` meets the positive normal space for `g'` only in `0`: the normal Hessian is negative definite
on the first and positive definite on the second.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* A. Banyaga and D. E. Hurtubise, *Lectures on Morse Homology*, Kluwer, 2004, Section 3.5.
-/

public section

open Bundle Function Set Module
open scoped ContDiff Manifold

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

/-- Projecting the normal bundle onto the negative normal bundle relative to a `C^k` fibre metric,
along the positive normal bundle, is a `C^k` map of total spaces. In the trivialization at any
point it reads `(s, y) ↦ (s, p s y)` for the `C^k` family of projections `p` of
`exists_contMDiffOn_negativeNormalSpace_eq_map`. -/
theorem contMDiff_projection_negativeNormalSpace
    (h : i.IsNondegenerateCriticalSubmanifold f) (hk : k + 1 ≤ n)
    (hf : ∀ s, ContMDiffAt I 𝓘(ℝ) (k + 2) f (i s))
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g : haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
      haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
      letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J k P fun s ↦ i.NormalSpace s hn) :
    haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
    haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
    haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    ContMDiff (J.prod 𝓘(ℝ, P)) (J.prod 𝓘(ℝ, P)) k
      (fun w : TotalSpace P (fun s ↦ i.NormalSpace s hn) ↦
        TotalSpace.mk' P (E := fun s ↦ i.NormalSpace s hn) w.proj ((h.negativeNormalSpace hn
          g.toRiemannianMetric w.proj).projection (h.positiveNormalSpace hn g.toRiemannianMetric
            w.proj) (h.isCompl_negativeNormalSpace_positiveNormalSpace hn _ _ w.proj) w.2)) := by
  have : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
  have : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
  have : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  have : IsManifold I (k + 1) M := .of_le (n := k + 2) (by gcongr; exact one_le_two)
  let := i.normalSpaceContMDiffVectorBundle hn hk hdim
  intro w₀
  rw [Bundle.contMDiffAt_totalSpace_iff]
  refine ⟨(Bundle.contMDiff_proj _).contMDiffAt, ?_⟩
  obtain ⟨p, hp, hps⟩ := exists_contMDiffOn_negativeNormalSpace_eq_map hn h hk hf hdim g w₀.proj
  set e := trivializationAt P (fun s ↦ i.NormalSpace s hn) w₀.proj
  have hw₀ : w₀.proj ∈ e.baseSet := mem_baseSet_trivializationAt P _ w₀.proj
  have hpw : ContMDiffAt (J.prod 𝓘(ℝ, P)) 𝓘(ℝ, P →L[ℝ] P) k (fun w ↦ p w.proj) w₀ :=
    (hp.contMDiffAt (e.open_baseSet.mem_nhds hw₀)).comp w₀ (Bundle.contMDiff_proj _).contMDiffAt
  have he : ContMDiffAt (J.prod 𝓘(ℝ, P)) 𝓘(ℝ, P) k (fun w ↦ (e w).2) w₀ :=
    ((e.contMDiffOn (IB := J) (n := k)).contMDiffAt
      (e.open_source.mem_nhds (e.mem_source.mpr hw₀))).snd
  refine (hpw.clm_apply he).congr_of_eventuallyEq ?_
  filter_upwards [(FiberBundle.continuous_proj P _).continuousAt.preimage_mem_nhds
    (e.open_baseSet.mem_nhds hw₀)] with w hw
  obtain ⟨hidem, hrange, hker, -, -⟩ := hps w.proj hw
  -- Split the coordinate vector `y` of `w` along the range and the kernel of `p`.
  set y := (e w).2
  have hy : w.2 = e.symmₗ ℝ w.proj (p w.proj y) + e.symmₗ ℝ w.proj (y - p w.proj y) := by
    rw [← map_add, add_sub_cancel, e.symmₗ_apply hw, e.symm_proj_apply w hw]
  have hneg : e.symmₗ ℝ w.proj (p w.proj y) ∈
      h.negativeNormalSpace hn g.toRiemannianMetric w.proj :=
    hrange ▸ Submodule.mem_map_of_mem (LinearMap.mem_range_self _ y)
  have hpos : e.symmₗ ℝ w.proj (y - p w.proj y) ∈
      h.positiveNormalSpace hn g.toRiemannianMetric w.proj := by
    refine hker ▸ Submodule.mem_map_of_mem ?_
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, map_sub, ← mul_apply_eq_comp,
      hidem.eq, sub_self]
  rw [hy, map_add, Submodule.projection_apply_of_mem_left _ hneg,
    (Submodule.projection_apply_eq_zero_iff _).mpr hpos, add_zero, e.symmₗ_apply hw]
  exact congr_arg Prod.snd (e.apply_mk_symm hw _)

/-- Projecting the normal bundle onto the positive normal bundle relative to a `C^k` fibre metric,
along the negative normal bundle, is a `C^k` map of total spaces: it is the identity minus the
projection of `contMDiff_projection_negativeNormalSpace`. -/
theorem contMDiff_projection_positiveNormalSpace
    (h : i.IsNondegenerateCriticalSubmanifold f) (hk : k + 1 ≤ n)
    (hf : ∀ s, ContMDiffAt I 𝓘(ℝ) (k + 2) f (i s))
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g : haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
      haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
      letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J k P fun s ↦ i.NormalSpace s hn) :
    haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
    haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
    haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    ContMDiff (J.prod 𝓘(ℝ, P)) (J.prod 𝓘(ℝ, P)) k
      (fun w : TotalSpace P (fun s ↦ i.NormalSpace s hn) ↦
        TotalSpace.mk' P (E := fun s ↦ i.NormalSpace s hn) w.proj ((h.positiveNormalSpace hn
          g.toRiemannianMetric w.proj).projection (h.negativeNormalSpace hn g.toRiemannianMetric
            w.proj) (h.isCompl_negativeNormalSpace_positiveNormalSpace hn _ _ w.proj).symm
          w.2)) := by
  have : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
  have : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
  have : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  have : IsManifold I (k + 1) M := .of_le (n := k + 2) (by gcongr; exact one_le_two)
  let := i.normalSpaceContMDiffVectorBundle hn hk hdim
  intro w₀
  have hA := Bundle.contMDiffAt_totalSpace_iff.mp
    (contMDiff_projection_negativeNormalSpace hn h hk hf hdim g w₀)
  rw [Bundle.contMDiffAt_totalSpace_iff]
  refine ⟨hA.1, ?_⟩
  set e := trivializationAt P (fun s ↦ i.NormalSpace s hn) w₀.proj
  have hw₀ : w₀.proj ∈ e.baseSet := mem_baseSet_trivializationAt P _ w₀.proj
  have he : ContMDiffAt (J.prod 𝓘(ℝ, P)) 𝓘(ℝ, P) k (fun w ↦ (e w).2) w₀ :=
    ((e.contMDiffOn (IB := J) (n := k)).contMDiffAt
      (e.open_source.mem_nhds (e.mem_source.mpr hw₀))).snd
  refine (he.sub hA.2).congr_of_eventuallyEq ?_
  filter_upwards [(FiberBundle.continuous_proj P _).continuousAt.preimage_mem_nhds
    (e.open_baseSet.mem_nhds hw₀)] with w hw
  -- In the trivialization, the fibre coordinate is linear on the fibre over `w.proj`.
  have hlin (x : i.NormalSpace w.proj hn) : (e ⟨w.proj, x⟩).2 = e.linearMapAt ℝ w.proj x := by
    rw [e.coe_linearMapAt_of_mem hw]
  simp only [TotalSpace.mk', hlin]
  rw [Submodule.projection_eq_self_sub_projection, map_sub]

/-- **The negative normal bundle does not depend on the metric, up to isomorphism.** Let `i` be a
nondegenerate critical submanifold of `f`, with `f` of class `C^{k+2}` along it, `i` of class
`C^{k+1}` and Morse index `r` at every point, and let `g` and `g'` be two `C^k` fibre metrics on
its normal bundle. Then the negative normal bundles relative to `g` and to `g'`
(`hasLocalContMDiffSubbundleFrames_negativeNormalSpace`) are isomorphic `C^k` vector bundles over
`S`: projecting along the positive normal bundle relative to `g'`
(`negativeNormalSpaceEquiv`) is a `C^k` diffeomorphism of their total spaces, which is a linear
isomorphism on each fibre. -/
theorem exists_bundleDiffeomorph_negativeNormalSpace
    (h : i.IsNondegenerateCriticalSubmanifold f) (hk : k + 1 ≤ n)
    (hf : ∀ s, ContMDiffAt I 𝓘(ℝ) (k + 2) f (i s))
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g g' : haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
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
    letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
    letI := (h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn hk hf hdim g hr).fiberBundle
    letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g'.toRiemannianMetric)
    letI := (h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn hk hf hdim g' hr).fiberBundle
    ∃ Φ : TotalSpace (Fin r → ℝ) (fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s)
        ≃ₘ^k⟮J.prod 𝓘(ℝ, Fin r → ℝ), J.prod 𝓘(ℝ, Fin r → ℝ)⟯
        TotalSpace (Fin r → ℝ) (fun s ↦ h.negativeNormalSpace hn g'.toRiemannianMetric s),
      ∀ v, Φ v = ⟨v.proj, h.negativeNormalSpaceEquiv hn g.toRiemannianMetric g'.toRiemannianMetric
        v.proj v.2⟩ := by
  have : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
  have : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
  have : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  have : IsManifold I (k + 1) M := .of_le (n := k + 2) (by gcongr; exact one_le_two)
  let := i.normalSpaceContMDiffVectorBundle hn hk hdim
  have hV := h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn hk hf hdim g hr
  have hV' := h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn hk hf hdim g' hr
  let := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
  let := hV.fiberBundle
  have := hV.vectorBundle
  let := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g'.toRiemannianMetric)
  let := hV'.fiberBundle
  have := hV'.vectorBundle
  -- Read in the normal bundle, the map is the inclusion of the negative normal bundle for `g`
  -- followed by the projection onto the negative normal bundle for `g'`.
  have hΦ : ContMDiff (J.prod 𝓘(ℝ, Fin r → ℝ)) (J.prod 𝓘(ℝ, Fin r → ℝ)) k
      (fun v : TotalSpace (Fin r → ℝ) (fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s) ↦
        TotalSpace.mk' (Fin r → ℝ)
          (E := fun s ↦ h.negativeNormalSpace hn g'.toRiemannianMetric s) v.proj
          ((h.negativeNormalSpaceEquiv hn g.toRiemannianMetric g'.toRiemannianMetric
            v.proj).toContinuousLinearEquiv v.2)) := fun v ↦
    (hV'.contMDiffAt_totalSpace_mk (b := TotalSpace.proj)
      ((contMDiff_projection_negativeNormalSpace hn h hk hf hdim g').comp
        hV.contMDiff_totalSpace_inclusion v) fun _ ↦ Submodule.coe_mem _).congr_of_eventuallyEq
      (.of_forall fun w ↦ TotalSpace.mk_inj.mpr <| Subtype.ext <| by simp)
  exact ⟨bundleDiffeomorph (fun s ↦ (h.negativeNormalSpaceEquiv hn g.toRiemannianMetric
    g'.toRiemannianMetric s).toContinuousLinearEquiv) hΦ, fun v ↦ by simp⟩

/-- **The positive normal bundle does not depend on the metric, up to isomorphism.** Let `i` be a
nondegenerate critical submanifold of `f`, with `f` of class `C^{k+2}` along it, `i` of class
`C^{k+1}` and the Morse index of `-f` equal to `r` at every point, and let `g` and `g'` be two
`C^k` fibre metrics on its normal bundle. Then the positive normal bundles relative to `g` and to
`g'` (`hasLocalContMDiffSubbundleFrames_positiveNormalSpace`) are isomorphic `C^k` vector bundles
over `S`: projecting along the negative normal bundle relative to `g'`
(`positiveNormalSpaceEquiv`) is a `C^k` diffeomorphism of their total spaces, which is a linear
isomorphism on each fibre. -/
theorem exists_bundleDiffeomorph_positiveNormalSpace
    (h : i.IsNondegenerateCriticalSubmanifold f) (hk : k + 1 ≤ n)
    (hf : ∀ s, ContMDiffAt I 𝓘(ℝ) (k + 2) f (i s))
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g g' : haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
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
    letI := subbundleTopology P (F' := Fin r → ℝ) (h.positiveNormalSpace hn g.toRiemannianMetric)
    letI := (h.hasLocalContMDiffSubbundleFrames_positiveNormalSpace hn hk hf hdim g hr).fiberBundle
    letI := subbundleTopology P (F' := Fin r → ℝ) (h.positiveNormalSpace hn g'.toRiemannianMetric)
    letI := (h.hasLocalContMDiffSubbundleFrames_positiveNormalSpace hn hk hf hdim g' hr).fiberBundle
    ∃ Φ : TotalSpace (Fin r → ℝ) (fun s ↦ h.positiveNormalSpace hn g.toRiemannianMetric s)
        ≃ₘ^k⟮J.prod 𝓘(ℝ, Fin r → ℝ), J.prod 𝓘(ℝ, Fin r → ℝ)⟯
        TotalSpace (Fin r → ℝ) (fun s ↦ h.positiveNormalSpace hn g'.toRiemannianMetric s),
      ∀ v, Φ v = ⟨v.proj, h.positiveNormalSpaceEquiv hn g.toRiemannianMetric g'.toRiemannianMetric
        v.proj v.2⟩ := by
  have : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
  have : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
  have : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  have : IsManifold I (k + 1) M := .of_le (n := k + 2) (by gcongr; exact one_le_two)
  let := i.normalSpaceContMDiffVectorBundle hn hk hdim
  have hV := h.hasLocalContMDiffSubbundleFrames_positiveNormalSpace hn hk hf hdim g hr
  have hV' := h.hasLocalContMDiffSubbundleFrames_positiveNormalSpace hn hk hf hdim g' hr
  let := subbundleTopology P (F' := Fin r → ℝ) (h.positiveNormalSpace hn g.toRiemannianMetric)
  let := hV.fiberBundle
  have := hV.vectorBundle
  let := subbundleTopology P (F' := Fin r → ℝ) (h.positiveNormalSpace hn g'.toRiemannianMetric)
  let := hV'.fiberBundle
  have := hV'.vectorBundle
  -- Read in the normal bundle, the map is the inclusion of the positive normal bundle for `g`
  -- followed by the projection onto the positive normal bundle for `g'`.
  have hΦ : ContMDiff (J.prod 𝓘(ℝ, Fin r → ℝ)) (J.prod 𝓘(ℝ, Fin r → ℝ)) k
      (fun v : TotalSpace (Fin r → ℝ) (fun s ↦ h.positiveNormalSpace hn g.toRiemannianMetric s) ↦
        TotalSpace.mk' (Fin r → ℝ)
          (E := fun s ↦ h.positiveNormalSpace hn g'.toRiemannianMetric s) v.proj
          ((h.positiveNormalSpaceEquiv hn g.toRiemannianMetric g'.toRiemannianMetric
            v.proj).toContinuousLinearEquiv v.2)) := fun v ↦
    (hV'.contMDiffAt_totalSpace_mk (b := TotalSpace.proj)
      ((contMDiff_projection_positiveNormalSpace hn h hk hf hdim g').comp
        hV.contMDiff_totalSpace_inclusion v) fun _ ↦ Submodule.coe_mem _).congr_of_eventuallyEq
      (.of_forall fun w ↦ TotalSpace.mk_inj.mpr <| Subtype.ext <| by simp)
  exact ⟨bundleDiffeomorph (fun s ↦ (h.positiveNormalSpaceEquiv hn g.toRiemannianMetric
    g'.toRiemannianMetric s).toContinuousLinearEquiv) hΦ, fun v ↦ by simp⟩

end TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold
