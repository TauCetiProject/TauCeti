/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.MetricChange
public import TauCeti.Geometry.Manifold.Morse.Bott.Splitting
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Subbundle
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import TauCeti.Geometry.Manifold.Morse.Bott.Index.Basic
import TauCeti.Geometry.Manifold.Morse.Bott.NegativeNormal
import TauCeti.Geometry.Manifold.VectorBundle.ComplementarySubbundle
import TauCeti.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Basic
import TauCeti.Geometry.Manifold.VectorBundle.SectionAlongMap.Regularity
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
subbundles of the normal bundle, the **negative and positive normal bundles** `ν⁻` and `ν⁺`.
Conversely, local frames of the negative normal spaces of any size `r` force the index to be `r`
(`IsNondegenerateCriticalSubmanifold.manifoldMorseIndex_eq_of_hasLocalSubbundleFrames`), so the
rank of `ν⁻` is the index of the submanifold. The indices are locally constant along a Morse–Bott
submanifold, so on a connected one the hypothesis holds automatically (the `_of_preconnectedSpace`
versions). For a smooth function and a smooth fibre metric, the negative normal spaces of a
submanifold of constant index therefore form a topological vector bundle whose rank is the index
(`IsNondegenerateCriticalSubmanifold.hasLocalSubbundleFrames_negativeNormalSpace`). The negative
normal bundle is the bundle whose disc bundle is attached when the critical level of the
submanifold is crossed.

The subbundles depend on the metric `g`, but their ranks do not. No eigenbasis of the normal
Hessian is chosen. In the preferred normal-bundle trivialization at `s₀`, with fibre model `P`, the
metric becomes a `C^k` family `G` of bilinear forms on `P`
(`Bundle.ContMDiffRiemannianMetric.exists_contMDiffOn_apply_eq_inner_symm`). The projections onto
the negative relative spectral subspaces of the normal Hessian with respect to `G`, along the
positive ones, are then a
`C^k` family of operators on `P` whose ranges and kernels read the negative and positive normal
spaces in the trivialization
(`IsNondegenerateCriticalSubmanifold.exists_contMDiffOn_negativeNormalProjection`), and a `C^k`
family of operators of constant rank has `C^k` local frames of its ranges
(`Bundle.Trivialization.exists_isSubbundleFrameOn_map_symmₗ`).

Although the subbundles depend on the metric, their isomorphism classes do not. For two `C^k`
fibre metrics `g` and `g'`, projecting along the positive normal bundle relative to `g'` is a
`C^k` diffeomorphism from the total space of the negative normal bundle relative to `g` onto that
relative to `g'`, linear on each fibre
(`IsNondegenerateCriticalSubmanifold.exists_bundleDiffeomorph_negativeNormalSpace`; its continuity
on total spaces is `IsNondegenerateCriticalSubmanifold.continuous_negativeNormalSpaceEquiv`), and
similarly for the positive normal bundles
(`IsNondegenerateCriticalSubmanifold.exists_bundleDiffeomorph_positiveNormalSpace`). Read in a
trivialization, the projection onto the negative normal spaces along the positive ones is the
`C^k` family of projections above, so it is a `C^k` map of the total space of the normal bundle to
itself. On each fibre it restricts to the linear isomorphism
`IsNondegenerateCriticalSubmanifold.negativeNormalSpaceEquiv`, since the negative normal space for
`g` meets the positive normal space for `g'` only in `0`: the normal Hessian is negative definite
on the first and positive definite on the second.

Both bundles can be carried across at once: the change of fibre metric
`IsNondegenerateCriticalSubmanifold.normalMetricChange g g'`, which is the sum of these projections
on the negative and positive parts, is a `C^k` automorphism of the normal bundle carrying the
negative and positive normal bundles relative to `g` onto those relative to `g'`
(`IsNondegenerateCriticalSubmanifold.contMDiff_normalMetricChange` and
`IsNondegenerateCriticalSubmanifold.normalMetricChangeDiffeomorph`).

Together the two subbundles recover the normal bundle. When both indices are constant, adding a
negative and a positive normal vector over the same point is a `C^k` diffeomorphism from the total
space of the direct-sum bundle `ν⁻ ×ᵇ ν⁺` onto that of `ν`
(`exists_bundleDiffeomorph_prod_negativeNormalSpace_positiveNormalSpace`, in the namespace
`TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold`), since `ν⁻ s` and `ν⁺ s` are
complementary in every normal space
(`TauCeti.HasLocalContMDiffSubbundleFrames.exists_bundleDiffeomorph_prod_of_isCompl`).

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
family of projections of the fibre model, which reads the projection onto the negative normal
space along the positive one. This is `exists_contMDiffOn_negativeNormalProjection` for the
metric read in the bundle chart at `s₀`. -/
theorem exists_contMDiffOn_negativeNormalProjection_trivializationAt
    (h : i.IsNondegenerateCriticalSubmanifold f) (hk : k + 1 ≤ n)
    (hf : ∀ s, ContMDiffAt I 𝓘(ℝ) (k + 2) f (i s))
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g : haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
      haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
      letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J k P fun s ↦ i.isImmersion.NormalSpace s hn) (s₀ : S) :
    haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
    haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
    haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    let e := trivializationAt P (fun s ↦ i.isImmersion.NormalSpace s hn) s₀
    ∃ p : S → P →L[ℝ] P, ContMDiffOn J 𝓘(ℝ, P →L[ℝ] P) k p e.baseSet ∧
      ∀ s ∈ e.baseSet, IsIdempotentElem (p s) ∧
        h.negativeNormalSpace hn g.toRiemannianMetric s = (p s).range.map (e.symmₗ ℝ s) ∧
        h.positiveNormalSpace hn g.toRiemannianMetric s = (p s).ker.map (e.symmₗ ℝ s) ∧
        finrank ℝ (p s).range = manifoldMorseIndex I f (i s) ∧
        finrank ℝ (p s).ker = manifoldMorseIndex I (-f) (i s) ∧
        ∀ u, e.symm s (p s u) =
          h.negativeNormalProjection hn g.toRiemannianMetric s (e.symm s u) := by
  have : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
  have : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
  have : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  have : IsManifold I (k + 1) M := .of_le (n := k + 2) (by gcongr; exact one_le_two)
  let := i.normalSpaceContMDiffVectorBundle hn hk hdim
  set e := trivializationAt P (fun s ↦ i.isImmersion.NormalSpace s hn) s₀
  -- The metric read in the trivialization.
  obtain ⟨G, hG, hGg⟩ := g.exists_contMDiffOn_apply_eq_inner_symm e
  obtain ⟨p, hp, hps⟩ := h.exists_contMDiffOn_negativeNormalProjection hn
    g.toRiemannianMetric (le_self_add.trans hk) hf hdim s₀ hG fun s hs u v ↦ by
      simp only [← normalSpaceFiberBundle_trivializationAt] at hs ⊢
      exact hGg s hs.2 u v
  -- The normal-bundle trivialization at `s₀` is the bundle chart `e` at `s₀`.
  simp only [← normalSpaceFiberBundle_trivializationAt] at hp hps
  exact ⟨p, hp.mono fun s hs ↦ ⟨hs, hs⟩, fun s hs ↦ hps s ⟨hs, hs⟩⟩

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
      ContMDiffRiemannianMetric J k P fun s ↦ i.isImmersion.NormalSpace s hn) {r : ℕ}
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
  obtain ⟨p, hp, hps⟩ :=
    exists_contMDiffOn_negativeNormalProjection_trivializationAt hn h hk hf hdim g s₀
  obtain ⟨U, hUe, hU, hs₀U, X, hX, hXk⟩ :=
    (trivializationAt P
        (fun s ↦ i.isImmersion.NormalSpace s hn) s₀).exists_isSubbundleFrameOn_map_symmₗ
      (trivializationAt P (fun s ↦ i.isImmersion.NormalSpace s hn) s₀).open_baseSet subset_rfl hp
      (fun s hs ↦ by obtain ⟨-, -, -, hrank, -⟩ := hps s hs; exact hrank.trans (hr s))
      (mem_baseSet_trivializationAt P (fun s ↦ i.isImmersion.NormalSpace s hn) s₀)
  exact ⟨U, hU, hs₀U, X, ⟨hX.continuousOn, hX.linearIndependent, fun hy ↦ by
    obtain ⟨-, hneg, -⟩ := hps _ (hUe hy); exact (hX.span_eq hy).trans hneg.symm⟩, hXk⟩

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
      ContMDiffRiemannianMetric J k P fun s ↦ i.isImmersion.NormalSpace s hn) {r : ℕ}
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
  obtain ⟨p, hp, hps⟩ :=
    exists_contMDiffOn_negativeNormalProjection_trivializationAt hn h hk hf hdim g s₀
  -- The kernel of a projection `p` is the range of the complementary projection `1 - p`.
  have hker (s : S)
      (hs : s ∈ (trivializationAt P (fun s ↦ i.isImmersion.NormalSpace s hn) s₀).baseSet) :
      (1 - p s).range = (p s).ker := by
    obtain ⟨hidem, -⟩ := hps s hs
    have hP : IsIdempotentElem (p s : P →ₗ[ℝ] P) := congr(($hidem : P →ₗ[ℝ] P))
    rw [LinearMap.IsIdempotentElem.ker_eq_range_one_sub hP,
      ContinuousLinearMap.toLinearMap_sub, ContinuousLinearMap.toLinearMap_one]
  obtain ⟨U, hUe, hU, hs₀U, X, hX, hXk⟩ :=
    (trivializationAt P
        (fun s ↦ i.isImmersion.NormalSpace s hn) s₀).exists_isSubbundleFrameOn_map_symmₗ
      (trivializationAt P (fun s ↦ i.isImmersion.NormalSpace s hn) s₀).open_baseSet subset_rfl
      (A := fun s ↦ 1 - p s) ((contDiff_const.sub contDiff_id :
        ContDiff ℝ k fun A : P →L[ℝ] P ↦ 1 - A).contMDiff.comp_contMDiffOn hp)
      (fun s hs ↦ by
        obtain ⟨-, -, -, -, hnull, -⟩ := hps s hs; exact (hker s hs ▸ hnull).trans (hr s))
      (mem_baseSet_trivializationAt P (fun s ↦ i.isImmersion.NormalSpace s hn) s₀)
  exact ⟨U, hU, hs₀U, X, ⟨hX.continuousOn, hX.linearIndependent, fun hy ↦ by
    obtain ⟨-, -, hpos, -⟩ := hps _ (hUe hy); rw [hX.span_eq hy, hker _ (hUe hy), hpos]⟩, hXk⟩

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
      ContMDiffRiemannianMetric J k P fun s ↦ i.isImmersion.NormalSpace s hn) (s₀ : S) :
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
      ContMDiffRiemannianMetric J k P fun s ↦ i.isImmersion.NormalSpace s hn) (s₀ : S) :
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
`exists_contMDiffOn_negativeNormalProjection_trivializationAt`. -/
theorem contMDiff_negativeNormalProjection
    (h : i.IsNondegenerateCriticalSubmanifold f) (hk : k + 1 ≤ n)
    (hf : ∀ s, ContMDiffAt I 𝓘(ℝ) (k + 2) f (i s))
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g : haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
      haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
      letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J k P fun s ↦ i.isImmersion.NormalSpace s hn) :
    haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
    haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
    haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    ContMDiff (J.prod 𝓘(ℝ, P)) (J.prod 𝓘(ℝ, P)) k
      (fun w : TotalSpace P (fun s ↦ i.isImmersion.NormalSpace s hn) ↦
        TotalSpace.mk' P (E := fun s ↦ i.isImmersion.NormalSpace s hn) w.proj
          (h.negativeNormalProjection hn g.toRiemannianMetric w.proj w.snd)) := by
  have : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
  have : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
  have : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  -- In the trivialization at any point, the projection reads as the `C^k` family `p`.
  refine contMDiff_bundleMap_of_contMDiffOn_symm
    (fun s ↦ h.negativeNormalProjection hn g.toRiemannianMetric s) fun s₀ ↦ ?_
  obtain ⟨p, hp, hps⟩ :=
    exists_contMDiffOn_negativeNormalProjection_trivializationAt hn h hk hf hdim g s₀
  refine ⟨p, hp.mono inter_subset_left, fun s hs ↦ ?_⟩
  obtain ⟨-, -, -, -, -, hpe⟩ := hps s hs.1
  exact hpe

/-- Projecting the normal bundle onto the positive normal bundle relative to a `C^k` fibre metric,
along the negative normal bundle, is a `C^k` map of total spaces: it is `v ↦ v - P v` for the
projection `P` of `contMDiff_negativeNormalProjection`. -/
theorem contMDiff_sub_negativeNormalProjection
    (h : i.IsNondegenerateCriticalSubmanifold f) (hk : k + 1 ≤ n)
    (hf : ∀ s, ContMDiffAt I 𝓘(ℝ) (k + 2) f (i s))
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g : haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
      haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
      letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J k P fun s ↦ i.isImmersion.NormalSpace s hn) :
    haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
    haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
    haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    ContMDiff (J.prod 𝓘(ℝ, P)) (J.prod 𝓘(ℝ, P)) k
      (fun w : TotalSpace P (fun s ↦ i.isImmersion.NormalSpace s hn) ↦
        TotalSpace.mk' P (E := fun s ↦ i.isImmersion.NormalSpace s hn) w.proj
          (w.snd - h.negativeNormalProjection hn g.toRiemannianMetric w.proj w.snd)) := by
  have : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
  have : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
  have : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  have : IsManifold I (k + 1) M := .of_le (n := k + 2) (by gcongr; exact one_le_two)
  let := i.normalSpaceContMDiffVectorBundle hn hk hdim
  intro w₀
  have hA := Bundle.contMDiffAt_totalSpace_iff.mp
    (contMDiff_negativeNormalProjection hn h hk hf hdim g w₀)
  rw [Bundle.contMDiffAt_totalSpace_iff]
  refine ⟨hA.1, ?_⟩
  set e := trivializationAt P (fun s ↦ i.isImmersion.NormalSpace s hn) w₀.proj
  have hw₀ : w₀.proj ∈ e.baseSet := mem_baseSet_trivializationAt P _ w₀.proj
  have he : ContMDiffAt (J.prod 𝓘(ℝ, P)) 𝓘(ℝ, P) k (fun w ↦ (e w).2) w₀ :=
    ((e.contMDiffOn (IB := J) (n := k)).contMDiffAt
      (e.open_source.mem_nhds (e.mem_source.mpr hw₀))).snd
  refine (he.sub hA.2).congr_of_eventuallyEq ?_
  filter_upwards [(FiberBundle.continuous_proj P _).continuousAt.preimage_mem_nhds
    (e.open_baseSet.mem_nhds hw₀)] with w hw
  -- In the trivialization, the fibre coordinate is linear on the fibre over `w.proj`.
  have hlin (x : i.isImmersion.NormalSpace w.proj hn) : (e ⟨w.proj, x⟩).2 =
      e.linearMapAt ℝ w.proj x := by
    rw [e.coe_linearMapAt_of_mem hw]
  simp only [TotalSpace.mk', hlin]
  rw [map_sub]

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
      ContMDiffRiemannianMetric J k P fun s ↦ i.isImmersion.NormalSpace s hn) {r : ℕ}
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
        v.proj v.snd⟩ := by
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
            v.proj).toContinuousLinearEquiv v.snd)) := fun v ↦
    (hV'.contMDiffAt_totalSpace_mk le_rfl (b := TotalSpace.proj)
      ((contMDiff_negativeNormalProjection hn h hk hf hdim g').comp
        hV.contMDiff_totalSpace_inclusion v) fun _ ↦
          h.negativeNormalProjection_apply_mem hn _ _).congr_of_eventuallyEq
      (.of_forall fun w ↦ TotalSpace.mk_inj.mpr <| Subtype.ext <| by simp)
  exact ⟨bundleDiffeomorph (fun s ↦ (h.negativeNormalSpaceEquiv hn g.toRiemannianMetric
    g'.toRiemannianMetric s).toContinuousLinearEquiv) hΦ, fun v ↦ by simp⟩

/-- Projecting the negative normal spaces of `g'` along the positive normal spaces of `g` is
continuous on the total spaces of the negative normal bundles. -/
theorem continuous_negativeNormalSpaceEquiv
    (h : i.IsNondegenerateCriticalSubmanifold f) (hk : k + 1 ≤ n)
    (hf : ∀ s, ContMDiffAt I 𝓘(ℝ) (k + 2) f (i s))
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g g' : haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
      haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
      letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J k P fun s ↦ i.isImmersion.NormalSpace s hn) {r : ℕ}
    (hr : ∀ s, manifoldMorseIndex I f (i s) = r) :
    haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
    haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
    haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
    letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g'.toRiemannianMetric)
    Continuous fun v : TotalSpace (Fin r → ℝ)
        (fun s ↦ h.negativeNormalSpace hn g'.toRiemannianMetric s) ↦
      TotalSpace.mk' (Fin r → ℝ) (E := fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s)
        v.proj ((h.negativeNormalSpaceEquiv hn g'.toRiemannianMetric g.toRiemannianMetric
          v.proj).toContinuousLinearEquiv v.snd) := by
  have : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
  have : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
  have : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  let := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
  let := (h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn hk hf hdim g hr).fiberBundle
  let := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g'.toRiemannianMetric)
  let := (h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn hk hf hdim g' hr).fiberBundle
  obtain ⟨Φ, hΦ⟩ := h.exists_bundleDiffeomorph_negativeNormalSpace hn hk hf hdim g' g hr
  refine Φ.continuous.congr fun v ↦ (hΦ v).trans ?_
  rw [LinearEquiv.coe_toContinuousLinearEquiv']

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
      ContMDiffRiemannianMetric J k P fun s ↦ i.isImmersion.NormalSpace s hn) {r : ℕ}
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
        v.proj v.snd⟩ := by
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
            v.proj).toContinuousLinearEquiv v.snd)) := fun v ↦
    (hV'.contMDiffAt_totalSpace_mk le_rfl (b := TotalSpace.proj)
      ((contMDiff_sub_negativeNormalProjection hn h hk hf hdim g').comp
        hV.contMDiff_totalSpace_inclusion v) fun _ ↦
          h.sub_negativeNormalProjection_apply_mem hn _ _).congr_of_eventuallyEq
      (.of_forall fun w ↦ TotalSpace.mk_inj.mpr <| Subtype.ext <| by
        simpa using h.projection_positiveNormalSpace_apply hn g'.toRiemannianMetric
          (w.snd : i.isImmersion.NormalSpace w.proj hn))
  exact ⟨bundleDiffeomorph (fun s ↦ (h.positiveNormalSpaceEquiv hn g.toRiemannianMetric
    g'.toRiemannianMetric s).toContinuousLinearEquiv) hΦ, fun v ↦ by simp⟩

/-- **A change of fibre metric is a `C^k` automorphism of the normal bundle.** Let `i` be a
nondegenerate critical submanifold of `f`, with `f` of class `C^{k+2}` along it and `i` of class
`C^{k+1}`, and let `g₀` and `g₁` be two `C^k` fibre metrics on the normal bundle, with fibre model
`P`. Then the change of fibre metric `normalMetricChange g₀ g₁`, which carries the negative and
positive normal spaces relative to `g₀` onto those relative to `g₁`
(`map_negativeNormalSpace_normalMetricChange` and `map_positiveNormalSpace_normalMetricChange`),
induces a `C^k` map of total spaces. No condition on the indices is needed.

So it is a `C^k` automorphism of the normal bundle with `C^k` inverse
(`normalMetricChangeDiffeomorph`), which carries the negative normal bundle of `g₀` onto that of
`g₁` and the positive normal bundle of `g₀` onto that of `g₁`, fibre by fibre. Unlike
`exists_bundleDiffeomorph_negativeNormalSpace` and `exists_bundleDiffeomorph_positiveNormalSpace`,
it transports both normal bundles at once. -/
theorem contMDiff_normalMetricChange
    (h : i.IsNondegenerateCriticalSubmanifold f) (hk : k + 1 ≤ n)
    (hf : ∀ s, ContMDiffAt I 𝓘(ℝ) (k + 2) f (i s))
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g₀ g₁ : haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
      haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
      letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J k P fun s ↦ i.isImmersion.NormalSpace s hn) :
    haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
    haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
    haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    ContMDiff (J.prod 𝓘(ℝ, P)) (J.prod 𝓘(ℝ, P)) k
      (fun v : TotalSpace P (fun s ↦ i.isImmersion.NormalSpace s hn) ↦
        TotalSpace.mk' P (E := fun s ↦ i.isImmersion.NormalSpace s hn) v.proj
          (h.normalMetricChange hn g₀.toRiemannianMetric g₁.toRiemannianMetric v.proj v.snd)) := by
  have : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
  have : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
  have : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  -- The change of metric is the sum of the composites of the projections for `g₀` and for `g₁`
  -- (`normalMetricChange_apply`), and each projection is a `C^k` map of total spaces.
  have hA := (contMDiff_negativeNormalProjection hn h hk hf hdim g₁).comp
    (contMDiff_negativeNormalProjection hn h hk hf hdim g₀)
  have hB := (contMDiff_sub_negativeNormalProjection hn h hk hf hdim g₁).comp
    (contMDiff_sub_negativeNormalProjection hn h hk hf hdim g₀)
  exact (hA.add_sectionAlong hB).congr fun v ↦ by rw [normalMetricChange_apply]

/-- **The change of fibre metric as a `C^k` automorphism of the normal bundle.** For two `C^k`
fibre metrics `g₀` and `g₁` on the normal bundle, this is the `C^k` diffeomorphism of the total
space which is the change of fibre metric `normalMetricChange g₀ g₁` on each fibre
(`contMDiff_normalMetricChange`). It carries the negative and positive normal bundles of `g₀` onto
those of `g₁` (`map_negativeNormalSpace_normalMetricChange` and
`map_positiveNormalSpace_normalMetricChange`). -/
def normalMetricChangeDiffeomorph
    (h : i.IsNondegenerateCriticalSubmanifold f) (hk : k + 1 ≤ n)
    (hf : ∀ s, ContMDiffAt I 𝓘(ℝ) (k + 2) f (i s))
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g₀ g₁ : haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
      haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
      letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J k P fun s ↦ i.isImmersion.NormalSpace s hn) :
    haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
    haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
    haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    TotalSpace P (fun s ↦ i.isImmersion.NormalSpace s hn) ≃ₘ^k⟮J.prod 𝓘(ℝ, P), J.prod 𝓘(ℝ, P)⟯
      TotalSpace P (fun s ↦ i.isImmersion.NormalSpace s hn) :=
  haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
  haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
  haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
  letI := i.normalSpaceFiberBundle hn hdim
  letI := i.normalSpaceVectorBundle hn hdim
  bundleDiffeomorph
    (fun s ↦ (h.normalMetricChange hn g₀.toRiemannianMetric g₁.toRiemannianMetric
      s).toContinuousLinearEquiv)
    (h.contMDiff_normalMetricChange hn hk hf hdim g₀ g₁)

/-- The change of fibre metric as an automorphism of the normal bundle keeps the base point and
applies `normalMetricChange g₀ g₁` in the fibre. -/
@[simp]
theorem normalMetricChangeDiffeomorph_apply
    (h : i.IsNondegenerateCriticalSubmanifold f) (hk : k + 1 ≤ n)
    (hf : ∀ s, ContMDiffAt I 𝓘(ℝ) (k + 2) f (i s))
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g₀ g₁ : haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
      haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
      letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J k P fun s ↦ i.isImmersion.NormalSpace s hn)
    (v : TotalSpace P fun s ↦ i.isImmersion.NormalSpace s hn) :
    haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
    haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
    haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    h.normalMetricChangeDiffeomorph hn hk hf hdim g₀ g₁ v =
      ⟨v.proj, h.normalMetricChange hn g₀.toRiemannianMetric g₁.toRiemannianMetric v.proj v.snd⟩ :=
  haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
  haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
  haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
  letI := i.normalSpaceFiberBundle hn hdim
  letI := i.normalSpaceVectorBundle hn hdim
  bundleDiffeomorph_apply _ _ v

/-- The inverse of the change of fibre metric as an automorphism of the normal bundle keeps the
base point and applies the inverse of `normalMetricChange g₀ g₁` in the fibre
(`normalMetricChange_symm_apply`). -/
@[simp]
theorem normalMetricChangeDiffeomorph_symm_apply
    (h : i.IsNondegenerateCriticalSubmanifold f) (hk : k + 1 ≤ n)
    (hf : ∀ s, ContMDiffAt I 𝓘(ℝ) (k + 2) f (i s))
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g₀ g₁ : haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
      haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
      letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J k P fun s ↦ i.isImmersion.NormalSpace s hn)
    (v : TotalSpace P fun s ↦ i.isImmersion.NormalSpace s hn) :
    haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
    haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
    haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    (h.normalMetricChangeDiffeomorph hn hk hf hdim g₀ g₁).symm v =
      ⟨v.proj,
        (h.normalMetricChange hn g₀.toRiemannianMetric g₁.toRiemannianMetric v.proj).symm v.snd⟩ :=
  haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
  haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
  haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
  letI := i.normalSpaceFiberBundle hn hdim
  letI := i.normalSpaceVectorBundle hn hdim
  bundleDiffeomorph_symm_apply _ _ v

/-- **The normal bundle of a Morse–Bott submanifold is the sum of its negative and positive normal
bundles.** Let `i` be a nondegenerate critical submanifold of `f`, with `f` of class `C^{k+2}`
along it and `i` of class `C^{k+1}`, and let `g` be a `C^k` fibre metric on its normal bundle `ν`.
If the Morse indices of `f` and of `-f` are `r` and `r'` at every point of the submanifold, then
`(s, u, v) ↦ (s, u + v)` is a `C^k` diffeomorphism from the total space of the direct-sum bundle
`ν⁻ ×ᵇ ν⁺` of the negative and positive normal bundles relative to `g`
(`hasLocalContMDiffSubbundleFrames_negativeNormalSpace` and
`hasLocalContMDiffSubbundleFrames_positiveNormalSpace`) onto the total space of `ν`. -/
theorem exists_bundleDiffeomorph_prod_negativeNormalSpace_positiveNormalSpace
    (h : i.IsNondegenerateCriticalSubmanifold f) (hk : k + 1 ≤ n)
    (hf : ∀ s, ContMDiffAt I 𝓘(ℝ) (k + 2) f (i s))
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g : haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
      haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
      letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J k P fun s ↦ i.isImmersion.NormalSpace s hn) {r r' : ℕ}
    (hr : ∀ s, manifoldMorseIndex I f (i s) = r) (hr' : ∀ s, manifoldMorseIndex I (-f) (i s) = r') :
    haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
    haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
    haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
    letI := (h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn hk hf hdim g hr).fiberBundle
    letI := subbundleTopology P (F' := Fin r' → ℝ) (h.positiveNormalSpace hn g.toRiemannianMetric)
    letI := (h.hasLocalContMDiffSubbundleFrames_positiveNormalSpace hn hk hf hdim g hr').fiberBundle
    ∃ Φ : TotalSpace ((Fin r → ℝ) × (Fin r' → ℝ))
          ((fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s) ×ᵇ
            fun s ↦ h.positiveNormalSpace hn g.toRiemannianMetric s)
        ≃ₘ^k⟮J.prod 𝓘(ℝ, (Fin r → ℝ) × (Fin r' → ℝ)), J.prod 𝓘(ℝ, P)⟯
        TotalSpace P (fun s ↦ i.isImmersion.NormalSpace s hn),
      ∀ v, Φ v = ⟨v.proj, (v.snd.1 : i.isImmersion.NormalSpace v.proj hn) + v.snd.2⟩ := by
  have : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
  have : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
  have : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  have : IsManifold I (k + 1) M := .of_le (n := k + 2) (by gcongr; exact one_le_two)
  let := i.normalSpaceContMDiffVectorBundle hn hk hdim
  exact (h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn hk hf hdim g hr
    ).exists_bundleDiffeomorph_prod_of_isCompl
    (h.hasLocalContMDiffSubbundleFrames_positiveNormalSpace hn hk hf hdim g hr')
    (h.isCompl_negativeNormalSpace_positiveNormalSpace hn _ _)

end TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold

/-! ### Smooth Morse–Bott submanifolds -/

namespace TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' H' S : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S] [IsManifold J ∞ S]
  {f : M → ℝ} {i : SmoothEmbedding J I ∞ S M} (hn : (∞ : ℕ∞ω) ≠ 0)
  [I.Boundaryless] [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
  {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- **The negative normal bundle of a smooth Morse–Bott submanifold.** For a smooth function `f`
and a smooth fibre metric `g` on the normal bundle of a nondegenerate critical submanifold of
constant Morse index `r`, the negative normal spaces relative to `g` have continuous local frames
of size `r`: they form the negative normal bundle, a topological vector bundle of rank `r`
(`TauCeti.HasLocalSubbundleFrames.vectorBundle`). This is the smooth case of
`hasLocalContMDiffSubbundleFrames_negativeNormalSpace`. -/
theorem hasLocalSubbundleFrames_negativeNormalSpace
    (h : i.IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f)
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J ∞ P fun s ↦ i.isImmersion.NormalSpace s hn) {r : ℕ}
    (hr : ∀ s, manifoldMorseIndex I f (i s) = r) :
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    HasLocalSubbundleFrames P (Fin r) (h.negativeNormalSpace hn g.toRiemannianMetric) := by
  have : IsManifold I (∞ + 2) M := .of_le (n := ∞) (by simp)
  have : IsManifold J (∞ + 1) S := by simpa using (inferInstance : IsManifold J ∞ S)
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  exact (h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn (k := ∞) (by simp)
    (fun s ↦ hfs.contMDiffAt.of_le (by simp)) hdim g hr).hasLocalSubbundleFrames

end TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold

/-! ### The rank of the negative normal bundle -/

namespace TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' S : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S]
  {f : M → ℝ} {n : ℕ∞ω} {i : SmoothEmbedding J I n S M} (hn : n ≠ 0)
  [I.Boundaryless] [IsManifold I 2 M] [FiniteDimensional ℝ E] {P : Type*}

/-- **The rank of the negative normal bundle is the Morse index.** If the negative normal spaces
of a nondegenerate critical submanifold relative to a fibre metric `g` have continuous local frames
of size `r`, then the Morse index of `f` is `r` all along the submanifold, since every negative
normal space has the dimension of the index (`finrank_negativeNormalSpace`). This is the converse
of `hasLocalSubbundleFrames_negativeNormalSpace`. -/
theorem manifoldMorseIndex_eq_of_hasLocalSubbundleFrames
    (h : i.IsNondegenerateCriticalSubmanifold f)
        (g : RiemannianMetric fun s ↦ i.isImmersion.NormalSpace s hn)
    {r : ℕ} (hV : HasLocalSubbundleFrames P (Fin r) (h.negativeNormalSpace hn g)) (s : S) :
    manifoldMorseIndex I f (i s) = r := by
  rw [← h.finrank_negativeNormalSpace hn g, hV.finrank_eq, Fintype.card_fin]

end TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold
