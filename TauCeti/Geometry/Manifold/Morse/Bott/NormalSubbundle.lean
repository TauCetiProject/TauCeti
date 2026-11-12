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

The subbundles depend on the metric `g`, but their ranks do not, and neither do their isomorphism
classes: for two `C^k` fibre metrics `g₀` and `g₁`, the change of fibre metric
`IsNondegenerateCriticalSubmanifold.normalMetricChange`, which carries the negative and positive
normal spaces of `g₀` onto those of `g₁`, is a `C^k` automorphism of the normal bundle
(`IsNondegenerateCriticalSubmanifold.contMDiff_normalMetricChange` and
`IsNondegenerateCriticalSubmanifold.normalMetricChangeDiffeomorph`).

No eigenbasis of the normal Hessian is chosen. In the preferred normal-bundle trivialization at
`s₀`, with fibre model `P`, the metric becomes a `C^k` family `G` of bilinear forms on `P`
(`Bundle.Trivialization.contMDiffOn_compl₁₂_symmₗ`). The projections onto the negative relative
spectral subspaces of the normal Hessian with respect to `G`, along the positive ones, are then a
`C^k` family of operators on `P` whose ranges and kernels read the negative and positive normal
spaces in the trivialization
(`IsNondegenerateCriticalSubmanifold.exists_contMDiffOn_negativeNormalProjection`), and a `C^k`
family of operators of constant rank has `C^k` local frames of its ranges
(`Bundle.Trivialization.exists_isSubbundleFrameOn_map_symmₗ`).

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

/-! ### Independence of the fibre metric -/

omit [FiniteDimensional ℝ E'] [FiniteDimensional ℝ P] in
/-- Read in a linear isomorphism `L` which carries the range and the kernel of an idempotent `p`
into the negative and positive normal spaces, the projection onto the negative normal space along
the positive one is `p`. -/
private theorem projection_negativeNormalSpace_symm_apply [IsManifold I 2 M]
    (h : i.IsNondegenerateCriticalSubmanifold f) (g : RiemannianMetric fun s ↦ i.NormalSpace s hn)
    {s : S} {p : P →L[ℝ] P} (hp : IsIdempotentElem p) (L : i.NormalSpace s hn ≃L[ℝ] P)
    (hneg : ∀ w ∈ p.range, L.symm w ∈ h.negativeNormalSpace hn g s)
    (hpos : ∀ w ∈ p.ker, L.symm w ∈ h.positiveNormalSpace hn g s) (w : P) :
    (h.negativeNormalSpace hn g s).projection (h.positiveNormalSpace hn g s)
        (h.isCompl_negativeNormalSpace_positiveNormalSpace hn g g s) (L.symm w) =
      L.symm (p w) := by
  -- Split `w` along `p`: its two parts are carried into the negative and positive normal spaces.
  have hpp : p (p w) = p w := congr($hp.eq w)
  have hpw : w - p w ∈ p.ker := by simp [LinearMap.mem_ker, hpp]
  have hw : L.symm w = L.symm (p w) + L.symm (w - p w) := by rw [← map_add, add_sub_cancel]
  rw [hw, map_add, Submodule.projection_apply_of_mem_left _ (hneg (p w) ⟨w, rfl⟩),
    Submodule.projection_apply_of_mem_right _ (hpos _ hpw), add_zero]

/-- **A change of fibre metric is a `C^k` automorphism of the normal bundle.** Let `i` be a
nondegenerate critical submanifold of `f`, with `f` of class `C^{k+2}` along it and `i` of class
`C^{k+1}`, and let `g₀` and `g₁` be two `C^k` fibre metrics on the normal bundle, with fibre model
`P`. Then the change of fibre metric `normalMetricChange g₀ g₁`, which carries the negative and
positive normal spaces relative to `g₀` onto those relative to `g₁`
(`map_negativeNormalSpace_normalMetricChange` and `map_positiveNormalSpace_normalMetricChange`),
induces a `C^k` map of total spaces. No condition on the indices is needed.

So it is a `C^k` automorphism of the normal bundle with `C^k` inverse
(`normalMetricChangeDiffeomorph`), which carries the negative normal bundle of `g₀` onto that of
`g₁` and the positive normal bundle of `g₀` onto that of `g₁`, fibre by fibre: up to isomorphism,
the negative and positive normal bundles do not depend on the fibre metric. -/
theorem contMDiff_normalMetricChange
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
    ContMDiff (J.prod 𝓘(ℝ, P)) (J.prod 𝓘(ℝ, P)) k
      (fun v : TotalSpace P (fun s ↦ i.NormalSpace s hn) ↦
        TotalSpace.mk' P (E := fun s ↦ i.NormalSpace s hn) v.proj
          (h.normalMetricChange hn g₀.toRiemannianMetric g₁.toRiemannianMetric v.proj v.2)) := by
  have : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
  have : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
  have : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  have : IsManifold I (k + 1) M := .of_le (n := k + 2) (by gcongr; exact one_le_two)
  let := i.normalSpaceContMDiffVectorBundle hn hk hdim
  set T : ∀ s, i.NormalSpace s hn →L[ℝ] i.NormalSpace s hn := fun s ↦
    LinearMap.toContinuousLinearMap
      (h.normalMetricChange hn g₀.toRiemannianMetric g₁.toRiemannianMetric s : _ →ₗ[ℝ] _)
  refine (contMDiff_hom_bundle_iff T).1 fun s₀ ↦ ?_
  -- Read in the trivialization at `s₀`, the change of metric is `p₁ p₀ + (1 - p₁) (1 - p₀)` for
  -- the `C^k` families `pⱼ` of projections of the fibre model describing the two splittings.
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  obtain ⟨p₀, hp₀, hps₀⟩ := exists_contMDiffOn_negativeNormalSpace_eq_map hn h hk hf hdim g₀ s₀
  obtain ⟨p₁, hp₁, hps₁⟩ := exists_contMDiffOn_negativeNormalSpace_eq_map hn h hk hf hdim g₁ s₀
  set e := trivializationAt P (fun s ↦ i.NormalSpace s hn) s₀
  have hs₀ : s₀ ∈ e.baseSet := mem_baseSet_trivializationAt P _ s₀
  have hU : ContMDiffOn J 𝓘(ℝ, P →L[ℝ] P) k
      (fun s ↦ p₁ s * p₀ s + (1 - p₁ s) * (1 - p₀ s)) e.baseSet := by
    simp only [ContinuousLinearMap.mul_def]
    exact (hp₁.clm_comp hp₀).add ((contMDiffOn_const.sub hp₁).clm_comp
      (contMDiffOn_const.sub hp₀))
  refine (hU.contMDiffAt (e.open_baseSet.mem_nhds hs₀)).congr_of_eventuallyEq ?_
  filter_upwards [e.open_baseSet.mem_nhds hs₀] with s hs
  rw [ContinuousLinearMap.inCoordinates_eq hs hs]
  set L := e.continuousLinearEquivAt ℝ s hs
  have hL (w : P) : L.symm w = e.symmₗ ℝ s w := by
    rw [e.symmₗ_apply hs, congr_fun (e.symm_continuousLinearEquivAt_eq hs) w, e.symmL_apply hs]
  -- Each projection onto a negative normal space, read in `L`, is the corresponding projection of
  -- the fibre model.
  have hpL {g : ContMDiffRiemannianMetric J k P fun s ↦ i.NormalSpace s hn} {p : P →L[ℝ] P}
      (hp : IsIdempotentElem p)
      (hneg : h.negativeNormalSpace hn g.toRiemannianMetric s = p.range.map (e.symmₗ ℝ s))
      (hpos : h.positiveNormalSpace hn g.toRiemannianMetric s = p.ker.map (e.symmₗ ℝ s))
      (w : P) :
      L.symm (p w) = (h.negativeNormalSpace hn g.toRiemannianMetric s).projection
          (h.positiveNormalSpace hn g.toRiemannianMetric s)
          (h.isCompl_negativeNormalSpace_positiveNormalSpace hn _ _ s) (L.symm w) :=
    (projection_negativeNormalSpace_symm_apply hn h _ hp L
      (fun w hw ↦ hneg ▸ hL w ▸ Submodule.mem_map_of_mem hw)
      (fun w hw ↦ hpos ▸ hL w ▸ Submodule.mem_map_of_mem hw) w).symm
  ext w
  apply L.symm.injective
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply, T, LinearMap.coe_toContinuousLinearMap',
    LinearEquiv.coe_coe]
  exact (h.normalMetricChange_symm_apply_eq hn _ _ L.toLinearEquiv
    (hpL (hps₀ s hs).1 (hps₀ s hs).2.1 (hps₀ s hs).2.2.1)
    (hpL (hps₁ s hs).1 (hps₁ s hs).2.1 (hps₁ s hs).2.2.1) w).symm

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
      ContMDiffRiemannianMetric J k P fun s ↦ i.NormalSpace s hn) :
    haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
    haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
    haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    TotalSpace P (fun s ↦ i.NormalSpace s hn) ≃ₘ^k⟮J.prod 𝓘(ℝ, P), J.prod 𝓘(ℝ, P)⟯
      TotalSpace P (fun s ↦ i.NormalSpace s hn) :=
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
      ContMDiffRiemannianMetric J k P fun s ↦ i.NormalSpace s hn)
    (v : TotalSpace P fun s ↦ i.NormalSpace s hn) :
    haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
    haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
    haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    h.normalMetricChangeDiffeomorph hn hk hf hdim g₀ g₁ v =
      ⟨v.proj, h.normalMetricChange hn g₀.toRiemannianMetric g₁.toRiemannianMetric v.proj v.2⟩ :=
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
      ContMDiffRiemannianMetric J k P fun s ↦ i.NormalSpace s hn)
    (v : TotalSpace P fun s ↦ i.NormalSpace s hn) :
    haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
    haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
    haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    (h.normalMetricChangeDiffeomorph hn hk hf hdim g₀ g₁).symm v =
      ⟨v.proj,
        (h.normalMetricChange hn g₀.toRiemannianMetric g₁.toRiemannianMetric v.proj).symm v.2⟩ :=
  haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
  haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
  haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
  letI := i.normalSpaceFiberBundle hn hdim
  letI := i.normalSpaceVectorBundle hn hdim
  bundleDiffeomorph_symm_apply _ _ v

end TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold
