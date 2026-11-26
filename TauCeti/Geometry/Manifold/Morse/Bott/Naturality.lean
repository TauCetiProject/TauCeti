/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.NegativeOrientation
public import TauCeti.Geometry.Manifold.RegularValue
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Map
import TauCeti.Geometry.Manifold.Morse.Submersion
import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.Map
import TauCeti.Geometry.Manifold.VectorBundle.Hom.Basic

/-!
# Negative normal bundles of Morse–Bott submanifolds along maps

Let `σ : M → M'` be a map between boundaryless manifolds, `f : M' → ℝ`, and let `i : S → M` and
`i' : S → M'` be embeddings of the same manifold with `σ ∘ i = i'`, such that `i` is a
nondegenerate critical submanifold of `f ∘ σ` and `i'` one of `f`. The main case is a
diffeomorphism `σ`, which carries the critical submanifolds of `f ∘ σ` to those of `f`. This file
shows that the negative normal bundles of `i` and `i'`, and their orientation local systems, agree,
when `σ` is smooth enough and its differential is surjective at the points of `i`.

The differential of `σ` induces a map of normal bundles (`TauCeti.SmoothEmbedding.normalMap`),
which carries the normal Hessian of `f` along `i'` back to the normal Hessian of `f ∘ σ` along `i`
by the second-order chain rule at a critical point
(`IsCriticalSubmanifold.normalHessian_normalMap`, in the namespace `TauCeti.SmoothEmbedding`).
So the Morse indices along `i` and `i'` agree
(`TauCeti.IsRegularPoint.manifoldMorseIndex_comp`), and for fibre metrics `g` on the normal bundle
of `i` and `g'` on that of `i'`, following the normal map by the projection onto the negative
normal space of `g'` along the positive one is a linear isomorphism `ν⁻_g(i) ≃ ν⁻_{g'}(i')` on each
fibre (`IsNondegenerateCriticalSubmanifold.negativeNormalSpaceEquivOfComp`): the normal Hessian of
`i'` is negative definite on the image of `ν⁻_g(i)` and positive definite on the positive normal
space of `g'`. The two metrics need not correspond under `σ`. When `σ` is `C^{k+2}`, `f` is
`C^{k+2}` along `i'` and the metrics are `C^k`, these isomorphisms form a `C^k` diffeomorphism of
the total spaces of the negative normal bundles
(`IsNondegenerateCriticalSubmanifold.exists_bundleDiffeomorph_negativeNormalSpace_of_comp`). Hence
the orientation local systems `o(ν⁻)` of the two negative normal bundles are isomorphic
(`IsNondegenerateCriticalSubmanifold.negativeNormalSpaceSignLocalSystemIsoOfComp`), and one bundle
is orientable exactly when the other is
(`nonempty_vectorBundleOrientation_negativeNormalSpace_iff_of_comp`, in the namespace
`TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold`).

Across a critical level, the relative homology of the sublevels is the homology of the critical
submanifolds twisted by these orientation local systems and shifted by their indices. So the
isomorphisms of orientation local systems here are the input needed to identify the twisted
homology of the critical submanifolds of `f ∘ σ` with that of the corresponding critical
submanifolds of `f`, as the diffeomorphism invariance of the critical-band spectral sequence
requires; this file does not state that homology comparison.

## Main definitions

In the namespace `TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold`:

* `negativeNormalSpaceEquivOfComp`: the fibrewise isomorphism `ν⁻_g(i) ≃ ν⁻_{g'}(i')`.
* `negativeNormalSpaceSignLocalSystemIsoOfComp`: the isomorphism of the orientation local systems
  of the two negative normal bundles.

## Main results

* `TauCeti.SmoothEmbedding.IsCriticalSubmanifold.normalHessian_normalMap`: the normal map induced
  by `dσ` carries the normal Hessian along `i'` back to the normal Hessian along `i`.

In the namespace `TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold`:

* `hasLocalContMDiffSubbundleFrames_negativeNormalSpace_of_comp`: the negative normal spaces of `i`
  form a bundle whose rank is the Morse index along `i'`.
* `contMDiff_negativeNormalSpaceEquivOfComp` and
  `exists_bundleDiffeomorph_negativeNormalSpace_of_comp`: the fibrewise isomorphisms form a `C^k`
  diffeomorphism of total spaces.
* `nonempty_vectorBundleOrientation_negativeNormalSpace_iff_of_comp`: the two negative normal
  bundles are orientable together.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* R. L. Cohen, K. Iga and P. Norbury, *Topics in Morse theory: lecture notes*, 2006, §15.
-/

public section

open Bundle Function Module Set
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.SmoothEmbedding

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M'] [ChartedSpace H' M']
  {F G S : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
  {J : ModelWithCorners ℝ F G} [TopologicalSpace S] [ChartedSpace G S]
  {σ : M → M'} {f : M' → ℝ} {n n' : ℕ∞ω} {i : SmoothEmbedding J I n S M}
  {i' : SmoothEmbedding J I' n' S M'} (hn : n ≠ 0) (hn' : n' ≠ 0) (hσi : σ ∘ i = i')

namespace IsCriticalSubmanifold

variable [I.Boundaryless] [I'.Boundaryless] [IsManifold I 2 M] [IsManifold I' 2 M']

/-- **The normal Hessian along a map.** If `σ ∘ i = i'`, with `i` a critical submanifold of
`f ∘ σ` and `i'` one of `f`, and `σ` is `C²` at `i s`, then the normal map induced by `dσ` carries
the normal Hessian of `f` along `i'` back to the normal Hessian of `f ∘ σ` along `i`. -/
theorem normalHessian_normalMap (h : i.IsCriticalSubmanifold (f ∘ σ))
    (h' : i'.IsCriticalSubmanifold f) {s : S} (hσ : ContMDiffAt I I' 2 σ (i s))
    (v w : i.isImmersion.NormalSpace s hn) :
    h'.normalHessian hn' s (i.normalMap i' (u := fun s ↦ s) hn hn' (.of_eq hσi) v)
        (i.normalMap i' (u := fun s ↦ s) hn hn' (.of_eq hσi) w) =
      h.normalHessian hn s v w := by
  obtain ⟨v, rfl⟩ := i.isImmersion.normalClass_surjective s hn v
  obtain ⟨w, rfl⟩ := i.isImmersion.normalClass_surjective s hn w
  rw [normalMap_normalClass, normalMap_normalClass, normalHessian_normalClass,
    normalHessian_normalClass]
  exact (criticalHessian_comp_apply (φ := σ) (congrFun hσi s) (h'.contMDiffAt s) hσ
    (h'.mem_criticalPoints s) v w).symm

end IsCriticalSubmanifold

namespace IsNondegenerateCriticalSubmanifold

variable [I.Boundaryless] [I'.Boundaryless] [IsManifold I 2 M] [IsManifold I' 2 M']
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
  (h : i.IsNondegenerateCriticalSubmanifold (f ∘ σ))
  (h' : i'.IsNondegenerateCriticalSubmanifold f)
  (g : RiemannianMetric fun s ↦ i.isImmersion.NormalSpace s hn)
  (g' : RiemannianMetric fun s ↦ i'.isImmersion.NormalSpace s hn') {s : S}
  (hσ : ContMDiffAt I I' 2 σ (i s)) (hσs : IsRegularPoint I I' σ (i s))

/-- **The negative normal spaces along a map.** If `σ ∘ i = i'`, with `i` a Morse–Bott
submanifold of `f ∘ σ` and `i'` one of `f`, and `σ` is `C²` at `i s` with surjective differential,
then the negative normal space of `i` at `s` relative to a fibre metric `g` is isomorphic to the
negative normal space of `i'` at `s` relative to a fibre metric `g'`. The isomorphism is the normal
map induced by `dσ` followed by the projection onto the negative normal space of `g'` along the
positive one (`coe_negativeNormalSpaceEquivOfComp_apply`); the two metrics need not correspond
under `dσ`. -/
def negativeNormalSpaceEquivOfComp :
    h.negativeNormalSpace hn g s ≃ₗ[ℝ] h'.negativeNormalSpace hn' g' s :=
  LinearMap.linearEquivOfInjective
    ((h'.negativeNormalProjection hn' g' s ∘ₗ
        (i.normalMap i' (u := fun s ↦ s) hn hn' (.of_eq hσi)).toLinearMap ∘ₗ
          (h.negativeNormalSpace hn g s).subtype).codRestrict _
      fun v ↦ h'.negativeNormalProjection_apply_mem hn' g' _)
    (by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      rintro ⟨v, hv⟩ hv0
      by_contra hne
      have hpos : i.normalMap i' (u := fun s ↦ s) hn hn' (.of_eq hσi) v ∈
          h'.positiveNormalSpace hn' g' s :=
        (h'.negativeNormalProjection_apply_eq_zero_iff hn' g').1 (congrArg Subtype.val hv0)
      have hneg := h.normalHessian_apply_self_neg_of_mem_negativeNormalSpace hn g hv
        fun hv ↦ hne (Subtype.ext hv)
      rw [← h.normalHessian_normalMap hn hn' hσi h'.toIsCriticalSubmanifold hσ] at hneg
      exact hneg.not_ge (h'.normalHessian_apply_self_nonneg_of_mem_positiveNormalSpace hn' g' hpos))
    (by
      have hσis : σ (i s) = i' s := congrFun hσi s
      rw [h.finrank_negativeNormalSpace hn g, h'.finrank_negativeNormalSpace hn' g',
        hσs.manifoldMorseIndex_comp (hσis ▸ h'.contMDiffAt s) hσ (hσis ▸ h'.mem_criticalPoints s),
        hσis])

/-- The identification of the negative normal spaces along a map sends `v` to the component, along
the negative normal space of `g'`, of its image under the normal map induced by `dσ`. -/
@[simp]
theorem coe_negativeNormalSpaceEquivOfComp_apply (v : h.negativeNormalSpace hn g s) :
    (h.negativeNormalSpaceEquivOfComp hn hn' hσi h' g g' hσ hσs v :
        i'.isImmersion.NormalSpace s hn') =
      h'.negativeNormalProjection hn' g' s
        (i.normalMap i' (u := fun s ↦ s) hn hn' (.of_eq hσi) v) :=
  (rfl)

end IsNondegenerateCriticalSubmanifold

/-! ### The negative normal bundles along a map -/

namespace IsNondegenerateCriticalSubmanifold

variable [I.Boundaryless] [I'.Boundaryless] [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
  [FiniteDimensional ℝ F] {P P' : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup P'] [NormedSpace ℝ P'] [FiniteDimensional ℝ P']
  {k : ℕ∞ω} [IsManifold I (k + 2) M] [IsManifold I' (k + 2) M'] [IsManifold J (k + 1) S]

omit [FiniteDimensional ℝ E'] in
include hσi in
/-- **The negative normal spaces along a map form a bundle of the same rank.** If `σ ∘ i = i'`,
with `i` a Morse–Bott submanifold of `f ∘ σ` and `i'` a critical submanifold of `f`, `σ` of class
`C^{k+2}` with surjective differential at the points of `i`, and `f` of class `C^{k+2}` along `i'`
and of Morse index `r` at every point of `i'`, then the negative normal spaces of `i` relative to a
`C^k` fibre metric have `C^k` local frames of size `r`: this is
`hasLocalContMDiffSubbundleFrames_negativeNormalSpace` for `f ∘ σ`, whose regularity and index
along `i` are those of `f` along `i'`. -/
theorem hasLocalContMDiffSubbundleFrames_negativeNormalSpace_of_comp
    (h : i.IsNondegenerateCriticalSubmanifold (f ∘ σ))
    (h' : i'.IsCriticalSubmanifold f) (hk : k + 1 ≤ n)
    (hσ : ∀ s, ContMDiffAt I I' (k + 2) σ (i s)) (hσs : ∀ s, IsRegularPoint I I' σ (i s))
    (hf : ∀ s, ContMDiffAt I' 𝓘(ℝ) (k + 2) f (i' s))
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ F)
    (g : haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
      haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
      letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J k P fun s ↦ i.isImmersion.NormalSpace s hn) {r : ℕ}
    (hr : ∀ s, manifoldMorseIndex I' f (i' s) = r) :
    haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
    haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
    haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    HasLocalContMDiffSubbundleFrames J k P (Fin r)
      (h.negativeNormalSpace hn g.toRiemannianMetric) := by
  have : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
  have : IsManifold I' 2 M' := .of_le (n := k + 2) le_add_self
  refine h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn hk
    (fun s ↦ (hf s).comp_of_eq (hσ s) (congrFun hσi s)) hdim g fun s ↦ ?_
  have hσis : σ (i s) = i' s := congrFun hσi s
  rw [← hr s, ← hσis]
  exact (hσs s).manifoldMorseIndex_comp (hσis ▸ h'.contMDiffAt s) ((hσ s).of_le le_add_self)
    (hσis ▸ h'.mem_criticalPoints s)

/-- **The identification of the negative normal bundles along a map is smooth.** In the setting of
`hasLocalContMDiffSubbundleFrames_negativeNormalSpace_of_comp`, with moreover `i'` a Morse–Bott
submanifold of `f` and `g'` a `C^k` fibre metric on its normal bundle, the fibrewise isomorphisms
`negativeNormalSpaceEquivOfComp` form a `C^k` map from the total space of the negative normal
bundle of `i` relative to `g` to that of `i'` relative to `g'`. Read in the normal bundles, it is
the `C^k` map of normal bundles induced by `σ` (`contMDiff_normalBundleMap`) followed by the
projection onto the negative normal bundle of `g'` (`contMDiff_negativeNormalProjection`). -/
theorem contMDiff_negativeNormalSpaceEquivOfComp
    (h : i.IsNondegenerateCriticalSubmanifold (f ∘ σ))
    (h' : i'.IsNondegenerateCriticalSubmanifold f) (hk : k + 1 ≤ n) (hk' : k + 1 ≤ n')
    (hσ : ContMDiff I I' (k + 2) σ) (hσs : ∀ s, IsRegularPoint I I' σ (i s))
    (hf : ∀ s, ContMDiffAt I' 𝓘(ℝ) (k + 2) f (i' s))
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ F)
    (hdim' : finrank ℝ P' = finrank ℝ E' - finrank ℝ F)
    (g : haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
      haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
      letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J k P fun s ↦ i.isImmersion.NormalSpace s hn)
    (g' : haveI : IsManifold I' 1 M' := .of_le (n := k + 2) (one_le_two.trans le_add_self)
      haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
      letI := i'.normalSpaceFiberBundle hn' hdim'
      letI := i'.normalSpaceVectorBundle hn' hdim'
      ContMDiffRiemannianMetric J k P' fun s ↦ i'.isImmersion.NormalSpace s hn') {r : ℕ}
    (hr : ∀ s, manifoldMorseIndex I' f (i' s) = r) :
    haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
    haveI : IsManifold I' 2 M' := .of_le (n := k + 2) le_add_self
    haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
    haveI : IsManifold I' 1 M' := .of_le (n := k + 2) (one_le_two.trans le_add_self)
    haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    letI := i'.normalSpaceFiberBundle hn' hdim'
    letI := i'.normalSpaceVectorBundle hn' hdim'
    letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
    letI := (h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace_of_comp hn hσi
      h'.toIsCriticalSubmanifold hk (fun s ↦ hσ (i s)) hσs hf hdim g hr).fiberBundle
    letI := subbundleTopology P' (F' := Fin r → ℝ)
      (h'.negativeNormalSpace hn' g'.toRiemannianMetric)
    letI := (h'.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn' hk' hf hdim' g'
      hr).fiberBundle
    ContMDiff (J.prod 𝓘(ℝ, Fin r → ℝ)) (J.prod 𝓘(ℝ, Fin r → ℝ)) k
      (fun v : TotalSpace (Fin r → ℝ) (fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s) ↦
        TotalSpace.mk' (Fin r → ℝ)
          (E := fun s ↦ h'.negativeNormalSpace hn' g'.toRiemannianMetric s) v.proj
          (h.negativeNormalSpaceEquivOfComp hn hn' hσi h' g.toRiemannianMetric
            g'.toRiemannianMetric ((hσ (i v.proj)).of_le le_add_self) (hσs v.proj) v.snd)) := by
  have : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
  have : IsManifold I' 2 M' := .of_le (n := k + 2) le_add_self
  have : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
  have : IsManifold I' 1 M' := .of_le (n := k + 2) (one_le_two.trans le_add_self)
  have : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
  have : IsManifold I (k + 1) M := .of_le (n := k + 2) (by gcongr; exact one_le_two)
  have : IsManifold I' (k + 1) M' := .of_le (n := k + 2) (by gcongr; exact one_le_two)
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  let := i.normalSpaceContMDiffVectorBundle hn hk hdim
  let := i'.normalSpaceFiberBundle hn' hdim'
  let := i'.normalSpaceVectorBundle hn' hdim'
  let := i'.normalSpaceContMDiffVectorBundle hn' hk' hdim'
  have hV := h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace_of_comp hn hσi
    h'.toIsCriticalSubmanifold hk (fun s ↦ hσ (i s)) hσs hf hdim g hr
  have hV' := h'.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn' hk' hf hdim' g' hr
  let := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
  let := hV.fiberBundle
  have := hV.vectorBundle
  let := subbundleTopology P' (F' := Fin r → ℝ) (h'.negativeNormalSpace hn' g'.toRiemannianMetric)
  let := hV'.fiberBundle
  have := hV'.vectorBundle
  -- Read in the normal bundles, the map is the inclusion of the negative normal bundle of `i`,
  -- followed by the map of normal bundles induced by `σ` and the projection onto the negative
  -- normal bundle of `i'`.
  have hN : ContMDiff (J.prod 𝓘(ℝ, P)) (J.prod 𝓘(ℝ, P')) k
      (fun p : TotalSpace P (fun s ↦ i.isImmersion.NormalSpace s hn) ↦
        TotalSpace.mk' P' (E := fun s ↦ i'.isImmersion.NormalSpace s hn') p.proj
          (i.normalMap i' (u := fun s ↦ s) hn hn' (.of_eq hσi) p.snd)) :=
    (contMDiff_normalBundleMap (P := P) (P' := P') i i' hn hn' hk hk' hdim hdim'
      (u := fun s ↦ s) (hσ.of_le (by gcongr; exact one_le_two)) hσi).congr fun p ↦ by
        rw [normalBundleMap_apply]
  exact fun v ↦ (hV'.contMDiffAt_totalSpace_mk le_rfl (b := TotalSpace.proj)
    ((contMDiff_negativeNormalProjection hn' h' hk' hf hdim' g').comp
      (hN.comp hV.contMDiff_totalSpace_inclusion) v) fun _ ↦
        h'.negativeNormalProjection_apply_mem hn' _ _).congr_of_eventuallyEq
    (.of_forall fun w ↦ TotalSpace.mk_inj.mpr <| Subtype.ext <| by simp)

/-- **The negative normal bundles along a map are isomorphic.** In the setting of
`contMDiff_negativeNormalSpaceEquivOfComp`, the negative normal bundle of `i` relative to `g` and
that of `i'` relative to `g'` are isomorphic `C^k` vector bundles over `S`: the fibrewise
isomorphisms `negativeNormalSpaceEquivOfComp` form a `C^k` diffeomorphism of their total spaces. -/
theorem exists_bundleDiffeomorph_negativeNormalSpace_of_comp
    (h : i.IsNondegenerateCriticalSubmanifold (f ∘ σ))
    (h' : i'.IsNondegenerateCriticalSubmanifold f) (hk : k + 1 ≤ n) (hk' : k + 1 ≤ n')
    (hσ : ContMDiff I I' (k + 2) σ) (hσs : ∀ s, IsRegularPoint I I' σ (i s))
    (hf : ∀ s, ContMDiffAt I' 𝓘(ℝ) (k + 2) f (i' s))
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ F)
    (hdim' : finrank ℝ P' = finrank ℝ E' - finrank ℝ F)
    (g : haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
      haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
      letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J k P fun s ↦ i.isImmersion.NormalSpace s hn)
    (g' : haveI : IsManifold I' 1 M' := .of_le (n := k + 2) (one_le_two.trans le_add_self)
      haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
      letI := i'.normalSpaceFiberBundle hn' hdim'
      letI := i'.normalSpaceVectorBundle hn' hdim'
      ContMDiffRiemannianMetric J k P' fun s ↦ i'.isImmersion.NormalSpace s hn') {r : ℕ}
    (hr : ∀ s, manifoldMorseIndex I' f (i' s) = r) :
    haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
    haveI : IsManifold I' 2 M' := .of_le (n := k + 2) le_add_self
    haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
    haveI : IsManifold I' 1 M' := .of_le (n := k + 2) (one_le_two.trans le_add_self)
    haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    letI := i'.normalSpaceFiberBundle hn' hdim'
    letI := i'.normalSpaceVectorBundle hn' hdim'
    letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
    letI := (h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace_of_comp hn hσi
      h'.toIsCriticalSubmanifold hk (fun s ↦ hσ (i s)) hσs hf hdim g hr).fiberBundle
    letI := subbundleTopology P' (F' := Fin r → ℝ)
      (h'.negativeNormalSpace hn' g'.toRiemannianMetric)
    letI := (h'.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn' hk' hf hdim' g'
      hr).fiberBundle
    ∃ Φ : TotalSpace (Fin r → ℝ) (fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s)
        ≃ₘ^k⟮J.prod 𝓘(ℝ, Fin r → ℝ), J.prod 𝓘(ℝ, Fin r → ℝ)⟯
        TotalSpace (Fin r → ℝ) (fun s ↦ h'.negativeNormalSpace hn' g'.toRiemannianMetric s),
      ∀ v, Φ v = ⟨v.proj, h.negativeNormalSpaceEquivOfComp hn hn' hσi h' g.toRiemannianMetric
        g'.toRiemannianMetric ((hσ (i v.proj)).of_le le_add_self) (hσs v.proj) v.snd⟩ := by
  have : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
  have : IsManifold I' 2 M' := .of_le (n := k + 2) le_add_self
  have : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
  have : IsManifold I' 1 M' := .of_le (n := k + 2) (one_le_two.trans le_add_self)
  have : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  let := i'.normalSpaceFiberBundle hn' hdim'
  let := i'.normalSpaceVectorBundle hn' hdim'
  have hV := h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace_of_comp hn hσi
    h'.toIsCriticalSubmanifold hk (fun s ↦ hσ (i s)) hσs hf hdim g hr
  have hV' := h'.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn' hk' hf hdim' g' hr
  let := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
  let := hV.fiberBundle
  have := hV.vectorBundle
  let := subbundleTopology P' (F' := Fin r → ℝ) (h'.negativeNormalSpace hn' g'.toRiemannianMetric)
  let := hV'.fiberBundle
  have := hV'.vectorBundle
  have hΦ := h.contMDiff_negativeNormalSpaceEquivOfComp hn hn' hσi h' hk hk' hσ hσs hf hdim hdim'
    g g' hr
  refine ⟨bundleDiffeomorph (fun s ↦ (h.negativeNormalSpaceEquivOfComp hn hn' hσi h'
    g.toRiemannianMetric g'.toRiemannianMetric ((hσ (i s)).of_le le_add_self)
      (hσs s)).toContinuousLinearEquiv) (hΦ.congr fun v ↦ by simp), fun v ↦ by simp⟩

/-- The inverses of the identifications `negativeNormalSpaceEquivOfComp` of the negative normal
spaces along a map are `C^k` on the total spaces of the negative normal bundles: the forward map is
a `C^k` family of fibrewise isomorphisms (`contMDiff_negativeNormalSpaceEquivOfComp`), so its
inverse is `C^k` too. -/
theorem contMDiff_negativeNormalSpaceEquivOfComp_symm
    (h : i.IsNondegenerateCriticalSubmanifold (f ∘ σ))
    (h' : i'.IsNondegenerateCriticalSubmanifold f) (hk : k + 1 ≤ n) (hk' : k + 1 ≤ n')
    (hσ : ContMDiff I I' (k + 2) σ) (hσs : ∀ s, IsRegularPoint I I' σ (i s))
    (hf : ∀ s, ContMDiffAt I' 𝓘(ℝ) (k + 2) f (i' s))
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ F)
    (hdim' : finrank ℝ P' = finrank ℝ E' - finrank ℝ F)
    (g : haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
      haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
      letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J k P fun s ↦ i.isImmersion.NormalSpace s hn)
    (g' : haveI : IsManifold I' 1 M' := .of_le (n := k + 2) (one_le_two.trans le_add_self)
      haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
      letI := i'.normalSpaceFiberBundle hn' hdim'
      letI := i'.normalSpaceVectorBundle hn' hdim'
      ContMDiffRiemannianMetric J k P' fun s ↦ i'.isImmersion.NormalSpace s hn') {r : ℕ}
    (hr : ∀ s, manifoldMorseIndex I' f (i' s) = r) :
    haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
    haveI : IsManifold I' 2 M' := .of_le (n := k + 2) le_add_self
    haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
    haveI : IsManifold I' 1 M' := .of_le (n := k + 2) (one_le_two.trans le_add_self)
    haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    letI := i'.normalSpaceFiberBundle hn' hdim'
    letI := i'.normalSpaceVectorBundle hn' hdim'
    letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
    letI := (h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace_of_comp hn hσi
      h'.toIsCriticalSubmanifold hk (fun s ↦ hσ (i s)) hσs hf hdim g hr).fiberBundle
    letI := subbundleTopology P' (F' := Fin r → ℝ)
      (h'.negativeNormalSpace hn' g'.toRiemannianMetric)
    letI := (h'.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn' hk' hf hdim' g'
      hr).fiberBundle
    ContMDiff (J.prod 𝓘(ℝ, Fin r → ℝ)) (J.prod 𝓘(ℝ, Fin r → ℝ)) k
      fun v : TotalSpace (Fin r → ℝ)
        (fun s ↦ h'.negativeNormalSpace hn' g'.toRiemannianMetric s) ↦
      TotalSpace.mk' (Fin r → ℝ) (E := fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s)
        v.proj ((h.negativeNormalSpaceEquivOfComp hn hn' hσi h' g.toRiemannianMetric
          g'.toRiemannianMetric ((hσ (i v.proj)).of_le le_add_self)
            (hσs v.proj)).toContinuousLinearEquiv.symm v.snd) := by
  have : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
  have : IsManifold I' 2 M' := .of_le (n := k + 2) le_add_self
  have : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
  have : IsManifold I' 1 M' := .of_le (n := k + 2) (one_le_two.trans le_add_self)
  have : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  let := i'.normalSpaceFiberBundle hn' hdim'
  let := i'.normalSpaceVectorBundle hn' hdim'
  have hV := h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace_of_comp hn hσi
    h'.toIsCriticalSubmanifold hk (fun s ↦ hσ (i s)) hσs hf hdim g hr
  have hV' := h'.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn' hk' hf hdim' g' hr
  let := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
  let := hV.fiberBundle
  have := hV.vectorBundle
  let := subbundleTopology P' (F' := Fin r → ℝ) (h'.negativeNormalSpace hn' g'.toRiemannianMetric)
  let := hV'.fiberBundle
  have := hV'.vectorBundle
  exact contMDiff_bundle_symm (fun s ↦ (h.negativeNormalSpaceEquivOfComp hn hn' hσi h'
    g.toRiemannianMetric g'.toRiemannianMetric ((hσ (i s)).of_le le_add_self)
      (hσs s)).toContinuousLinearEquiv)
    ((h.contMDiff_negativeNormalSpaceEquivOfComp hn hn' hσi h' hk hk' hσ hσs hf hdim hdim' g g'
      hr).congr fun v ↦ by simp)

/-- **The negative normal bundles along a map are orientable together.** In the setting of
`contMDiff_negativeNormalSpaceEquivOfComp`, the negative normal bundle of `i` relative to `g` is
orientable if and only if that of `i'` relative to `g'` is. -/
theorem nonempty_vectorBundleOrientation_negativeNormalSpace_iff_of_comp
    (h : i.IsNondegenerateCriticalSubmanifold (f ∘ σ))
    (h' : i'.IsNondegenerateCriticalSubmanifold f) (hk : k + 1 ≤ n) (hk' : k + 1 ≤ n')
    (hσ : ContMDiff I I' (k + 2) σ) (hσs : ∀ s, IsRegularPoint I I' σ (i s))
    (hf : ∀ s, ContMDiffAt I' 𝓘(ℝ) (k + 2) f (i' s))
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ F)
    (hdim' : finrank ℝ P' = finrank ℝ E' - finrank ℝ F)
    (g : haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
      haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
      letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J k P fun s ↦ i.isImmersion.NormalSpace s hn)
    (g' : haveI : IsManifold I' 1 M' := .of_le (n := k + 2) (one_le_two.trans le_add_self)
      haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
      letI := i'.normalSpaceFiberBundle hn' hdim'
      letI := i'.normalSpaceVectorBundle hn' hdim'
      ContMDiffRiemannianMetric J k P' fun s ↦ i'.isImmersion.NormalSpace s hn') {r : ℕ}
    (hr : ∀ s, manifoldMorseIndex I' f (i' s) = r) :
    haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
    haveI : IsManifold I' 2 M' := .of_le (n := k + 2) le_add_self
    haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
    haveI : IsManifold I' 1 M' := .of_le (n := k + 2) (one_le_two.trans le_add_self)
    haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    letI := i'.normalSpaceFiberBundle hn' hdim'
    letI := i'.normalSpaceVectorBundle hn' hdim'
    letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
    letI := (h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace_of_comp hn hσi
      h'.toIsCriticalSubmanifold hk (fun s ↦ hσ (i s)) hσs hf hdim g hr).fiberBundle
    haveI := (h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace_of_comp hn hσi
      h'.toIsCriticalSubmanifold hk (fun s ↦ hσ (i s)) hσs hf hdim g hr).vectorBundle
    letI := subbundleTopology P' (F' := Fin r → ℝ)
      (h'.negativeNormalSpace hn' g'.toRiemannianMetric)
    letI := (h'.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn' hk' hf hdim' g'
      hr).fiberBundle
    haveI := (h'.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn' hk' hf hdim' g'
      hr).vectorBundle
    Nonempty (VectorBundleOrientation (Fin r → ℝ)
        (fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s) (Fin r)) ↔
      Nonempty (VectorBundleOrientation (Fin r → ℝ)
        (fun s ↦ h'.negativeNormalSpace hn' g'.toRiemannianMetric s) (Fin r)) := by
  have : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
  have : IsManifold I' 2 M' := .of_le (n := k + 2) le_add_self
  have : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
  have : IsManifold I' 1 M' := .of_le (n := k + 2) (one_le_two.trans le_add_self)
  have : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  let := i'.normalSpaceFiberBundle hn' hdim'
  let := i'.normalSpaceVectorBundle hn' hdim'
  have hV := h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace_of_comp hn hσi
    h'.toIsCriticalSubmanifold hk (fun s ↦ hσ (i s)) hσs hf hdim g hr
  have hV' := h'.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn' hk' hf hdim' g' hr
  let := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
  let := hV.fiberBundle
  have := hV.vectorBundle
  let := subbundleTopology P' (F' := Fin r → ℝ) (h'.negativeNormalSpace hn' g'.toRiemannianMetric)
  let := hV'.fiberBundle
  have := hV'.vectorBundle
  exact VectorBundleOrientation.nonempty_iff_of_fiberwise (F := Fin r → ℝ) (F' := Fin r → ℝ)
    (φ := fun s ↦ (h.negativeNormalSpaceEquivOfComp hn hn' hσi h' g.toRiemannianMetric
      g'.toRiemannianMetric ((hσ (i s)).of_le le_add_self) (hσs s)).toContinuousLinearEquiv)
    (by simp) ((h.contMDiff_negativeNormalSpaceEquivOfComp hn hn' hσi h' hk hk' hσ hσs hf hdim
      hdim' g g' hr).continuous.congr fun v ↦ by simp)

end IsNondegenerateCriticalSubmanifold

end TauCeti.SmoothEmbedding

/-! ### Orientation local systems of the negative normal bundles along a map

Local coefficient systems on `S` with isomorphic values must lie in one universe, so here the models
of `M` and `M'`, which carry the normal spaces, lie in a common universe. -/

namespace TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold

universe u

variable {E : Type u} {H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type u} {H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M'] [ChartedSpace H' M']
  {F G S : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
  {J : ModelWithCorners ℝ F G} [TopologicalSpace S] [ChartedSpace G S]
  {σ : M → M'} {f : M' → ℝ} {n n' : ℕ∞ω} {i : SmoothEmbedding J I n S M}
  {i' : SmoothEmbedding J I' n' S M'} (hn : n ≠ 0) (hn' : n' ≠ 0) (hσi : σ ∘ i = i')
  [I.Boundaryless] [I'.Boundaryless] [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
  [FiniteDimensional ℝ F] {P P' : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup P'] [NormedSpace ℝ P'] [FiniteDimensional ℝ P']
  {k : ℕ∞ω} [IsManifold I (k + 2) M] [IsManifold I' (k + 2) M'] [IsManifold J (k + 1) S]

variable (R : Type*) [Ring R]

/-- **The orientation local systems of the negative normal bundles along a map are isomorphic.**
In the setting of `contMDiff_negativeNormalSpaceEquivOfComp`, the orientation local systems
`o(ν⁻)` of the negative normal bundle of `i` relative to `g` and of `i'` relative to `g'` are
isomorphic: the fibrewise isomorphisms `negativeNormalSpaceEquivOfComp` transport orientations of
fibres. For a diffeomorphism `σ`, this is what is needed to identify the homology with
coefficients in the orientation local system of the negative normal bundle of the critical
submanifold `i'` of `f` with that of its preimage `i` under `σ`, a critical submanifold of
`f ∘ σ`. -/
def negativeNormalSpaceSignLocalSystemIsoOfComp
    (h : i.IsNondegenerateCriticalSubmanifold (f ∘ σ))
    (h' : i'.IsNondegenerateCriticalSubmanifold f) (hk : k + 1 ≤ n) (hk' : k + 1 ≤ n')
    (hσ : ContMDiff I I' (k + 2) σ) (hσs : ∀ s, IsRegularPoint I I' σ (i s))
    (hf : ∀ s, ContMDiffAt I' 𝓘(ℝ) (k + 2) f (i' s))
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ F)
    (hdim' : finrank ℝ P' = finrank ℝ E' - finrank ℝ F)
    (g : haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
      haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
      letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J k P fun s ↦ i.isImmersion.NormalSpace s hn)
    (g' : haveI : IsManifold I' 1 M' := .of_le (n := k + 2) (one_le_two.trans le_add_self)
      haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
      letI := i'.normalSpaceFiberBundle hn' hdim'
      letI := i'.normalSpaceVectorBundle hn' hdim'
      ContMDiffRiemannianMetric J k P' fun s ↦ i'.isImmersion.NormalSpace s hn') {r : ℕ}
    (hr : ∀ s, manifoldMorseIndex I' f (i' s) = r) :
    haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
    haveI : IsManifold I' 2 M' := .of_le (n := k + 2) le_add_self
    haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
    haveI : IsManifold I' 1 M' := .of_le (n := k + 2) (one_le_two.trans le_add_self)
    haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    letI := i'.normalSpaceFiberBundle hn' hdim'
    letI := i'.normalSpaceVectorBundle hn' hdim'
    letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
    letI := (h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace_of_comp hn hσi
      h'.toIsCriticalSubmanifold hk (fun s ↦ hσ (i s)) hσs hf hdim g hr).fiberBundle
    haveI := (h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace_of_comp hn hσi
      h'.toIsCriticalSubmanifold hk (fun s ↦ hσ (i s)) hσs hf hdim g hr).vectorBundle
    letI := subbundleTopology P' (F' := Fin r → ℝ)
      (h'.negativeNormalSpace hn' g'.toRiemannianMetric)
    letI := (h'.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn' hk' hf hdim' g'
      hr).fiberBundle
    haveI := (h'.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn' hk' hf hdim' g'
      hr).vectorBundle
    VectorBundleOrientationCover.signLocalSystem (Fin r → ℝ)
        (fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s) R
        (ι := Fin r) (by simp) ≅
      VectorBundleOrientationCover.signLocalSystem (Fin r → ℝ)
        (fun s ↦ h'.negativeNormalSpace hn' g'.toRiemannianMetric s) R
        (ι := Fin r) (by simp) :=
  haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
  haveI : IsManifold I' 2 M' := .of_le (n := k + 2) le_add_self
  haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
  haveI : IsManifold I' 1 M' := .of_le (n := k + 2) (one_le_two.trans le_add_self)
  haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
  letI := i.normalSpaceFiberBundle hn hdim
  letI := i.normalSpaceVectorBundle hn hdim
  letI := i'.normalSpaceFiberBundle hn' hdim'
  letI := i'.normalSpaceVectorBundle hn' hdim'
  letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
  letI := (h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace_of_comp hn hσi
    h'.toIsCriticalSubmanifold hk (fun s ↦ hσ (i s)) hσs hf hdim g hr).fiberBundle
  haveI := (h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace_of_comp hn hσi
    h'.toIsCriticalSubmanifold hk (fun s ↦ hσ (i s)) hσs hf hdim g hr).vectorBundle
  letI := subbundleTopology P' (F' := Fin r → ℝ)
    (h'.negativeNormalSpace hn' g'.toRiemannianMetric)
  letI := (h'.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn' hk' hf hdim' g'
    hr).fiberBundle
  haveI := (h'.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn' hk' hf hdim' g'
    hr).vectorBundle
  VectorBundleOrientationCover.signLocalSystemIsoOfFiberwise R (F := Fin r → ℝ)
    (F' := Fin r → ℝ) (ι := Fin r) (φ := fun s ↦ (h.negativeNormalSpaceEquivOfComp hn hn' hσi h'
      g.toRiemannianMetric g'.toRiemannianMetric ((hσ (i s)).of_le le_add_self)
        (hσs s)).toContinuousLinearEquiv.symm) (by simp) (by simp)
    (h.contMDiff_negativeNormalSpaceEquivOfComp_symm hn hn' hσi h' hk hk' hσ hσs hf hdim hdim' g
      g' hr).continuous

/-- The isomorphism of orientation local systems of the negative normal bundles along a map is the
one induced by the inverses of the fibrewise isomorphisms `negativeNormalSpaceEquivOfComp`
(`TauCeti.VectorBundleOrientationCover.signLocalSystemIsoOfFiberwise`). -/
@[simp]
theorem negativeNormalSpaceSignLocalSystemIsoOfComp_def
    (h : i.IsNondegenerateCriticalSubmanifold (f ∘ σ))
    (h' : i'.IsNondegenerateCriticalSubmanifold f) (hk : k + 1 ≤ n) (hk' : k + 1 ≤ n')
    (hσ : ContMDiff I I' (k + 2) σ) (hσs : ∀ s, IsRegularPoint I I' σ (i s))
    (hf : ∀ s, ContMDiffAt I' 𝓘(ℝ) (k + 2) f (i' s))
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ F)
    (hdim' : finrank ℝ P' = finrank ℝ E' - finrank ℝ F)
    (g : haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
      haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
      letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J k P fun s ↦ i.isImmersion.NormalSpace s hn)
    (g' : haveI : IsManifold I' 1 M' := .of_le (n := k + 2) (one_le_two.trans le_add_self)
      haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
      letI := i'.normalSpaceFiberBundle hn' hdim'
      letI := i'.normalSpaceVectorBundle hn' hdim'
      ContMDiffRiemannianMetric J k P' fun s ↦ i'.isImmersion.NormalSpace s hn') {r : ℕ}
    (hr : ∀ s, manifoldMorseIndex I' f (i' s) = r) :
    haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
    haveI : IsManifold I' 2 M' := .of_le (n := k + 2) le_add_self
    haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
    haveI : IsManifold I' 1 M' := .of_le (n := k + 2) (one_le_two.trans le_add_self)
    haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    letI := i'.normalSpaceFiberBundle hn' hdim'
    letI := i'.normalSpaceVectorBundle hn' hdim'
    letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
    letI := (h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace_of_comp hn hσi
      h'.toIsCriticalSubmanifold hk (fun s ↦ hσ (i s)) hσs hf hdim g hr).fiberBundle
    haveI := (h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace_of_comp hn hσi
      h'.toIsCriticalSubmanifold hk (fun s ↦ hσ (i s)) hσs hf hdim g hr).vectorBundle
    letI := subbundleTopology P' (F' := Fin r → ℝ)
      (h'.negativeNormalSpace hn' g'.toRiemannianMetric)
    letI := (h'.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn' hk' hf hdim' g'
      hr).fiberBundle
    haveI := (h'.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn' hk' hf hdim' g'
      hr).vectorBundle
    h.negativeNormalSpaceSignLocalSystemIsoOfComp hn hn' hσi R h' hk hk' hσ hσs hf hdim hdim' g g'
        hr =
      VectorBundleOrientationCover.signLocalSystemIsoOfFiberwise R (F := Fin r → ℝ)
        (F' := Fin r → ℝ) (ι := Fin r) (φ := fun s ↦ (h.negativeNormalSpaceEquivOfComp hn hn' hσi
          h' g.toRiemannianMetric g'.toRiemannianMetric ((hσ (i s)).of_le le_add_self)
            (hσs s)).toContinuousLinearEquiv.symm) (by simp) (by simp)
        (h.contMDiff_negativeNormalSpaceEquivOfComp_symm hn hn' hσi h' hk hk' hσ hσs hf hdim hdim'
          g g' hr).continuous :=
  (rfl)

end TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold
