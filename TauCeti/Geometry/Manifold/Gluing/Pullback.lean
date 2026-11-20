/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Gluing.GlueData
public import TauCeti.Geometry.Manifold.ContMDiff.Pullback
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Pullback

/-!
# Transporting glued manifold atlases along homeomorphisms

This file relates open-embedding gluing (`TauCeti.chartedSpaceOfIsOpenEmbedding`) and compatible
`TopCat.GlueData` gluing (`TopCat.GlueData.chartedSpace`) to atlas pullback along homeomorphisms
(`Homeomorph.pullbackChartedSpace`).

First, pulling back the glued atlas along a homeomorphism `e : N ≃ₜ M` onto the glued carrier
makes `N` a `C^n` manifold for which the transported inclusions `e.symm ∘ φ j` are `C^n` local
diffeomorphisms, so the pulled-back glued atlas has the same maximal atlas as gluing the pieces
directly along `e.symm ∘ φ j`. By `TauCeti.diffeomorphOfForallIsLocalDiffeomorphEquiv`, any
charted-space structure on `N` with local-diffeomorphism inclusions `e.symm ∘ φ j` is `C^n`
diffeomorphic to the glued manifold via `e`
(`TopCat.GlueData.IsCompatible.pullbackGluedDiffeomorph`).

Second, transporting charts onto the pieces `D.U i` (and overlaps `D.V ij`) of `D : TopCat.GlueData`
along homeomorphisms `eU i : D.U i ≃ₜ M i` produces a named glued atlas
`TopCat.GlueData.pullbackPieceChartedSpace` on `D.toGlueData.glued`, without installing competing
global instances. Overlap compatibility translates to local diffeomorphy of the conjugated overlap
maps between the model pieces and model overlaps
(`TopCat.GlueData.isCompatible_pullbackChartedSpace_iff`), and two piece-transported atlases whose
piecewise coordinate changes are local diffeomorphisms are canonically related on
`D.toGlueData.glued` by the identity `C^n` diffeomorphism
(`TopCat.GlueData.pullbackPieceComparisonDiffeomorph`,
`TopCat.GlueData.IsCompatible.pullbackPieceDiffeomorph`).

For `𝕜 = ℂ` all results apply without change to holomorphic gluings and biholomorphisms.

## Main definitions

* `TopCat.GlueData.IsCompatible.pullbackGluedDiffeomorph`: upgrading `e : M ≃ₜ D.toGlueData.glued`
  to a `C^n` diffeomorphism when every `e.symm ∘ D.toGlueData.ι i` is a local diffeomorphism.
* `TopCat.GlueData.pullbackPieceChartedSpace`: named atlas on `D.toGlueData.glued` glued from piece
  atlases pulled back along `eU : ∀ i, D.U i ≃ₜ M i`.
* `TopCat.GlueData.pullbackPieceComparisonDiffeomorph`,
  `TopCat.GlueData.IsCompatible.pullbackPieceDiffeomorph`: identity `C^n` diffeomorphisms between
  piece-transported atlases on `D.toGlueData.glued`.

## Main results

* `TauCeti.maximalAtlas_pullbackChartedSpace_eq_chartedSpaceOfIsOpenEmbedding`: pulling back an
  open-embedding glued atlas along `e : N ≃ₜ M` gives the same maximal atlas as gluing along
  `e.symm ∘ φ j`.
* `TopCat.GlueData.isCompatible_pullbackChartedSpace_iff`,
  `TopCat.GlueData.isCompatible_pullbackPieceChartedSpace_iff`: overlap compatibility for
  pulled-back piece and overlap atlases.
* `TopCat.GlueData.isCompatible_diffeomorph_pullbackChartedSpace_iff`: recharting pieces and
  overlaps along `C^n` diffeomorphisms preserves `IsCompatible`.
* `TopCat.GlueData.isManifold_pullbackPieceChartedSpace`,
  `TopCat.GlueData.IsCompatible.isManifold_pullbackPieceChartedSpace`: manifold structure on
  `D.toGlueData.glued` for piece-transported atlases.
* `TopCat.GlueData.maximalAtlas_pullbackPieceChartedSpace_eq_of_isLocalDiffeomorph`,
  `TopCat.GlueData.IsCompatible.maximalAtlas_pullbackPieceChartedSpace_eq`: equality of maximal
  atlases on `D.toGlueData.glued` under piecewise diffeomorphic recharting.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 1 (the smooth manifold chart lemma).
* Shoshichi Kobayashi and Katsumi Nomizu, *Foundations of Differential Geometry*, Volume I,
  Chapter I, Section 1 (atlases compatible with a pseudogroup).
-/

public section

open Set Filter Topology IsManifold
open scoped Manifold ContDiff

namespace TauCeti

section OpenEmbeddingPullback

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω}
  {J : Type*} {U : J → Type*} [∀ j, TopologicalSpace (U j)] [∀ j, ChartedSpace H (U j)]
  [∀ j, IsManifold I n (U j)]
  {M : Type*} [TopologicalSpace M] {N : Type*} [TopologicalSpace N]
  {φ : ∀ j, U j → M} (hφ : ∀ j, IsOpenEmbedding (φ j)) (hcover : ∀ x, ∃ j y, φ j y = x)
  (hdeck : ∀ (j k : J) (x : U j) (y : U k), φ j x = φ k y →
    ∃ T : U j → U k, ContMDiffAt I I n T x ∧ φ k ∘ T =ᶠ[𝓝 x] φ j)

include hdeck in
/-- Pulling back `chartedSpaceOfIsOpenEmbedding` along `e : N ≃ₜ M` makes `N` a `C^n` manifold. -/
theorem isManifold_pullbackChartedSpace_chartedSpaceOfIsOpenEmbedding (e : N ≃ₜ M) :
    letI := chartedSpaceOfIsOpenEmbedding (H := H) hφ hcover
    letI := e.pullbackChartedSpace (H := H)
    IsManifold I n N := by
  let := chartedSpaceOfIsOpenEmbedding (H := H) hφ hcover
  have := isManifold_chartedSpaceOfIsOpenEmbedding hφ hcover hdeck
  exact e.pullback_isManifold I n

include hdeck in
/-- For the atlas on `N` pulled back from `chartedSpaceOfIsOpenEmbedding` along `e : N ≃ₜ M`,
each transported embedding `e.symm ∘ φ j` is a `C^n` local diffeomorphism. -/
theorem isLocalDiffeomorph_symm_comp_chartedSpaceOfIsOpenEmbedding (e : N ≃ₜ M) (j : J) :
    letI := chartedSpaceOfIsOpenEmbedding (H := H) hφ hcover
    letI := e.pullbackChartedSpace (H := H)
    IsLocalDiffeomorph I I n (e.symm ∘ φ j) := by
  let := chartedSpaceOfIsOpenEmbedding (H := H) hφ hcover
  exact (e.isLocalDiffeomorph_symm_comp_pullbackChartedSpace_iff (I := I) (I' := I) (f := φ j)).2
    (isLocalDiffeomorph_chartedSpaceOfIsOpenEmbedding hφ hcover hdeck j)

include hdeck in
/-- Any `C^n` manifold structure on `N` making every `e.symm ∘ φ j` a `C^n` local diffeomorphism
has the same maximal atlas as the structure pulled back from `chartedSpaceOfIsOpenEmbedding` along
`e : N ≃ₜ M`. -/
theorem maximalAtlas_pullbackChartedSpace_chartedSpaceOfIsOpenEmbedding_eq (e : N ≃ₜ M)
    {cN : ChartedSpace H N} (hcN : letI := cN; IsManifold I n N)
    (hφN : ∀ j, letI := cN; IsLocalDiffeomorph I I n (e.symm ∘ φ j)) :
    (letI := chartedSpaceOfIsOpenEmbedding (H := H) hφ hcover
     letI := e.pullbackChartedSpace (H := H)
     maximalAtlas I n N) =
      (letI := cN; maximalAtlas I n N) := by
  have hcover' : ∀ z : N, ∃ j y, (e.symm ∘ φ j) y = z := fun z ↦ by
    obtain ⟨j, y, hy⟩ := hcover (e z)
    exact ⟨j, y, by simp only [Function.comp_apply, hy, e.symm_apply_apply]⟩
  exact maximalAtlas_eq_of_forall_isLocalDiffeomorph hcover'
    (isManifold_pullbackChartedSpace_chartedSpaceOfIsOpenEmbedding hφ hcover hdeck e) hcN
    (isLocalDiffeomorph_symm_comp_chartedSpaceOfIsOpenEmbedding hφ hcover hdeck e) hφN

include hdeck in
/-- **Pulling back a glued atlas vs. gluing along pulled-back embeddings.** Pulling back
`chartedSpaceOfIsOpenEmbedding hφ hcover` along `e : N ≃ₜ M` produces the same maximal `C^n` atlas
on `N` as `chartedSpaceOfIsOpenEmbedding` built directly from `e.symm ∘ φ j`. -/
theorem maximalAtlas_pullbackChartedSpace_eq_chartedSpaceOfIsOpenEmbedding (e : N ≃ₜ M) :
    (letI := chartedSpaceOfIsOpenEmbedding (H := H) hφ hcover
     letI := e.pullbackChartedSpace (H := H)
     maximalAtlas I n N) =
      (letI := chartedSpaceOfIsOpenEmbedding (H := H)
        (fun j ↦ e.symm.isOpenEmbedding.comp (hφ j))
        (fun z ↦ let ⟨j, y, hy⟩ := hcover (e z)
          ⟨j, y, by simp only [Function.comp_apply, hy, e.symm_apply_apply]⟩)
       maximalAtlas I n N) := by
  have hφ' : ∀ j, IsOpenEmbedding (e.symm ∘ φ j) := fun j ↦ e.symm.isOpenEmbedding.comp (hφ j)
  have hcover' : ∀ z : N, ∃ j y, (e.symm ∘ φ j) y = z := fun z ↦
    let ⟨j, y, hy⟩ := hcover (e z)
    ⟨j, y, by simp only [Function.comp_apply, hy, e.symm_apply_apply]⟩
  have hdeck' : ∀ (j k : J) (x : U j) (y : U k), (e.symm ∘ φ j) x = (e.symm ∘ φ k) y →
      ∃ T : U j → U k, ContMDiffAt I I n T x ∧ (e.symm ∘ φ k) ∘ T =ᶠ[𝓝 x] e.symm ∘ φ j := by
    intro j k x y hxy
    obtain ⟨T, hT, hTφ⟩ := hdeck j k x y (e.symm.injective hxy)
    exact ⟨T, hT, hTφ.fun_comp e.symm⟩
  exact maximalAtlas_pullbackChartedSpace_chartedSpaceOfIsOpenEmbedding_eq hφ hcover hdeck e
    (isManifold_chartedSpaceOfIsOpenEmbedding hφ' hcover' hdeck')
    (isLocalDiffeomorph_chartedSpaceOfIsOpenEmbedding hφ' hcover' hdeck')

end OpenEmbeddingPullback

end TauCeti

namespace TopCat.GlueData

universe u

section TargetPullback

variable {D : TopCat.GlueData.{u}} {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'} {n : ℕ∞ω}
  [∀ i, ChartedSpace H (D.U i)] [∀ ij, ChartedSpace H (D.V ij)] [∀ i, IsManifold I n (D.U i)]

namespace IsCompatible

/-- Pulling back the glued atlas of a compatible gluing along `e : M ≃ₜ D.toGlueData.glued` makes
`M` a `C^n` manifold. -/
theorem isManifold_pullbackChartedSpace (h : D.IsCompatible I n) {M : Type*} [TopologicalSpace M]
    (e : M ≃ₜ D.toGlueData.glued) :
    letI := D.chartedSpace H
    letI := e.pullbackChartedSpace (H := H)
    IsManifold I n M :=
  TauCeti.isManifold_pullbackChartedSpace_chartedSpaceOfIsOpenEmbedding
    D.ι_isOpenEmbedding D.ι_jointly_surjective
    (fun _ _ _ _ ↦ h.exists_contMDiffAt_transition) e

/-- For the atlas on `M` pulled back from `D.chartedSpace H` along `e : M ≃ₜ D.toGlueData.glued`,
every transported canonical map `e.symm ∘ D.toGlueData.ι i` is a `C^n` local diffeomorphism. -/
theorem isLocalDiffeomorph_symm_comp_ι (h : D.IsCompatible I n) {M : Type*} [TopologicalSpace M]
    (e : M ≃ₜ D.toGlueData.glued) (i : D.J) :
    letI := D.chartedSpace H
    letI := e.pullbackChartedSpace (H := H)
    IsLocalDiffeomorph I I n (e.symm ∘ D.toGlueData.ι i) :=
  TauCeti.isLocalDiffeomorph_symm_comp_chartedSpaceOfIsOpenEmbedding
    D.ι_isOpenEmbedding D.ι_jointly_surjective
    (fun _ _ _ _ ↦ h.exists_contMDiffAt_transition) e i

/-- For `m ≤ n`, a map out of `M` equipped with the glued atlas pulled back along
`e : M ≃ₜ D.toGlueData.glued` is `C^m` if and only if its composite with every transported
canonical map `e.symm ∘ D.toGlueData.ι i` is `C^m`. -/
theorem contMDiff_iff_pullbackChartedSpace (h : D.IsCompatible I n) {M : Type*}
    [TopologicalSpace M] (e : M ≃ₜ D.toGlueData.glued) {N : Type*} [TopologicalSpace N]
    [ChartedSpace H' N] {m : ℕ∞ω} (hm : m ≤ n) {g : M → N} :
    letI := D.chartedSpace H
    letI := e.pullbackChartedSpace (H := H)
    ContMDiff I I' m g ↔ ∀ i, ContMDiff I I' m (g ∘ (e.symm ∘ D.toGlueData.ι i)) := by
  let := D.chartedSpace H
  let := e.pullbackChartedSpace (H := H)
  rw [e.contMDiff_pullbackChartedSpace_left_iff, h.contMDiff_iff hm]
  rfl

/-- A map out of `M` equipped with the glued atlas pulled back along `e : M ≃ₜ D.toGlueData.glued`
is a `C^n` local diffeomorphism if and only if its composite with every transported canonical map
`e.symm ∘ D.toGlueData.ι i` is one. -/
theorem isLocalDiffeomorph_iff_pullbackChartedSpace (h : D.IsCompatible I n) {M : Type*}
    [TopologicalSpace M] (e : M ≃ₜ D.toGlueData.glued) {N : Type*} [TopologicalSpace N]
    [ChartedSpace H' N] {g : M → N} :
    letI := D.chartedSpace H
    letI := e.pullbackChartedSpace (H := H)
    IsLocalDiffeomorph I I' n g ↔
      ∀ i, IsLocalDiffeomorph I I' n (g ∘ (e.symm ∘ D.toGlueData.ι i)) := by
  let := D.chartedSpace H
  let := e.pullbackChartedSpace (H := H)
  rw [e.isLocalDiffeomorph_pullbackChartedSpace_left_iff, h.isLocalDiffeomorph_iff]
  rfl

/-- Any `C^n` manifold structure `cM` on `M` making every `e.symm ∘ D.toGlueData.ι i` a `C^n`
local diffeomorphism has the same maximal atlas as the glued atlas pulled back along
`e : M ≃ₜ D.toGlueData.glued`. -/
theorem maximalAtlas_pullbackChartedSpace_eq (h : D.IsCompatible I n) {M : Type*}
    [TopologicalSpace M] (e : M ≃ₜ D.toGlueData.glued) {cM : ChartedSpace H M}
    (hcM : letI := cM; IsManifold I n M)
    (hιM : ∀ i, letI := cM; IsLocalDiffeomorph I I n (e.symm ∘ D.toGlueData.ι i)) :
    (letI := D.chartedSpace H
     letI := e.pullbackChartedSpace (H := H)
     maximalAtlas I n M) =
      (letI := cM; maximalAtlas I n M) :=
  TauCeti.maximalAtlas_pullbackChartedSpace_chartedSpaceOfIsOpenEmbedding_eq
    D.ι_isOpenEmbedding D.ι_jointly_surjective
    (fun _ _ _ _ ↦ h.exists_contMDiffAt_transition) e hcM hιM

/-- **Upgrading a homeomorphism onto a compatible gluing to a diffeomorphism.** If `M` carries a
charted-space structure for which every `e.symm ∘ D.toGlueData.ι i` is a `C^n` local
diffeomorphism, then `e : M ≃ₜ D.toGlueData.glued` upgrades to a `C^n` diffeomorphism
`M ≃ₘ^n⟮I', I⟯ D.toGlueData.glued`. -/
noncomputable def pullbackGluedDiffeomorph (h : D.IsCompatible I n) {M : Type*}
    [TopologicalSpace M] [ChartedSpace H' M] (e : M ≃ₜ D.toGlueData.glued)
    (hιM : ∀ i, IsLocalDiffeomorph I I' n (e.symm ∘ D.toGlueData.ι i)) :
    letI := D.chartedSpace H
    M ≃ₘ^n⟮I', I⟯ D.toGlueData.glued :=
  letI := D.chartedSpace H
  TauCeti.diffeomorphOfForallIsLocalDiffeomorphEquiv D.ι_jointly_surjective
    e.toEquiv (fun i ↦ h.isLocalDiffeomorph_ι i) hιM

/-- The forward map of `pullbackGluedDiffeomorph` is `e`. -/
@[simp]
theorem coe_pullbackGluedDiffeomorph (h : D.IsCompatible I n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H' M] (e : M ≃ₜ D.toGlueData.glued)
    (hιM : ∀ i, IsLocalDiffeomorph I I' n (e.symm ∘ D.toGlueData.ι i)) :
    letI := D.chartedSpace H
    ⇑(h.pullbackGluedDiffeomorph e hιM) = e :=
  letI := D.chartedSpace H
  TauCeti.coe_diffeomorphOfForallIsLocalDiffeomorphEquiv ..

/-- The inverse map of `pullbackGluedDiffeomorph` is `e.symm`. -/
@[simp]
theorem coe_pullbackGluedDiffeomorph_symm (h : D.IsCompatible I n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H' M] (e : M ≃ₜ D.toGlueData.glued)
    (hιM : ∀ i, IsLocalDiffeomorph I I' n (e.symm ∘ D.toGlueData.ι i)) :
    letI := D.chartedSpace H
    ⇑(h.pullbackGluedDiffeomorph e hιM).symm = e.symm :=
  letI := D.chartedSpace H
  TauCeti.coe_diffeomorphOfForallIsLocalDiffeomorphEquiv_symm ..

/-- Evaluating `pullbackGluedDiffeomorph` at `z` gives `e z`. -/
@[simp]
theorem pullbackGluedDiffeomorph_apply (h : D.IsCompatible I n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H' M] (e : M ≃ₜ D.toGlueData.glued)
    (hιM : ∀ i, IsLocalDiffeomorph I I' n (e.symm ∘ D.toGlueData.ι i)) (z : M) :
    letI := D.chartedSpace H
    h.pullbackGluedDiffeomorph e hιM z = e z :=
  letI := D.chartedSpace H
  TauCeti.diffeomorphOfForallIsLocalDiffeomorphEquiv_apply ..

/-- Evaluating the inverse of `pullbackGluedDiffeomorph` at `x` gives `e.symm x`. -/
@[simp]
theorem pullbackGluedDiffeomorph_symm_apply (h : D.IsCompatible I n) {M : Type*}
    [TopologicalSpace M] [ChartedSpace H' M] (e : M ≃ₜ D.toGlueData.glued)
    (hιM : ∀ i, IsLocalDiffeomorph I I' n (e.symm ∘ D.toGlueData.ι i)) (x : D.toGlueData.glued) :
    letI := D.chartedSpace H
    (h.pullbackGluedDiffeomorph e hιM).symm x = e.symm x :=
  letI := D.chartedSpace H
  TauCeti.diffeomorphOfForallIsLocalDiffeomorphEquiv_symm_apply ..

/-- The underlying homeomorphism of `pullbackGluedDiffeomorph` is `e`. -/
@[simp]
theorem pullbackGluedDiffeomorph_toHomeomorph (h : D.IsCompatible I n) {M : Type*}
    [TopologicalSpace M] [ChartedSpace H' M] (e : M ≃ₜ D.toGlueData.glued)
    (hιM : ∀ i, IsLocalDiffeomorph I I' n (e.symm ∘ D.toGlueData.ι i)) :
    letI := D.chartedSpace H
    (h.pullbackGluedDiffeomorph e hιM).toHomeomorph = e := by
  let := D.chartedSpace H
  ext x
  exact h.pullbackGluedDiffeomorph_apply e hιM x

end IsCompatible

end TargetPullback

section PiecePullback

variable (D : TopCat.GlueData.{u}) {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'} {n : ℕ∞ω}

variable (H) in
/-- **Glued atlas from transported piece charts.** Given homeomorphisms `eU i : D.U i ≃ₜ M i` onto
charted spaces `M i`, pulling back the charts of each `M i` to `D.U i` and gluing along `D` produces
a named `ChartedSpace H D.toGlueData.glued` structure, without installing competing global
instances on either `D.U i` or `D.toGlueData.glued`. -/
@[instance_reducible]
noncomputable def pullbackPieceChartedSpace
    {M : D.J → Type*} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace H (M i)]
    (eU : ∀ i, D.U i ≃ₜ M i) : ChartedSpace H D.toGlueData.glued :=
  letI : ∀ i, ChartedSpace H (D.U i) := fun i ↦ (eU i).pullbackChartedSpace
  D.chartedSpace H

/-- Every chart of `D.pullbackPieceChartedSpace H eU` is the inverse of the canonical inclusion of
a piece containing the point, followed by `eU i` and the chart of `M i` at `eU i y`. -/
theorem exists_chartAt_pullbackPieceChartedSpace_eq
    {M : D.J → Type*} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace H (M i)]
    (eU : ∀ i, D.U i ≃ₜ M i) (x : D.toGlueData.glued) :
    ∃ (i : D.J) (y : D.U i), D.toGlueData.ι i y = x ∧
      haveI : Nonempty (D.U i) := ⟨y⟩
      @chartAt H _ _ _ (D.pullbackPieceChartedSpace H eU) x =
        ((D.ι_isOpenEmbedding i).toOpenPartialHomeomorph _).symm.trans
          ((eU i).transOpenPartialHomeomorph (chartAt H (eU i y))) := by
  let : ∀ i, ChartedSpace H (D.U i) := fun i ↦ (eU i).pullbackChartedSpace
  exact D.exists_chartAt_chartedSpace_eq x

/-- Pulling back piece charts along `Homeomorph.refl` returns `D.chartedSpace H`. -/
@[simp]
theorem pullbackPieceChartedSpace_refl [inst : ∀ i, ChartedSpace H (D.U i)] :
    D.pullbackPieceChartedSpace H (fun i ↦ Homeomorph.refl (D.U i)) = D.chartedSpace H := by
  have heq : (fun i ↦ (Homeomorph.refl (D.U i)).pullbackChartedSpace (H := H)) = inst :=
    funext fun i ↦ Homeomorph.pullbackChartedSpace_refl
  exact congrArg (fun c ↦ @TopCat.GlueData.chartedSpace D H _ c) heq

/-- Pulling back piece charts along a composite `fun i ↦ (e₁ i).trans (e₂ i)` is pulling back the
charts of `M' i` to `M i` along `e₂` and then to `D.U i` along `e₁`. -/
theorem pullbackPieceChartedSpace_trans
    {M : D.J → Type*} [∀ i, TopologicalSpace (M i)]
    {M' : D.J → Type*} [∀ i, TopologicalSpace (M' i)] [∀ i, ChartedSpace H (M' i)]
    (e₁ : ∀ i, D.U i ≃ₜ M i) (e₂ : ∀ i, M i ≃ₜ M' i) :
    D.pullbackPieceChartedSpace H (fun i ↦ (e₁ i).trans (e₂ i)) =
      (letI : ∀ i, ChartedSpace H (M i) := fun i ↦ (e₂ i).pullbackChartedSpace
       D.pullbackPieceChartedSpace H e₁) := by
  have heq :
      (fun i ↦ ((e₁ i).trans (e₂ i)).pullbackChartedSpace (H := H)) =
        (fun i ↦ letI := (e₂ i).pullbackChartedSpace (H := H); (e₁ i).pullbackChartedSpace) :=
    funext fun i ↦ Homeomorph.pullbackChartedSpace_trans (e₁ i) (e₂ i)
  exact congrArg (fun c ↦ @TopCat.GlueData.chartedSpace D H _ c) heq

variable {D}

/-- **Compatibility under transported piece and overlap atlases.** Equipping `D.U i` with
`(eU i).pullbackChartedSpace` and `D.V ij` with `(eV ij).pullbackChartedSpace` makes `D`
`C^n` compatible if and only if the conjugated overlap maps into `M i` and `M j` are `C^n` local
diffeomorphisms. -/
theorem isCompatible_pullbackChartedSpace_iff
    {M : D.J → Type*} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace H (M i)]
    {N : D.J × D.J → Type*} [∀ ij, TopologicalSpace (N ij)] [∀ ij, ChartedSpace H (N ij)]
    (eU : ∀ i, D.U i ≃ₜ M i) (eV : ∀ ij, D.V ij ≃ₜ N ij) :
    (letI : ∀ i, ChartedSpace H (D.U i) := fun i ↦ (eU i).pullbackChartedSpace
     letI : ∀ ij, ChartedSpace H (D.V ij) := fun ij ↦ (eV ij).pullbackChartedSpace
     D.IsCompatible I n) ↔
      (∀ i j, IsLocalDiffeomorph I I n (eU i ∘ D.f i j ∘ (eV (i, j)).symm)) ∧
        ∀ i j, IsLocalDiffeomorph I I n
          (eU j ∘ (D.f j i ∘ D.t i j) ∘ (eV (i, j)).symm) := by
  let : ∀ i, ChartedSpace H (D.U i) := fun i ↦ (eU i).pullbackChartedSpace
  let : ∀ ij, ChartedSpace H (D.V ij) := fun ij ↦ (eV ij).pullbackChartedSpace
  constructor
  · intro h
    exact ⟨fun i j ↦ ((eV (i, j)).isLocalDiffeomorph_pullbackChartedSpace_iff (eU i)).1
        (h.isLocalDiffeomorph_f i j),
      fun i j ↦ ((eV (i, j)).isLocalDiffeomorph_pullbackChartedSpace_iff (eU j)).1
        (h.isLocalDiffeomorph_f_comp_t i j)⟩
  · rintro ⟨hf, hft⟩
    exact
      { isLocalDiffeomorph_f := fun i j ↦
          ((eV (i, j)).isLocalDiffeomorph_pullbackChartedSpace_iff (eU i)).2 (hf i j)
        isLocalDiffeomorph_f_comp_t := fun i j ↦
          ((eV (i, j)).isLocalDiffeomorph_pullbackChartedSpace_iff (eU j)).2 (hft i j) }

/-- **Compatibility under transported piece atlases.** When the overlaps `D.V ij` already carry
charted-space structures, equipping `D.U i` with `(eU i).pullbackChartedSpace` makes `D` `C^n`
compatible if and only if `eU i ∘ D.f i j` and `eU j ∘ (D.f j i ∘ D.t i j)` are `C^n` local
diffeomorphisms. -/
theorem isCompatible_pullbackPieceChartedSpace_iff [∀ ij, ChartedSpace H (D.V ij)]
    {M : D.J → Type*} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace H (M i)]
    (eU : ∀ i, D.U i ≃ₜ M i) :
    (letI : ∀ i, ChartedSpace H (D.U i) := fun i ↦ (eU i).pullbackChartedSpace
     D.IsCompatible I n) ↔
      (∀ i j, IsLocalDiffeomorph I I n (eU i ∘ D.f i j)) ∧
        ∀ i j, IsLocalDiffeomorph I I n (eU j ∘ (D.f j i ∘ D.t i j)) := by
  let : ∀ i, ChartedSpace H (D.U i) := fun i ↦ (eU i).pullbackChartedSpace
  constructor
  · intro h
    exact ⟨fun i j ↦ ((eU i).isLocalDiffeomorph_pullbackChartedSpace_right_iff (I := I)).1
        (h.isLocalDiffeomorph_f i j),
      fun i j ↦ ((eU j).isLocalDiffeomorph_pullbackChartedSpace_right_iff (I := I)).1
        (h.isLocalDiffeomorph_f_comp_t i j)⟩
  · rintro ⟨hf, hft⟩
    exact
      { isLocalDiffeomorph_f := fun i j ↦
          ((eU i).isLocalDiffeomorph_pullbackChartedSpace_right_iff (I := I)).2 (hf i j)
        isLocalDiffeomorph_f_comp_t := fun i j ↦
          ((eU j).isLocalDiffeomorph_pullbackChartedSpace_right_iff (I := I)).2 (hft i j) }

/-- If `M i` are `C^n` manifolds and `D` is `C^n` compatible for the piece atlases pulled back
along `eU i : D.U i ≃ₜ M i` (for some overlap atlases `cV`), then
`D.pullbackPieceChartedSpace H eU` makes `D.toGlueData.glued` a `C^n` manifold. -/
theorem isManifold_pullbackPieceChartedSpace
    {M : D.J → Type*} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace H (M i)]
    [∀ i, IsManifold I n (M i)] (eU : ∀ i, D.U i ≃ₜ M i)
    {cV : ∀ ij, ChartedSpace H (D.V ij)}
    (h : letI : ∀ i, ChartedSpace H (D.U i) := fun i ↦ (eU i).pullbackChartedSpace
      letI := cV
      D.IsCompatible I n) :
    letI := D.pullbackPieceChartedSpace H eU
    IsManifold I n D.toGlueData.glued := by
  let : ∀ i, ChartedSpace H (D.U i) := fun i ↦ (eU i).pullbackChartedSpace
  let := cV
  have : ∀ i, IsManifold I n (D.U i) := fun i ↦ (eU i).pullback_isManifold I n
  exact h.isManifold

/-- Under `D.pullbackPieceChartedSpace H eU`, the parametrisation `D.toGlueData.ι i ∘ (eU i).symm`
from each model piece `M i` into `D.toGlueData.glued` is a `C^n` local diffeomorphism. -/
theorem isLocalDiffeomorph_ι_comp_symm_pullbackPieceChartedSpace
    {M : D.J → Type*} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace H (M i)]
    [∀ i, IsManifold I n (M i)] (eU : ∀ i, D.U i ≃ₜ M i)
    {cV : ∀ ij, ChartedSpace H (D.V ij)}
    (h : letI : ∀ i, ChartedSpace H (D.U i) := fun i ↦ (eU i).pullbackChartedSpace
      letI := cV
      D.IsCompatible I n) (i : D.J) :
    letI := D.pullbackPieceChartedSpace H eU
    IsLocalDiffeomorph I I n (D.toGlueData.ι i ∘ (eU i).symm) := by
  let : ∀ i, ChartedSpace H (D.U i) := fun i ↦ (eU i).pullbackChartedSpace
  let := cV
  let := D.pullbackPieceChartedSpace H eU
  have : ∀ i, IsManifold I n (D.U i) := fun i ↦ (eU i).pullback_isManifold I n
  exact ((eU i).isLocalDiffeomorph_pullbackChartedSpace_left_iff (I := I) (I' := I)).1
    (h.isLocalDiffeomorph_ι i)

/-- **Comparing two piece-transported atlases on `D.toGlueData.glued`.** Suppose `eU₁` and `eU₂`
transport compatible manifold atlases from two model families `M₁` and `M₂` onto `D.U`, giving two
named atlases `D.pullbackPieceChartedSpace H eU₁` and `D.pullbackPieceChartedSpace H' eU₂` on the
same carrier `D.toGlueData.glued`. If every piecewise coordinate change `eU₂ i ∘ (eU₁ i).symm` is
a `C^n` local diffeomorphism, then the identity map on `D.toGlueData.glued` is a `C^n`
diffeomorphism between the two glued atlases. -/
noncomputable def pullbackPieceComparisonDiffeomorph
    {M₁ : D.J → Type*} [∀ i, TopologicalSpace (M₁ i)] [∀ i, ChartedSpace H (M₁ i)]
    [∀ i, IsManifold I n (M₁ i)]
    {M₂ : D.J → Type*} [∀ i, TopologicalSpace (M₂ i)] [∀ i, ChartedSpace H' (M₂ i)]
    [∀ i, IsManifold I' n (M₂ i)]
    (eU₁ : ∀ i, D.U i ≃ₜ M₁ i) (eU₂ : ∀ i, D.U i ≃ₜ M₂ i)
    {cV₁ : ∀ ij, ChartedSpace H (D.V ij)} {cV₂ : ∀ ij, ChartedSpace H' (D.V ij)}
    (h₁ : letI : ∀ i, ChartedSpace H (D.U i) := fun i ↦ (eU₁ i).pullbackChartedSpace
      letI := cV₁
      D.IsCompatible I n)
    (h₂ : letI : ∀ i, ChartedSpace H' (D.U i) := fun i ↦ (eU₂ i).pullbackChartedSpace
      letI := cV₂
      D.IsCompatible I' n)
    (hchange : ∀ i, IsLocalDiffeomorph I I' n (eU₂ i ∘ (eU₁ i).symm)) :
    @Diffeomorph 𝕜 _ E _ _ E' _ _ H _ H' _ I I'
      D.toGlueData.glued _ (D.pullbackPieceChartedSpace H eU₁)
      D.toGlueData.glued _ (D.pullbackPieceChartedSpace H' eU₂) n :=
  TauCeti.diffeomorphOfForallIsLocalDiffeomorph
    (D.pullbackPieceChartedSpace H eU₁) (D.pullbackPieceChartedSpace H' eU₂)
    (φ := fun i ↦ D.toGlueData.ι i ∘ (eU₁ i).symm)
    (fun x ↦
      let ⟨i, z, hz⟩ := D.ι_jointly_surjective x
      ⟨i, eU₁ i z, by simp only [Function.comp_apply, Homeomorph.symm_apply_apply, hz]⟩)
    (isLocalDiffeomorph_ι_comp_symm_pullbackPieceChartedSpace eU₁ h₁)
    (fun i x ↦ by
      let := D.pullbackPieceChartedSpace H' eU₂
      have hcomp := (hchange i x).comp
        (hg := isLocalDiffeomorph_ι_comp_symm_pullbackPieceChartedSpace eU₂ h₂ i
          ((eU₂ i ∘ (eU₁ i).symm) x))
      have heq : (D.toGlueData.ι i ∘ (eU₂ i).symm) ∘ (eU₂ i ∘ (eU₁ i).symm) =
          D.toGlueData.ι i ∘ (eU₁ i).symm :=
        funext fun w ↦ by simp only [Function.comp_apply, Homeomorph.symm_apply_apply]
      rwa [heq] at hcomp)

/-- The underlying map of `pullbackPieceComparisonDiffeomorph` is the identity. -/
@[simp]
theorem coe_pullbackPieceComparisonDiffeomorph
    {M₁ : D.J → Type*} [∀ i, TopologicalSpace (M₁ i)] [∀ i, ChartedSpace H (M₁ i)]
    [∀ i, IsManifold I n (M₁ i)]
    {M₂ : D.J → Type*} [∀ i, TopologicalSpace (M₂ i)] [∀ i, ChartedSpace H' (M₂ i)]
    [∀ i, IsManifold I' n (M₂ i)]
    (eU₁ : ∀ i, D.U i ≃ₜ M₁ i) (eU₂ : ∀ i, D.U i ≃ₜ M₂ i)
    {cV₁ : ∀ ij, ChartedSpace H (D.V ij)} {cV₂ : ∀ ij, ChartedSpace H' (D.V ij)}
    (h₁ : letI : ∀ i, ChartedSpace H (D.U i) := fun i ↦ (eU₁ i).pullbackChartedSpace
      letI := cV₁
      D.IsCompatible I n)
    (h₂ : letI : ∀ i, ChartedSpace H' (D.U i) := fun i ↦ (eU₂ i).pullbackChartedSpace
      letI := cV₂
      D.IsCompatible I' n)
    (hchange : ∀ i, IsLocalDiffeomorph I I' n (eU₂ i ∘ (eU₁ i).symm)) :
    ⇑(pullbackPieceComparisonDiffeomorph eU₁ eU₂ h₁ h₂ hchange) = id :=
  TauCeti.coe_diffeomorphOfForallIsLocalDiffeomorph ..

/-- `pullbackPieceComparisonDiffeomorph` fixes every point of `D.toGlueData.glued`. -/
@[simp]
theorem pullbackPieceComparisonDiffeomorph_apply
    {M₁ : D.J → Type*} [∀ i, TopologicalSpace (M₁ i)] [∀ i, ChartedSpace H (M₁ i)]
    [∀ i, IsManifold I n (M₁ i)]
    {M₂ : D.J → Type*} [∀ i, TopologicalSpace (M₂ i)] [∀ i, ChartedSpace H' (M₂ i)]
    [∀ i, IsManifold I' n (M₂ i)]
    (eU₁ : ∀ i, D.U i ≃ₜ M₁ i) (eU₂ : ∀ i, D.U i ≃ₜ M₂ i)
    {cV₁ : ∀ ij, ChartedSpace H (D.V ij)} {cV₂ : ∀ ij, ChartedSpace H' (D.V ij)}
    (h₁ : letI : ∀ i, ChartedSpace H (D.U i) := fun i ↦ (eU₁ i).pullbackChartedSpace
      letI := cV₁
      D.IsCompatible I n)
    (h₂ : letI : ∀ i, ChartedSpace H' (D.U i) := fun i ↦ (eU₂ i).pullbackChartedSpace
      letI := cV₂
      D.IsCompatible I' n)
    (hchange : ∀ i, IsLocalDiffeomorph I I' n (eU₂ i ∘ (eU₁ i).symm))
    (x : D.toGlueData.glued) :
    pullbackPieceComparisonDiffeomorph eU₁ eU₂ h₁ h₂ hchange x = x :=
  TauCeti.diffeomorphOfForallIsLocalDiffeomorph_apply ..

/-- The inverse of `pullbackPieceComparisonDiffeomorph` fixes every point of
`D.toGlueData.glued`. -/
@[simp]
theorem pullbackPieceComparisonDiffeomorph_symm_apply
    {M₁ : D.J → Type*} [∀ i, TopologicalSpace (M₁ i)] [∀ i, ChartedSpace H (M₁ i)]
    [∀ i, IsManifold I n (M₁ i)]
    {M₂ : D.J → Type*} [∀ i, TopologicalSpace (M₂ i)] [∀ i, ChartedSpace H' (M₂ i)]
    [∀ i, IsManifold I' n (M₂ i)]
    (eU₁ : ∀ i, D.U i ≃ₜ M₁ i) (eU₂ : ∀ i, D.U i ≃ₜ M₂ i)
    {cV₁ : ∀ ij, ChartedSpace H (D.V ij)} {cV₂ : ∀ ij, ChartedSpace H' (D.V ij)}
    (h₁ : letI : ∀ i, ChartedSpace H (D.U i) := fun i ↦ (eU₁ i).pullbackChartedSpace
      letI := cV₁
      D.IsCompatible I n)
    (h₂ : letI : ∀ i, ChartedSpace H' (D.U i) := fun i ↦ (eU₂ i).pullbackChartedSpace
      letI := cV₂
      D.IsCompatible I' n)
    (hchange : ∀ i, IsLocalDiffeomorph I I' n (eU₂ i ∘ (eU₁ i).symm))
    (x : D.toGlueData.glued) :
    @Diffeomorph.symm 𝕜 _ E _ _ E' _ _ H _ H' _ I I'
      D.toGlueData.glued _ (D.pullbackPieceChartedSpace H eU₁)
      D.toGlueData.glued _ (D.pullbackPieceChartedSpace H' eU₂) n
      (pullbackPieceComparisonDiffeomorph eU₁ eU₂ h₁ h₂ hchange) x = x :=
  TauCeti.diffeomorphOfForallIsLocalDiffeomorph_symm_apply ..

/-- Forgetting smoothness of `pullbackPieceComparisonDiffeomorph` gives `Equiv.refl _`. -/
@[simp]
theorem pullbackPieceComparisonDiffeomorph_toEquiv
    {M₁ : D.J → Type*} [∀ i, TopologicalSpace (M₁ i)] [∀ i, ChartedSpace H (M₁ i)]
    [∀ i, IsManifold I n (M₁ i)]
    {M₂ : D.J → Type*} [∀ i, TopologicalSpace (M₂ i)] [∀ i, ChartedSpace H' (M₂ i)]
    [∀ i, IsManifold I' n (M₂ i)]
    (eU₁ : ∀ i, D.U i ≃ₜ M₁ i) (eU₂ : ∀ i, D.U i ≃ₜ M₂ i)
    {cV₁ : ∀ ij, ChartedSpace H (D.V ij)} {cV₂ : ∀ ij, ChartedSpace H' (D.V ij)}
    (h₁ : letI : ∀ i, ChartedSpace H (D.U i) := fun i ↦ (eU₁ i).pullbackChartedSpace
      letI := cV₁
      D.IsCompatible I n)
    (h₂ : letI : ∀ i, ChartedSpace H' (D.U i) := fun i ↦ (eU₂ i).pullbackChartedSpace
      letI := cV₂
      D.IsCompatible I' n)
    (hchange : ∀ i, IsLocalDiffeomorph I I' n (eU₂ i ∘ (eU₁ i).symm)) :
    @Diffeomorph.toEquiv 𝕜 _ E _ _ E' _ _ H _ H' _ I I'
      D.toGlueData.glued _ (D.pullbackPieceChartedSpace H eU₁)
      D.toGlueData.glued _ (D.pullbackPieceChartedSpace H' eU₂) n
      (pullbackPieceComparisonDiffeomorph eU₁ eU₂ h₁ h₂ hchange) = Equiv.refl D.toGlueData.glued :=
  TauCeti.diffeomorphOfForallIsLocalDiffeomorph_toEquiv ..

/-- Two piece-transported atlases on `D.toGlueData.glued` with the same model `I` and `C^n`
local-diffeomorphism piecewise coordinate changes have the same maximal `C^n` atlas. -/
theorem maximalAtlas_pullbackPieceChartedSpace_eq_of_isLocalDiffeomorph
    {M₁ : D.J → Type*} [∀ i, TopologicalSpace (M₁ i)] [∀ i, ChartedSpace H (M₁ i)]
    [∀ i, IsManifold I n (M₁ i)]
    {M₂ : D.J → Type*} [∀ i, TopologicalSpace (M₂ i)] [∀ i, ChartedSpace H (M₂ i)]
    [∀ i, IsManifold I n (M₂ i)]
    (eU₁ : ∀ i, D.U i ≃ₜ M₁ i) (eU₂ : ∀ i, D.U i ≃ₜ M₂ i)
    {cV₁ : ∀ ij, ChartedSpace H (D.V ij)} {cV₂ : ∀ ij, ChartedSpace H (D.V ij)}
    (h₁ : letI : ∀ i, ChartedSpace H (D.U i) := fun i ↦ (eU₁ i).pullbackChartedSpace
      letI := cV₁
      D.IsCompatible I n)
    (h₂ : letI : ∀ i, ChartedSpace H (D.U i) := fun i ↦ (eU₂ i).pullbackChartedSpace
      letI := cV₂
      D.IsCompatible I n)
    (hchange : ∀ i, IsLocalDiffeomorph I I n (eU₂ i ∘ (eU₁ i).symm)) :
    (letI := D.pullbackPieceChartedSpace H eU₁; maximalAtlas I n D.toGlueData.glued) =
      (letI := D.pullbackPieceChartedSpace H eU₂; maximalAtlas I n D.toGlueData.glued) := by
  have hcover : ∀ x : D.toGlueData.glued, ∃ i y, (D.toGlueData.ι i ∘ (eU₁ i).symm) y = x :=
    fun x ↦ by
      obtain ⟨i, z, rfl⟩ := D.ι_jointly_surjective x
      exact ⟨i, eU₁ i z, by simp only [Function.comp_apply, Homeomorph.symm_apply_apply]⟩
  refine TauCeti.maximalAtlas_eq_of_forall_isLocalDiffeomorph hcover
    (isManifold_pullbackPieceChartedSpace eU₁ h₁)
    (isManifold_pullbackPieceChartedSpace eU₂ h₂)
    (isLocalDiffeomorph_ι_comp_symm_pullbackPieceChartedSpace eU₁ h₁)
    fun i x ↦ ?_
  let := D.pullbackPieceChartedSpace H eU₂
  have hcomp := (hchange i x).comp
    (hg := isLocalDiffeomorph_ι_comp_symm_pullbackPieceChartedSpace eU₂ h₂ i
      ((eU₂ i ∘ (eU₁ i).symm) x))
  have heq : (D.toGlueData.ι i ∘ (eU₂ i).symm) ∘ (eU₂ i ∘ (eU₁ i).symm) =
      D.toGlueData.ι i ∘ (eU₁ i).symm :=
    funext fun w ↦ by simp only [Function.comp_apply, Homeomorph.symm_apply_apply]
  rwa [heq] at hcomp

/-! ### Recharting pieces and overlaps along diffeomorphisms -/

section DiffeomorphRecharting

variable [∀ i, ChartedSpace H (D.U i)] [∀ ij, ChartedSpace H (D.V ij)]

/-- Recharting both pieces and overlaps of `D` by pulling back atlases along `C^n` diffeomorphisms
into spaces modelled on `I'` preserves `IsCompatible`. -/
@[simp]
theorem isCompatible_diffeomorph_pullbackChartedSpace_iff
    {M : D.J → Type*} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace H' (M i)]
    {N : D.J × D.J → Type*} [∀ ij, TopologicalSpace (N ij)] [∀ ij, ChartedSpace H' (N ij)]
    (dU : ∀ i, D.U i ≃ₘ^n⟮I, I'⟯ M i) (dV : ∀ ij, D.V ij ≃ₘ^n⟮I, I'⟯ N ij) :
    (letI : ∀ i, ChartedSpace H' (D.U i) := fun i ↦ (dU i).toHomeomorph.pullbackChartedSpace
     letI : ∀ ij, ChartedSpace H' (D.V ij) := fun ij ↦ (dV ij).toHomeomorph.pullbackChartedSpace
     D.IsCompatible I' n) ↔ D.IsCompatible I n := by
  rw [isCompatible_pullbackChartedSpace_iff]
  have hcoe : ∀ i, ⇑(dU i).toHomeomorph = ⇑(dU i) := fun _ ↦ rfl
  have hsymm : ∀ ij, ⇑(dV ij).toHomeomorph.symm = ⇑(dV ij).symm := fun _ ↦ rfl
  simp only [hcoe, hsymm, Diffeomorph.isLocalDiffeomorph_diffeomorph_comp_iff _ le_rfl,
    Diffeomorph.isLocalDiffeomorph_comp_diffeomorph_iff _ le_rfl]
  exact ⟨fun ⟨hf, hft⟩ ↦ ⟨hf, hft⟩, fun h ↦ ⟨h.isLocalDiffeomorph_f, h.isLocalDiffeomorph_f_comp_t⟩⟩

/-- Recharting the pieces of `D` by pulling back atlases along `C^n` diffeomorphisms (with the same
model `I` as the overlaps) preserves `IsCompatible`. -/
@[simp]
theorem isCompatible_diffeomorph_pullbackPieceChartedSpace_iff
    {M : D.J → Type*} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace H (M i)]
    (dU : ∀ i, D.U i ≃ₘ^n⟮I, I⟯ M i) :
    (letI : ∀ i, ChartedSpace H (D.U i) := fun i ↦ (dU i).toHomeomorph.pullbackChartedSpace
     D.IsCompatible I n) ↔ D.IsCompatible I n := by
  rw [isCompatible_pullbackPieceChartedSpace_iff]
  have hcoe : ∀ i, ⇑(dU i).toHomeomorph = ⇑(dU i) := fun _ ↦ rfl
  simp only [hcoe, Diffeomorph.isLocalDiffeomorph_diffeomorph_comp_iff _ le_rfl]
  exact ⟨fun ⟨hf, hft⟩ ↦ ⟨hf, hft⟩, fun h ↦ ⟨h.isLocalDiffeomorph_f, h.isLocalDiffeomorph_f_comp_t⟩⟩

private theorem exists_contMDiffAt_transition_diffeomorph
    {M : D.J → Type*} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace H' (M i)]
    (h : D.IsCompatible I n) (dU : ∀ i, D.U i ≃ₘ^n⟮I, I'⟯ M i)
    (i j : D.J) (x : D.U i) (y : D.U j) (hxy : D.toGlueData.ι i x = D.toGlueData.ι j y) :
    letI : ∀ k, ChartedSpace H' (D.U k) := fun k ↦ (dU k).toHomeomorph.pullbackChartedSpace
    ∃ T : D.U i → D.U j, ContMDiffAt I' I' n T x ∧
      D.toGlueData.ι j ∘ T =ᶠ[𝓝 x] D.toGlueData.ι i := by
  obtain ⟨T, hT, hTι⟩ := h.exists_contMDiffAt_transition hxy
  let : ∀ k, ChartedSpace H' (D.U k) := fun k ↦ (dU k).toHomeomorph.pullbackChartedSpace
  refine ⟨T, ((dU i).toHomeomorph.contMDiffAt_pullbackChartedSpace_iff (dU j).toHomeomorph).2 ?_,
    hTι⟩
  have hx : ⇑(dU i).toHomeomorph.symm ((dU i).toHomeomorph x) = x := (dU i).symm_apply_apply x
  have h1 : ContMDiffAt I' I n (T ∘ ⇑(dU i).toHomeomorph.symm) ((dU i).toHomeomorph x) :=
    ContMDiffAt.comp _ (by simpa only [hx] using hT) (dU i).symm.contMDiff.contMDiffAt
  exact (dU j).contMDiff.contMDiffAt.comp _ h1

/-- Recharting the pieces of a compatible gluing along `C^n` diffeomorphisms
`dU i : D.U i ≃ₘ^n⟮I, I'⟯ M i` into `C^n` manifolds `M i` makes `D.toGlueData.glued` a `C^n`
manifold modelled on `I'` under `D.pullbackPieceChartedSpace H' (fun i ↦ (dU i).toHomeomorph)`,
without needing new charts on the overlaps. -/
theorem IsCompatible.isManifold_pullbackPieceChartedSpace
    {M : D.J → Type*} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace H' (M i)]
    [∀ i, IsManifold I' n (M i)]
    (h : D.IsCompatible I n) (dU : ∀ i, D.U i ≃ₘ^n⟮I, I'⟯ M i) :
    letI := D.pullbackPieceChartedSpace H' (fun i ↦ (dU i).toHomeomorph)
    IsManifold I' n D.toGlueData.glued := by
  let : ∀ i, ChartedSpace H' (D.U i) := fun i ↦ (dU i).toHomeomorph.pullbackChartedSpace
  have : ∀ i, IsManifold I' n (D.U i) := fun i ↦ (dU i).toHomeomorph.pullback_isManifold I' n
  exact TauCeti.isManifold_chartedSpaceOfIsOpenEmbedding
    D.ι_isOpenEmbedding D.ι_jointly_surjective
    (exists_contMDiffAt_transition_diffeomorph h dU)

/-- Recharting the pieces of a compatible gluing along `C^n` diffeomorphisms `dU i` leaves the
maximal `C^n` atlas of `D.toGlueData.glued` unchanged. -/
theorem IsCompatible.maximalAtlas_pullbackPieceChartedSpace_eq
    [∀ i, IsManifold I n (D.U i)]
    {M : D.J → Type*} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace H (M i)]
    [∀ i, IsManifold I n (M i)]
    (h : D.IsCompatible I n) (dU : ∀ i, D.U i ≃ₘ^n⟮I, I⟯ M i) :
    (letI := D.pullbackPieceChartedSpace H (fun i ↦ (dU i).toHomeomorph)
     maximalAtlas I n D.toGlueData.glued) =
      (letI := D.chartedSpace H; maximalAtlas I n D.toGlueData.glued) := by
  rw [← D.pullbackPieceChartedSpace_refl]
  exact maximalAtlas_pullbackPieceChartedSpace_eq_of_isLocalDiffeomorph
    (fun i ↦ (dU i).toHomeomorph) (fun i ↦ Homeomorph.refl (D.U i))
    ((isCompatible_diffeomorph_pullbackPieceChartedSpace_iff dU).2 h)
    ((isCompatible_diffeomorph_pullbackPieceChartedSpace_iff
      (fun i ↦ Diffeomorph.refl I (D.U i) n)).2 h)
    fun i ↦ (dU i).symm.isLocalDiffeomorph

/-- **Identity diffeomorphism after recharting pieces along diffeomorphisms.** Recharting the
pieces of a compatible gluing along `C^n` diffeomorphisms `dU i : D.U i ≃ₘ^n⟮I, I'⟯ M i` yields a
named atlas `D.pullbackPieceChartedSpace H' (fun i ↦ (dU i).toHomeomorph)` that is `C^n`
diffeomorphic to `D.chartedSpace H` via the identity map on `D.toGlueData.glued`. -/
noncomputable def IsCompatible.pullbackPieceDiffeomorph
    [∀ i, IsManifold I n (D.U i)]
    {M : D.J → Type*} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace H' (M i)]
    [∀ i, IsManifold I' n (M i)]
    (h : D.IsCompatible I n) (dU : ∀ i, D.U i ≃ₘ^n⟮I, I'⟯ M i) :
    @Diffeomorph 𝕜 _ E' _ _ E _ _ H' _ H _ I' I
      D.toGlueData.glued _ (D.pullbackPieceChartedSpace H' (fun i ↦ (dU i).toHomeomorph))
      D.toGlueData.glued _ (D.chartedSpace H) n :=
  TauCeti.diffeomorphOfForallIsLocalDiffeomorph (I₀ := I) (I := I') (I' := I)
    (D.pullbackPieceChartedSpace H' (fun i ↦ (dU i).toHomeomorph)) (D.chartedSpace H)
    D.ι_jointly_surjective
    (fun i ↦ by
      have hι' : (letI : ∀ k, ChartedSpace H' (D.U k) :=
            fun k ↦ (dU k).toHomeomorph.pullbackChartedSpace
          letI := D.pullbackPieceChartedSpace H' (fun k ↦ (dU k).toHomeomorph)
          IsLocalDiffeomorph I' I' n (D.toGlueData.ι i)) := by
        let : ∀ k, ChartedSpace H' (D.U k) := fun k ↦ (dU k).toHomeomorph.pullbackChartedSpace
        have : ∀ k, IsManifold I' n (D.U k) :=
          fun k ↦ (dU k).toHomeomorph.pullback_isManifold I' n
        exact TauCeti.isLocalDiffeomorph_chartedSpaceOfIsOpenEmbedding
          D.ι_isOpenEmbedding D.ι_jointly_surjective
          (exists_contMDiffAt_transition_diffeomorph h dU) i
      let := D.pullbackPieceChartedSpace H' (fun k ↦ (dU k).toHomeomorph)
      have hsymm : IsLocalDiffeomorph I' I' n (D.toGlueData.ι i ∘ ⇑(dU i).toHomeomorph.symm) :=
        ((dU i).toHomeomorph.isLocalDiffeomorph_pullbackChartedSpace_left_iff
          (I := I') (I' := I')).1 hι'
      have heq : (D.toGlueData.ι i ∘ ⇑(dU i).toHomeomorph.symm) ∘ ⇑(dU i) = D.toGlueData.ι i :=
        funext fun x ↦ congrArg (D.toGlueData.ι i) ((dU i).symm_apply_apply x)
      rw [← heq]
      exact ((dU i).isLocalDiffeomorph_comp_diffeomorph_iff le_rfl).2 hsymm)
    (fun i ↦ by let := D.chartedSpace H; exact h.isLocalDiffeomorph_ι i)

/-- The underlying map of `IsCompatible.pullbackPieceDiffeomorph` is the identity. -/
@[simp]
theorem IsCompatible.coe_pullbackPieceDiffeomorph
    [∀ i, IsManifold I n (D.U i)]
    {M : D.J → Type*} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace H' (M i)]
    [∀ i, IsManifold I' n (M i)]
    (h : D.IsCompatible I n) (dU : ∀ i, D.U i ≃ₘ^n⟮I, I'⟯ M i) :
    ⇑(h.pullbackPieceDiffeomorph dU) = id :=
  TauCeti.coe_diffeomorphOfForallIsLocalDiffeomorph ..

/-- `IsCompatible.pullbackPieceDiffeomorph` fixes every point of `D.toGlueData.glued`. -/
@[simp]
theorem IsCompatible.pullbackPieceDiffeomorph_apply
    [∀ i, IsManifold I n (D.U i)]
    {M : D.J → Type*} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace H' (M i)]
    [∀ i, IsManifold I' n (M i)]
    (h : D.IsCompatible I n) (dU : ∀ i, D.U i ≃ₘ^n⟮I, I'⟯ M i) (x : D.toGlueData.glued) :
    h.pullbackPieceDiffeomorph dU x = x :=
  TauCeti.diffeomorphOfForallIsLocalDiffeomorph_apply ..

/-- The inverse of `IsCompatible.pullbackPieceDiffeomorph` fixes every point of
`D.toGlueData.glued`. -/
@[simp]
theorem IsCompatible.pullbackPieceDiffeomorph_symm_apply
    [∀ i, IsManifold I n (D.U i)]
    {M : D.J → Type*} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace H' (M i)]
    [∀ i, IsManifold I' n (M i)]
    (h : D.IsCompatible I n) (dU : ∀ i, D.U i ≃ₘ^n⟮I, I'⟯ M i) (x : D.toGlueData.glued) :
    @Diffeomorph.symm 𝕜 _ E' _ _ E _ _ H' _ H _ I' I
      D.toGlueData.glued _ (D.pullbackPieceChartedSpace H' (fun i ↦ (dU i).toHomeomorph))
      D.toGlueData.glued _ (D.chartedSpace H) n
      (h.pullbackPieceDiffeomorph dU) x = x :=
  TauCeti.diffeomorphOfForallIsLocalDiffeomorph_symm_apply ..

/-- Forgetting smoothness of `IsCompatible.pullbackPieceDiffeomorph` gives `Equiv.refl _`. -/
@[simp]
theorem IsCompatible.pullbackPieceDiffeomorph_toEquiv
    [∀ i, IsManifold I n (D.U i)]
    {M : D.J → Type*} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace H' (M i)]
    [∀ i, IsManifold I' n (M i)]
    (h : D.IsCompatible I n) (dU : ∀ i, D.U i ≃ₘ^n⟮I, I'⟯ M i) :
    @Diffeomorph.toEquiv 𝕜 _ E' _ _ E _ _ H' _ H _ I' I
      D.toGlueData.glued _ (D.pullbackPieceChartedSpace H' (fun i ↦ (dU i).toHomeomorph))
      D.toGlueData.glued _ (D.chartedSpace H) n
      (h.pullbackPieceDiffeomorph dU) = Equiv.refl D.toGlueData.glued :=
  TauCeti.diffeomorphOfForallIsLocalDiffeomorph_toEquiv ..

end DiffeomorphRecharting

end PiecePullback

end TopCat.GlueData
