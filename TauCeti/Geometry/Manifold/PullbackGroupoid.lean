/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Shin, The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import TauCeti.Topology.OpenPartialHomeomorph.Composition

/-!
# Pulling back charted-space and groupoid structures along a homeomorphism

Given a charted space `M` modelled on `H` and a homeomorphism `e : N ≃ₜ M`, the space `N`
receives the pulled-back charted-space structure `Homeomorph.pullbackChartedSpace e`, whose
atlas is `{e.transOpenPartialHomeomorph c | c ∈ atlas H M}` and whose chart at `x` is the chart of
`M` at `e x` precomposed with `e`.

The coordinate changes of the pulled-back atlas are *equal* to the coordinate changes of the
original atlas (Mathlib's `Homeomorph.transOpenPartialHomeomorph_symm_trans`): for a global
homeomorphism nothing of the transport survives in the overlaps. Consequently the pulled-back
structure satisfies every structure groupoid that `M` satisfies, with no
`ClosedUnderRestriction` assumption, and `e` itself is a structomorphism. For the `C^n` groupoid
of a model `I` this makes `N` a `C^n` manifold, and `e` a `C^n` diffeomorphism whose underlying map
is `e`.

This complements Mathlib's `Homeomorph.chartedSpace`, which pushes charts forward through local
inverses chosen by the `IsLocalHomeomorph` machinery, and Tau Ceti's
`IsLocalHomeomorph.chartedSpaceComap`, which pulls charts back along local inverses of a local
homeomorphism. Composing with the global homeomorphism instead keeps the charts explicit, and makes
the transport strictly functorial: pulling back along `Homeomorph.refl` returns the original
structure, pulling back along a composite is pulling back twice, and pulling back along `e` and then
along `e.symm` returns the original structure.

The construction does not by itself compare the pulled-back structure with a structure that `N`
already carries. When `N` is a `C^n` manifold and `e` is a `C^n` diffeomorphism, the pulled-back
charts belong to the maximal atlas of `N`, so the two structures are compatible.

## Main definitions

* `Homeomorph.pullbackChartedSpace e`: the charted-space structure on `N` pulled back along
  `e : N ≃ₜ M`.
* `Homeomorph.pullbackStructomorph e G`: `e` as a `G`-structomorphism for the pulled-back
  structure.
* `Homeomorph.pullbackDiffeomorph e I n`: `e` as a `C^n` diffeomorphism for the pulled-back
  structure.

## Main results

* `Homeomorph.pullback_hasGroupoid`: the pulled-back structure satisfies every structure groupoid
  that the original structure satisfies.
* `Homeomorph.pullback_isManifold`: the pulled-back structure of a `C^n` manifold is a `C^n`
  manifold.
* `Homeomorph.pullbackChartedSpace_refl`, `Homeomorph.pullbackChartedSpace_trans` and
  `Homeomorph.pullbackChartedSpace_symm_pullbackChartedSpace`: the identity, composition and
  inverse laws of the transport.
* `Diffeomorph.transOpenPartialHomeomorph_mem_maximalAtlas`: a `C^n` diffeomorphism pulls a chart
  of the maximal atlas of its target back to a chart of the maximal atlas of its source.
* `Diffeomorph.atlas_pullbackChartedSpace_subset_maximalAtlas`: the charts pulled back along a
  `C^n` diffeomorphism belong to the maximal atlas of its source.

The definitions and the first lemmas follow the Mathlib pull request
[mathlib4#42847](https://github.com/leanprover-community/mathlib4/pull/42847) by Ryan Shin, which
adds `Mathlib.Geometry.Manifold.PullbackGroupoid`.

## References

* Shoshichi Kobayashi and Katsumi Nomizu, *Foundations of Differential Geometry*, Volume I,
  Chapter I, Section 1, for atlases compatible with a pseudogroup.
-/

public section

open Set ChartedSpace
open scoped Manifold ContDiff

variable {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] {P : Type*} [TopologicalSpace P]

namespace Homeomorph

/-- The charted-space structure on `N` pulled back along a homeomorphism `e : N ≃ₜ M`: the atlas
is `{e.transOpenPartialHomeomorph c | c ∈ atlas H M}` and the chart at `x` is the chart of `M` at
`e x` precomposed with `e`. -/
@[expose, instance_reducible]
def pullbackChartedSpace (e : N ≃ₜ M) : ChartedSpace H N where
  atlas := (e.transOpenPartialHomeomorph ·) '' atlas H M
  chartAt x := e.transOpenPartialHomeomorph (chartAt H (e x))
  mem_chart_source x := mem_chart_source H (e x)
  chart_mem_atlas x := ⟨_, chart_mem_atlas _ (e x), rfl⟩

/-- The pulled-back chart at `x` is the chart of `M` at `e x` precomposed with `e`. -/
@[simp, mfld_simps]
theorem pullbackChartedSpace_chartAt (e : N ≃ₜ M) (x : N) :
    letI := e.pullbackChartedSpace (H := H)
    chartAt H x = e.transOpenPartialHomeomorph (chartAt H (e x)) :=
  (rfl)

/-- The pulled-back atlas consists of the charts of `M` precomposed with `e`. -/
@[simp, mfld_simps]
theorem pullbackChartedSpace_atlas (e : N ≃ₜ M) :
    letI := e.pullbackChartedSpace (H := H)
    atlas H N = (e.transOpenPartialHomeomorph ·) '' atlas H M :=
  (rfl)

/-- A chart of `M` precomposed with `e` is a chart of the pulled-back atlas. -/
theorem transOpenPartialHomeomorph_mem_pullbackChartedSpace_atlas (e : N ≃ₜ M)
    {c : OpenPartialHomeomorph M H} (hc : c ∈ atlas H M) :
    letI := e.pullbackChartedSpace (H := H)
    e.transOpenPartialHomeomorph c ∈ atlas H N :=
  ⟨c, hc, rfl⟩

/-- Pulling back along the identity homeomorphism returns the original structure. -/
theorem pullbackChartedSpace_refl :
    (Homeomorph.refl M).pullbackChartedSpace (H := H) = ‹ChartedSpace H M› := by
  ext1
  · simp
  · funext x
    simp

/-- Pulling back along a composite of homeomorphisms is pulling back twice. -/
theorem pullbackChartedSpace_trans (e₁ : P ≃ₜ N) (e₂ : N ≃ₜ M) :
    (e₁.trans e₂).pullbackChartedSpace (H := H) =
      (letI := e₂.pullbackChartedSpace (H := H); e₁.pullbackChartedSpace) := by
  let := e₂.pullbackChartedSpace (H := H)
  ext1
  · simp only [pullbackChartedSpace_atlas, image_image, trans_transOpenPartialHomeomorph]
  · funext x
    exact trans_transOpenPartialHomeomorph e₁ e₂ _

/-- Pulling back along `e` and then along `e.symm` returns the original structure. -/
theorem pullbackChartedSpace_symm_pullbackChartedSpace (e : N ≃ₜ M) :
    (letI := e.pullbackChartedSpace (H := H); e.symm.pullbackChartedSpace) =
      ‹ChartedSpace H M› := by
  rw [← pullbackChartedSpace_trans, symm_trans_self, pullbackChartedSpace_refl]

/-- The pulled-back structure satisfies every structure groupoid that the original structure
satisfies, since its coordinate changes are coordinate changes of `M`. -/
theorem pullback_hasGroupoid (e : N ≃ₜ M) (G : StructureGroupoid H) [HasGroupoid M G] :
    letI := e.pullbackChartedSpace (H := H)
    HasGroupoid N G := by
  let := e.pullbackChartedSpace (H := H)
  refine ⟨?_⟩
  rintro _ _ ⟨c, hc, rfl⟩ ⟨c', hc', rfl⟩
  rw [transOpenPartialHomeomorph_symm_trans]
  exact StructureGroupoid.compatible _ hc hc'

/-- A homeomorphism onto a `G`-structured space is a `G`-structomorphism for the pulled-back
structure. -/
def pullbackStructomorph (e : N ≃ₜ M) (G : StructureGroupoid H) [HasGroupoid M G] :
    letI := e.pullbackChartedSpace (H := H)
    Structomorph G N M :=
  letI := e.pullbackChartedSpace (H := H)
  { e with
    mem_groupoid := by
      rintro _ c' ⟨c, hc, rfl⟩ hc'
      rw [← transOpenPartialHomeomorph_eq_trans, transOpenPartialHomeomorph_symm_trans]
      exact StructureGroupoid.compatible _ hc hc' }

/-- The underlying homeomorphism of the pulled-back structomorphism is `e`. -/
@[simp]
theorem pullbackStructomorph_toHomeomorph (e : N ≃ₜ M) (G : StructureGroupoid H)
    [HasGroupoid M G] :
    letI := e.pullbackChartedSpace (H := H)
    (e.pullbackStructomorph G).toHomeomorph = e :=
  (rfl)

section Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω)

/-- The pulled-back extended chart at `x` is `e` followed by the extended chart of `M` at `e x`. -/
theorem pullbackChartedSpace_extChartAt (e : N ≃ₜ M) (x : N) :
    letI := e.pullbackChartedSpace (H := H)
    extChartAt I x = e.toEquiv.transPartialEquiv (extChartAt I (e x)) := by
  let := e.pullbackChartedSpace (H := H)
  rw [extChartAt, OpenPartialHomeomorph.extend, pullbackChartedSpace_chartAt, extChartAt,
    OpenPartialHomeomorph.extend]
  -- The underlying partial equivalence of `e.transOpenPartialHomeomorph c` is, by definition,
  -- `e.toEquiv.transPartialEquiv c.toPartialEquiv`.
  exact e.toEquiv.transPartialEquiv_trans _ _

/-- The structure pulled back from a `C^n` manifold along a homeomorphism is a `C^n` manifold. -/
theorem pullback_isManifold (e : N ≃ₜ M) [IsManifold I n M] :
    letI := e.pullbackChartedSpace (H := H)
    IsManifold I n N :=
  letI := e.pullbackChartedSpace (H := H)
  haveI := e.pullback_hasGroupoid (contDiffGroupoid n I)
  { }

/-- A homeomorphism onto a charted space is a `C^n` diffeomorphism for the pulled-back structure:
read in a pulled-back chart and in the corresponding chart of `M`, both it and its inverse are the
identity. -/
def pullbackDiffeomorph (e : N ≃ₜ M) :
    letI := e.pullbackChartedSpace (H := H)
    N ≃ₘ^n⟮I, I⟯ M :=
  letI := e.pullbackChartedSpace (H := H)
  -- In matching charts `e` and `e.symm` read as the identity, since the pulled-back chart at `x`
  -- is the chart of `M` at `e x` precomposed with `e` (`pullbackChartedSpace_chartAt`, a simp
  -- lemma). So both fields reduce to the smoothness of the identity of `M`.
  { e.toEquiv with
    contMDiff_toFun := fun x ↦ by
      have h := contMDiffAt_id (I := I) (n := n) (x := e x)
      rw [contMDiffAt_iff] at h ⊢
      refine ⟨e.continuous.continuousAt, ?_⟩
      convert h.2 using 1 <;> simp [Function.comp_def]
    contMDiff_invFun := fun y ↦ by
      have h := contMDiffAt_id (I := I) (n := n) (x := y)
      rw [contMDiffAt_iff] at h ⊢
      refine ⟨e.symm.continuous.continuousAt, ?_⟩
      convert h.2 using 1
      simp [Function.comp_def] }

/-- The underlying map of the pulled-back diffeomorphism is `e`. -/
@[simp]
theorem coe_pullbackDiffeomorph (e : N ≃ₜ M) :
    letI := e.pullbackChartedSpace (H := H)
    ⇑(e.pullbackDiffeomorph I n) = e :=
  (rfl)

/-- The underlying map of the inverse of the pulled-back diffeomorphism is `e.symm`. -/
@[simp]
theorem coe_pullbackDiffeomorph_symm (e : N ≃ₜ M) :
    letI := e.pullbackChartedSpace (H := H)
    ⇑(e.pullbackDiffeomorph I n).symm = e.symm :=
  (rfl)

/-- The underlying homeomorphism of the pulled-back diffeomorphism is `e`. -/
@[simp]
theorem pullbackDiffeomorph_toHomeomorph (e : N ≃ₜ M) :
    letI := e.pullbackChartedSpace (H := H)
    (e.pullbackDiffeomorph I n).toHomeomorph = e :=
  (rfl)

end Manifold

end Homeomorph

namespace Diffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω} [ChartedSpace H N] [IsManifold I n N]

/-- A `C^n` diffeomorphism `h : N ≃ₘ^n⟮I, I⟯ M` pulls a chart `φ` of the maximal `C^n` atlas of
`M` back to the chart `φ ∘ h` of the maximal `C^n` atlas of `N`. For a mere homeomorphism the
pulled-back chart lies in the topological atlas, but not in general in the maximal `C^n` atlas. -/
theorem transOpenPartialHomeomorph_mem_maximalAtlas (h : N ≃ₘ^n⟮I, I⟯ M)
    {φ : OpenPartialHomeomorph M H} (hφ : φ ∈ IsManifold.maximalAtlas I n M) :
    h.toHomeomorph.transOpenPartialHomeomorph φ ∈ IsManifold.maximalAtlas I n N := by
  rw [IsManifold.mem_maximalAtlas_iff_contMDiffOn]
  exact ⟨(contMDiffOn_of_mem_maximalAtlas hφ).comp h.contMDiff.contMDiffOn fun _ hx ↦ hx,
    h.symm.contMDiff.comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas hφ)⟩

/-- The charts pulled back along a `C^n` diffeomorphism `h : N ≃ₘ^n⟮I, I⟯ M` belong to the maximal
`C^n` atlas of `N`. So the pulled-back structure is compatible with the structure that `N` already
carries. -/
theorem atlas_pullbackChartedSpace_subset_maximalAtlas [IsManifold I n M]
    (h : N ≃ₘ^n⟮I, I⟯ M) :
    (h.toHomeomorph.pullbackChartedSpace (H := H)).atlas ⊆ IsManifold.maximalAtlas I n N := by
  rintro _ ⟨c, hc, rfl⟩
  exact h.transOpenPartialHomeomorph_mem_maximalAtlas (IsManifold.subset_maximalAtlas hc)

end Diffeomorph
