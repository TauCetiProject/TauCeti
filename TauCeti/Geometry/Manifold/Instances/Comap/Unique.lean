/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.Comap
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Lift

/-!
# Uniqueness of the smooth structure pulled back along a local homeomorphism

The charts pulled back along a local homeomorphism belong to the maximal smooth atlas of any
smooth structure for which the map is a local diffeomorphism. Thus the pulled-back atlas and
any such atlas are compatible. In particular, a covering map of a `C^n` manifold determines a
unique `C^n` structure on its total space, up to atlas compatibility, among those making the
projection a `C^n` local diffeomorphism.

We use `IsLocalHomeomorph.chartedSpaceComap` for the lifted atlas and Mathlib's
`OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn` to recognize its charts.
The theorems `TauCeti.chartedSpaceComap_atlas_subset_maximalAtlas` and
`TauCeti.compatible_chartedSpaceComap` express the inclusion and compatibility.

For a covering map `hp : IsCoveringMap p`, equip its total space with
`hp.isLocalHomeomorph.chartedSpaceComap`. A continuous lift `f` of a `C^n` map is then `C^n` by
`hp.isLocalHomeomorph.contMDiff_chartedSpaceComap_iff.2 ⟨hf, hpf⟩`, where `hf : Continuous f`
and `hpf : ContMDiff J I n (p ∘ f)`. For an arbitrary atlas making `p` a local diffeomorphism,
use `TauCeti.contMDiff_of_comp_isLocalDiffeomorph` instead.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 4,
  "Smooth Covering Maps".
-/

public section

open Set IsManifold TauCeti
open scoped Manifold ContDiff

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M B : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace B] [ChartedSpace H B] {n : ℕ∞ω}

/-- Every chart pulled back along a local homeomorphism belongs to any maximal `C^n` atlas
for which the map is a `C^n` local diffeomorphism. -/
theorem chartedSpaceComap_atlas_subset_maximalAtlas [IsManifold I n M] [IsManifold I n B]
    {p : M → B} (hp : IsLocalHomeomorph p) (hpd : IsLocalDiffeomorph I I n p) :
    hp.chartedSpaceComap.atlas ⊆ maximalAtlas I n M := by
  intro e he
  obtain ⟨x, rfl⟩ := (mem_atlas_chartedSpaceComap_iff hp e).mp he
  let L := hp.localInverseAt x
  let e := chartAt H (p x)
  have hL : ContMDiffOn I I n L L.source :=
    contMDiffOn_of_comp_isLocalDiffeomorphOn p (hpd.isLocalDiffeomorphOn _) L.continuousOn
      (contMDiffOn_id.congr fun y hy ↦ hp.apply_localInverseAt_of_mem hy)
  have hLs : ⇑L.symm = p := hp.localInverseAt_symm x
  refine (L.symm.trans e).mem_maximalAtlas_of_contMDiffOn ?_ ?_
  · simp only [OpenPartialHomeomorph.coe_trans, OpenPartialHomeomorph.trans_source,
      hLs]
    exact (contMDiffOn_chart (I := I) (n := n)).comp
      hpd.contMDiff.contMDiffOn (fun y hy ↦ hy.2)
  · simp only [OpenPartialHomeomorph.coe_trans_symm, OpenPartialHomeomorph.trans_target,
      OpenPartialHomeomorph.symm_symm, OpenPartialHomeomorph.symm_target]
    exact hL.comp ((contMDiffOn_chart_symm (I := I) (n := n)).mono
      (fun y hy ↦ hy.1)) (fun y hy ↦ hy.2)

/-- A maximal atlas making a local homeomorphism a `C^n` local diffeomorphism is compatible with
the pulled-back atlas: every mixed transition belongs to the `C^n` structure groupoid.
This applies in particular to the total space of a covering map. -/
theorem compatible_chartedSpaceComap [IsManifold I n M] [IsManifold I n B]
    {p : M → B} (hp : IsLocalHomeomorph p) (hpd : IsLocalDiffeomorph I I n p)
    {e e' : OpenPartialHomeomorph M H} (he : e ∈ maximalAtlas I n M)
    (he' : e' ∈ hp.chartedSpaceComap.atlas) :
    e.symm.trans e' ∈ contDiffGroupoid n I :=
  compatible_of_mem_maximalAtlas he (chartedSpaceComap_atlas_subset_maximalAtlas hp hpd he')

end TauCeti
