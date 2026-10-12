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
any such atlas are compatible. In particular, a covering map determines a unique smooth
structure on its total space up to atlas compatibility.

We use `IsLocalHomeomorph.chartedSpaceComap` for the lifted atlas and Mathlib's
`OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn` to recognize its charts.
No second charted-space constructor is needed, and no global instance is installed.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 4,
  "Smooth Covering Maps".
-/

public section

open Set IsManifold
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
    (p : M → B) (hp : IsLocalHomeomorph p) (hpd : IsLocalDiffeomorph I I n p) :
    hp.chartedSpaceComap.atlas ⊆ maximalAtlas I n M := by
  intro e he
  obtain ⟨x, rfl⟩ := (mem_atlas_chartedSpaceComap hp e).mp he
  let L := hp.localInverseAt x
  let e := chartAt H (p x)
  have hL : ContMDiffOn I I n L L.source :=
    contMDiffOn_of_comp_isLocalDiffeomorph p hpd L.continuousOn
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

/-- An atlas making a local homeomorphism a `C^n` local diffeomorphism is compatible with
the pulled-back atlas: every mixed transition belongs to the `C^n` structure groupoid.
This applies in particular to the total space of a covering map. -/
theorem chartedSpaceComap_compatible [IsManifold I n M] [IsManifold I n B]
    (p : M → B) (hp : IsLocalHomeomorph p) (hpd : IsLocalDiffeomorph I I n p)
    {e e' : OpenPartialHomeomorph M H} (he : e ∈ atlas H M)
    (he' : e' ∈ hp.chartedSpaceComap.atlas) :
    e.symm.trans e' ∈ contDiffGroupoid n I :=
  compatible_of_mem_maximalAtlas (subset_maximalAtlas he)
    (chartedSpaceComap_atlas_subset_maximalAtlas p hp hpd he')

end TauCeti
