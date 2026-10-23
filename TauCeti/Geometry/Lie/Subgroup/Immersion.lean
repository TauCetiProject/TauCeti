/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.LieGroup
public import Mathlib.Geometry.Manifold.ImmersionDiff
public import Mathlib.Geometry.Manifold.MFDeriv.Tangent

/-!
# The differential of a slice-chart subgroup inclusion

A smooth ambient chart identifying a subgroup with the zero transverse slice makes the subgroup
inclusion smooth.  This file records that the inclusion is moreover an immersion in the sense of
differentials: at every point its differential admits a continuous left inverse, hence is
injective.

The reason is that the inclusion has a smooth left inverse in charts.  The preferred chart of the
subgroup at `g` is the tangential coordinate `x ↦ (e (g⁻¹ * x)).1` of the translated ambient chart,
and that same formula is a smooth function on a neighbourhood of `g` in the *ambient* group.
Composing it with the inclusion returns the subgroup chart itself, whose differential at its own
base point is the identity, so the differential of the ambient tangential coordinate splits the
differential of the inclusion.

Since the subgroup carries its subspace topology, the inclusion is also a topological embedding, so
together these say the inclusion is an embedding of smooth manifolds.  What is recorded here is the
differential form of being an immersion, `IsDiffImmersionAt`; the chart form,
`Manifold.IsImmersion`, which asks for charts of the subgroup and of the ambient group in which the
inclusion reads as `u ↦ (u, 0)`, is not derived from it.

## Main result

* `Subgroup.isDiffImmersionAt_subtypeVal_chartedSpaceOfIsSliceChart`: the differential of the
  subgroup inclusion has a continuous left inverse at every point.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd edition (2013), Theorem 20.12.
* J. Hilgert and K.-H. Neeb, *Structure and Geometry of Lie Groups* (2012), Section 9.1.
-/

public section

noncomputable section

namespace Subgroup

open Set
open scoped ContDiff Manifold Topology

variable {E H G F F' : Type*} {n : ℕ∞ω} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup F'] [NormedSpace ℝ F']
  [ContMDiffMul I n G]

variable (K : Subgroup G) (e : OpenPartialHomeomorph G (F × F'))
  (he : TauCeti.IsSliceChart e ((univ : Set F) ×ˢ ({0} : Set F')) (K : Set G))
  (h1 : (1 : G) ∈ e.source)
  (he' : ContMDiffOn I 𝓘(ℝ, F × F') n e e.source)
  (he_symm : ContMDiffOn 𝓘(ℝ, F × F') I n e.symm e.target)

include he' he_symm in
/-- The inclusion of a subgroup carrying its slice-chart manifold structure into the ambient
smooth group is an immersion in the sense of differentials: its differential at each point has a
continuous left inverse, and so is injective. -/
theorem isDiffImmersionAt_subtypeVal_chartedSpaceOfIsSliceChart (hn : 1 ≤ n) (k : K) :
    let _ : ContinuousMul G := continuousMul_of_contMDiffMul I n
    let _ : ChartedSpace F K := chartedSpaceOfIsSliceChart K e he h1
    IsDiffImmersionAt 𝓘(ℝ, F) I (fun x : K ↦ (x : G)) k := by
  dsimp only
  let _ : ContinuousMul G := continuousMul_of_contMDiffMul I n
  let _ : ChartedSpace F K := chartedSpaceOfIsSliceChart K e he h1
  let _ : IsManifold 𝓘(ℝ, F) n K :=
    isManifold_chartedSpaceOfIsSliceChart K e he h1 he' he_symm
  have _ : IsManifold I 1 G := IsManifold.of_le hn
  have _ : IsManifold 𝓘(ℝ, F) 1 K := IsManifold.of_le hn
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have hsrc : (k : G)⁻¹ * (k : G) ∈ e.source := by simpa using h1
  -- The tangential coordinate of the ambient chart translated to `k`, as a function on `G`.
  have hr : ContMDiffAt I 𝓘(ℝ, F) n (fun x : G ↦ (e ((k : G)⁻¹ * x)).1) (k : G) :=
    contDiff_fst.contMDiff.contMDiffAt.comp _
      ((he'.contMDiffAt (e.open_source.mem_nhds hsrc)).comp _ contMDiff_mul_left.contMDiffAt)
  have hincl : ContMDiff 𝓘(ℝ, F) I n (fun x : K ↦ (x : G)) :=
    contMDiff_subtypeVal_chartedSpaceOfIsSliceChart K e he h1 he_symm
  -- Restricted to the subgroup it is the preferred subgroup chart at `k`.
  have hcomp : (fun x : G ↦ (e ((k : G)⁻¹ * x)).1) ∘ (fun x : K ↦ (x : G)) =
      ⇑(chartAt F k) := by
    funext x
    rw [chartedSpaceOfIsSliceChart_chartAt K e he h1 k, preferredSliceChart_apply]
    rfl
  refine IsDiffImmersionAt.of_comp (hincl.mdifferentiableAt hn0) (hr.mdifferentiableAt hn0) ?_
  -- A chart has the identity as its differential at its own base point.
  rw [isDiffImmersionAt_iff, hcomp,
    mfderiv_chartAt_eq_tangentCoordChange (mem_chart_source F k)]
  refine ⟨ContinuousLinearMap.id ℝ F, fun v ↦ ?_⟩
  exact tangentCoordChange_self (I := 𝓘(ℝ, F)) (mem_extChartAt_source (I := 𝓘(ℝ, F)) k)

end Subgroup
