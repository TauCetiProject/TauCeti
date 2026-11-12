/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Cone.StrictInward
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

/-!
# Strictly inward tangent vectors and vector fields

A tangent vector at a point `x` of a manifold with corners is strictly inward when, read in the
preferred chart at `x`, it lies in the strict inward cone of the range of the model
(`TauCeti.strictInwardTangentCone`). Since the range of a model is convex with nonempty interior,
the derivatives of the changes of coordinates preserve these cones, so strict inwardness can be
read in any chart (`TauCeti.mem_strictInwardTangentCone_iff_tangentCoordChange`). The cone in
each tangent space is open, convex, nonempty and invariant under positive scaling; it is the
whole tangent space exactly at interior points.

On a Hausdorff σ-compact manifold over a finite-dimensional model there is a smooth vector field
that is strictly inward at every point
(`TauCeti.exists_contMDiffSection_mem_strictInwardTangentCone`). Near a point `x₀`, the field
which is constant in the chart at `x₀`, equal to `q - x₀` for an interior point `q` of the model,
is strictly inward; these local fields are glued by a smooth partition of unity, which keeps them
in the convex cones. Such fields are the input for forward semiflows that push a manifold with
corners into its interior.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013: Chapter 8 (inward-pointing vector fields along the boundary, glued from local
  ones by a partition of unity) and Theorems 9.24–9.26 (their flows). Here the model is any
  model with corners, and inwardness is required at every point.
-/

public section

open Set Filter Bundle
open scoped Topology Manifold ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) [TopologicalSpace M] [ChartedSpace H M]

/-- The strict inward cone in the tangent space at `x`: the tangent vectors which, read in the
preferred chart at `x`, are strictly inward to the range of the model. -/
noncomputable def strictInwardTangentCone (x : M) : Set (TangentSpace I x) :=
  strictInwardCone (E := E) (range I) (extChartAt I x x)

variable {I}

/-- A tangent vector is strictly inward when, read in the preferred chart, it is strictly inward
to the range of the model. -/
theorem mem_strictInwardTangentCone_iff {x : M} {v : TangentSpace I x} :
    v ∈ strictInwardTangentCone I x ↔ (v : E) ∈ strictInwardCone (range I) (extChartAt I x x) :=
  Iff.rfl

/-- The derivative of a change of coordinates sends strictly inward vectors to strictly inward
vectors. -/
theorem tangentCoordChange_mem_strictInwardCone [IsManifold I 1 M] {x y z : M}
    (hz : z ∈ (extChartAt I x).source ∩ (extChartAt I y).source) {v : E}
    (hv : v ∈ strictInwardCone (range I) (extChartAt I x z)) :
    tangentCoordChange I x y z v ∈ strictInwardCone (range I) (extChartAt I y z) := by
  have hsurj : Function.Surjective (tangentCoordChange I x y z) := fun u ↦
    ⟨tangentCoordChange I y x z u, by
      rw [tangentCoordChange_comp ⟨⟨hz.2, hz.1⟩, hz.2⟩, tangentCoordChange_self hz.2]⟩
  have h := (hasFDerivWithinAt_tangentCoordChange hz).mapsTo_strictInwardCone
    hsurj.denseRange I.convex_range I.nonempty_interior
    (Eventually.of_forall fun p ↦ by
      rw [Function.comp_apply, extChartAt_coe]; exact mem_range_self _)
    (by rw [Function.comp_apply, extChartAt_coe]; exact mem_range_self _) hv
  rwa [Function.comp_apply, (extChartAt I x).left_inv hz.1] at h

/-- Strict inwardness of a vector is independent of the chart it is read in. -/
theorem tangentCoordChange_mem_strictInwardCone_iff [IsManifold I 1 M] {x y z : M}
    (hz : z ∈ (extChartAt I x).source ∩ (extChartAt I y).source) {v : E} :
    tangentCoordChange I x y z v ∈ strictInwardCone (range I) (extChartAt I y z) ↔
      v ∈ strictInwardCone (range I) (extChartAt I x z) := by
  refine ⟨fun h ↦ ?_, tangentCoordChange_mem_strictInwardCone hz⟩
  have h' := tangentCoordChange_mem_strictInwardCone ⟨hz.2, hz.1⟩ h
  rwa [tangentCoordChange_comp ⟨⟨hz.1, hz.2⟩, hz.1⟩, tangentCoordChange_self hz.1] at h'

/-- A tangent vector at `x` is strictly inward exactly when it is so read in any chart whose
domain contains `x`. -/
theorem mem_strictInwardTangentCone_iff_tangentCoordChange [IsManifold I 1 M] {x y : M}
    (hx : x ∈ (extChartAt I y).source) {v : TangentSpace I x} :
    v ∈ strictInwardTangentCone I x ↔
      tangentCoordChange I x y x v ∈ strictInwardCone (range I) (extChartAt I y x) :=
  (tangentCoordChange_mem_strictInwardCone_iff (v := v) ⟨mem_extChartAt_source x, hx⟩).symm

variable (I)

/-- The strict inward cone in a tangent space is open. -/
theorem isOpen_strictInwardTangentCone (x : M) : IsOpen (strictInwardTangentCone I x) := by
  rw [strictInwardTangentCone]
  exact isOpen_strictInwardCone (range I) (extChartAt I x x)

/-- The strict inward cone in a tangent space is convex. -/
theorem convex_strictInwardTangentCone (x : M) : Convex ℝ (strictInwardTangentCone I x) := by
  rw [strictInwardTangentCone]
  exact I.convex_range.convex_strictInwardCone (extChartAt I x x)

/-- Every tangent space contains strictly inward vectors. -/
theorem strictInwardTangentCone_nonempty (x : M) : (strictInwardTangentCone I x).Nonempty := by
  rw [strictInwardTangentCone]
  exact I.convex_range.strictInwardCone_nonempty (x := extChartAt I x x)
    (by rw [extChartAt_coe]; exact mem_range_self _) I.nonempty_interior

/-- Every tangent vector is strictly inward exactly at interior points. -/
@[simp]
theorem strictInwardTangentCone_eq_univ_iff {x : M} :
    strictInwardTangentCone I x = univ ↔ I.IsInteriorPoint x := by
  rw [strictInwardTangentCone, ModelWithCorners.IsInteriorPoint]
  exact strictInwardCone_eq_univ_iff

/-- On a manifold without boundary every tangent vector is strictly inward. -/
@[simp]
theorem strictInwardTangentCone_eq_univ [BoundarylessManifold I M] (x : M) :
    strictInwardTangentCone I x = univ :=
  (strictInwardTangentCone_eq_univ_iff I).mpr BoundarylessManifold.isInteriorPoint

variable {I}

/-- Positive rescaling preserves and reflects strict inwardness of tangent vectors. -/
@[simp]
theorem smul_mem_strictInwardTangentCone_iff {x : M} {v : TangentSpace I x} {c : ℝ}
    (hc : 0 < c) : c • v ∈ strictInwardTangentCone I x ↔ v ∈ strictInwardTangentCone I x := by
  rw [mem_strictInwardTangentCone_iff, mem_strictInwardTangentCone_iff]
  exact smul_mem_strictInwardCone_iff (E := E) (v := v) hc

variable (I)

/-- **Strictly inward vector fields exist.** A Hausdorff σ-compact manifold over a
finite-dimensional model carries a smooth vector field which is strictly inward at every point. -/
theorem exists_contMDiffSection_mem_strictInwardTangentCone [FiniteDimensional ℝ E] [T2Space M]
    [SigmaCompactSpace M] [IsManifold I ∞ M] :
    ∃ X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯, ∀ x, X x ∈ strictInwardTangentCone I x := by
  refine exists_contMDiffSection_forall_mem_convex_of_local I (TangentSpace I)
    (strictInwardTangentCone I) (convex_strictInwardTangentCone I) fun x₀ ↦ ?_
  obtain ⟨q, hq⟩ := I.nonempty_interior
  have hrange (y : M) : extChartAt I x₀ y ∈ range I := by
    rw [extChartAt_coe]; exact mem_range_self _
  -- The constant vector `q - x₀` of the chart at `x₀` stays strictly inward near `x₀`.
  set w : E := q - extChartAt I x₀ x₀
  have hw : ∀ᶠ y in 𝓝 x₀, w ∈ strictInwardCone (range I) (extChartAt I x₀ y) := by
    have hc : ContinuousAt (fun y : M ↦ ((⟨extChartAt I x₀ y, hrange y⟩ : range I), w)) x₀ :=
      ((continuousAt_extChartAt x₀).codRestrict hrange).prodMk continuousAt_const
    exact hc.preimage_mem_nhds (I.convex_range.isOpen_setOf_mem_strictInwardCone.mem_nhds
      (I.convex_range.sub_mem_strictInwardCone (hrange x₀) hq))
  refine ⟨(extChartAt I x₀).source ∩ {y | w ∈ strictInwardCone (range I) (extChartAt I x₀ y)},
    inter_mem (extChartAt_source_mem_nhds x₀) hw, fun y ↦ tangentCoordChange I x₀ y y w, ?_, ?_⟩
  · -- In the trivialization at `x₀` the local field is the constant `w`.
    refine ContMDiffOn.mono ?_ inter_subset_left
    refine ((trivializationAt E (TangentSpace I) x₀).contMDiffOn_section_iff
      (isOpen_extChartAt_source x₀) (by simp)).mpr ?_
    refine (contMDiffOn_const (c := w)).congr fun y hy ↦ ?_
    rw [TangentBundle.trivializationAt_apply, ← extChartAt.eq_1, ← extChartAt.eq_1,
      ← tangentCoordChange_def]
    exact (tangentCoordChange_comp (w := x₀) (x := y) (y := x₀)
      ⟨⟨hy, mem_extChartAt_source y⟩, hy⟩).trans (tangentCoordChange_self hy)
  · rintro y ⟨hy, hyw⟩
    exact mem_strictInwardTangentCone_iff.mpr
      ((tangentCoordChange_mem_strictInwardCone_iff ⟨hy, mem_extChartAt_source y⟩).mpr hyw)

end TauCeti
