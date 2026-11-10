/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.PLGroupoid.Map
import TauCeti.Topology.PL.LocalInverse

/-!
# PL homeomorphisms have PL inverses

A homeomorphism of charted spaces which is a PL map has a PL inverse (`TauCeti.IsPLMap.symm`),
pointwise as `TauCeti.IsPLMapAt.symm`. So the PL homeomorphisms between PL manifolds are exactly
the homeomorphisms that are PL maps, with no separate condition on the inverse. The model spaces
are finite dimensional, and the range of the source model with corners is a convex polyhedron.
This covers the boundaryless models, whose range is the whole space
(`ModelWithCorners.isConvexPolyhedron_range`), and the half-space model
`TauCeti.modelWithCornersHalfSpace`
(`TauCeti.isConvexPolyhedron_range_modelWithCornersHalfSpace`), on which the realizations of
combinatorial manifolds with boundary are modelled. In the same way, an open partial
homeomorphism of the model which is PL in the forward direction belongs to the PL groupoid
(`TauCeti.mem_PLGroupoid_iff_isPLOn`).

Read in charts, the inverse is a local inverse of the chart reading of the map, so this is
`TauCeti.IsPLWithinAt.of_local_left_inverse` applied in the model vector spaces.

Reference: C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer
(1972), Chapter 1 (PL maps and PL manifolds).
-/

public section

open Set Filter Topology

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'}
  {M M' : Type*} [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace M']
  [ChartedSpace H' M']

/-- The range of a boundaryless model with corners, the whole model vector space, is a convex
polyhedron. -/
theorem _root_.ModelWithCorners.isConvexPolyhedron_range (I : ModelWithCorners ℝ E H)
    [I.Boundaryless] : IsConvexPolyhedron (range I) :=
  I.range_eq_univ ▸ isConvexPolyhedron_univ

/-- Near a point `w` of the range of `I` whose preimage lies in the source of `e`, reading `e` in
the model vector spaces and then reading `e.symm` back is the identity. -/
private theorem eventually_modelReading_symm_modelReading (e : OpenPartialHomeomorph H H')
    {w : E} (hw : I.symm w ∈ e.source) :
    ∀ᶠ z in 𝓝[range I] w, (I ∘ e.symm ∘ I'.symm) ((I' ∘ e ∘ I.symm) z) = z := by
  filter_upwards [inter_mem_nhdsWithin (range I)
    ((e.open_source.preimage I.continuous_symm).mem_nhds hw)] with z ⟨⟨v, hv⟩, hzs⟩
  subst hv
  simp only [mem_preimage, I.left_inv] at hzs
  simp [e.left_inv hzs]

/-- Near the chart image of `x`, reading `φ` in the preferred charts at `x` and `φ x` and then
reading `φ.symm` back is the identity. -/
private theorem eventually_chartReading_symm_chartReading (φ : M ≃ₜ M') (x : M) :
    ∀ᶠ z in 𝓝[range I] (I (chartAt H x x)),
      (I ∘ chartAt H x ∘ φ.symm ∘ (chartAt H' (φ x)).symm ∘ I'.symm)
        ((I' ∘ chartAt H' (φ x) ∘ φ ∘ (chartAt H x).symm ∘ I.symm) z) = z := by
  have := eventually_modelReading_symm_modelReading (I := I) (I' := I')
    (((chartAt H x).symm.trans φ.toOpenPartialHomeomorph).trans (chartAt H' (φ x)))
    (w := I (chartAt H x x)) (by simp [mem_chart_source])
  simpa [OpenPartialHomeomorph.coe_trans, OpenPartialHomeomorph.coe_trans_symm,
    Function.comp_assoc] using this

/-- **A PL homeomorphism has a PL inverse, pointwise.** If a homeomorphism `φ` is PL at `x`,
then its inverse is PL at `φ x`, provided the model spaces are finite dimensional and the range
of the model of the source is a convex polyhedron. -/
theorem IsPLMapAt.symm [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
    (hI : IsConvexPolyhedron (range I)) {φ : M ≃ₜ M'} {x : M} (h : IsPLMapAt I I' φ x) :
    IsPLMapAt I' I φ.symm (φ x) := by
  rw [isPLMapAt_iff] at h ⊢
  refine ⟨φ.symm.continuous.continuousAt, ?_⟩
  simp only [Homeomorph.symm_apply_apply]
  set c := chartAt H x
  set d := chartAt H' (φ x)
  have hga : (I ∘ c ∘ φ.symm ∘ d.symm ∘ I'.symm) (I' (d (φ x))) = I (c x) := by
    simp [c, d, mem_chart_source]
  have hg : ContinuousAt (I ∘ c ∘ φ.symm ∘ d.symm ∘ I'.symm) (I' (d (φ x))) := by
    refine I.continuous.continuousAt.comp (ContinuousAt.comp ?_
      (φ.symm.continuous.continuousAt.comp ((d.continuousAt_symm ?_).comp
        I'.continuous_symm.continuousAt)))
    · simpa [c, d, mem_chart_source] using c.continuousAt (mem_chart_source H x)
    · simp [d]
  refine (hga ▸ h.2).of_local_left_inverse hI hg.continuousWithinAt (mem_range_self _) ?_
    (hga ▸ eventually_chartReading_symm_chartReading φ x)
  have hback := eventually_chartReading_symm_chartReading (I := I') (I' := I) φ.symm (φ x)
  simp only [Homeomorph.symm_apply_apply, Homeomorph.symm_symm] at hback
  filter_upwards [hback] with y hy
  exact ⟨mem_range_self _, hy⟩

/-- **A PL homeomorphism has a PL inverse.** The inverse of a homeomorphism which is a PL map is
a PL map, provided the model spaces are finite dimensional and the range of the model of the
source is a convex polyhedron. -/
theorem IsPLMap.symm [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
    (hI : IsConvexPolyhedron (range I)) {φ : M ≃ₜ M'} (h : IsPLMap I I' φ) :
    IsPLMap I' I φ.symm := isPLMap_iff_forall_isPLMapAt.2 fun y => by
  simpa using (h.isPLMapAt (φ.symm y)).symm hI

/-- **The PL groupoid consists of the PL open partial homeomorphisms.** When the model space is
finite dimensional and the range of the model is a convex polyhedron, an open partial
homeomorphism of the model belongs to `TauCeti.PLGroupoid I` as soon as it is PL when read in the
model vector space: its inverse is then PL automatically. -/
theorem mem_PLGroupoid_iff_isPLOn [FiniteDimensional ℝ E] (hI : IsConvexPolyhedron (range I))
    {e : OpenPartialHomeomorph H H} :
    e ∈ PLGroupoid I ↔ IsPLOn (I ∘ e ∘ I.symm) (I.symm ⁻¹' e.source ∩ range I) := by
  refine ⟨fun he => ((mem_PLGroupoid_iff I).1 he).1, fun he => (mem_PLGroupoid_iff I).2 ⟨he, ?_⟩⟩
  refine isPLOn_iff_forall_isPLWithinAt.2 fun w hw => ?_
  have hwt : I.symm w ∈ e.target := hw.1
  have hsource : I.symm ⁻¹' e.source ∈ 𝓝 ((I ∘ e.symm ∘ I.symm) w) :=
    (e.open_source.preimage I.continuous_symm).mem_nhds (by simpa using e.map_target hwt)
  have hf : IsPLWithinAt (I ∘ e ∘ I.symm) (range I) ((I ∘ e.symm ∘ I.symm) w) := by
    rw [← isPLWithinAt_inter hsource, inter_comm]
    exact he.isPLWithinAt ⟨by simpa using e.map_target hwt, mem_range_self _⟩
  have hg : ContinuousWithinAt (I ∘ e.symm ∘ I.symm) (range I) w :=
    (I.continuous.continuousAt.comp ((e.continuousAt_symm hwt).comp
      I.continuous_symm.continuousAt)).continuousWithinAt
  refine (hf.of_local_left_inverse hI hg hw.2 ?_ ?_).mono inter_subset_right
  · filter_upwards [eventually_modelReading_symm_modelReading (I' := I) e.symm hwt] with y hy
    exact ⟨mem_range_self _, by simpa using hy⟩
  · exact eventually_modelReading_symm_modelReading (I' := I) e (by simpa using e.map_target hwt)

end TauCeti
