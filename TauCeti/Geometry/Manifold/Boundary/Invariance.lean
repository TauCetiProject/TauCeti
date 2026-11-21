/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Real
public import TauCeti.AlgebraicTopology.Singular.InvarianceOfDomain
public import TauCeti.Geometry.Manifold.IsManifold.InteriorBoundary

/-!
# Topological invariance of the boundary of a manifold

Mathlib defines the interior and boundary points of a manifold with corners through the preferred
chart at each point, and proves that every other chart detects them only for `C¹` manifolds
(`ModelWithCorners.isInteriorPoint_iff_of_mem_atlas`), by a derivative argument. This file proves
the same chart independence for topological manifolds modelled on a finite-dimensional space, by
invariance of domain (`IsOpen.image_of_continuousOn_of_injOn`). So the boundary of a manifold
whose transition maps are merely continuous, for instance PL, can be read off in any chart. Over a
field other than `ℝ` or `ℂ` the range of a model with corners is the whole space, so there is no
boundary; over `ℂ` the real invariance of domain applies after restricting scalars.

* `ContinuousOn.isInteriorPoint_of_injOn`: a continuous map injective on a neighbourhood of an
  interior point, between manifolds modelled on spaces of the same finite dimension, sends it to
  an interior point.
* `ContinuousOn.image_mem_nhds_of_injOn`: over `ℝ` or `ℂ`, the image of such a neighbourhood is a
  neighbourhood of the image point.
* `OpenPartialHomeomorph.isInteriorPoint_iff` and `OpenPartialHomeomorph.isBoundaryPoint_iff`:
  a partial homeomorphism between charted spaces modelled on spaces of the same finite dimension
  preserves interior and boundary points. No groupoid or `IsManifold` assumption is needed, so
  this applies to topological and PL manifolds with boundary.
* `ModelWithCorners.isInteriorPoint_iff_mem_interior_range_of_finiteDimensional` and
  `ModelWithCorners.isBoundaryPoint_iff_mem_frontier_range_of_finiteDimensional`: any chart
  around a point, in the atlas or not, detects whether it is an interior or a boundary point.
* `ModelWithCorners.isOpen_interior_of_finiteDimensional`,
  `ModelWithCorners.isClosed_boundary_of_finiteDimensional`: the interior is open and the boundary
  is closed.

As a consequence, let `A` be a subset of a finite-dimensional real normed space `E`, and let `φ` be
a homeomorphism from an open subset of `A` onto an open subset of the half-space model
`EuclideanHalfSpace m × V`, where `m + dim V = dim E`. A point `y` of the source of `φ` which is not
an interior point of `A` in `E` is sent to the boundary hyperplane: the zeroth coordinate of `φ y`
vanishes (`OpenPartialHomeomorph.coe_fst_apply_zero_eq_zero_of_notMem_interior`). This is the form
needed when an arbitrary chart of a subset with nonempty frontier, such as a closed ball, takes
values in a half-space model. Otherwise `φ y` would be an interior point of the half-space model,
and `φ.symm`, a continuous injection into `E` with image in `A`, would carry a neighbourhood of
`φ y` onto a neighbourhood of `y`, so `y` would be an interior point of `A`.

The reduction from `𝕜` to `ℝ` in `ContinuousOn.isInteriorPoint_of_injOn` follows Mathlib's
`MDifferentiableAt.isInteriorPoint_of_surjective_mfderiv`, and the proofs of
`ModelWithCorners.isOpen_interior_of_finiteDimensional` and
`ModelWithCorners.isClosed_boundary_of_finiteDimensional` follow Mathlib's
`ModelWithCorners.isOpen_interior` and `ModelWithCorners.isClosed_boundary`, all in
`Mathlib/Geometry/Manifold/IsManifold/InteriorBoundary.lean` (Michael Rothgang, Ben Eltschig).

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press (2002), Theorem 2B.3 (invariance
  of domain).
-/

public section

open Set Module Topology

open scoped Manifold

section ChartIndependence

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E H E' H' : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [NormedAddCommGroup E']
  [NormedSpace 𝕜 E'] [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'} {M N : Type*}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]

/-- Over `ℝ` or `ℂ`, a map continuous and injective on a neighbourhood `U` of an interior point
`x`, between charted spaces modelled on spaces of the same finite dimension, sends `x` to an
interior point and `U` onto a neighbourhood of `f x`. -/
private theorem ContinuousOn.isInteriorPoint_and_image_mem_nhds_of_injOn [IsRCLikeNormedField 𝕜]
    [FiniteDimensional 𝕜 E'] (hEE' : finrank 𝕜 E = finrank 𝕜 E') {f : M → N} {U : Set M}
    {x : M} (hf : ContinuousOn f U) (hU : U ∈ 𝓝 x) (hinj : InjOn f U)
    (hx : I.IsInteriorPoint x) : I'.IsInteriorPoint (f x) ∧ f '' U ∈ 𝓝 (f x) := by
  simp only [ModelWithCorners.IsInteriorPoint, extChartAt_coe, Function.comp_apply] at hx ⊢
  set c := chartAt H x
  set d := chartAt H' (f x)
  -- Read `f` in the model spaces, on the open set `W` of interior coordinates of the points of
  -- the interior of `U` that `f` carries into the source of `d`.
  set V := interior U ∩ f ⁻¹' d.source
  have hV : IsOpen V :=
    (hf.mono interior_subset).isOpen_inter_preimage isOpen_interior d.open_source
  set W : Set E := interior (range I) ∩ I.symm ⁻¹' (c.target ∩ c.symm ⁻¹' V)
  have hW : IsOpen W :=
    isOpen_interior.inter (I.continuous_symm.isOpen_preimage _ (c.isOpen_inter_preimage_symm hV))
  set g : E → E' := I' ∘ d ∘ f ∘ c.symm ∘ I.symm
  have hg : ContinuousOn g W :=
    I'.continuous.comp_continuousOn <| d.continuousOn.comp
      ((hf.mono (inter_subset_left.trans interior_subset)).comp
        (c.continuousOn_symm.comp I.continuous_symm.continuousOn fun _ hy => hy.2.1)
        fun _ hy => hy.2.2)
      fun _ hy => hy.2.2.2
  have hginj : InjOn g W := by
    intro y hy z hz hyz
    have h₁ := hinj (interior_subset hy.2.2.1) (interior_subset hz.2.2.1)
      (d.injOn hy.2.2.2 hz.2.2.2 (I'.injective hyz))
    have h₂ := c.symm.injOn (c.symm_source ▸ hy.2.1) (c.symm_source ▸ hz.2.1) h₁
    rw [← I.right_inv (interior_subset hy.1), ← I.right_inv (interior_subset hz.1)]
    exact congrArg I h₂
  have hgW : IsOpen (g '' W) :=
    hW.image_of_continuousOn_of_injOn_of_isRCLikeNormedField (E := E) (F := E') hg hginj hEE'
  have hxW : I (c x) ∈ W := by
    have hxV : x ∈ V := ⟨mem_interior_iff_mem_nhds.2 hU, mem_chart_source H' (f x)⟩
    refine ⟨hx, by simp [c, mem_chart_source], ?_⟩
    simpa [c, mem_chart_source] using hxV
  have hgx : I' (d (f x)) ∈ g '' W := by
    convert mem_image_of_mem g hxW using 1
    simp [g, c, mem_chart_source]
  refine ⟨?_, ?_⟩
  · -- The open set `g '' W` lies in `range I'`, hence in its interior.
    exact interior_maximal (image_subset_iff.2 fun _ _ => mem_range_self _) hgW hgx
  · -- Through `d`, the open set `I' ⁻¹' (g '' W)` is a neighbourhood of `f x` inside `f '' U`.
    have hO : I' ⁻¹' (g '' W) ∈ 𝓝 (d (f x)) := (hgW.preimage I'.continuous).mem_nhds hgx
    refine Filter.mem_of_superset (d.left_inv (mem_chart_source H' (f x)) ▸
      d.symm.image_mem_nhds (d.map_source (mem_chart_source H' (f x))) hO) ?_
    rintro _ ⟨z, ⟨w, hw, hwz⟩, rfl⟩
    refine ⟨c.symm (I.symm w), interior_subset hw.2.2.1, ?_⟩
    rw [← d.left_inv hw.2.2.2, ← I'.injective hwz]
    rfl

/-- **Invariance of domain in charted spaces.** Over `ℝ` or `ℂ`, let `M` and `N` be charted spaces
modelled with corners, `N` through `I'`, on normed spaces of the same finite dimension. A map
`f : M → N` which is continuous and injective on a neighbourhood `U` of an interior point `x` of
`M` sends `U` onto a neighbourhood of `f x`. The model `I'` only serves to read `N` in a normed
space; the conclusion does not mention it. -/
theorem ContinuousOn.image_mem_nhds_of_injOn [IsRCLikeNormedField 𝕜] [FiniteDimensional 𝕜 E']
    (I' : ModelWithCorners 𝕜 E' H') (hEE' : finrank 𝕜 E = finrank 𝕜 E') {f : M → N} {U : Set M}
    {x : M} (hf : ContinuousOn f U) (hU : U ∈ 𝓝 x) (hinj : InjOn f U)
    (hx : I.IsInteriorPoint x) : f '' U ∈ 𝓝 (f x) :=
  (hf.isInteriorPoint_and_image_mem_nhds_of_injOn (I' := I') hEE' hU hinj hx).2

/-- **Invariance of interior points.** Let `M` and `N` be charted spaces modelled with corners on
normed spaces of the same finite dimension. A map `f : M → N` which is continuous and injective on
a neighbourhood of an interior point `x` of `M` sends `x` to an interior point of `N`. -/
theorem ContinuousOn.isInteriorPoint_of_injOn [FiniteDimensional 𝕜 E']
    (hEE' : finrank 𝕜 E = finrank 𝕜 E') {f : M → N} {U : Set M} {x : M} (hf : ContinuousOn f U)
    (hU : U ∈ 𝓝 x) (hinj : InjOn f U) (hx : I.IsInteriorPoint x) :
    I'.IsInteriorPoint (f x) := by
  -- Over a field other than `ℝ` or `ℂ`, the model `I'` has full range.
  wlog _ : IsRCLikeNormedField 𝕜
  · simp [ModelWithCorners.IsInteriorPoint, I'.range_eq_univ_of_not_isRCLikeNormedField ‹_›]
  exact (hf.isInteriorPoint_and_image_mem_nhds_of_injOn hEE' hU hinj hx).1

namespace OpenPartialHomeomorph

variable (I I')

/-- **Topological invariance of the interior.** A partial homeomorphism between charted spaces
modelled with corners on spaces of the same finite dimension preserves interior points. -/
theorem isInteriorPoint_iff [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 E']
    (φ : OpenPartialHomeomorph M N) (hEE' : finrank 𝕜 E = finrank 𝕜 E') {x : M}
    (hx : x ∈ φ.source) : I.IsInteriorPoint x ↔ I'.IsInteriorPoint (φ x) := by
  refine ⟨fun h => φ.continuousOn.isInteriorPoint_of_injOn hEE' (φ.open_source.mem_nhds hx)
    φ.injOn h, fun h => ?_⟩
  simpa [φ.left_inv hx] using
    φ.continuousOn_symm.isInteriorPoint_of_injOn (I' := I) hEE'.symm
      (φ.open_target.mem_nhds (φ.map_source hx)) φ.symm.injOn h

/-- **Topological invariance of the boundary.** A partial homeomorphism between charted spaces
modelled with corners on spaces of the same finite dimension preserves boundary points. -/
theorem isBoundaryPoint_iff [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 E']
    (φ : OpenPartialHomeomorph M N) (hEE' : finrank 𝕜 E = finrank 𝕜 E') {x : M}
    (hx : x ∈ φ.source) : I.IsBoundaryPoint x ↔ I'.IsBoundaryPoint (φ x) := by
  rw [I.isBoundaryPoint_iff_not_isInteriorPoint, I'.isBoundaryPoint_iff_not_isInteriorPoint,
    φ.isInteriorPoint_iff I I' hEE' hx]

end OpenPartialHomeomorph

namespace ModelWithCorners

/-- **Chart independence of interior points.** On a charted space modelled with corners on a
finite-dimensional space, every chart around `x`, in the atlas or not, detects whether `x` is an
interior point: exactly when it reads `x` in the interior of the range of the model. -/
theorem isInteriorPoint_iff_mem_interior_range_of_finiteDimensional [FiniteDimensional 𝕜 E]
    {e : OpenPartialHomeomorph M H} {x : M} (hx : x ∈ e.source) :
    I.IsInteriorPoint x ↔ I (e x) ∈ interior (range I) := by
  rw [e.isInteriorPoint_iff I I rfl hx, isInteriorPoint_iff_mem_interior_range_self]

/-- **Chart independence of boundary points.** On a charted space modelled with corners on a
finite-dimensional space, every chart around `x`, in the atlas or not, detects whether `x` is a
boundary point: exactly when it reads `x` in the frontier of the range of the model. -/
theorem isBoundaryPoint_iff_mem_frontier_range_of_finiteDimensional [FiniteDimensional 𝕜 E]
    {e : OpenPartialHomeomorph M H} {x : M} (hx : x ∈ e.source) :
    I.IsBoundaryPoint x ↔ I (e x) ∈ frontier (range I) := by
  rw [I.isBoundaryPoint_iff_not_isInteriorPoint,
    isInteriorPoint_iff_mem_interior_range_of_finiteDimensional hx, I.isClosed_range.frontier_eq]
  simp

variable (I M)

/-- The interior of a charted space modelled with corners on a finite-dimensional space is
open. -/
theorem isOpen_interior_of_finiteDimensional [FiniteDimensional 𝕜 E] : IsOpen (I.interior M) := by
  refine isOpen_iff_forall_mem_open.2 fun x hx => ⟨_, fun y hy => ?_,
    isOpen_extChartAt_preimage (I := I) x isOpen_interior, mem_chart_source H x, hx⟩
  exact (isInteriorPoint_iff_mem_interior_range_of_finiteDimensional hy.1).2 (by simpa using hy.2)

/-- The boundary of a charted space modelled with corners on a finite-dimensional space is
closed. -/
theorem isClosed_boundary_of_finiteDimensional [FiniteDimensional 𝕜 E] :
    IsClosed (I.boundary M) := by
  rw [← I.compl_interior, isClosed_compl_iff]
  exact isOpen_interior_of_finiteDimensional I M

end ModelWithCorners

end ChartIndependence

namespace OpenPartialHomeomorph

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {m : ℕ} [NeZero m]
  {A : Set E}

/-- **Invariance of the boundary of the half-space.** Let `φ` be a chart of a subset `A` of `E`
with values in the half-space model `EuclideanHalfSpace m × V`, where `m + dim V = dim E`. Then
`φ` sends every point of its source that is not an interior point of `A` to the boundary
hyperplane, where the zeroth coordinate vanishes. -/
theorem coe_fst_apply_zero_eq_zero_of_notMem_interior
    (φ : OpenPartialHomeomorph A (EuclideanHalfSpace m × V))
    (hdim : finrank ℝ E = m + finrank ℝ V) {y : A} (hy : y ∈ φ.source)
    (hyA : (y : E) ∉ interior A) : (φ y).1.val 0 = 0 := by
  by_contra hne
  have hpos : 0 < (φ y).1.val 0 := lt_of_le_of_ne (φ y).1.property (Ne.symm hne)
  -- Then `φ y` is an interior point of the half-space model, and `φ.symm` carries a neighbourhood
  -- of it onto a neighbourhood of `y` in `E`, which lies in `A`.
  have hint : ((𝓡∂ m).prod 𝓘(ℝ, V)).IsInteriorPoint (φ y) := by
    simp only [ModelWithCorners.IsInteriorPoint, extChartAt_prod, PartialEquiv.prod_coe,
      ModelWithCorners.range_prod, interior_prod_eq, mem_prod, extChartAt_self_apply,
      interior_range_modelWithCornersEuclideanHalfSpace,
      ModelWithCorners.Boundaryless.range_eq_univ, interior_univ, mem_univ, and_true,
      mem_ofPred_eq, modelWithCornersEuclideanHalfSpace_apply]
    exact hpos
  have hfin : finrank ℝ (EuclideanSpace ℝ (Fin m) × V) = finrank ℝ E := by
    rw [hdim, finrank_prod, finrank_euclideanSpace_fin]
  have hA : (Subtype.val ∘ φ.symm) '' φ.target ∈ 𝓝 (y : E) := by
    simpa [φ.left_inv hy] using
      (continuous_subtypeVal.comp_continuousOn φ.continuousOn_symm).image_mem_nhds_of_injOn
        𝓘(ℝ, E) hfin (φ.open_target.mem_nhds (φ.map_source hy))
        (Subtype.val_injective.comp_injOn φ.symm.injOn) hint
  refine hyA (mem_interior_iff_mem_nhds.2 (Filter.mem_of_superset hA ?_))
  rintro _ ⟨p, -, rfl⟩
  exact (φ.symm p).property

end OpenPartialHomeomorph
