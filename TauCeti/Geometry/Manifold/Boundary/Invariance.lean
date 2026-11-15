/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Real
public import TauCeti.AlgebraicTopology.Singular.InvarianceOfDomain

/-!
# Topological invariance of the boundary of a manifold

Mathlib defines the interior and boundary points of a manifold with corners through the preferred
chart at each point, and proves that every other chart detects them only for `C¹` manifolds
(`ModelWithCorners.isInteriorPoint_iff_of_mem_atlas`), by a derivative argument. This file proves
the same chart independence for topological manifolds modelled on a finite-dimensional real space,
by invariance of domain (`IsOpen.image_of_continuousOn_of_injOn`). So the boundary of a manifold
whose transition maps are merely continuous, for instance PL, can be read off in any chart.

* `ContinuousOn.isInteriorPoint_of_injOn`: a continuous map injective on an open neighbourhood of
  an interior point, between manifolds modelled on spaces of the same finite dimension, sends it
  to an interior point.
* `ModelWithCorners.isInteriorPoint_iff_mem_interior_range_of_finiteDimensional` and
  `ModelWithCorners.isBoundaryPoint_iff_mem_frontier_range_of_finiteDimensional`: any chart
  around a point, in the atlas or not, detects whether it is an interior or a boundary point.
* `ModelWithCorners.isOpen_interior_of_finiteDimensional`,
  `ModelWithCorners.isClosed_boundary_of_finiteDimensional`: the interior is open and the boundary
  is closed.

In the same way, let `A` be a subset of a finite-dimensional real normed space `E`, and let `φ` be
a homeomorphism from an open subset of `A` onto an open subset of the half-space model
`EuclideanHalfSpace m × V`, where `m + dim V = dim E`. A point `y` of the source of `φ` which is not
an interior point of `A` in `E` is sent to the boundary hyperplane: the zeroth coordinate of `φ y`
vanishes (`OpenPartialHomeomorph.coe_fst_apply_zero_eq_zero_of_notMem_interior`). This is the form
needed when an arbitrary chart of a subset with nonempty frontier, such as a closed ball, takes
values in a half-space model. Otherwise `φ.symm`, restricted to the open set of points of the
target with positive zeroth coordinate, would be a continuous injection of an open subset of
`ℝᵐ × V` into `E` whose image contains `y` and lies in `A`. By invariance of domain that image is
open in `E`, so `y` would be an interior point of `A`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press (2002), Theorem 2B.3 (invariance
  of domain).
-/

public section

open Set Module

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
    (hyA : (y : E) ∉ interior A) : (φ y).1.1 0 = 0 := by
  by_contra hne
  have hpos : 0 < (φ y).1.1 0 := lt_of_le_of_ne (φ y).1.2 (Ne.symm hne)
  -- Read the target of `φ` in `ℝᵐ × V` through the model `𝓡∂ m` and its continuous inverse.
  set I := modelWithCornersEuclideanHalfSpace m
  let j : EuclideanSpace ℝ (Fin m) × V → EuclideanHalfSpace m × V := Prod.map I.symm id
  have hj : Continuous j := I.continuous_symm.prodMap continuous_id
  set U : Set (EuclideanSpace ℝ (Fin m) × V) := j ⁻¹' φ.target ∩ {p | 0 < p.1 0}
  have hU : IsOpen U :=
    (hj.isOpen_preimage _ φ.open_target).inter
      (isOpen_lt continuous_const ((PiLp.continuous_apply 2 _ 0).comp continuous_fst))
  let f : EuclideanSpace ℝ (Fin m) × V → E := fun p => (φ.symm (j p) : E)
  have hf : ContinuousOn f U :=
    continuous_subtype_val.comp_continuousOn
      (φ.continuousOn_symm.comp hj.continuousOn fun _ hp => hp.1)
  -- On points of positive zeroth coordinate, `j` is injective, so `f` is injective on `U`.
  have hjI {p : EuclideanSpace ℝ (Fin m) × V} (hp : 0 < p.1 0) : I (j p).1 = p.1 :=
    I.right_inv (by
      rw [range_modelWithCornersEuclideanHalfSpace]
      exact hp.le)
  have hinj : InjOn f U := by
    intro p hp q hq hpq
    have hjpq : j p = j q := φ.symm.injOn (φ.symm_source ▸ hp.1) (φ.symm_source ▸ hq.1)
      (Subtype.ext hpq)
    have h2 : (j p).2 = (j q).2 := congrArg Prod.snd hjpq
    exact Prod.ext (by rw [← hjI hp.2, ← hjI hq.2, hjpq]) h2
  have hfin : finrank ℝ (EuclideanSpace ℝ (Fin m) × V) = finrank ℝ E := by
    rw [hdim, finrank_prod, finrank_euclideanSpace_fin]
  have hopen : IsOpen (f '' U) := hU.image_of_continuousOn_of_injOn hf hinj hfin
  -- The point `y` is the image of the reading of `φ y`, and the image of `f` lies in `A`.
  set p₀ : EuclideanSpace ℝ (Fin m) × V := (I (φ y).1, (φ y).2)
  have hjp₀ : j p₀ = φ y := Prod.ext (I.left_inv _) rfl
  have hp₀ : p₀ ∈ U := ⟨by rw [mem_preimage, hjp₀]; exact φ.map_source hy, hpos⟩
  have hfp₀ : f p₀ = y := by
    simp only [f, hjp₀, φ.left_inv hy]
  refine hyA (interior_maximal ?_ hopen ⟨p₀, hp₀, hfp₀⟩)
  rintro _ ⟨p, -, rfl⟩
  exact (φ.symm (j p)).2

end OpenPartialHomeomorph

section ChartIndependence

variable {E H E' H' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} {M N : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace H' N]

/-- **Invariance of interior points.** Let `M` and `N` be charted spaces modelled with corners on
real normed spaces of the same finite dimension. A map `f : M → N` which is continuous and
injective on an open neighbourhood of an interior point `x` of `M` sends `x` to an interior point
of `N`. -/
theorem ContinuousOn.isInteriorPoint_of_injOn [FiniteDimensional ℝ E']
    (hEE' : finrank ℝ E = finrank ℝ E') {f : M → N} {U : Set M} (hf : ContinuousOn f U)
    (hU : IsOpen U) (hinj : InjOn f U) {x : M} (hxU : x ∈ U) (hx : I.IsInteriorPoint x) :
    I'.IsInteriorPoint (f x) := by
  set c := chartAt H x
  set d := chartAt H' (f x)
  -- Read `f` in the model spaces, on the open set `W` of interior coordinates of the points of
  -- `U` that `f` carries into the source of `d`.
  set V := U ∩ f ⁻¹' d.source
  have hV : IsOpen V := hf.isOpen_inter_preimage hU d.open_source
  set W : Set E := interior (range I) ∩ I.symm ⁻¹' (c.target ∩ c.symm ⁻¹' V)
  have hW : IsOpen W :=
    isOpen_interior.inter (I.continuous_symm.isOpen_preimage _ (c.isOpen_inter_preimage_symm hV))
  set g : E → E' := I' ∘ d ∘ f ∘ c.symm ∘ I.symm
  have hg : ContinuousOn g W :=
    I'.continuous.comp_continuousOn <| d.continuousOn.comp
      ((hf.mono inter_subset_left).comp
        (c.continuousOn_symm.comp I.continuous_symm.continuousOn fun _ hy => hy.2.1)
        fun _ hy => hy.2.2)
      fun _ hy => hy.2.2.2
  have hginj : InjOn g W := by
    intro y hy z hz hyz
    have h₁ := hinj hy.2.2.1 hz.2.2.1
      (d.injOn hy.2.2.2 hz.2.2.2 (I'.injective hyz))
    have h₂ := c.symm.injOn (c.symm_source ▸ hy.2.1) (c.symm_source ▸ hz.2.1) h₁
    rw [← I.right_inv (interior_subset hy.1), ← I.right_inv (interior_subset hz.1)]
    exact congrArg I h₂
  -- By invariance of domain `g '' W` is open; it lies in `range I'`, hence in its interior.
  have hgW : g '' W ⊆ interior (range I') :=
    interior_maximal (image_subset_iff.2 fun _ _ => mem_range_self _)
      (hW.image_of_continuousOn_of_injOn hg hginj hEE')
  have hxW : I (c x) ∈ W := by
    have hxV : x ∈ V := ⟨hxU, mem_chart_source H' (f x)⟩
    refine ⟨hx, by simp [c, mem_chart_source], ?_⟩
    simpa [c, mem_chart_source] using hxV
  have := hgW (mem_image_of_mem g hxW)
  simpa [ModelWithCorners.IsInteriorPoint, g, c, d, mem_chart_source] using this

namespace ModelWithCorners

/-- On a model space, a point is an interior point exactly when the model sends it into the
interior of its range. -/
private theorem isInteriorPoint_iff_mem_interior_range_self {z : H} :
    I.IsInteriorPoint z ↔ I z ∈ interior (range I) := by
  rw [IsInteriorPoint, extChartAt_self_apply]

/-- **Chart independence of interior points.** On a charted space modelled with corners on a
finite-dimensional real space, every chart around `x`, in the atlas or not, detects whether `x` is
an interior point: exactly when it reads `x` in the interior of the range of the model. -/
theorem isInteriorPoint_iff_mem_interior_range_of_finiteDimensional [FiniteDimensional ℝ E]
    {e : OpenPartialHomeomorph M H} {x : M} (hx : x ∈ e.source) :
    I.IsInteriorPoint x ↔ I (e x) ∈ interior (range I) := by
  rw [← isInteriorPoint_iff_mem_interior_range_self]
  refine ⟨fun h => e.continuousOn.isInteriorPoint_of_injOn rfl e.open_source e.injOn hx h,
    fun h => ?_⟩
  simpa [e.left_inv hx] using
    e.continuousOn_symm.isInteriorPoint_of_injOn (I' := I) rfl e.open_target e.symm.injOn
      (e.map_source hx) h

/-- **Chart independence of boundary points.** On a charted space modelled with corners on a
finite-dimensional real space, every chart around `x`, in the atlas or not, detects whether `x` is
a boundary point: exactly when it reads `x` in the frontier of the range of the model. -/
theorem isBoundaryPoint_iff_mem_frontier_range_of_finiteDimensional [FiniteDimensional ℝ E]
    {e : OpenPartialHomeomorph M H} {x : M} (hx : x ∈ e.source) :
    I.IsBoundaryPoint x ↔ I (e x) ∈ frontier (range I) := by
  rw [I.isBoundaryPoint_iff_not_isInteriorPoint,
    isInteriorPoint_iff_mem_interior_range_of_finiteDimensional hx, I.isClosed_range.frontier_eq]
  simp

variable (I M)

/-- The interior of a charted space modelled with corners on a finite-dimensional real space is
open. -/
theorem isOpen_interior_of_finiteDimensional [FiniteDimensional ℝ E] : IsOpen (I.interior M) := by
  refine isOpen_iff_forall_mem_open.2 fun x hx => ⟨_, fun y hy => ?_,
    isOpen_extChartAt_preimage (I := I) x isOpen_interior, mem_chart_source H x, hx⟩
  exact (isInteriorPoint_iff_mem_interior_range_of_finiteDimensional hy.1).2 (by simpa using hy.2)

/-- The boundary of a charted space modelled with corners on a finite-dimensional real space is
closed. -/
theorem isClosed_boundary_of_finiteDimensional [FiniteDimensional ℝ E] :
    IsClosed (I.boundary M) := by
  rw [← I.compl_interior, isClosed_compl_iff]
  exact isOpen_interior_of_finiteDimensional I M

end ModelWithCorners

end ChartIndependence
