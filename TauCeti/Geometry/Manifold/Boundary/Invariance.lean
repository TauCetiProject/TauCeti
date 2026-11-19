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

Mathlib detects the interior and boundary points of a manifold with boundary in an arbitrary chart
only for `C^1` manifolds (`ModelWithCorners.isInteriorPoint_iff_of_mem_atlas`), because its proof
reads the boundary off the derivative of the transition maps. For finite-dimensional real models
the statement is purely topological: by invariance of domain
(`IsOpen.image_of_continuousOn_of_injOn`), a continuous injection of an open subset of `ℝᵈ` into
`ℝᵈ` has open image, so a homeomorphism between open subsets of two models of the same dimension
carries interior points of the models to interior points. This file records the consequences.

* `OpenPartialHomeomorph.isInteriorPoint_iff` and `OpenPartialHomeomorph.isBoundaryPoint_iff`:
  a partial homeomorphism between charted spaces over finite-dimensional real models of the same
  dimension preserves interior and boundary points. No groupoid or `IsManifold` assumption is
  needed, so this applies to topological and PL manifolds with boundary.
* `OpenPartialHomeomorph.isInteriorPoint_iff_mem_interior_range` and
  `OpenPartialHomeomorph.isBoundaryPoint_iff_mem_frontier_range`: in particular, interior and
  boundary points are detected in *every* chart, not only in the preferred chart at the point.
* `ModelWithCorners.isOpen_interior_of_finiteDimensional` and
  `ModelWithCorners.isClosed_boundary_of_finiteDimensional`: hence the interior of a charted space
  over a finite-dimensional real model is open and its boundary is closed.
* `OpenPartialHomeomorph.coe_fst_apply_zero_eq_zero_of_notMem_interior`: let `A` be a subset of a
  finite-dimensional real normed space `E`, and let `φ` be a homeomorphism from an open subset of
  `A` onto an open subset of the half-space model `EuclideanHalfSpace m × V`, where
  `m + dim V = dim E`. A point `y` of the source of `φ` which is not an interior point of `A` in
  `E` is sent to the boundary hyperplane: the zeroth coordinate of `φ y` vanishes. This is the form
  needed when an arbitrary chart of a subset with nonempty frontier, such as a closed ball, takes
  values in a half-space model.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press (2002), Theorem 2B.3 (invariance
  of domain).
-/

public section

open Set Module

open scoped Manifold

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

section Manifold

variable {E' H H' M M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H] [TopologicalSpace H'] (I : ModelWithCorners ℝ E H)
  (J : ModelWithCorners ℝ E' H') [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace M']
  [ChartedSpace H' M']

omit [FiniteDimensional ℝ E] in
variable {I J} in
/-- A partial homeomorphism between models of the same finite dimension sends a point read in the
interior of the first model to a point read in the interior of the second. -/
private theorem mem_interior_range_apply (φ : OpenPartialHomeomorph H H')
    (hEF : finrank ℝ E = finrank ℝ E') {z : H} (hz : z ∈ φ.source)
    (hi : I z ∈ interior (range I)) : J (φ z) ∈ interior (range J) := by
  -- Read `φ` in the model vector spaces on the interior part of its source: there it is a
  -- continuous injection, so its image is open by invariance of domain.
  set W : Set E := interior (range I) ∩ I.symm ⁻¹' φ.source
  have hW : IsOpen W := isOpen_interior.inter (φ.open_source.preimage I.continuous_symm)
  have hg : ContinuousOn (J ∘ φ ∘ I.symm) W :=
    J.continuous.comp_continuousOn
      (φ.continuousOn.comp I.continuous_symm.continuousOn fun _ hy ↦ hy.2)
  have hinj : InjOn (J ∘ φ ∘ I.symm) W := by
    intro y hy y' hy' h
    rw [← I.right_inv (interior_subset hy.1), ← I.right_inv (interior_subset hy'.1),
      φ.injOn hy.2 hy'.2 (J.injective h)]
  refine interior_maximal ?_ (hW.image_of_continuousOn_of_injOn hg hinj hEF)
    ⟨I z, ⟨hi, by simpa using hz⟩, by simp⟩
  rintro _ ⟨y, -, rfl⟩
  exact mem_range_self _

/-- **Topological invariance of the interior.** A partial homeomorphism between charted spaces over
finite-dimensional real models of the same dimension preserves interior points. -/
theorem isInteriorPoint_iff (φ : OpenPartialHomeomorph M M') (hEF : finrank ℝ E = finrank ℝ E')
    {x : M} (hx : x ∈ φ.source) : I.IsInteriorPoint x ↔ J.IsInteriorPoint (φ x) := by
  -- Compare the preferred charts at `x` and at `φ x` through the transition map `ψ`.
  set ψ := (chartAt H x).symm ≫ₕ φ ≫ₕ chartAt H' (φ x)
  have hz : chartAt H x x ∈ ψ.source := by
    simp [ψ, mem_chart_source, hx]
  have hψz : ψ (chartAt H x x) = chartAt H' (φ x) (φ x) := by
    simp [ψ, mem_chart_source]
  have hψz' : ψ.symm (chartAt H' (φ x) (φ x)) = chartAt H x x := by
    rw [← hψz, ψ.left_inv hz]
  simp only [ModelWithCorners.IsInteriorPoint, extChartAt_coe, Function.comp_apply]
  refine ⟨fun h ↦ hψz ▸ mem_interior_range_apply ψ hEF hz h, fun h ↦ ?_⟩
  rw [← hψz']
  exact mem_interior_range_apply ψ.symm hEF.symm (by simpa [← hψz] using ψ.map_source hz) h

/-- **Topological invariance of the boundary.** A partial homeomorphism between charted spaces over
finite-dimensional real models of the same dimension preserves boundary points. -/
theorem isBoundaryPoint_iff (φ : OpenPartialHomeomorph M M') (hEF : finrank ℝ E = finrank ℝ E')
    {x : M} (hx : x ∈ φ.source) : I.IsBoundaryPoint x ↔ J.IsBoundaryPoint (φ x) := by
  rw [I.isBoundaryPoint_iff_not_isInteriorPoint, J.isBoundaryPoint_iff_not_isInteriorPoint,
    φ.isInteriorPoint_iff I J hEF hx]

/-- Over a finite-dimensional real model, an interior point of a charted space is detected by any
chart around it, not only by the preferred chart at the point. -/
theorem isInteriorPoint_iff_mem_interior_range (e : OpenPartialHomeomorph M H) {x : M}
    (hx : x ∈ e.source) : I.IsInteriorPoint x ↔ I (e x) ∈ interior (range I) := by
  rw [e.isInteriorPoint_iff I I rfl hx, ModelWithCorners.IsInteriorPoint,
    extChartAt_self_apply]

/-- Over a finite-dimensional real model, a boundary point of a charted space is detected by any
chart around it, not only by the preferred chart at the point. -/
theorem isBoundaryPoint_iff_mem_frontier_range (e : OpenPartialHomeomorph M H) {x : M}
    (hx : x ∈ e.source) : I.IsBoundaryPoint x ↔ I (e x) ∈ frontier (range I) := by
  rw [e.isBoundaryPoint_iff I I rfl hx, ModelWithCorners.IsBoundaryPoint,
    extChartAt_self_apply]

end Manifold

end OpenPartialHomeomorph

namespace ModelWithCorners

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [TopologicalSpace M] [ChartedSpace H M]

/-- Over a finite-dimensional real model, the interior of a charted space is open. Unlike
Mathlib's `ModelWithCorners.isOpen_interior`, no `C^1` structure is needed. -/
theorem isOpen_interior_of_finiteDimensional : IsOpen (I.interior M) := by
  refine isOpen_iff_forall_mem_open.2 fun x hx ↦ ⟨_, fun y hy ↦ ?_,
    isOpen_extChartAt_preimage (I := I) x isOpen_interior, mem_chart_source H x, hx⟩
  exact ((chartAt H x).isInteriorPoint_iff_mem_interior_range I hy.1).2 hy.2

/-- Over a finite-dimensional real model, the boundary of a charted space is closed. Unlike
Mathlib's `ModelWithCorners.isClosed_boundary`, no `C^1` structure is needed. -/
theorem isClosed_boundary_of_finiteDimensional : IsClosed (I.boundary M) := by
  rw [← I.compl_interior, isClosed_compl_iff]
  exact I.isOpen_interior_of_finiteDimensional

end ModelWithCorners
