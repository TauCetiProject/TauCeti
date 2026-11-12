/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Cone.StrictInward
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

/-!
# Strictly inward tangent vectors and vector fields

A tangent vector at a point `x` of a manifold with corners is strictly inward when, read in the
preferred chart at `x`, it lies in the strict inward cone of the range of the model
(`TauCeti.strictInwardTangentCone`). Since the range of a model is convex with nonempty interior,
the derivatives of the changes of coordinates preserve these cones, so strict inwardness can be
read in the preferred chart at any point whose domain contains `x`
(`TauCeti.mem_strictInwardTangentCone_iff_tangentCoordChange`). More generally, differentials of
dense range preserve strict inwardness (`MDifferentiableAt.mapsTo_strictInwardTangentCone`). The
cone in each tangent space is open, convex, nonempty and invariant under positive scaling; it is
the whole tangent space exactly at interior points.

On a Hausdorff σ-compact manifold over a finite-dimensional model there is a smooth vector field
that is strictly inward at every point
(`TauCeti.exists_contMDiffSection_mem_strictInwardTangentCone`). Such fields are the input for
forward semiflows that push a manifold with corners into its interior.

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
preferred chart at `x`, are strictly inward to the range of the model. A tangent vector is read in
the preferred chart through `tangentSpaceCastModel`, as in Mathlib's `HasMFDerivAt`. -/
noncomputable def strictInwardTangentCone (x : M) : Set (TangentSpace I x) :=
  tangentSpaceCastModel I x ⁻¹' strictInwardCone (range I) (extChartAt I x x)

variable {I}

/-- A tangent vector is strictly inward when, read in the preferred chart, it is strictly inward
to the range of the model. -/
theorem mem_strictInwardTangentCone_iff {x : M} {v : TangentSpace I x} :
    v ∈ strictInwardTangentCone I x ↔
      tangentSpaceCastModel I x v ∈ strictInwardCone (range I) (extChartAt I x x) :=
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
      rw [Function.comp_apply, extChartAt_coe]; exact mem_range_self _) hv
  rwa [Function.comp_apply, (extChartAt I x).left_inv hz.1] at h

/-- Strict inwardness of a vector is independent of the preferred chart it is read in. -/
theorem tangentCoordChange_mem_strictInwardCone_iff [IsManifold I 1 M] {x y z : M}
    (hz : z ∈ (extChartAt I x).source ∩ (extChartAt I y).source) {v : E} :
    tangentCoordChange I x y z v ∈ strictInwardCone (range I) (extChartAt I y z) ↔
      v ∈ strictInwardCone (range I) (extChartAt I x z) := by
  refine ⟨fun h ↦ ?_, tangentCoordChange_mem_strictInwardCone hz⟩
  have h' := tangentCoordChange_mem_strictInwardCone ⟨hz.2, hz.1⟩ h
  rwa [tangentCoordChange_comp ⟨⟨hz.1, hz.2⟩, hz.1⟩, tangentCoordChange_self hz.1] at h'

/-- A tangent vector at `x` is strictly inward exactly when it is so read in the preferred chart
at any point `y` whose domain contains `x`. -/
theorem mem_strictInwardTangentCone_iff_tangentCoordChange [IsManifold I 1 M] {x y : M}
    (hx : x ∈ (extChartAt I y).source) {v : TangentSpace I x} :
    v ∈ strictInwardTangentCone I x ↔ tangentCoordChange I x y x (tangentSpaceCastModel I x v) ∈
      strictInwardCone (range I) (extChartAt I y x) :=
  (tangentCoordChange_mem_strictInwardCone_iff ⟨mem_extChartAt_source x, hx⟩).symm

/-- **Differentials preserve strict inwardness.** A differential of dense range between manifolds
with corners sends strictly inward tangent vectors to strictly inward tangent vectors. -/
theorem _root_.MDifferentiableAt.mapsTo_strictInwardTangentCone {E' H' M' : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M'] [ChartedSpace H' M'] {f : M → M'}
    {x : M} (hf : MDifferentiableAt I I' f x) (hf' : DenseRange (mfderiv I I' f x)) :
    MapsTo (mfderiv I I' f x) (strictInwardTangentCone I x) (strictInwardTangentCone I' (f x)) := by
  intro v hv
  have hd : DenseRange (tangentSpaceCastModel I' (f x) ∘L mfderiv I I' f x ∘L
      (tangentSpaceCastModel I x).symm : E →L[ℝ] E') :=
    (tangentSpaceCastModel I' (f x)).surjective.denseRange.comp
      (hf'.comp (tangentSpaceCastModel I x).symm.surjective.denseRange
        (mfderiv I I' f x).continuous) (tangentSpaceCastModel I' (f x)).continuous
  have h := hf.hasMFDerivAt.2.mapsTo_strictInwardCone hd I'.convex_range I'.nonempty_interior
    (Eventually.of_forall fun z ↦ by
      rw [writtenInExtChartAt, Function.comp_apply, extChartAt_coe]; exact mem_range_self _)
    (mem_strictInwardTangentCone_iff.mp hv)
  rw [writtenInExtChartAt, Function.comp_apply, Function.comp_apply, extChartAt_to_inv] at h
  rw [mem_strictInwardTangentCone_iff]
  simpa using h

variable (I)

/-- The strict inward cone in a tangent space is open. -/
theorem isOpen_strictInwardTangentCone (x : M) : IsOpen (strictInwardTangentCone I x) := by
  exact (isOpen_strictInwardCone _ _).preimage (tangentSpaceCastModel I x).continuous

/-- The strict inward cone in a tangent space is convex. -/
theorem convex_strictInwardTangentCone (x : M) : Convex ℝ (strictInwardTangentCone I x) := by
  exact (I.convex_range.convex_strictInwardCone _).linear_preimage
    (tangentSpaceCastModel I x).toLinearMap

/-- Every tangent space contains strictly inward vectors. -/
theorem strictInwardTangentCone_nonempty (x : M) : (strictInwardTangentCone I x).Nonempty := by
  exact (tangentSpaceCastModel I x).surjective.nonempty_preimage.mpr
    (I.convex_range.strictInwardCone_nonempty (by rw [extChartAt_coe]; exact mem_range_self _)
      I.nonempty_interior)

/-- Every tangent vector is strictly inward exactly at interior points. -/
@[simp]
theorem strictInwardTangentCone_eq_univ_iff {x : M} :
    strictInwardTangentCone I x = univ ↔ I.IsInteriorPoint x := by
  rw [strictInwardTangentCone, ← preimage_univ (f := tangentSpaceCastModel I x),
    (tangentSpaceCastModel I x).surjective.preimage_injective.eq_iff, strictInwardCone_eq_univ_iff,
    ModelWithCorners.IsInteriorPoint]

/-- On a manifold without boundary every tangent vector is strictly inward. -/
@[simp]
theorem strictInwardTangentCone_eq_univ [BoundarylessManifold I M] (x : M) :
    strictInwardTangentCone I x = univ :=
  (strictInwardTangentCone_eq_univ_iff I).mpr BoundarylessManifold.isInteriorPoint

variable {I}

/-- The zero tangent vector is strictly inward exactly at interior points. -/
@[simp]
theorem zero_mem_strictInwardTangentCone_iff {x : M} :
    (0 : TangentSpace I x) ∈ strictInwardTangentCone I x ↔ I.IsInteriorPoint x := by
  rw [mem_strictInwardTangentCone_iff, map_zero, zero_mem_strictInwardCone_iff,
    ModelWithCorners.IsInteriorPoint]

/-- Positive rescaling preserves and reflects strict inwardness of tangent vectors. -/
@[simp]
theorem smul_mem_strictInwardTangentCone_iff {x : M} {v : TangentSpace I x} {c : ℝ}
    (hc : 0 < c) : c • v ∈ strictInwardTangentCone I x ↔ v ∈ strictInwardTangentCone I x := by
  rw [mem_strictInwardTangentCone_iff, mem_strictInwardTangentCone_iff, map_smul]
  exact smul_mem_strictInwardCone_iff hc

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
  -- The vector `w` from the chart image of `x₀` to `q` stays strictly inward near `x₀`.
  set w : E := q - extChartAt I x₀ x₀
  have hw : ∀ᶠ y in 𝓝 x₀, w ∈ strictInwardCone (range I) (extChartAt I x₀ y) := by
    have hc : ContinuousAt (fun y : M ↦ ((⟨extChartAt I x₀ y, hrange y⟩ : range I), w)) x₀ :=
      ((continuousAt_extChartAt x₀).codRestrict hrange).prodMk continuousAt_const
    exact hc.preimage_mem_nhds (I.convex_range.isOpen_setOf_mem_strictInwardCone.mem_nhds
      (I.convex_range.sub_mem_strictInwardCone (hrange x₀) hq))
  -- The local field has the constant coordinates `w` in the trivialization at `x₀`.
  set e := trivializationAt E (TangentSpace I) x₀
  have hsource : (extChartAt I x₀).source = e.baseSet := by
    rw [extChartAt_source, TangentBundle.trivializationAt_baseSet]
  refine ⟨(extChartAt I x₀).source ∩ {y | w ∈ strictInwardCone (range I) (extChartAt I x₀ y)},
    inter_mem (extChartAt_source_mem_nhds x₀) hw, fun y ↦ e.symm y w,
    (Manifold.contMDiffOn_symm_baseSet w).mono (hsource ▸ inter_subset_left), ?_⟩
  rintro y ⟨hy, hyw⟩
  rw [mem_ofPred_eq] at hyw
  rw [mem_strictInwardTangentCone_iff_tangentCoordChange hy]
  convert hyw
  calc tangentCoordChange I y x₀ y (tangentSpaceCastModel I y (e.symm y w))
      = (e ⟨y, e.symm y w⟩).2 := (TangentBundle.trivializationAt_apply_tangentCoordChange _).symm
    _ = w := by rw [e.apply_mk_symm (hsource ▸ hy)]

end TauCeti
