/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Gluing.GlueData
public import TauCeti.Topology.Category.TopCat.GlueData.Double

/-!
# Doubling a manifold along an open subset

The double `TauCeti.doubleGlueData X U` glues two copies of a space `X` along an open subset `U`
by the identity. When `X` is a charted space, every piece of the double carries the atlas of `X`
and every overlap the atlas of an open subset of `X`. With these atlases the double is a
two-chart instance of compatible open gluing (`TauCeti.isCompatible_doubleGlueData`): both maps
out of an overlap are inclusions of open subsets of `X`, hence local diffeomorphisms for any
model and regularity.

The general results on compatible gluings then apply to the double. If `X` is a `C^n` manifold,
`TopCat.GlueData.IsCompatible.isManifold` makes the double a `C^n` manifold for the glued atlas
`TopCat.GlueData.chartedSpace`, and `TopCat.GlueData.IsCompatible.isLocalDiffeomorph_ι` makes the
two canonical maps from `X` into it `C^n` local diffeomorphisms. The double is Hausdorff only when
`U` is closed (`TauCeti.t2Space_doubleGlueData_iff`), so the gluing theorem supplies manifold
structures that need not be Hausdorff. The basic example is the plane with a doubled origin, a
complex manifold which is not Hausdorff.

## Main declarations

* `TauCeti.isCompatible_doubleGlueData`: the double of a charted space along an open subset is a
  compatible gluing.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 1 (the line with two origins).
-/

public section

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace TauCeti

universe u

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω}
  {X : Type u} [TopologicalSpace X] [ChartedSpace H X] (U : Opens X)

/-- Each piece of the double of `X` carries the atlas of `X`. -/
noncomputable instance instChartedSpaceDoubleGlueDataU (i : (doubleGlueData X U).J) :
    ChartedSpace H ((doubleGlueData X U).U i) :=
  inferInstanceAs (ChartedSpace H X)

/-- The overlap of the pieces `i` and `j` of the double carries the atlas of the open subset of
`X` that it is: all of `X` if `i = j`, and `U` otherwise. -/
noncomputable instance instChartedSpaceDoubleGlueDataV (p : (doubleGlueData X U).J ×
    (doubleGlueData X U).J) : ChartedSpace H ((doubleGlueData X U).V p) :=
  inferInstanceAs (ChartedSpace H (⟨{x | p.1 = p.2 ∨ x ∈ U}, by
    by_cases h : p.1 = p.2
    · simp [h]
    · simpa [h] using U.isOpen⟩ : Opens X))

/-- Each piece of the double of a `C^n` manifold is a `C^n` manifold. -/
instance instIsManifoldDoubleGlueDataU [IsManifold I n X] (i : (doubleGlueData X U).J) :
    IsManifold I n ((doubleGlueData X U).U i) :=
  inferInstanceAs (IsManifold I n X)

/-- **The double is a compatible gluing.** Both maps out of an overlap of the double are inclusions
of open subsets of `X`, so they are `C^n` local diffeomorphisms. -/
theorem isCompatible_doubleGlueData : (doubleGlueData X U).IsCompatible I n := by
  -- By definition (`doubleGlueData_f`), each map `f i j` is the inclusion of an open subset.
  refine .of_isLocalDiffeomorph_t (fun i j ↦ isLocalDiffeomorph_subtype_val) fun i j x ↦ ?_
  -- Followed by the inclusion into `X`, the transition is the inclusion of the overlap.
  exact IsLocalDiffeomorphAt.of_comp_left (f := ((doubleGlueData X U).f j i : _ → X))
    (isLocalDiffeomorph_subtype_val x) (isLocalDiffeomorph_subtype_val _)
    ((doubleGlueData X U).t i j).hom.continuous.continuousAt

end TauCeti
