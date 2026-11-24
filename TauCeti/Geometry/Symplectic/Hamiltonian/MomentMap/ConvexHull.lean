/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.DualHull
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.Critical
-- Proof-only: closedness of fixed-point sets.
import TauCeti.Topology.Algebra.ConstMulAction

/-!
# The image of a torus moment map lies in the convex hull of the fixed-point images

Let a torus `G`, a compact connected commutative Lie group, act smoothly on a compact boundaryless
manifold `M` with a nondegenerate two-form `σ`, with moment map `μ : M → 𝔤*`. Write `M^G` for the
fixed-point set. This file proves the inclusion

`μ(M) ⊆ conv μ(M^G)`

(`TauCeti.SmoothTwoForm.IsMomentMap.range_subset_convexHull_image_fixedPoints`), hence
`conv μ(M) = conv μ(M^G)`. This is one half of the convexity theorem of Atiyah and
Guillemin–Sternberg, which says that for connected `M` the image `μ(M)` is itself the convex hull
of `μ(M^G)`; the other half is the convexity of `μ(M)`.

The argument is Atiyah's. For a generic `ξ ∈ 𝔤`, one whose one-parameter subgroup is dense in `G`,
the critical set of the component `μ^ξ = ⟨μ, ξ⟩` is exactly `M^G`
(`TauCeti.SmoothTwoForm.IsMomentMap.dense_setOf_criticalPoints_eq_fixedPoints`). On the compact
manifold `M` the function `μ^ξ` attains its maximum, at a critical point, so at a point of `M^G`.
Thus every value `μ(x)` is dominated in each generic direction `ξ` by a value on `M^G`. The
generic directions are dense, and `M^G` is compact, so the support-function criterion
`IsCompact.mem_convexHull_image_of_dense` places `μ(x)` in the convex hull of `μ(M^G)`.

Conversely, maximizing a linear functional over that convex hull, every component `μ^ξ`, generic
or not, attains its maximum and its minimum on `M^G`
(`TauCeti.SmoothTwoForm.IsMomentMap.exists_mem_fixedPoints_forall_ge`). In particular a
Hamiltonian torus action on a nonempty compact manifold has a fixed point
(`TauCeti.SmoothTwoForm.IsMomentMap.nonempty_fixedPoints`).

Neither closedness of `σ`, equivariance of `μ`, nor connectedness of `M` is used.

## Main results

All declarations are in the namespace `TauCeti.SmoothTwoForm.IsMomentMap`.

* `range_subset_convexHull_image_fixedPoints`: the image of the moment map lies in the convex hull
  of the image of the fixed-point set.
* `convexHull_range_eq_convexHull_image_fixedPoints`: the two convex hulls agree.
* `exists_mem_fixedPoints_forall_ge`, `exists_mem_fixedPoints_forall_le`: every
  component of the moment map attains its maximum and its minimum on the fixed-point set.
* `nonempty_fixedPoints`: a nonempty compact Hamiltonian torus space has a fixed point.

## References

* M. F. Atiyah, *Convexity and commuting Hamiltonians*, Bull. London Math. Soc. 14 (1982), 1–15,
  § 2.
* V. Guillemin and S. Sternberg, *Convexity properties of the moment mapping*, Invent. Math. 67
  (1982), 491–513.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Lecture 27.
-/

public section

noncomputable section

open Set
open scoped ContDiff Manifold

namespace TauCeti.SmoothTwoForm.IsMomentMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G] [T2Space G]
  [IsTopologicalGroup G] [IsMulCommutative G] [CompactSpace G] [PreconnectedSpace G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [T2Space M]
  [BoundarylessManifold I' M] [CompactSpace M] [MulAction G M] [ContMDiffSMul I I' ∞ G M]
  {σ : SmoothTwoForm I' M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

/-- **The image of a torus moment map lies in the convex hull of the fixed-point images.** For a
moment map `μ` of a smooth action of a compact connected commutative Lie group `G` on a compact
boundaryless manifold `M` with a nondegenerate two-form, `μ(M) ⊆ conv μ(M^G)`. -/
theorem range_subset_convexHull_image_fixedPoints
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) (hσ : σ.IsNondegenerate) :
    range μ ⊆ convexHull ℝ (μ '' MulAction.fixedPoints G M) := by
  have : ContinuousSMul G M := ContMDiffSMul.continuousSMul (I := I) (I' := I') ∞
  rintro _ ⟨x, rfl⟩
  refine isClosed_fixedPoints_of_continuousConstSMul.isCompact.mem_convexHull_image_of_dense
    (fun ξ ↦ (h.contMDiff ξ).continuous.continuousOn)
    (dense_setOf_criticalPoints_eq_fixedPoints G h hσ) fun ξ hξ ↦ ?_
  -- For generic `ξ`, the maximum of `μ^ξ` on the compact manifold is a critical point of `μ^ξ`,
  -- by Fermat's theorem, hence a fixed point.
  obtain ⟨y, -, hy⟩ := isCompact_univ.exists_isMaxOn ⟨x, mem_univ x⟩
    (h.contMDiff ξ).continuous.continuousOn
  refine ⟨y, ?_, hy (mem_univ x)⟩
  rw [← mem_ofPred_eq.mp hξ]
  exact hy.mem_criticalPoints BoundarylessManifold.isInteriorPoint

/-- **The convex hull of a torus moment image is spanned by the fixed points.** For a moment map
`μ` of a smooth action of a compact connected commutative Lie group `G` on a compact boundaryless
manifold `M` with a nondegenerate two-form, `conv μ(M) = conv μ(M^G)`. -/
theorem convexHull_range_eq_convexHull_image_fixedPoints
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) (hσ : σ.IsNondegenerate) :
    convexHull ℝ (range μ) = convexHull ℝ (μ '' MulAction.fixedPoints G M) :=
  (convexHull_min (h.range_subset_convexHull_image_fixedPoints hσ)
    (convex_convexHull ℝ _)).antisymm (convexHull_mono (image_subset_range μ _))

/-- **Components of a torus moment map attain their maxima on the fixed-point set.** For a moment
map `μ` of a smooth action of a compact connected commutative Lie group `G` on a nonempty compact
boundaryless manifold `M` with a nondegenerate two-form, every component `μ^ξ` has a maximum point
fixed by `G`. -/
theorem exists_mem_fixedPoints_forall_ge [Nonempty M]
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) (hσ : σ.IsNondegenerate)
    (ξ : GroupLieAlgebra I G) :
    ∃ y ∈ MulAction.fixedPoints G M, ∀ x, μ x ξ ≤ μ y ξ := by
  obtain ⟨x₀, -, hx₀⟩ := isCompact_univ.exists_isMaxOn univ_nonempty
    (h.contMDiff ξ).continuous.continuousOn
  -- Evaluation at `ξ` is linear, so its maximum on `conv μ(M^G) ∋ μ(x₀)` is attained on `μ(M^G)`.
  obtain ⟨_, ⟨y, hy, rfl⟩, hle⟩ :=
    ((Module.Dual.eval ℝ _ ξ).convexOn convex_univ).exists_ge_of_mem_convexHull (subset_univ _)
      (h.range_subset_convexHull_image_fixedPoints hσ (mem_range_self x₀))
  exact ⟨y, hy, fun x ↦ (hx₀ (mem_univ x)).trans hle⟩

/-- **Components of a torus moment map attain their minima on the fixed-point set.** For a moment
map `μ` of a smooth action of a compact connected commutative Lie group `G` on a nonempty compact
boundaryless manifold `M` with a nondegenerate two-form, every component `μ^ξ` has a minimum point
fixed by `G`. -/
theorem exists_mem_fixedPoints_forall_le [Nonempty M]
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) (hσ : σ.IsNondegenerate)
    (ξ : GroupLieAlgebra I G) :
    ∃ y ∈ MulAction.fixedPoints G M, ∀ x, μ y ξ ≤ μ x ξ := by
  obtain ⟨y, hy, hle⟩ := h.exists_mem_fixedPoints_forall_ge hσ (-ξ)
  exact ⟨y, hy, fun x ↦ by simpa only [map_neg, neg_le_neg_iff] using hle x⟩

/-- **A Hamiltonian torus action on a compact manifold has a fixed point.** If a compact connected
commutative Lie group `G` acts smoothly on a nonempty compact boundaryless manifold `M` with a
nondegenerate two-form and has a moment map, then some point of `M` is fixed by `G`. -/
theorem nonempty_fixedPoints [Nonempty M]
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) (hσ : σ.IsNondegenerate) :
    (MulAction.fixedPoints G M).Nonempty :=
  let ⟨y, hy, _⟩ := h.exists_mem_fixedPoints_forall_ge hσ 0
  ⟨y, hy⟩

end TauCeti.SmoothTwoForm.IsMomentMap
