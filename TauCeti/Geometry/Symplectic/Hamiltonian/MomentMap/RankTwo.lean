/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.ConnectedLevel
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.ConvexHull
import TauCeti.Analysis.Convex.ConnectedFiber

/-!
# Convexity of moment maps of groups of dimension at most two

Let a compact Lie group `G` whose Lie algebra `𝔤` has dimension at most two act smoothly on a
compact connected boundaryless manifold `M`, preserving a nondegenerate two-form `σ`, with moment
map `μ : M → 𝔤*`. This file proves that **the image of `μ` is convex**
(`TauCeti.SmoothTwoForm.IsMomentMap.convex_range_of_finrank_le_two`), with no assumption on the
isotropy of the action. If moreover `G` is connected and commutative, a torus `T²` (or a circle,
or trivial), the image is the convex hull of the images of the fixed points
(`TauCeti.SmoothTwoForm.IsMomentMap.range_eq_convexHull_image_fixedPoints_of_finrank_le_two`),
which are finitely many values (`TauCeti.SmoothTwoForm.IsMomentMap.finite_image_fixedPoints`), so
the image is a convex polygon. This is the convexity half of the theorem of Atiyah and
Guillemin–Sternberg for two-dimensional tori; the connectedness of the fibres of `μ` is not proved
here. For a circle, the image and the fibres were already treated in
`TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.LocallyFree`
(`TauCeti.SmoothTwoForm.IsMomentMap.range_eq_convexHull_image_fixedPoints_of_finrank_eq_one`).

The argument is Atiyah's. In dimension two every affine line of `𝔤*` is a level set
`{ν | ν ξ = c}` for some `ξ ∈ 𝔤`, and its intersection with the image of `μ` is the image of the
level set `{x | ⟨μ x, ξ⟩ = c}` of the component `μ^ξ`. These level sets are connected, because
`μ^ξ` is a Morse–Bott function of even indices
(`TauCeti.SmoothTwoForm.IsMomentMap.isPreconnected_setOf_apply_eq`), so the image of `μ` meets
every line in an interval, hence is convex
(`TauCeti.convex_range_of_isPreconnected_setOf_apply_eq`). Unlike the local-to-global argument of
`TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.LocallyFree`, this needs no local normal form at
points whose isotropy algebra is neither `0` nor `𝔤`, which exist for actions of `T²`.

## Main results

* `TauCeti.SmoothTwoForm.IsMomentMap.convex_range_of_finrank_le_two`: the image of a moment map of
  a compact group of dimension at most two is convex.
* `TauCeti.SmoothTwoForm.IsMomentMap.range_eq_convexHull_image_fixedPoints_of_finrank_le_two`: for
  a torus of dimension at most two, the image is the convex hull of the fixed-point images.

## References

* M. F. Atiyah, *Convexity and commuting Hamiltonians*, Bull. London Math. Soc. 14 (1982), 1–15,
  § 2.
* V. Guillemin and S. Sternberg, *Convexity properties of the moment mapping*, Invent. Math. 67
  (1982), 491–513.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Lecture 27.
-/

public section

open Set
open scoped ContDiff Manifold

namespace TauCeti.SmoothTwoForm.IsMomentMap

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G] [T2Space G]
  [IsTopologicalGroup G] [CompactSpace G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {M : Type*} [TopologicalSpace M] [ChartedSpace E' M] [IsManifold 𝓘(ℝ, E') ∞ M] [T2Space M]
  [CompactSpace M] [PreconnectedSpace M] [MulAction G M] [ContMDiffSMul I 𝓘(ℝ, E') ∞ G M]
  {σ : SmoothTwoForm 𝓘(ℝ, E') M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}

/-- **Convexity for groups of dimension at most two.** Let a compact Lie group `G` of dimension at
most two act smoothly on a compact connected boundaryless finite-dimensional manifold `M`,
preserving a nondegenerate two-form `σ`, with moment map `μ`. Then the image of `μ` is convex. -/
theorem convex_range_of_finrank_le_two
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G 𝓘(ℝ, E') M) μ)
    (hσ : σ.IsNondegenerate)
    (hσG : ∀ (a : G) (x : M) (u v : TangentSpace 𝓘(ℝ, E') x),
      σ.eval₂ (a • x) (mfderiv 𝓘(ℝ, E') 𝓘(ℝ, E') (a • ·) x u)
        (mfderiv 𝓘(ℝ, E') 𝓘(ℝ, E') (a • ·) x v) = σ.eval₂ x u v)
    (hE : Module.finrank ℝ E ≤ 2) :
    Convex ℝ (range μ) :=
  -- `GroupLieAlgebra I G` is the tangent space at `1`, which is the model space `E` by
  -- definition, so `hE` is its dimension.
  have : FiniteDimensional ℝ (GroupLieAlgebra I G) := inferInstanceAs (FiniteDimensional ℝ E)
  convex_range_of_isPreconnected_setOf_apply_eq hE (fun ξ ↦ (h.contMDiff ξ).continuous)
    (h.isPreconnected_setOf_apply_eq hσ hσG)

/-- **The convexity theorem for tori of dimension at most two.** Let a compact connected
commutative Lie group `G` of dimension at most two act smoothly on a compact connected boundaryless
finite-dimensional manifold `M`, preserving a nondegenerate two-form `σ`, with moment map `μ`.
Then `μ(M) = conv μ(M^G)`: the image of `μ` is the convex hull of the values of `μ` at the fixed
points. -/
theorem range_eq_convexHull_image_fixedPoints_of_finrank_le_two [IsMulCommutative G]
    [PreconnectedSpace G] (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G 𝓘(ℝ, E') M) μ)
    (hσ : σ.IsNondegenerate)
    (hσG : ∀ (a : G) (x : M) (u v : TangentSpace 𝓘(ℝ, E') x),
      σ.eval₂ (a • x) (mfderiv 𝓘(ℝ, E') 𝓘(ℝ, E') (a • ·) x u)
        (mfderiv 𝓘(ℝ, E') 𝓘(ℝ, E') (a • ·) x v) = σ.eval₂ x u v)
    (hE : Module.finrank ℝ E ≤ 2) :
    range μ = convexHull ℝ (μ '' MulAction.fixedPoints G M) :=
  (h.range_subset_convexHull_image_fixedPoints hσ).antisymm
    (convexHull_min (image_subset_range μ _) (h.convex_range_of_finrank_le_two hσ hσG hE))

end TauCeti.SmoothTwoForm.IsMomentMap
