/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Boundary.Convexity.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Boundary.SecondFundamentalForm.Smooth
import TauCeti.Topology.VectorBundle.Bilinear

/-!
# Strict convexity and strict concavity of the boundary are open conditions

Let `M` be a Riemannian manifold with boundary. The points of `∂M` at which the boundary is
strictly convex, respectively strictly concave, form an open subset of `∂M`
(`TauCeti.isOpen_setOf_isStrictlyConvexAt`, `TauCeti.isOpen_setOf_isStrictlyConcaveAt`).

The proof uses that `II` is a continuous section of the bundle of bilinear forms on `T∂M`
(`TauCeti.continuousAt_boundarySecondFundamentalForm`), and that positivity on nonzero diagonal
vectors is an open condition in that bundle
(`TauCeti.isOpen_setOf_forall_bilinear_bundle_apply_self_pos`). Strict concavity is positive
definiteness of `-II`, so both cases are positivity of `s • II` for a sign `s`, proved once.

## Main results

* `TauCeti.IsStrictlyConvexAt.eventually`, `TauCeti.isOpen_setOf_isStrictlyConvexAt`:
  strict convexity of the boundary is an open condition.
* `TauCeti.IsStrictlyConcaveAt.eventually`, `TauCeti.isOpen_setOf_isStrictlyConcaveAt`:
  strict concavity of the boundary is an open condition.

## References

* G. P. Paternain, M. Salo, G. Uhlmann, *Geometric Inverse Problems, with Emphasis on Two
  Dimensions*, Cambridge University Press (2023), Definition 3.1.7.
-/

public section

noncomputable section

open Bundle Filter Function Topology
open scoped Manifold ContDiff

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) 2 M]

/-- The boundary of the `C²` manifold `M` is a `C¹` manifold, as the continuity of `II` needs. -/
local instance isManifoldBoundaryOfTwo :
    IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1 ((𝓡∂ (n + 1)).boundary M) :=
  have : IsManifold (𝓡∂ (n + 1)) 1 M := IsManifold.of_le (n := 2) (by norm_num)
  isManifold_boundary M

variable [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]
  [IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]

/-- For a fixed scalar `s`, positivity of `s * II_q(u, u)` on nonzero `u ∈ T_q∂M` is an open
condition on `q`: `s • II` is a section of the bilinear bundle continuous at `q₀`, by
`continuousAt_boundarySecondFundamentalForm`. -/
private theorem eventually_forall_mul_boundarySecondFundamentalForm_pos (s : ℝ)
    {q₀ : (𝓡∂ (n + 1)).boundary M}
    (h : ∀ u : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q₀, u ≠ 0 →
      0 < s * boundarySecondFundamentalForm q₀ u u) :
    ∀ᶠ q in 𝓝 q₀, ∀ u : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q, u ≠ 0 →
      0 < s * boundarySecondFundamentalForm q u u := by
  let b : ∀ q : (𝓡∂ (n + 1)).boundary M, TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q →L[ℝ]
      TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q →L[ℝ] ℝ :=
    fun q ↦ s • (boundarySecondFundamentalForm q).toContinuousBilinearMap
  have hb : ∀ q u v, b q u v = s * boundarySecondFundamentalForm q u v := fun q u v ↦ by
    simp only [b, smul_apply, LinearMap.toContinuousBilinearMap_apply,
      smul_eq_mul]
  -- `b` is the section `II` multiplied by the constant function `s`.
  have hcont : ContinuousAt (fun q ↦ TotalSpace.mk'
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
      (E := fun q : (𝓡∂ (n + 1)).boundary M ↦ TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q →L[ℝ]
        TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q →L[ℝ] ℝ) q (b q)) q₀ :=
    (contMDiff_zero_iff.1 ((contMDiff_const (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (c := s))
      |>.smul_section (contMDiff_zero_iff.2
        (continuous_boundarySecondFundamentalForm n M)))).continuousAt
  simpa only [hb] using hcont.eventually
    (isOpen_setOf_forall_bilinear_bundle_apply_self_pos.mem_nhds
      (by simpa only [Set.mem_ofPred_eq, hb] using h))

/-- **Strict convexity of the boundary is an open condition**: if `∂M` is strictly convex at `q₀`,
it is strictly convex at every point of `∂M` near `q₀`. -/
theorem IsStrictlyConvexAt.eventually {q₀ : (𝓡∂ (n + 1)).boundary M}
    (h : IsStrictlyConvexAt q₀) : ∀ᶠ q in 𝓝 q₀, IsStrictlyConvexAt q := by
  simpa only [isStrictlyConvexAt_iff, one_mul] using
    eventually_forall_mul_boundarySecondFundamentalForm_pos 1
      (by simpa only [one_mul] using isStrictlyConvexAt_iff.1 h)

/-- **Strict concavity of the boundary is an open condition**: if `∂M` is strictly concave at
`q₀`, it is strictly concave at every point of `∂M` near `q₀`. -/
theorem IsStrictlyConcaveAt.eventually {q₀ : (𝓡∂ (n + 1)).boundary M}
    (h : IsStrictlyConcaveAt q₀) : ∀ᶠ q in 𝓝 q₀, IsStrictlyConcaveAt q := by
  simpa only [isStrictlyConcaveAt_iff, neg_one_mul, neg_pos] using
    eventually_forall_mul_boundarySecondFundamentalForm_pos (-1)
      (by simpa only [neg_one_mul, neg_pos] using isStrictlyConcaveAt_iff.1 h)

variable (n M) in
/-- The set of points of `∂M` at which the boundary is strictly convex is open in `∂M`. -/
theorem isOpen_setOf_isStrictlyConvexAt :
    IsOpen {q : (𝓡∂ (n + 1)).boundary M | IsStrictlyConvexAt q} :=
  isOpen_iff_mem_nhds.2 fun _ hq ↦ IsStrictlyConvexAt.eventually hq

variable (n M) in
/-- The set of points of `∂M` at which the boundary is strictly concave is open in `∂M`. -/
theorem isOpen_setOf_isStrictlyConcaveAt :
    IsOpen {q : (𝓡∂ (n + 1)).boundary M | IsStrictlyConcaveAt q} :=
  isOpen_iff_mem_nhds.2 fun _ hq ↦ IsStrictlyConcaveAt.eventually hq

end TauCeti
