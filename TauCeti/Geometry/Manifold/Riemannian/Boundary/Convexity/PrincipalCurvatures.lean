/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Boundary.Convexity.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Boundary.Weingarten.Basic

/-!
# Convexity of the boundary through the principal curvatures

Let `M` be a Riemannian manifold with boundary modelled on the half-space `𝓡∂ (n + 1)` and
`q ∈ ∂M`. In the basis `(eᵢ)` of principal directions at `q`, orthonormal for the induced metric,
the second fundamental form is diagonal with entries the principal curvatures `κᵢ`, so
`II_q(u, u) = ∑ᵢ κᵢ uᵢ²` (`TauCeti.boundarySecondFundamentalForm_self_eq_sum`), where `uᵢ` are
the coordinates of `u`. Hence:

* the boundary is strictly convex at `q` iff every principal curvature at `q` is positive
  (`TauCeti.isStrictlyConvexAt_iff_forall_boundaryPrincipalCurvatures_pos`), convex iff every
  principal curvature is nonnegative, and strictly concave iff every principal curvature is
  negative;
* for `n ≥ 1`, strict convexity at `q` gives `H(q) > 0`
  (`TauCeti.IsStrictlyConvexAt.boundaryMeanCurvature_pos`), convexity gives `H(q) ≥ 0`
  (`TauCeti.IsConvexAt.boundaryMeanCurvature_nonneg`), and strict concavity gives `H(q) < 0`
  (`TauCeti.IsStrictlyConcaveAt.boundaryMeanCurvature_neg`).

## References

* G. P. Paternain, M. Salo, G. Uhlmann, *Geometric Inverse Problems, with Emphasis on Two
  Dimensions*, Cambridge University Press (2023), Definition 3.1.7.
-/

public section

noncomputable section

open Bundle
open scoped Manifold

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]
  [IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]

/-- A nonzero tangent vector of the boundary has a nonzero coordinate in the basis of principal
directions. -/
private theorem exists_boundaryPrincipalBasis_repr_ne_zero {q : (𝓡∂ (n + 1)).boundary M}
    {u : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q} (hu : u ≠ 0) :
    ∃ i, (boundaryPrincipalBasis q).repr u i ≠ 0 :=
  DFunLike.ne_iff.1 ((boundaryPrincipalBasis q).repr.map_ne_zero_iff.2 hu)

/-- **Strict convexity through the principal curvatures**: the boundary is strictly convex at
`q` iff every principal curvature at `q` is positive. -/
theorem isStrictlyConvexAt_iff_forall_boundaryPrincipalCurvatures_pos
    {q : (𝓡∂ (n + 1)).boundary M} :
    IsStrictlyConvexAt q ↔ ∀ i, 0 < boundaryPrincipalCurvatures q i := by
  refine ⟨fun h i ↦ ?_, fun h ↦ isStrictlyConvexAt_iff.2 fun u hu ↦ ?_⟩
  · have := isStrictlyConvexAt_iff.1 h _ (boundaryPrincipalDirection_ne_zero q i)
    simpa using this
  · obtain ⟨i, hi⟩ := exists_boundaryPrincipalBasis_repr_ne_zero hu
    rw [boundarySecondFundamentalForm_self_eq_sum]
    exact Finset.sum_pos' (fun j _ ↦ mul_nonneg (h j).le (sq_nonneg _))
      ⟨i, Finset.mem_univ i, mul_pos (h i) (by positivity)⟩

/-- **Convexity through the principal curvatures**: the boundary is convex at `q` iff every
principal curvature at `q` is nonnegative. -/
theorem isConvexAt_iff_forall_boundaryPrincipalCurvatures_nonneg {q : (𝓡∂ (n + 1)).boundary M} :
    IsConvexAt q ↔ ∀ i, 0 ≤ boundaryPrincipalCurvatures q i := by
  refine ⟨fun h i ↦ ?_, fun h ↦ isConvexAt_iff.2 fun u ↦ ?_⟩
  · have := isConvexAt_iff.1 h (boundaryPrincipalDirection q i)
    simpa using this
  · rw [boundarySecondFundamentalForm_self_eq_sum]
    exact Finset.sum_nonneg fun j _ ↦ mul_nonneg (h j) (sq_nonneg _)

/-- **Strict concavity through the principal curvatures**: the boundary is strictly concave at
`q` iff every principal curvature at `q` is negative. -/
theorem isStrictlyConcaveAt_iff_forall_boundaryPrincipalCurvatures_neg
    {q : (𝓡∂ (n + 1)).boundary M} :
    IsStrictlyConcaveAt q ↔ ∀ i, boundaryPrincipalCurvatures q i < 0 := by
  refine ⟨fun h i ↦ ?_, fun h ↦ isStrictlyConcaveAt_iff.2 fun u hu ↦ ?_⟩
  · have := isStrictlyConcaveAt_iff.1 h _ (boundaryPrincipalDirection_ne_zero q i)
    simpa using this
  · obtain ⟨i, hi⟩ := exists_boundaryPrincipalBasis_repr_ne_zero hu
    rw [boundarySecondFundamentalForm_self_eq_sum]
    exact Finset.sum_neg' (fun j _ ↦ mul_nonpos_of_nonpos_of_nonneg (h j).le (sq_nonneg _))
      ⟨i, Finset.mem_univ i, mul_neg_of_neg_of_pos (h i) (by positivity)⟩

/-- **Strict convexity gives positive mean curvature**: for `n ≥ 1`, if the boundary is strictly
convex at `q`, then `H(q) > 0`. -/
theorem IsStrictlyConvexAt.boundaryMeanCurvature_pos [NeZero n] {q : (𝓡∂ (n + 1)).boundary M}
    (h : IsStrictlyConvexAt q) : 0 < boundaryMeanCurvature q := by
  have hκ := isStrictlyConvexAt_iff_forall_boundaryPrincipalCurvatures_pos.1 h
  rw [boundaryMeanCurvature_eq_sum_div]
  exact div_pos (Finset.sum_pos (fun i _ ↦ hκ i) Finset.univ_nonempty)
    (Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne n)))

/-- **Convexity gives nonnegative mean curvature**: if the boundary is convex at `q`, then
`H(q) ≥ 0`. -/
theorem IsConvexAt.boundaryMeanCurvature_nonneg {q : (𝓡∂ (n + 1)).boundary M}
    (h : IsConvexAt q) : 0 ≤ boundaryMeanCurvature q := by
  have hκ := isConvexAt_iff_forall_boundaryPrincipalCurvatures_nonneg.1 h
  rw [boundaryMeanCurvature_eq_sum_div]
  exact div_nonneg (Finset.sum_nonneg fun i _ ↦ hκ i) (Nat.cast_nonneg n)

/-- **Strict concavity gives negative mean curvature**: for `n ≥ 1`, if the boundary is strictly
concave at `q`, then `H(q) < 0`. -/
theorem IsStrictlyConcaveAt.boundaryMeanCurvature_neg [NeZero n] {q : (𝓡∂ (n + 1)).boundary M}
    (h : IsStrictlyConcaveAt q) : boundaryMeanCurvature q < 0 := by
  have hκ := isStrictlyConcaveAt_iff_forall_boundaryPrincipalCurvatures_neg.1 h
  rw [boundaryMeanCurvature_eq_sum_div]
  exact div_neg_of_neg_of_pos (Finset.sum_neg (fun i _ ↦ hκ i) Finset.univ_nonempty)
    (Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne n)))

end TauCeti
