/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Boundary.Convexity.Basic

/-!
# Hessian characterisation of the convexity of the boundary

Let `M` be a Riemannian manifold with boundary modelled on the half-space `𝓡∂ (n + 1)`, let
`q ∈ ∂M`, and let `ρ` be a boundary defining function on an open set `U ∋ q`
(`TauCeti.IsBoundaryDefiningFunctionOn`). The second fundamental form of the boundary is
`II_q(u, w) = -Hess ρ(dι u, dι w) / |dρ_q|`
(`TauCeti.IsBoundaryDefiningFunctionOn.boundarySecondFundamentalForm_apply`), with `|dρ_q| > 0`.
Hence the convexity predicates of the boundary at `q` read off the sign of the Hessian of `ρ` on the
tangent space of the boundary:

* `∂M` is strictly convex at `q` iff `Hess ρ(dι u, dι u) < 0` for every nonzero `u ∈ T_q∂M`
  (`TauCeti.IsBoundaryDefiningFunctionOn.isStrictlyConvexAt_iff_forall_hessian_neg`);
* `∂M` is convex at `q` iff `Hess ρ(dι u, dι u) ≤ 0` for every `u ∈ T_q∂M`
  (`TauCeti.IsBoundaryDefiningFunctionOn.isConvexAt_iff_forall_hessian_nonpos`);
* `∂M` is strictly concave at `q` iff `Hess ρ(dι u, dι u) > 0` for every nonzero `u ∈ T_q∂M`
  (`TauCeti.IsBoundaryDefiningFunctionOn.isStrictlyConcaveAt_iff_forall_hessian_pos`).

In particular each sign condition holds for one boundary defining function at `q` iff it holds for
every one (`TauCeti.IsBoundaryDefiningFunctionOn.forall_hessian_neg_iff` and its companions).

## References

* G. P. Paternain, M. Salo, G. Uhlmann, *Geometric Inverse Problems, with Emphasis on Two
  Dimensions*, Cambridge University Press (2023), Lemma 3.1.12.
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

namespace IsBoundaryDefiningFunctionOn

variable {ρ ρ' : M → ℝ} {U U' : Set M} {q : (𝓡∂ (n + 1)).boundary M}

/-- **Hessian characterisation of strict convexity.** For a boundary defining function `ρ` on an
open set containing `q ∈ ∂M`, the boundary is strictly convex at `q` iff `Hess ρ(dι u, dι u) < 0`
for every nonzero `u ∈ T_q∂M`. -/
theorem isStrictlyConvexAt_iff_forall_hessian_neg (hρ : IsBoundaryDefiningFunctionOn n ρ U)
    (hqU : (q : M) ∈ U) :
    IsStrictlyConvexAt q ↔ ∀ u : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q, u ≠ 0 →
      Manifold.hessian (𝓡∂ (n + 1)) ρ q
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
          (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q u)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
          (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q u) < 0 := by
  simp only [isStrictlyConvexAt_iff, hρ.boundarySecondFundamentalForm_apply hqU,
    lt_div_iff₀ (hρ.norm_mvfderiv_pos hqU q.property), zero_mul, neg_pos]

/-- **Hessian characterisation of convexity.** For a boundary defining function `ρ` on an open set
containing `q ∈ ∂M`, the boundary is convex at `q` iff `Hess ρ(dι u, dι u) ≤ 0` for every
`u ∈ T_q∂M`. -/
theorem isConvexAt_iff_forall_hessian_nonpos (hρ : IsBoundaryDefiningFunctionOn n ρ U)
    (hqU : (q : M) ∈ U) :
    IsConvexAt q ↔ ∀ u : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q,
      Manifold.hessian (𝓡∂ (n + 1)) ρ q
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
          (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q u)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
          (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q u) ≤ 0 := by
  simp only [isConvexAt_iff, hρ.boundarySecondFundamentalForm_apply hqU,
    le_div_iff₀ (hρ.norm_mvfderiv_pos hqU q.property), zero_mul, neg_nonneg]

/-- **Hessian characterisation of strict concavity.** For a boundary defining function `ρ` on an
open set containing `q ∈ ∂M`, the boundary is strictly concave at `q` iff
`Hess ρ(dι u, dι u) > 0` for every nonzero `u ∈ T_q∂M`. -/
theorem isStrictlyConcaveAt_iff_forall_hessian_pos (hρ : IsBoundaryDefiningFunctionOn n ρ U)
    (hqU : (q : M) ∈ U) :
    IsStrictlyConcaveAt q ↔ ∀ u : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q, u ≠ 0 →
      0 < Manifold.hessian (𝓡∂ (n + 1)) ρ q
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
          (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q u)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
          (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q u) := by
  simp only [isStrictlyConcaveAt_iff, hρ.boundarySecondFundamentalForm_apply hqU,
    div_lt_iff₀ (hρ.norm_mvfderiv_pos hqU q.property), zero_mul, neg_lt_zero]

/-- The sign condition `Hess ρ < 0` on the nonzero tangent vectors of the boundary at `q` holds for
one boundary defining function iff it holds for every other one. -/
theorem forall_hessian_neg_iff (hρ : IsBoundaryDefiningFunctionOn n ρ U) (hqU : (q : M) ∈ U)
    (hρ' : IsBoundaryDefiningFunctionOn n ρ' U') (hqU' : (q : M) ∈ U') :
    (∀ u : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q, u ≠ 0 →
      Manifold.hessian (𝓡∂ (n + 1)) ρ q
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
          (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q u)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
          (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q u) < 0) ↔
    ∀ u : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q, u ≠ 0 →
      Manifold.hessian (𝓡∂ (n + 1)) ρ' q
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
          (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q u)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
          (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q u) < 0 := by
  rw [← hρ.isStrictlyConvexAt_iff_forall_hessian_neg hqU,
    hρ'.isStrictlyConvexAt_iff_forall_hessian_neg hqU']

/-- The sign condition `Hess ρ ≤ 0` on the tangent space of the boundary at `q` holds for one
boundary defining function iff it holds for every other one. -/
theorem forall_hessian_nonpos_iff (hρ : IsBoundaryDefiningFunctionOn n ρ U) (hqU : (q : M) ∈ U)
    (hρ' : IsBoundaryDefiningFunctionOn n ρ' U') (hqU' : (q : M) ∈ U') :
    (∀ u : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q,
      Manifold.hessian (𝓡∂ (n + 1)) ρ q
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
          (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q u)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
          (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q u) ≤ 0) ↔
    ∀ u : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q,
      Manifold.hessian (𝓡∂ (n + 1)) ρ' q
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
          (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q u)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
          (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q u) ≤ 0 := by
  rw [← hρ.isConvexAt_iff_forall_hessian_nonpos hqU,
    hρ'.isConvexAt_iff_forall_hessian_nonpos hqU']

/-- The sign condition `Hess ρ > 0` on the nonzero tangent vectors of the boundary at `q` holds for
one boundary defining function iff it holds for every other one. -/
theorem forall_hessian_pos_iff (hρ : IsBoundaryDefiningFunctionOn n ρ U) (hqU : (q : M) ∈ U)
    (hρ' : IsBoundaryDefiningFunctionOn n ρ' U') (hqU' : (q : M) ∈ U') :
    (∀ u : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q, u ≠ 0 →
      0 < Manifold.hessian (𝓡∂ (n + 1)) ρ q
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
          (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q u)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
          (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q u)) ↔
    ∀ u : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q, u ≠ 0 →
      0 < Manifold.hessian (𝓡∂ (n + 1)) ρ' q
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
          (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q u)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
          (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q u) := by
  rw [← hρ.isStrictlyConcaveAt_iff_forall_hessian_pos hqU,
    hρ'.isStrictlyConcaveAt_iff_forall_hessian_pos hqU']

end IsBoundaryDefiningFunctionOn

end TauCeti
