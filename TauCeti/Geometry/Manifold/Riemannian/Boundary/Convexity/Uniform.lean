/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Boundary.Convexity.PrincipalCurvatures
public import TauCeti.Geometry.Manifold.Riemannian.Boundary.SecondFundamentalForm.Smooth
import TauCeti.Topology.VectorBundle.Bilinear

/-!
# Uniform convexity of a compact strictly convex boundary

Let `M` be a Riemannian manifold with boundary, with second fundamental form `II` and induced
metric `h` on the boundary. If the boundary is strictly convex at every point of a compact set
`K ⊆ ∂M`, there is a single constant `c > 0` with `II_q(u, u) ≥ c h_q(u, u)` for every `q ∈ K`
and every `u ∈ T_q∂M`
(`TauCeti.IsStrictlyConvexOn.exists_pos_mul_boundaryInducedForm_le_boundarySecondFundamentalForm`);
equivalently, every principal curvature at a point of `K` is at least `c`
(`TauCeti.IsStrictlyConvexOn.exists_pos_le_boundaryPrincipalCurvatures`). In particular this
holds on all of `∂M` when `∂M` is compact and strictly convex
(`IsStrictlyConvexBoundary.exists_pos_mul_boundaryInducedForm_le_boundarySecondFundamentalForm`,
`TauCeti.IsStrictlyConvexBoundary.exists_pos_le_boundaryPrincipalCurvatures`).

The proof uses that `II` and `h` are continuous sections of the bundle of bilinear forms on `T∂M`
(`TauCeti.continuous_boundarySecondFundamentalForm`, `TauCeti.continuous_boundaryInducedForm`) and
the comparison of two such families over a compact set
(`IsCompact.exists_pos_eventually_mul_bilinear_apply_self_le`). Pointwise, the bound
`II_q ≥ c h_q` is the bound `κᵢ(q) ≥ c` on the principal curvatures
(`TauCeti.forall_mul_boundaryInducedForm_le_boundarySecondFundamentalForm_iff`).

## References

* G. P. Paternain, M. Salo, G. Uhlmann, *Geometric Inverse Problems, with Emphasis on Two
  Dimensions*, Cambridge University Press (2023), Definition 3.1.7.
-/

public section

noncomputable section

open Bundle Filter Set
open scoped Manifold

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]
  [IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]

/-- **Uniform strict convexity on a compact set**: if the boundary is strictly convex at every
point of a compact set `K ⊆ ∂M`, there is `c > 0` with `II_q(u, u) ≥ c h_q(u, u)` for every
`q ∈ K` and every `u ∈ T_q∂M`. -/
theorem IsStrictlyConvexOn.exists_pos_mul_boundaryInducedForm_le_boundarySecondFundamentalForm
    {K : Set ((𝓡∂ (n + 1)).boundary M)} (hK : IsCompact K) (h : IsStrictlyConvexOn K) :
    ∃ c > 0, ∀ q ∈ K, ∀ u : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q,
      c * boundaryInducedForm q u u ≤ boundarySecondFundamentalForm q u u := by
  have : IsManifold (𝓡∂ (n + 1)) 1 M := .of_le (n := 2) (by norm_num)
  have : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 0 (EuclideanSpace ℝ (Fin (n + 1)))
      (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) := .of_le (n := 1) zero_le_one
  have : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1 ((𝓡∂ (n + 1)).boundary M) :=
    isManifold_boundary M
  have hproj : Continuous (fun z : Unit × K ↦ (z.2 : (𝓡∂ (n + 1)).boundary M)) :=
    continuous_subtypeVal.comp continuous_snd
  obtain ⟨c, hc, hle⟩ := IsCompact.exists_pos_eventually_mul_bilinear_apply_self_le
    (B := (𝓡∂ (n + 1)).boundary M) (F := EuclideanSpace ℝ (Fin n))
    (V := fun q : (𝓡∂ (n + 1)).boundary M ↦ TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q)
    (K := K) (p₀ := ()) hK
    (b := fun _ q ↦
      (boundarySecondFundamentalForm (q : (𝓡∂ (n + 1)).boundary M)).toContinuousBilinearMap)
    (b₀ := fun _ q ↦ (boundaryInducedForm (q : (𝓡∂ (n + 1)).boundary M)).toContinuousBilinearMap)
    (fun _ ↦ ((continuous_boundarySecondFundamentalForm n M).comp hproj).continuousAt)
    (fun _ ↦ ((continuous_boundaryInducedForm n M).comp hproj).continuousAt)
    (fun q u hu ↦ by
      simpa using isStrictlyConvexAt_iff.1 (isStrictlyConvexOn_iff.1 h q q.property) u hu)
  exact ⟨c, hc, fun q hq u ↦ by simpa using hle.self_of_nhds ⟨q, hq⟩ u⟩

/-- **Uniform lower bound on the principal curvatures on a compact set**: if the boundary is
strictly convex at every point of a compact set `K ⊆ ∂M`, there is `c > 0` such that every
principal curvature at every point of `K` is at least `c`. -/
theorem IsStrictlyConvexOn.exists_pos_le_boundaryPrincipalCurvatures
    {K : Set ((𝓡∂ (n + 1)).boundary M)} (hK : IsCompact K) (h : IsStrictlyConvexOn K) :
    ∃ c > 0, ∀ q ∈ K, ∀ i, c ≤ boundaryPrincipalCurvatures q i := by
  obtain ⟨c, hc, hle⟩ :=
    h.exists_pos_mul_boundaryInducedForm_le_boundarySecondFundamentalForm hK
  exact ⟨c, hc, fun q hq ↦
    forall_mul_boundaryInducedForm_le_boundarySecondFundamentalForm_iff.1 (hle q hq)⟩

variable [CompactSpace ((𝓡∂ (n + 1)).boundary M)]

/-- **Uniform strict convexity of a compact boundary**: if `∂M` is compact and strictly convex,
there is `c > 0` with `II_q(u, u) ≥ c h_q(u, u)` for every `q ∈ ∂M` and every `u ∈ T_q∂M`. -/
theorem IsStrictlyConvexBoundary.exists_pos_mul_boundaryInducedForm_le_boundarySecondFundamentalForm
    (h : IsStrictlyConvexBoundary n M) :
    ∃ c > 0, ∀ (q : (𝓡∂ (n + 1)).boundary M) (u : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q),
      c * boundaryInducedForm q u u ≤ boundarySecondFundamentalForm q u u := by
  obtain ⟨c, hc, hle⟩ :=
    IsStrictlyConvexOn.exists_pos_mul_boundaryInducedForm_le_boundarySecondFundamentalForm
      isCompact_univ (isStrictlyConvexOn_iff.2 fun q _ ↦ isStrictlyConvexBoundary_iff.1 h q)
  exact ⟨c, hc, fun q ↦ hle q (mem_univ q)⟩

/-- **Uniform lower bound on the principal curvatures of a compact boundary**: if `∂M` is compact
and strictly convex, there is `c > 0` such that every principal curvature at every point of `∂M`
is at least `c`. -/
theorem IsStrictlyConvexBoundary.exists_pos_le_boundaryPrincipalCurvatures
    (h : IsStrictlyConvexBoundary n M) :
    ∃ c > 0, ∀ (q : (𝓡∂ (n + 1)).boundary M) (i : Fin n), c ≤ boundaryPrincipalCurvatures q i := by
  obtain ⟨c, hc, hle⟩ := h.exists_pos_mul_boundaryInducedForm_le_boundarySecondFundamentalForm
  exact ⟨c, hc, fun q ↦
    forall_mul_boundaryInducedForm_le_boundarySecondFundamentalForm_iff.1 (hle q)⟩

end TauCeti
