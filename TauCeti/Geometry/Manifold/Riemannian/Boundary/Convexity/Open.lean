/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Boundary.Convexity.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Boundary.SecondFundamentalForm.Smooth
import TauCeti.Topology.Algebra.QuadraticForm.PosDef

/-!
# Strict convexity and strict concavity of the boundary are open conditions

Let `M` be a Riemannian manifold with boundary. The points of `∂M` at which the boundary is
strictly convex, respectively strictly concave, form an open subset of `∂M`
(`TauCeti.isOpen_setOf_isStrictlyConvexAt`, `TauCeti.isOpen_setOf_isStrictlyConcaveAt`).

The proof reads `II` in a local frame of `T∂M`: near `q₀`, transporting `II_q` to the model fibre
along a local trivialization of `T∂M` gives a family of bilinear forms on a fixed vector space
whose entries on a basis are continuous, because `II` pairs continuous tangent fields to a
continuous function. Positive definiteness is an open condition on such a family
(`LinearMap.BilinForm.eventually_posDef_of_continuousAt`). Strict concavity is positive
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
local instance : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1 ((𝓡∂ (n + 1)).boundary M) :=
  have : IsManifold (𝓡∂ (n + 1)) 1 M := IsManifold.of_le (n := 2) (by norm_num)
  isManifold_boundary M

variable [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]
  [IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]

/-- Near `q₀`, transporting a bilinear form on `T_q∂M` along the local trivialization of `T∂M` at
`q₀` gives a bilinear form on the model fibre; for `II` its entries on a basis are continuous at
`q₀`. -/
private theorem continuousAt_boundarySecondFundamentalForm_symmL (q₀ : (𝓡∂ (n + 1)).boundary M)
    (v w : EuclideanSpace ℝ (Fin n)) :
    ContinuousAt (fun q : (𝓡∂ (n + 1)).boundary M ↦ boundarySecondFundamentalForm q
      ((trivializationAt (EuclideanSpace ℝ (Fin n))
        (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) q₀).symmL ℝ q v)
      ((trivializationAt (EuclideanSpace ℝ (Fin n))
        (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) q₀).symmL ℝ q w)) q₀ := by
  set e := trivializationAt (EuclideanSpace ℝ (Fin n))
    (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) q₀
  have hq₀ : q₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' q₀
  have hsec : ∀ y : EuclideanSpace ℝ (Fin n),
      ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).tangent 0
        (T% (fun q ↦ e.symmL ℝ q y)) q₀ := by
    intro y
    refine (e.contMDiffOn_section_baseSet_iff.2 ((contMDiffOn_const (c := y)).congr ?_)).contMDiffAt
      (e.open_baseSet.mem_nhds hq₀)
    intro q hq
    simp [hq]
  exact (contMDiffAt_boundarySecondFundamentalForm_apply (k := 0) (m := 2) (l := 1) (by norm_num)
    (by norm_num) (hsec v) (hsec w)).continuousAt

/-- For a fixed scalar `s`, positivity of `s * II_q(u, u)` on nonzero `u ∈ T_q∂M` is an open
condition on `q`: read in the local trivialization of `T∂M` at `q₀`, `s • II` is a family of
bilinear forms on the model fibre with continuous entries. -/
private theorem eventually_forall_mul_boundarySecondFundamentalForm_pos (s : ℝ)
    {q₀ : (𝓡∂ (n + 1)).boundary M}
    (h : ∀ u : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q₀, u ≠ 0 →
      0 < s * boundarySecondFundamentalForm q₀ u u) :
    ∀ᶠ q in 𝓝 q₀, ∀ u : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q, u ≠ 0 →
      0 < s * boundarySecondFundamentalForm q u u := by
  set e := trivializationAt (EuclideanSpace ℝ (Fin n))
    (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) q₀
  have hq₀ : q₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' q₀
  let B : (𝓡∂ (n + 1)).boundary M → LinearMap.BilinForm ℝ (EuclideanSpace ℝ (Fin n)) :=
    fun q ↦ s • (boundarySecondFundamentalForm q).compl₁₂ (e.symmL ℝ q).toLinearMap
      (e.symmL ℝ q).toLinearMap
  have hB : ∀ q x, (B q).toQuadraticMap x =
      s * boundarySecondFundamentalForm q (e.symmL ℝ q x) (e.symmL ℝ q x) := fun _ _ ↦ rfl
  have hpos : ∀ q ∈ e.baseSet, (∀ u : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q, u ≠ 0 →
      0 < s * boundarySecondFundamentalForm q u u) ↔ (B q).toQuadraticMap.PosDef := by
    intro q hq
    constructor
    · intro hII x hx
      rw [hB]
      exact hII _ fun h0 ↦ hx (by
        rw [← e.continuousLinearMapAt_symmL (R := ℝ) hq x, h0, map_zero])
    · intro hBq u hu
      have hx : e.continuousLinearMapAt ℝ q u ≠ 0 := fun h0 ↦ hu (by
        rw [← e.symmL_continuousLinearMapAt (R := ℝ) hq u, h0, map_zero])
      simpa only [hB, e.symmL_continuousLinearMapAt (R := ℝ) hq u] using hBq _ hx
  filter_upwards [LinearMap.BilinForm.eventually_posDef_of_continuousAt
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
      (fun i j ↦ continuousAt_const.mul (continuousAt_boundarySecondFundamentalForm_symmL q₀ _ _))
      ((hpos q₀ hq₀).1 h), e.open_baseSet.mem_nhds hq₀] with q hq hqe
  exact (hpos q hqe).2 hq

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
