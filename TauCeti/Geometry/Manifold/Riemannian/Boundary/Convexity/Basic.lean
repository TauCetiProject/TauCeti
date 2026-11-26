/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Boundary.SecondFundamentalForm.Isometry

/-!
# Convexity of the boundary of a Riemannian manifold

Let `M` be a Riemannian manifold with boundary modelled on the half-space `𝓡∂ (n + 1)`, and let
`II_q` be the second fundamental form of the boundary at `q ∈ ∂M`
(`TauCeti.boundarySecondFundamentalForm`), with the sign for which the closed unit ball has
`II = h`. The boundary is

* *strictly convex at `q`* (`TauCeti.IsStrictlyConvexAt`) if `II_q(u, u) > 0` for every nonzero
  `u ∈ T_q∂M`, that is, the quadratic form of `II_q` is positive definite (`QuadraticMap.PosDef`);
* *convex at `q`* (`TauCeti.IsConvexAt`) if `II_q(u, u) ≥ 0` for every `u ∈ T_q∂M`, that is,
  `II_q` is nonnegative (`LinearMap.IsNonneg`);
* *strictly concave at `q`* (`TauCeti.IsStrictlyConcaveAt`) if `II_q(u, u) < 0` for every nonzero
  `u ∈ T_q∂M`, that is, the quadratic form of `-II_q` is positive definite.

`TauCeti.IsStrictlyConvexOn S` asks for strict convexity at every point of `S ⊆ ∂M`, and
`TauCeti.IsStrictlyConvexBoundary n M` at every point of `∂M`.

## Main statements

* `TauCeti.IsStrictlyConvexAt.isConvexAt`: strict convexity implies convexity.
* `TauCeti.IsStrictlyConvexAt.not_isStrictlyConcaveAt`: for `n ≥ 1`, strict convexity and strict
  concavity at a point exclude each other.
* `TauCeti.isStrictlyConvexAt_of_eq_zero`, `TauCeti.isStrictlyConcaveAt_of_eq_zero`: in dimension
  one (`n = 0`), `T_q∂M = 0` and the boundary is both strictly convex and strictly concave at every
  point, so the exclusion needs `n ≥ 1`.
* `TauCeti.RiemannianIsometry.isStrictlyConvexAt_iff`, `isConvexAt_iff`,
  `isStrictlyConcaveAt_iff`, `isStrictlyConvexOn_iff` and `isStrictlyConvexBoundary_iff`: the
  predicates are invariant under isometries of Riemannian manifolds with boundary, since
  corresponding tangent vectors of the boundaries (`TauCeti.BoundaryTangentCorr`) have the same
  second fundamental form.

## References

* G. P. Paternain, M. Salo, G. Uhlmann, *Geometric Inverse Problems, with Emphasis on Two
  Dimensions*, Cambridge University Press (2023), Definition 3.1.7.
-/

public section

noncomputable section

open Bundle Function
open scoped Manifold ContDiff

namespace TauCeti

variable {n : ℕ} {M M' : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]
  [IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]

/-- The boundary is **strictly convex at** `q ∈ ∂M` if `II_q(u, u) > 0` for every nonzero
`u ∈ T_q∂M`, that is, the quadratic form of `II_q` is positive definite. -/
def IsStrictlyConvexAt (q : (𝓡∂ (n + 1)).boundary M) : Prop :=
  (boundarySecondFundamentalForm q).toQuadraticMap.PosDef

/-- The boundary is **convex at** `q ∈ ∂M` if `II_q(u, u) ≥ 0` for every `u ∈ T_q∂M`, that is,
`II_q` is nonnegative. -/
def IsConvexAt (q : (𝓡∂ (n + 1)).boundary M) : Prop :=
  LinearMap.IsNonneg (boundarySecondFundamentalForm q)

/-- The boundary is **strictly concave at** `q ∈ ∂M` if `II_q(u, u) < 0` for every nonzero
`u ∈ T_q∂M`, that is, the quadratic form of `-II_q` is positive definite. -/
def IsStrictlyConcaveAt (q : (𝓡∂ (n + 1)).boundary M) : Prop :=
  (-(boundarySecondFundamentalForm q).toQuadraticMap).PosDef

/-- The boundary is **strictly convex on** `S ⊆ ∂M` if it is strictly convex at every point of
`S`. -/
def IsStrictlyConvexOn (S : Set ((𝓡∂ (n + 1)).boundary M)) : Prop :=
  ∀ q ∈ S, IsStrictlyConvexAt q

variable (n M) in
/-- The boundary of `M` is **strictly convex** if it is strictly convex at every point of `∂M`. -/
def IsStrictlyConvexBoundary : Prop :=
  ∀ q : (𝓡∂ (n + 1)).boundary M, IsStrictlyConvexAt q

/-- Strict convexity at `q` is positive definiteness of the quadratic form of `II_q`. -/
theorem isStrictlyConvexAt_iff_posDef {q : (𝓡∂ (n + 1)).boundary M} :
    IsStrictlyConvexAt q ↔ (boundarySecondFundamentalForm q).toQuadraticMap.PosDef :=
  Iff.rfl

/-- Strict convexity at `q`: `II_q(u, u) > 0` for every nonzero `u ∈ T_q∂M`. -/
theorem isStrictlyConvexAt_iff {q : (𝓡∂ (n + 1)).boundary M} :
    IsStrictlyConvexAt q ↔ ∀ u : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q, u ≠ 0 →
      0 < boundarySecondFundamentalForm q u u := by
  simp only [isStrictlyConvexAt_iff_posDef, QuadraticMap.PosDef,
    LinearMap.BilinMap.toQuadraticMap_apply]

/-- Convexity at `q` is nonnegativity of `II_q`. -/
theorem isConvexAt_iff_isNonneg {q : (𝓡∂ (n + 1)).boundary M} :
    IsConvexAt q ↔ LinearMap.IsNonneg (boundarySecondFundamentalForm q) :=
  Iff.rfl

/-- Convexity at `q`: `II_q(u, u) ≥ 0` for every `u ∈ T_q∂M`. -/
theorem isConvexAt_iff {q : (𝓡∂ (n + 1)).boundary M} :
    IsConvexAt q ↔ ∀ u : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q,
      0 ≤ boundarySecondFundamentalForm q u u :=
  LinearMap.isNonneg_def

/-- Strict concavity at `q` is positive definiteness of the quadratic form of `-II_q`. -/
theorem isStrictlyConcaveAt_iff_posDef {q : (𝓡∂ (n + 1)).boundary M} :
    IsStrictlyConcaveAt q ↔ (-(boundarySecondFundamentalForm q).toQuadraticMap).PosDef :=
  Iff.rfl

/-- Strict concavity at `q`: `II_q(u, u) < 0` for every nonzero `u ∈ T_q∂M`. -/
theorem isStrictlyConcaveAt_iff {q : (𝓡∂ (n + 1)).boundary M} :
    IsStrictlyConcaveAt q ↔ ∀ u : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q, u ≠ 0 →
      boundarySecondFundamentalForm q u u < 0 := by
  simp only [isStrictlyConcaveAt_iff_posDef, QuadraticMap.PosDef, neg_apply,
    LinearMap.BilinMap.toQuadraticMap_apply, neg_pos]

/-- Strict convexity on `S`: strict convexity at every point of `S`. -/
theorem isStrictlyConvexOn_iff {S : Set ((𝓡∂ (n + 1)).boundary M)} :
    IsStrictlyConvexOn S ↔ ∀ q ∈ S, IsStrictlyConvexAt q :=
  Iff.rfl

/-- Strict convexity of the boundary: strict convexity at every point of `∂M`. -/
theorem isStrictlyConvexBoundary_iff :
    IsStrictlyConvexBoundary n M ↔ ∀ q : (𝓡∂ (n + 1)).boundary M, IsStrictlyConvexAt q :=
  Iff.rfl

/-- The boundary is strictly convex on all of `∂M` exactly when it is strictly convex. -/
@[simp]
theorem isStrictlyConvexOn_univ_iff :
    IsStrictlyConvexOn (Set.univ : Set ((𝓡∂ (n + 1)).boundary M)) ↔
      IsStrictlyConvexBoundary n M :=
  ⟨fun h q ↦ h q (Set.mem_univ q), fun h q _ ↦ h q⟩

/-- Strict convexity at a point implies convexity there. -/
theorem IsStrictlyConvexAt.isConvexAt {q : (𝓡∂ (n + 1)).boundary M}
    (h : IsStrictlyConvexAt q) : IsConvexAt q :=
  isConvexAt_iff.2 fun u ↦ (h.nonneg u).trans_eq (LinearMap.BilinMap.toQuadraticMap_apply _ u)

/-- For `n ≥ 1`, the boundary is not both strictly convex and strictly concave at a point: the
tangent space of the boundary has a nonzero vector. -/
theorem IsStrictlyConvexAt.not_isStrictlyConcaveAt [NeZero n] {q : (𝓡∂ (n + 1)).boundary M}
    (h : IsStrictlyConvexAt q) : ¬ IsStrictlyConcaveAt q := fun h' ↦ by
  obtain ⟨u, hu⟩ := exists_ne (0 : EuclideanSpace ℝ (Fin n))
  exact (isStrictlyConvexAt_iff.1 h u hu).not_gt (isStrictlyConcaveAt_iff.1 h' u hu)

/-- In dimension one (`n = 0`) every tangent vector of the boundary vanishes: `T_q∂M` is the type
`EuclideanSpace ℝ (Fin 0)`, a subsingleton, under the name `TangentSpace`. -/
private theorem eq_zero_of_eq_zero (hn : n = 0) {q : (𝓡∂ (n + 1)).boundary M}
    (u : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q) : u = 0 := by
  subst hn
  exact Subsingleton.elim (α := EuclideanSpace ℝ (Fin 0)) u 0

/-- In dimension one (`n = 0`) the tangent space of the boundary is zero, so the boundary is
strictly convex at every point. -/
theorem isStrictlyConvexAt_of_eq_zero (hn : n = 0) (q : (𝓡∂ (n + 1)).boundary M) :
    IsStrictlyConvexAt q :=
  isStrictlyConvexAt_iff.2 fun u hu ↦ (hu (eq_zero_of_eq_zero hn u)).elim

/-- In dimension one (`n = 0`) the tangent space of the boundary is zero, so the boundary is
strictly concave at every point. -/
theorem isStrictlyConcaveAt_of_eq_zero (hn : n = 0) (q : (𝓡∂ (n + 1)).boundary M) :
    IsStrictlyConcaveAt q :=
  isStrictlyConcaveAt_iff.2 fun u hu ↦ (hu (eq_zero_of_eq_zero hn u)).elim

/-! ### Invariance under isometries -/

variable [TopologicalSpace M'] [ChartedSpace (EuclideanHalfSpace (n + 1)) M']
  [IsManifold (𝓡∂ (n + 1)) 2 M']
  [RiemannianBundle (fun x : M' ↦ TangentSpace (𝓡∂ (n + 1)) x)]
  [IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : M' ↦ TangentSpace (𝓡∂ (n + 1)) x)]

namespace RiemannianIsometry

variable (Φ : RiemannianIsometry (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) M M') (q : (𝓡∂ (n + 1)).boundary M)

/-- An isometry `Φ` transfers a condition on the vanishing of a tangent vector of the boundary and
on its second fundamental form between `T_{Φ q}∂M'` and `T_q∂M`, through corresponding vectors. -/
private theorem forall_boundaryTangent_iff (p : Prop → ℝ → Prop) :
    (∀ u' : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        (⟨Φ q, Φ.apply_mem_boundary q.property⟩ : (𝓡∂ (n + 1)).boundary M'),
        p (u' = 0) (boundarySecondFundamentalForm _ u' u')) ↔
      ∀ u : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q,
        p (u = 0) (boundarySecondFundamentalForm q u u) := by
  refine ⟨fun h u ↦ ?_, fun h u' ↦ ?_⟩
  · obtain ⟨u', hc⟩ := exists_boundaryTangentCorr (by simp) Φ.toDiffeomorph q u
    rw [← hc.eq_zero_iff (Φ.mfderiv_injective q),
      ← Φ.boundarySecondFundamentalForm_map q u u u' u' hc hc]
    exact h u'
  · obtain ⟨u, hc⟩ := exists_boundaryTangentCorr_symm (by simp) Φ.toDiffeomorph q u'
    rw [hc.eq_zero_iff (Φ.mfderiv_injective q),
      Φ.boundarySecondFundamentalForm_map q u u u' u' hc hc]
    exact h u

/-- Strict convexity of the boundary at a point is invariant under isometries. -/
@[simp]
theorem isStrictlyConvexAt_iff :
    IsStrictlyConvexAt (⟨Φ q, Φ.apply_mem_boundary q.property⟩ : (𝓡∂ (n + 1)).boundary M') ↔
      IsStrictlyConvexAt q := by
  simp only [TauCeti.isStrictlyConvexAt_iff, ne_eq]
  exact Φ.forall_boundaryTangent_iff q fun z r ↦ ¬z → 0 < r

/-- Strict concavity of the boundary at a point is invariant under isometries. -/
@[simp]
theorem isStrictlyConcaveAt_iff :
    IsStrictlyConcaveAt (⟨Φ q, Φ.apply_mem_boundary q.property⟩ : (𝓡∂ (n + 1)).boundary M') ↔
      IsStrictlyConcaveAt q := by
  simp only [TauCeti.isStrictlyConcaveAt_iff, ne_eq]
  exact Φ.forall_boundaryTangent_iff q fun z r ↦ ¬z → r < 0

/-- Convexity of the boundary at a point is invariant under isometries. -/
@[simp]
theorem isConvexAt_iff :
    IsConvexAt (⟨Φ q, Φ.apply_mem_boundary q.property⟩ : (𝓡∂ (n + 1)).boundary M') ↔
      IsConvexAt q := by
  rw [TauCeti.isConvexAt_iff, TauCeti.isConvexAt_iff]
  exact Φ.forall_boundaryTangent_iff q fun _ r ↦ 0 ≤ r

/-- Strict convexity of the boundary on a set is invariant under isometries: `∂M'` is strictly
convex on `S'` exactly when `∂M` is strictly convex on the preimage of `S'` under `Φ`. -/
theorem isStrictlyConvexOn_iff (Φ : RiemannianIsometry (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) M M')
    {S' : Set ((𝓡∂ (n + 1)).boundary M')} :
    IsStrictlyConvexOn S' ↔ IsStrictlyConvexOn
      {q : (𝓡∂ (n + 1)).boundary M | ⟨Φ q, Φ.apply_mem_boundary q.property⟩ ∈ S'} := by
  simp only [TauCeti.isStrictlyConvexOn_iff, Set.mem_ofPred_eq]
  refine ⟨fun h q hq ↦ (Φ.isStrictlyConvexAt_iff q).1 (h _ hq), fun h q' hq' ↦ ?_⟩
  have hq : Φ.symm (q' : M') ∈ (𝓡∂ (n + 1)).boundary M :=
    Φ.symm.apply_mem_boundary q'.property
  have hΦq : (⟨Φ (Φ.symm q'), Φ.apply_mem_boundary hq⟩ : (𝓡∂ (n + 1)).boundary M') = q' :=
    Subtype.ext (Φ.apply_symm_apply _)
  rw [← hΦq] at hq' ⊢
  exact (Φ.isStrictlyConvexAt_iff ⟨_, hq⟩).2 (h _ hq')

/-- Strict convexity of the boundary is invariant under isometries. -/
theorem isStrictlyConvexBoundary_iff (Φ : RiemannianIsometry (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) M M') :
    IsStrictlyConvexBoundary n M' ↔ IsStrictlyConvexBoundary n M := by
  rw [← isStrictlyConvexOn_univ_iff, ← isStrictlyConvexOn_univ_iff, Φ.isStrictlyConvexOn_iff]
  simp only [Set.mem_univ, Set.ofPred_true]

end RiemannianIsometry

end TauCeti
