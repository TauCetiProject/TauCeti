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
  `u ∈ T_q∂M`;
* *convex at `q`* (`TauCeti.IsConvexAt`) if `II_q(u, u) ≥ 0` for every `u ∈ T_q∂M`;
* *strictly concave at `q`* (`TauCeti.IsStrictlyConcaveAt`) if `II_q(u, u) < 0` for every nonzero
  `u ∈ T_q∂M`.

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
  `isStrictlyConcaveAt_iff` and `isStrictlyConvexBoundary_iff`: the predicates are invariant under
  isometries of Riemannian manifolds with boundary.

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
`u ∈ T_q∂M`. -/
def IsStrictlyConvexAt (q : (𝓡∂ (n + 1)).boundary M) : Prop :=
  ∀ u : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q, u ≠ 0 →
    0 < boundarySecondFundamentalForm q u u

/-- The boundary is **convex at** `q ∈ ∂M` if `II_q(u, u) ≥ 0` for every `u ∈ T_q∂M`. -/
def IsConvexAt (q : (𝓡∂ (n + 1)).boundary M) : Prop :=
  ∀ u : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q, 0 ≤ boundarySecondFundamentalForm q u u

/-- The boundary is **strictly concave at** `q ∈ ∂M` if `II_q(u, u) < 0` for every nonzero
`u ∈ T_q∂M`. -/
def IsStrictlyConcaveAt (q : (𝓡∂ (n + 1)).boundary M) : Prop :=
  ∀ u : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q, u ≠ 0 →
    boundarySecondFundamentalForm q u u < 0

/-- The boundary is **strictly convex on** `S ⊆ ∂M` if it is strictly convex at every point of
`S`. -/
def IsStrictlyConvexOn (S : Set ((𝓡∂ (n + 1)).boundary M)) : Prop :=
  ∀ q ∈ S, IsStrictlyConvexAt q

variable (n M) in
/-- The boundary of `M` is **strictly convex** if it is strictly convex at every point of `∂M`. -/
def IsStrictlyConvexBoundary : Prop :=
  ∀ q : (𝓡∂ (n + 1)).boundary M, IsStrictlyConvexAt q

/-- The boundary is strictly convex on all of `∂M` exactly when it is strictly convex. -/
theorem isStrictlyConvexOn_univ_iff :
    IsStrictlyConvexOn (Set.univ : Set ((𝓡∂ (n + 1)).boundary M)) ↔
      IsStrictlyConvexBoundary n M :=
  ⟨fun h q ↦ h q (Set.mem_univ q), fun h q _ ↦ h q⟩

/-- Strict convexity at a point implies convexity there. -/
theorem IsStrictlyConvexAt.isConvexAt {q : (𝓡∂ (n + 1)).boundary M}
    (h : IsStrictlyConvexAt q) : IsConvexAt q := fun u ↦ by
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  · exact (h u hu).le

/-- For `n ≥ 1`, the boundary is not both strictly convex and strictly concave at a point: the
tangent space of the boundary has a nonzero vector. -/
theorem IsStrictlyConvexAt.not_isStrictlyConcaveAt [NeZero n] {q : (𝓡∂ (n + 1)).boundary M}
    (h : IsStrictlyConvexAt q) : ¬ IsStrictlyConcaveAt q := fun h' ↦ by
  let u : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q := EuclideanSpace.single 0 1
  have hu0 : (EuclideanSpace.single (0 : Fin n) (1 : ℝ) : EuclideanSpace ℝ (Fin n)) ≠ 0 :=
    norm_ne_zero_iff.1 (by simp)
  have hu : u ≠ 0 := hu0
  exact (h u hu).not_gt (h' u hu)

/-- In dimension one (`n = 0`) the tangent space of the boundary is zero, so the boundary is
strictly convex at every point. -/
theorem isStrictlyConvexAt_of_eq_zero (hn : n = 0) (q : (𝓡∂ (n + 1)).boundary M) :
    IsStrictlyConvexAt q := fun u hu ↦ by
  subst hn
  exact (hu (Subsingleton.elim (α := EuclideanSpace ℝ (Fin 0)) u 0)).elim

/-- In dimension one (`n = 0`) the tangent space of the boundary is zero, so the boundary is
strictly concave at every point. -/
theorem isStrictlyConcaveAt_of_eq_zero (hn : n = 0) (q : (𝓡∂ (n + 1)).boundary M) :
    IsStrictlyConcaveAt q := fun u hu ↦ by
  subst hn
  exact (hu (Subsingleton.elim (α := EuclideanSpace ℝ (Fin 0)) u 0)).elim

/-! ### Invariance under isometries -/

variable [TopologicalSpace M'] [ChartedSpace (EuclideanHalfSpace (n + 1)) M']
  [IsManifold (𝓡∂ (n + 1)) 2 M']
  [RiemannianBundle (fun x : M' ↦ TangentSpace (𝓡∂ (n + 1)) x)]
  [IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : M' ↦ TangentSpace (𝓡∂ (n + 1)) x)]

namespace RiemannianIsometry

variable (Φ : RiemannianIsometry (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) M M') (q : (𝓡∂ (n + 1)).boundary M)

/-- The boundary point `Φ q` of `M'`, for an isometry `Φ` and a boundary point `q` of `M`. -/
abbrev boundaryMap : (𝓡∂ (n + 1)).boundary M' := ⟨Φ q, Φ.apply_mem_boundary q.property⟩

/-- Two tangent vectors `u ∈ T_q∂M` and `u' ∈ T_{Φ q}∂M'` correspond under an isometry `Φ` when
`dι' u' = dΦ (dι u)`. -/
abbrev BoundaryTangentCorr (u : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q)
    (u' : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (Φ.boundaryMap q)) : Prop :=
  mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
      (Subtype.val : (𝓡∂ (n + 1)).boundary M' → M') (Φ.boundaryMap q) u' =
    mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) Φ q
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
        (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q u)

omit [IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]
  [IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : M' ↦ TangentSpace (𝓡∂ (n + 1)) x)] in
private theorem map_mfderiv_boundaryTangentSpace' :
    (boundaryTangentSpace q).map (mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) Φ q).toLinearMap =
      boundaryTangentSpace (Φ.boundaryMap q) :=
  map_mfderiv_boundaryTangentSpace (k := ∞) (by simp) Φ.toDiffeomorph q

omit [IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]
  [IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : M' ↦ TangentSpace (𝓡∂ (n + 1)) x)] in
/-- Every tangent vector of `∂M` at `q` corresponds under an isometry to one of `∂M'` at `Φ q`. -/
theorem exists_boundaryTangentCorr (u : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q) :
    ∃ u', Φ.BoundaryTangentCorr q u u' := by
  have hmem := Φ.map_mfderiv_boundaryTangentSpace' q ▸
    Submodule.mem_map_of_mem (f := (mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) Φ q).toLinearMap)
      (mfderiv_subtypeVal_mem_boundaryTangentSpace q u)
  rw [boundaryTangentSpace_def, LinearMap.mem_range] at hmem
  obtain ⟨u', hu'⟩ := hmem
  exact ⟨u', hu'⟩

omit [IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]
  [IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : M' ↦ TangentSpace (𝓡∂ (n + 1)) x)] in
/-- Every tangent vector of `∂M'` at `Φ q` corresponds under an isometry to one of `∂M` at `q`. -/
theorem exists_boundaryTangentCorr_symm
    (u' : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (Φ.boundaryMap q)) :
    ∃ u, Φ.BoundaryTangentCorr q u u' := by
  have hmem : mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
      (Subtype.val : (𝓡∂ (n + 1)).boundary M' → M') (Φ.boundaryMap q) u' ∈
        (boundaryTangentSpace q).map (mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) Φ q).toLinearMap := by
    rw [Φ.map_mfderiv_boundaryTangentSpace' q]
    exact mfderiv_subtypeVal_mem_boundaryTangentSpace _ u'
  obtain ⟨v, hv, hvu⟩ := Submodule.mem_map.1 hmem
  rw [boundaryTangentSpace_def, LinearMap.mem_range] at hv
  obtain ⟨u, rfl⟩ := hv
  exact ⟨u, hvu.symm⟩

omit [IsManifold (𝓡∂ (n + 1)) 2 M]
  [IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)] [IsManifold (𝓡∂ (n + 1)) 2 M']
  [IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : M' ↦ TangentSpace (𝓡∂ (n + 1)) x)] in
/-- Corresponding tangent vectors are zero together. -/
theorem BoundaryTangentCorr.eq_zero_iff {u : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q}
    {u' : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (Φ.boundaryMap q)}
    (h : Φ.BoundaryTangentCorr q u u') : u' = 0 ↔ u = 0 := by
  rw [← (injective_mfderiv_subtypeVal_boundary (Φ.boundaryMap q)).eq_iff, map_zero, h,
    ← map_zero (mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) Φ q), (Φ.mfderiv_injective q).eq_iff,
    ← map_zero (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
      (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q),
    (injective_mfderiv_subtypeVal_boundary q).eq_iff]

/-- Corresponding tangent vectors have the same second fundamental form. -/
theorem BoundaryTangentCorr.boundarySecondFundamentalForm_eq
    {u : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q}
    {u' : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (Φ.boundaryMap q)}
    (h : Φ.BoundaryTangentCorr q u u') :
    boundarySecondFundamentalForm (Φ.boundaryMap q) u' u' =
      boundarySecondFundamentalForm q u u :=
  Φ.boundarySecondFundamentalForm_map q u u u' u' h h

private theorem forall_ne_zero_iff (p : ℝ → Prop) :
    (∀ u' : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (Φ.boundaryMap q), u' ≠ 0 →
        p (boundarySecondFundamentalForm (Φ.boundaryMap q) u' u')) ↔
      ∀ u : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q, u ≠ 0 →
        p (boundarySecondFundamentalForm q u u) := by
  refine ⟨fun h u hu ↦ ?_, fun h u' hu' ↦ ?_⟩
  · obtain ⟨u', hc⟩ := Φ.exists_boundaryTangentCorr q u
    rw [← hc.boundarySecondFundamentalForm_eq]
    exact h u' fun h0 ↦ hu ((hc.eq_zero_iff).1 h0)
  · obtain ⟨u, hc⟩ := Φ.exists_boundaryTangentCorr_symm q u'
    rw [hc.boundarySecondFundamentalForm_eq]
    exact h u fun h0 ↦ hu' ((hc.eq_zero_iff).2 h0)

/-- Strict convexity of the boundary at a point is invariant under isometries. -/
theorem isStrictlyConvexAt_iff : IsStrictlyConvexAt (Φ.boundaryMap q) ↔ IsStrictlyConvexAt q :=
  Φ.forall_ne_zero_iff q (0 < ·)

/-- Strict concavity of the boundary at a point is invariant under isometries. -/
theorem isStrictlyConcaveAt_iff :
    IsStrictlyConcaveAt (Φ.boundaryMap q) ↔ IsStrictlyConcaveAt q :=
  Φ.forall_ne_zero_iff q (· < 0)

/-- Convexity of the boundary at a point is invariant under isometries. -/
theorem isConvexAt_iff : IsConvexAt (Φ.boundaryMap q) ↔ IsConvexAt q := by
  refine ⟨fun h u ↦ ?_, fun h u' ↦ ?_⟩
  · obtain ⟨u', hc⟩ := Φ.exists_boundaryTangentCorr q u
    rw [← hc.boundarySecondFundamentalForm_eq]
    exact h u'
  · obtain ⟨u, hc⟩ := Φ.exists_boundaryTangentCorr_symm q u'
    rw [hc.boundarySecondFundamentalForm_eq]
    exact h u

/-- Strict convexity of the boundary is invariant under isometries. -/
theorem isStrictlyConvexBoundary_iff (Φ : RiemannianIsometry (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) M M') :
    IsStrictlyConvexBoundary n M' ↔ IsStrictlyConvexBoundary n M := by
  refine ⟨fun h q ↦ (Φ.isStrictlyConvexAt_iff q).1 (h _), fun h q' ↦ ?_⟩
  have hq : Φ.symm (q' : M') ∈ (𝓡∂ (n + 1)).boundary M :=
    Φ.symm.apply_mem_boundary q'.property
  have hq' : Φ.boundaryMap ⟨Φ.symm q', hq⟩ = q' := Subtype.ext (Φ.apply_symm_apply _)
  rw [← hq']
  exact (Φ.isStrictlyConvexAt_iff _).2 (h _)

end RiemannianIsometry

end TauCeti
