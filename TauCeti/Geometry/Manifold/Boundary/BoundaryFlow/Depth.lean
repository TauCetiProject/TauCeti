/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.BoundaryFlow.Basic
public import TauCeti.Geometry.Manifold.Boundary.Charts
public import TauCeti.Geometry.Manifold.ContMDiffMap.Radius

/-!
# A smooth depth for the inward flow of the boundary

Let `M` be a smooth Hausdorff sigma-compact manifold modeled on the Euclidean half-space
`𝓡∂ (n + 1)` and `v` a smooth vector field on `M` pointing inward at every boundary point. The
forward flow `Φ` of `v` along the boundary (`TauCeti.exists_contMDiffOn_boundaryFlow`) is defined
on an open set `W ⊆ M × ℝ` containing `∂M × {0}`. This file chooses a smooth positive depth
`δ : ∂M → ℝ`, below `1`, such that `Φ x t` is defined for `0 ≤ t ≤ δ x`
(`TauCeti.exists_contMDiffMap_depth_boundaryFlow`): `(x, t) ↦ Φ x t` is smooth on
`{(x, t) ∈ ∂M × ℝ | 0 ≤ t ≤ δ x}`, `t ↦ Φ x t` is an integral curve of `v` on `[0, δ x]` starting
at `x`, and `Φ x t` lies in the interior of `M` for `0 < t ≤ δ x`. Here `∂M` carries the manifold
structure of `TauCeti.isManifold_boundary`, and it is sigma-compact as a closed subset of `M`.

This is the second step of the flow construction of a smooth collar (Hirsch, *Differential
Topology*, Chapter 4, Theorem 6.1; Lee, *Introduction to Smooth Manifolds*, Theorem 9.25), whose
collar is `(x, s) ↦ Φ x (δ x s)`; the depth is Tau Ceti's smooth radius
`TauCeti.exists_contMDiffMap_closedBall_subset` on the boundary manifold.

## Main results

* `TauCeti.exists_contMDiffMap_depth_boundaryFlow`: a smooth depth for the inward flow of an
  inward-pointing field.
* `TauCeti.IsOutwardPointingField.exists_contMDiffMap_depth_boundaryFlow`: the same for the
  negative of an outward-pointing field.
-/

public section

open Filter Function Manifold Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ∞ M] [T2Space M] [SigmaCompactSpace M]

/-- **A smooth depth for the inward flow of the boundary.** Let `v` be a smooth vector field on a
Hausdorff sigma-compact manifold modeled on `𝓡∂ (n + 1)`, pointing inward at every boundary
point. There are a smooth function `δ : ∂M → (0, 1)` and a family `Φ x t` such that
`(x, t) ↦ Φ x t` is smooth on `{(x, t) ∈ ∂M × ℝ | 0 ≤ t ≤ δ x}` and, for every boundary point `x`,
the curve `t ↦ Φ x t` starts at `x`, is an integral curve of `v` on `[0, δ x]`, and lies in the
interior of `M` for `0 < t ≤ δ x`. -/
theorem exists_contMDiffMap_depth_boundaryFlow (v : (x : M) → TangentSpace (𝓡∂ (n + 1)) x)
    (hv : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞
      (fun x ↦ (⟨x, v x⟩ : TangentBundle (𝓡∂ (n + 1)) M)))
    (hin : ∀ a ∈ (𝓡∂ (n + 1)).boundary M, IsOutwardPointing a (-v a)) :
    ∃ δ : (letI := isManifold_boundary (n := n) (k := ∞) M;
        C^∞⟮𝓡 n, (𝓡∂ (n + 1)).boundary M; 𝓘(ℝ), ℝ⟯),
      (∀ x, 0 < δ x) ∧ (∀ x, δ x < 1) ∧ ∃ Φ : M → ℝ → M,
        ContMDiffOn ((𝓡 n).prod 𝓘(ℝ)) (𝓡∂ (n + 1)) ∞
          (fun p : (𝓡∂ (n + 1)).boundary M × ℝ ↦ Φ p.1 p.2) {p | p.2 ∈ Icc 0 (δ p.1)} ∧
        ∀ x : (𝓡∂ (n + 1)).boundary M, Φ x 0 = x ∧ IsMIntegralCurveOn (Φ x) v (Icc 0 (δ x)) ∧
          ∀ t ∈ Ioc 0 (δ x), Φ x t ∈ (𝓡∂ (n + 1)).interior M := by
  let _ := isManifold_boundary (n := n) (k := ∞) M
  have : SigmaCompactSpace ((𝓡∂ (n + 1)).boundary M) :=
    ((𝓡∂ (n + 1)).isClosed_boundary (by simp : (∞ : ℕ∞ω) ≠ 0)).sigmaCompactSpace
  obtain ⟨W, hW, hW0, Φ, hΦ, hΦW⟩ := exists_contMDiffOn_boundaryFlow v hv hin
  -- The inclusion `∂M × ℝ → M × ℝ` is smooth.
  have hg : ContMDiff ((𝓡 n).prod 𝓘(ℝ)) ((𝓡∂ (n + 1)).prod 𝓘(ℝ)) ∞
      (fun p : (𝓡∂ (n + 1)).boundary M × ℝ ↦ ((p.1 : M), p.2)) :=
    ((isImmersion_subtypeVal_boundary (k := ∞) M).contMDiff.comp contMDiff_fst).prodMk
      contMDiff_snd
  have hU (x : (𝓡∂ (n + 1)).boundary M) :
      (fun p : (𝓡∂ (n + 1)).boundary M × ℝ ↦ ((p.1 : M), p.2)) ⁻¹' W ∈ 𝓝 (x, (0 : ℝ)) :=
    (hW.preimage hg.continuous).mem_nhds (hW0 x x.property)
  obtain ⟨δ, hδpos, hδ1, hδU⟩ := exists_contMDiffMap_closedBall_subset (I := 𝓡 n) hU
    (ε := fun _ ↦ 1) lowerSemicontinuous_const fun _ ↦ one_pos
  have hmem (x : (𝓡∂ (n + 1)).boundary M) (t : ℝ) (ht : t ∈ Icc 0 (δ x)) :
      ((x : M), t) ∈ W := by
    refine hδU x t ?_
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
    exact ht.2
  refine ⟨δ, hδpos, hδ1, Φ, ?_, fun x ↦ ?_⟩
  · exact hΦ.comp hg.contMDiffOn fun p hp ↦ ⟨hmem p.1 p.2 hp, mem_univ _, hp.1⟩
  · obtain ⟨-, h0, hcurve, -⟩ := hΦW x (δ x) (hmem x _ ⟨(hδpos x).le, le_rfl⟩) (hδpos x).le
    exact ⟨h0, hcurve, fun t ht ↦ (hΦW x t (hmem x t ⟨ht.1.le, ht.2⟩) ht.1.le).2.2.2 ht.1⟩

/-- **A smooth depth for the inward flow along an outward field.** For a smooth field `V` pointing
outward at every boundary point, the conclusion of `TauCeti.exists_contMDiffMap_depth_boundaryFlow`
holds for the inward field `-V`. Such a `V` exists by `TauCeti.exists_isOutwardPointingField`. -/
theorem IsOutwardPointingField.exists_contMDiffMap_depth_boundaryFlow
    {V : (x : M) → TangentSpace (𝓡∂ (n + 1)) x} (hV : IsOutwardPointingField V) :
    ∃ δ : (letI := isManifold_boundary (n := n) (k := ∞) M;
        C^∞⟮𝓡 n, (𝓡∂ (n + 1)).boundary M; 𝓘(ℝ), ℝ⟯),
      (∀ x, 0 < δ x) ∧ (∀ x, δ x < 1) ∧ ∃ Φ : M → ℝ → M,
        ContMDiffOn ((𝓡 n).prod 𝓘(ℝ)) (𝓡∂ (n + 1)) ∞
          (fun p : (𝓡∂ (n + 1)).boundary M × ℝ ↦ Φ p.1 p.2) {p | p.2 ∈ Icc 0 (δ p.1)} ∧
        ∀ x : (𝓡∂ (n + 1)).boundary M, Φ x 0 = x ∧ IsMIntegralCurveOn (Φ x) (-V) (Icc 0 (δ x)) ∧
          ∀ t ∈ Ioc 0 (δ x), Φ x t ∈ (𝓡∂ (n + 1)).interior M :=
  TauCeti.exists_contMDiffMap_depth_boundaryFlow (-V)
    hV.contMDiff_neg hV.isOutwardPointing_neg_neg

end TauCeti
