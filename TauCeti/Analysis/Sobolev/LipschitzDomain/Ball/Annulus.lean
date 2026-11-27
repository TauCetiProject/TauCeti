/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.Ball.SphereChart
import TauCeti.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Boundary charts of an annulus

Let `y` be a point of `ℝⁿ⁺¹ = EuclideanSpace ℝ (Fin (n + 1))` and `0 < r < R`. This file shows
that the annulus `A = ball y R ∩ (closedBall y r)ᶜ` has `C^{1,α}` boundary in the form that the
`C^{1,β}` estimates up to the boundary take as input
(`TauCeti.PDE.exists_holderOnWith_gradient_closure_of_isBounded` and its Morrey-datum version):
at every frontier point `x` of `A` there are rigid coordinates `e : ℝⁿ⁺¹ ≃ ℝ × ℝⁿ` with
`e x = 0` in which, inside a small cylinder, `A` is the region strictly above the graph of a
`C¹` function `γ : ℝⁿ → ℝ` with `γ 0 = 0` and `α`-Hölder derivative, for every `α ≤ 1`
(`TauCeti.exists_affineIsometryEquiv_graph_of_mem_frontier_annulus`).

The frontier of `A` lies on its two spheres. On the outer sphere the chart is that of the ball
of radius `R` (`TauCeti.exists_affineIsometryEquiv_graph_ball`), and on the inner sphere that of
the exterior of the closed ball of radius `r`
(`TauCeti.exists_affineIsometryEquiv_graph_compl_closedBall`), both with the fixed base `ℝⁿ` that
those estimates require. A cylinder of half-height and radius at most `(R - r) / 2` about the
chart centre does not meet the other sphere, so inside it `A` agrees with the ball, respectively
with the exterior.

Annuli are the comparison domains of barrier arguments at a boundary point, as in the proof of
Hopf's boundary-point lemma for divergence-form equations.

## References

* L. Rosales, *Generalizing Hopf's boundary point lemma*, Canad. Math. Bull. **62** (2019),
  arXiv:1806.07003, Lemma 3.1 (the `C^{1,α}` estimate on the annulus `B₁ ∖ closedBall 0 (1/2)`).
-/

public section

noncomputable section

open Metric Set
open scoped NNReal

namespace TauCeti

variable {n : ℕ}

local notation "F" => EuclideanSpace ℝ (Fin (n + 1))

/-- In rigid coordinates centred at `x`, a point of the normal cylinder of half-height and radius
`h` lies within `2 h` of `x`. -/
private theorem dist_symm_lt_of_mem_normalCylinder
    {e : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × EuclideanSpace ℝ (Fin n))} {x : F} (he : e x = 0) {h : ℝ}
    {z : WithLp 2 (ℝ × EuclideanSpace ℝ (Fin n))} (hz : z ∈ normalCylinder h h) :
    dist (e.symm z) x < 2 * h := by
  obtain ⟨h1, h2, h3⟩ := mem_normalCylinder.1 hz
  have hh : 0 < h := (norm_nonneg _).trans_lt h3
  rw [← e.dist_map, e.apply_symm_apply, he, dist_zero_right,
    ← pow_lt_pow_iff_left₀ (norm_nonneg z) (by positivity) two_ne_zero,
    WithLp.prod_norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs]
  nlinarith [norm_nonneg z.snd]

/-- The conclusion of `exists_affineIsometryEquiv_graph_of_mem_frontier_annulus` at a point `x`
for a set `A`. -/
private def HasGraphChart (A : Set F) (x : F) (α : ℝ≥0) : Prop :=
  ∃ (e : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × EuclideanSpace ℝ (Fin n))) (γ : EuclideanSpace ℝ (Fin n) → ℝ)
    (h₀ r₀ : ℝ) (Kγ : ℝ≥0), e x = 0 ∧ 0 < h₀ ∧ 0 < r₀ ∧ γ 0 = 0 ∧ ContDiff ℝ 1 γ ∧
      HolderWith Kγ α (fderiv ℝ γ) ∧ ∀ z ∈ normalCylinder h₀ r₀, (e.symm z ∈ A ↔ γ z.snd < z.fst)

/-- On the outer sphere the annulus is, near `x`, the ball of radius `R`. -/
private theorem hasGraphChart_of_mem_sphere_outer {y x : F} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hx : x ∈ sphere y R) {α : ℝ≥0} (hα : α ≤ 1) :
    HasGraphChart (ball y R ∩ (closedBall y r)ᶜ) x α := by
  have : Fact (Module.finrank ℝ F = n + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hR : 0 < R := hr.trans hrR
  obtain ⟨e, γ, K, he, h0, hγ, hK, H⟩ := exists_affineIsometryEquiv_graph_ball (n := n) hR hx hα
  set h := min (R / 4) ((R - r) / 2)
  have hh : 0 < h := lt_min (by positivity) (by linarith)
  refine ⟨e, γ, h, h, K, he, hh, hh, h0, hγ, hK, fun z hz => ?_⟩
  have hd := dist_symm_lt_of_mem_normalCylinder he hz
  have hout : e.symm z ∈ (closedBall y r)ᶜ := by
    rw [mem_compl_iff, mem_closedBall, not_le]
    linarith [dist_triangle_left x y (e.symm z), mem_sphere.1 hx,
      min_le_right (R / 4) ((R - r) / 2)]
  obtain ⟨h1, h2, h3⟩ := mem_normalCylinder.1 hz
  rw [mem_inter_iff, and_iff_left hout]
  exact H z (mem_normalCylinder.2 ⟨by linarith [min_le_left (R / 4) ((R - r) / 2)],
    by linarith [min_le_left (R / 4) ((R - r) / 2)], h3.trans_le (min_le_left _ _)⟩)

/-- On the inner sphere the annulus is, near `x`, the exterior of the closed ball of radius `r`. -/
private theorem hasGraphChart_of_mem_sphere_inner {y x : F} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hx : x ∈ sphere y r) {α : ℝ≥0} (hα : α ≤ 1) :
    HasGraphChart (ball y R ∩ (closedBall y r)ᶜ) x α := by
  have : Fact (Module.finrank ℝ F = n + 1) := ⟨finrank_euclideanSpace_fin⟩
  obtain ⟨e, γ, K, he, h0, hγ, hK, H⟩ :=
    exists_affineIsometryEquiv_graph_compl_closedBall (n := n) hr hx hα
  set h := min (r / 4) ((R - r) / 2)
  have hh : 0 < h := lt_min (by positivity) (by linarith)
  refine ⟨e, γ, h, h, K, he, hh, hh, h0, hγ, hK, fun z hz => ?_⟩
  have hd := dist_symm_lt_of_mem_normalCylinder he hz
  have hin : e.symm z ∈ ball y R := by
    rw [mem_ball]
    linarith [dist_triangle (e.symm z) x y, mem_sphere.1 hx, min_le_right (r / 4) ((R - r) / 2)]
  obtain ⟨h1, h2, h3⟩ := mem_normalCylinder.1 hz
  rw [mem_inter_iff, and_iff_right hin]
  exact H z (mem_normalCylinder.2 ⟨by linarith [min_le_left (r / 4) ((R - r) / 2)],
    by linarith [min_le_left (r / 4) ((R - r) / 2)], h3.trans_le (min_le_left _ _)⟩)

/-- **`C^{1,α}` boundary charts of an annulus.** Let `0 < r < R` and let `x` be a frontier point
of the annulus `A = ball y R ∩ (closedBall y r)ᶜ` of `ℝⁿ⁺¹`. There are rigid coordinates
`e : ℝⁿ⁺¹ ≃ ℝ × ℝⁿ` with `e x = 0` and a `C¹` function `γ : ℝⁿ → ℝ` with `γ 0 = 0` whose
derivative is `α`-Hölder, `α ≤ 1`, such that inside the normal cylinder of half-height `h₀` and
radius `r₀` about the origin, `A` is the region strictly above the graph of `γ`. -/
theorem exists_affineIsometryEquiv_graph_of_mem_frontier_annulus {y x : F} {r R : ℝ} (hr : 0 < r)
    (hrR : r < R) (hx : x ∈ frontier (ball y R ∩ (closedBall y r)ᶜ)) {α : ℝ≥0} (hα : α ≤ 1) :
    ∃ (e : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × EuclideanSpace ℝ (Fin n))) (γ : EuclideanSpace ℝ (Fin n) → ℝ)
      (h₀ r₀ : ℝ) (Kγ : ℝ≥0), e x = 0 ∧ 0 < h₀ ∧ 0 < r₀ ∧ γ 0 = 0 ∧ ContDiff ℝ 1 γ ∧
        HolderWith Kγ α (fderiv ℝ γ) ∧
        ∀ z ∈ normalCylinder h₀ r₀,
          (e.symm z ∈ ball y R ∩ (closedBall y r)ᶜ ↔ γ z.snd < z.fst) :=
  (frontier_ball_inter_compl_closedBall_subset y r R hx).elim
    (hasGraphChart_of_mem_sphere_outer hr hrR · hα) (hasGraphChart_of_mem_sphere_inner hr hrR · hα)

end TauCeti
