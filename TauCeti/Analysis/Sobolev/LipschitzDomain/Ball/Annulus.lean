/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.Ball.SphereChart
public import Mathlib.Analysis.InnerProductSpace.PiL2
import TauCeti.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Analysis.SpecialFunctions.Sqrt

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

The base of every chart is the same space `ℝⁿ`, as those estimates require; the tangent space
`(ℝ ∙ ν)ᗮ` of the sphere at a point with normal `ν` is identified with `ℝⁿ` by a linear
isometry. On the outer sphere the annulus lies on the side of the centre, and near the chart
centre the graph is that of `v ↦ R - √(R² - ‖v‖²)`; on the inner sphere it lies on the far side,
and the graph is that of `v ↦ √(r² - ‖v‖²) - r`. Both are the rescaled sphere graphs
`v ↦ s * unitSphereGraph (s⁻¹ • v)`, with `s = R` and `s = -r` respectively.

Annuli are the comparison domains of barrier arguments at a boundary point, as in the proof of
Hopf's boundary-point lemma for divergence-form equations.

## References

* L. Rosales, *Generalizing Hopf's boundary point lemma*, Canad. Math. Bull. **62** (2019),
  arXiv:1806.07003, Lemma 3.1 (the `C^{1,α}` estimate on the annulus `B₁ ∖ closedBall 0 (1/2)`).
-/

public section

noncomputable section

open Metric Set
open scoped NNReal InnerProductSpace

namespace TauCeti

section Graph

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- The sphere graph rescaled by `s ≠ 0`: `v ↦ s * unitSphereGraph (s⁻¹ • v)`, which near the
origin is `s (1 - √(1 - ‖v‖² / s²))`. -/
private def scaledSphereGraph (s : ℝ) (v : K) : ℝ :=
  s * unitSphereGraph (s⁻¹ • v)

private theorem scaledSphereGraph_zero (s : ℝ) : scaledSphereGraph s (0 : K) = 0 := by
  simp [scaledSphereGraph]

private theorem contDiff_scaledSphereGraph (s : ℝ) {k : ℕ∞} :
    ContDiff ℝ k (scaledSphereGraph (K := K) s) :=
  contDiff_const.mul (contDiff_unitSphereGraph.comp (contDiff_const_smul s⁻¹))

/-- The derivative of the rescaled sphere graph at `v` is that of the sphere graph at `s⁻¹ • v`. -/
private theorem fderiv_scaledSphereGraph {s : ℝ} (hs : s ≠ 0) :
    fderiv ℝ (scaledSphereGraph (K := K) s) =
      fun v => fderiv ℝ (unitSphereGraph (K := K)) (s⁻¹ • v) := by
  funext v
  have hg : HasFDerivAt (unitSphereGraph (K := K))
      (fderiv ℝ (unitSphereGraph (K := K)) (s⁻¹ • v)) (s⁻¹ • v) :=
    ((contDiff_unitSphereGraph (K := K) (k := 1)).differentiable one_ne_zero _).hasFDerivAt
  have hl : HasFDerivAt (fun w : K => s⁻¹ • w) (s⁻¹ • ContinuousLinearMap.id ℝ K) v :=
    (hasFDerivAt_id v).const_smul s⁻¹
  refine ((hg.comp v hl).const_mul s).fderiv.trans ?_
  ext w
  simp [smul_smul, hs]

/-- The derivative of the rescaled sphere graph is Hölder continuous, for every exponent at most
one. -/
private theorem exists_holderWith_fderiv_scaledSphereGraph [FiniteDimensional ℝ K] {s : ℝ}
    (hs : s ≠ 0) {α : ℝ≥0} (hα : α ≤ 1) :
    ∃ C : ℝ≥0, HolderWith C α (fderiv ℝ (scaledSphereGraph (K := K) s)) := by
  obtain ⟨C, hC⟩ := exists_holderWith_fderiv_unitSphereGraph (K := K) hα
  have hl : HolderWith ‖s⁻¹‖₊ 1 fun v : K => s⁻¹ • v := (lipschitzWith_smul s⁻¹).holderWith
  refine ⟨C * ‖s⁻¹‖₊ ^ (α : ℝ), ?_⟩
  rw [fderiv_scaledSphereGraph hs]
  simpa only [mul_one, Function.comp_def] using hC.comp hl

/-- The squared distance `(s - t)² + ‖v‖²` in the coordinates rescaled by `s ≠ 0`. -/
private theorem sub_sq_add_norm_sq_eq {s : ℝ} (hs : s ≠ 0) (t : ℝ) (v : K) :
    (s - t) ^ 2 + ‖v‖ ^ 2 = s ^ 2 * ((1 - t / s) ^ 2 + ‖s⁻¹ • v‖ ^ 2) := by
  rw [norm_smul, norm_inv, Real.norm_eq_abs, mul_pow, inv_pow, sq_abs]
  field_simp

private theorem norm_inv_smul_le {s : ℝ} (hs : s ≠ 0) {v : K} (hv : ‖v‖ ≤ |s| / 4) :
    ‖s⁻¹ • v‖ ≤ 1 / 4 := by
  rw [norm_smul, norm_inv, Real.norm_eq_abs, inv_mul_le_iff₀ (abs_pos.2 hs)]
  linarith

/-- **The region above the rescaled sphere graph, `s > 0`.** For `‖v‖ ≤ s / 4` and `t ≤ s`, the
point at height `t` over `v` lies in the open ball of radius `s` about the point at height `s`
exactly when it lies above the graph. This is `TauCeti.unitSphereGraph_lt_iff`, rescaled. -/
private theorem scaledSphereGraph_lt_iff_of_pos {s t : ℝ} (hs : 0 < s) (ht : t ≤ s) {v : K}
    (hv : ‖v‖ ≤ s / 4) :
    scaledSphereGraph s v < t ↔ (s - t) ^ 2 + ‖v‖ ^ 2 < s ^ 2 := by
  rw [scaledSphereGraph, ← lt_div_iff₀' hs,
    unitSphereGraph_lt_iff (norm_inv_smul_le hs.ne' (by rwa [abs_of_pos hs]))
      ((div_le_one hs).2 ht), sub_sq_add_norm_sq_eq hs.ne', mul_lt_iff_lt_one_right (by positivity)]

/-- **The region above the rescaled sphere graph, `s < 0`.** For `‖v‖ ≤ -s / 4` and `s < t`, the
point at height `t` over `v` lies outside the closed ball of radius `-s` about the point at height
`s` exactly when it lies above the graph. This is `TauCeti.lt_unitSphereGraph_iff`, rescaled. -/
private theorem scaledSphereGraph_lt_iff_of_neg {s t : ℝ} (hs : s < 0) (ht : s < t) {v : K}
    (hv : ‖v‖ ≤ -s / 4) :
    scaledSphereGraph s v < t ↔ s ^ 2 < (s - t) ^ 2 + ‖v‖ ^ 2 := by
  rw [scaledSphereGraph, mul_comm, ← div_lt_iff_of_neg hs,
    lt_unitSphereGraph_iff (norm_inv_smul_le hs.ne (by rwa [abs_of_neg hs]))
      ((div_lt_one_of_neg hs).2 ht), sub_sq_add_norm_sq_eq hs.ne,
    lt_mul_iff_one_lt_right (by nlinarith)]

end Graph

section Chart

variable {n : ℕ}

local notation "F" => EuclideanSpace ℝ (Fin (n + 1))

/-- The tangent space of a sphere of `ℝⁿ⁺¹` at a point with unit normal `μ`, identified with
`ℝⁿ`. -/
private def orthogonalSpanEquiv (μ : F) (hμ : ‖μ‖ = 1) :
    (ℝ ∙ μ)ᗮ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
  haveI : Fact (Module.finrank ℝ F = n + 1) := ⟨finrank_euclideanSpace_fin⟩
  (OrthonormalBasis.fromOrthogonalSpanSingleton n
    (norm_ne_zero_iff.1 (by rw [hμ]; exact one_ne_zero))).repr

/-- The rigid coordinates at `x` in the direction `μ`: `x` goes to the origin and `-μ` to the
first axis, `(sphereChart x μ hμ).symm (t, w) = x - t μ + w`, with `w` read in the tangent space
`(ℝ ∙ μ)ᗮ`. -/
private def sphereChart (x μ : F) (hμ : ‖μ‖ = 1) :
    F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × EuclideanSpace ℝ (Fin n)) :=
  ((AffineIsometryEquiv.constVAdd ℝ F (μ - x)).trans (unitSphereChart μ hμ)).trans
    (LinearIsometryEquiv.withLpProdCongr 2 (LinearIsometryEquiv.refl ℝ ℝ)
      (orthogonalSpanEquiv μ hμ)).toAffineIsometryEquiv

private theorem sphereChart_symm_apply (x μ : F) (hμ : ‖μ‖ = 1)
    (z : WithLp 2 (ℝ × EuclideanSpace ℝ (Fin n))) :
    (sphereChart x μ hμ).symm z =
      x - z.fst • μ + ((orthogonalSpanEquiv μ hμ).symm z.snd : F) := by
  obtain ⟨⟨t, w⟩⟩ := z
  rw [AffineIsometryEquiv.symm_apply_eq]
  have h : (unitSphereChart μ hμ).symm (WithLp.toLp 2 (t, (orthogonalSpanEquiv μ hμ).symm w)) =
      μ - t • μ + ((orthogonalSpanEquiv μ hμ).symm w : F) := unitSphereChart_symm_apply _ _ _
  rw [AffineIsometryEquiv.symm_apply_eq] at h
  simp only [sphereChart, AffineIsometryEquiv.coe_trans, Function.comp_apply,
    AffineIsometryEquiv.coe_constVAdd, vadd_eq_add,
    LinearIsometryEquiv.coe_toAffineIsometryEquiv, WithLp.toLp_fst, WithLp.toLp_snd]
  rw [show μ - x + (x - t • μ + ((orthogonalSpanEquiv μ hμ).symm w : F)) =
    μ - t • μ + ((orthogonalSpanEquiv μ hμ).symm w : F) by abel, ← h]
  simp [LinearIsometryEquiv.withLpProdCongr]

private theorem sphereChart_self (x μ : F) (hμ : ‖μ‖ = 1) : sphereChart x μ hμ x = 0 := by
  simp [sphereChart, LinearIsometryEquiv.withLpProdCongr]

/-- In the chart at `x` in the direction `μ`, the squared distance to `x - s μ`, the point with
coordinates `(s, 0)`, is `(s - t)² + ‖w‖²`. -/
private theorem norm_sphereChart_symm_sub_sq (x μ : F) (hμ : ‖μ‖ = 1) (s : ℝ)
    (z : WithLp 2 (ℝ × EuclideanSpace ℝ (Fin n))) :
    ‖(sphereChart x μ hμ).symm z - (x - s • μ)‖ ^ 2 = (s - z.fst) ^ 2 + ‖z.snd‖ ^ 2 := by
  have h : x - s • μ = (sphereChart x μ hμ).symm (WithLp.toLp 2 (s, 0)) := by
    simp [sphereChart_symm_apply]
  rw [h, ← dist_eq_norm, AffineIsometryEquiv.dist_map, dist_eq_norm, WithLp.prod_norm_sq_eq_of_L2,
    Real.norm_eq_abs, sq_abs, WithLp.sub_fst, WithLp.sub_snd]
  simp only [WithLp.toLp_fst, WithLp.toLp_snd, sub_zero]
  ring

/-- The conclusion of `exists_affineIsometryEquiv_graph_of_mem_frontier_annulus` at a point `x`
for a set `A`. -/
private def HasGraphChart (A : Set F) (x : F) (α : ℝ≥0) : Prop :=
  ∃ (e : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × EuclideanSpace ℝ (Fin n))) (γ : EuclideanSpace ℝ (Fin n) → ℝ)
    (h₀ r₀ : ℝ) (Kγ : ℝ≥0), e x = 0 ∧ 0 < h₀ ∧ 0 < r₀ ∧ γ 0 = 0 ∧ ContDiff ℝ 1 γ ∧
      HolderWith Kγ α (fderiv ℝ γ) ∧ ∀ z ∈ normalCylinder h₀ r₀, (e.symm z ∈ A ↔ γ z.snd < z.fst)

/-- On the outer sphere the annulus lies on the side of the centre `y = x - R μ`. -/
private theorem hasGraphChart_of_mem_sphere_outer {y x : F} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hx : x ∈ sphere y R) {α : ℝ≥0} (hα : α ≤ 1) :
    HasGraphChart (ball y R ∩ (closedBall y r)ᶜ) x α := by
  have hR : 0 < R := hr.trans hrR
  have hxy : ‖x - y‖ = R := by rwa [← dist_eq_norm, ← mem_sphere]
  set μ : F := R⁻¹ • (x - y)
  have hμ : ‖μ‖ = 1 := by rw [norm_smul, hxy, norm_inv, Real.norm_of_nonneg hR.le,
    inv_mul_cancel₀ hR.ne']
  have hc : x - R • μ = y := by rw [smul_smul, mul_inv_cancel₀ hR.ne', one_smul, sub_sub_cancel]
  obtain ⟨K, hK⟩ := exists_holderWith_fderiv_scaledSphereGraph
    (K := EuclideanSpace ℝ (Fin n)) hR.ne' hα
  set h := min (R / 4) (R - r)
  have hh : 0 < h := lt_min (by positivity) (by linarith)
  refine ⟨sphereChart x μ hμ, scaledSphereGraph R, h, h, K, sphereChart_self x μ hμ, hh, hh,
    scaledSphereGraph_zero R, contDiff_scaledSphereGraph R, hK, fun z hz => ?_⟩
  obtain ⟨-, ht2, hw⟩ := mem_normalCylinder.1 hz
  have hnorm := norm_sphereChart_symm_sub_sq x μ hμ R z
  rw [hc] at hnorm
  have hRt : r < R - z.fst := by linarith [min_le_right (R / 4) (R - r)]
  rw [scaledSphereGraph_lt_iff_of_pos hR (by linarith) (hw.le.trans (min_le_left _ _)), ← hnorm,
    mem_inter_iff, mem_ball_iff_norm, mem_compl_iff, mem_closedBall_iff_norm, not_le,
    ← pow_lt_pow_iff_left₀ (norm_nonneg _) hR.le two_ne_zero]
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  rw [← pow_lt_pow_iff_left₀ hr.le (norm_nonneg _) two_ne_zero, hnorm]
  nlinarith [sq_nonneg ‖z.snd‖]

/-- On the inner sphere the annulus lies on the far side of the centre `y = x + r μ`. -/
private theorem hasGraphChart_of_mem_sphere_inner {y x : F} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hx : x ∈ sphere y r) {α : ℝ≥0} (hα : α ≤ 1) :
    HasGraphChart (ball y R ∩ (closedBall y r)ᶜ) x α := by
  have hR : 0 < R := hr.trans hrR
  have hxy : ‖x - y‖ = r := by rwa [← dist_eq_norm, ← mem_sphere]
  set μ : F := -(r⁻¹ • (x - y))
  have hμ : ‖μ‖ = 1 := by rw [norm_neg, norm_smul, hxy, norm_inv, Real.norm_of_nonneg hr.le,
    inv_mul_cancel₀ hr.ne']
  have hc : x - (-r) • μ = y := by
    rw [smul_neg, neg_smul, neg_neg, smul_smul, mul_inv_cancel₀ hr.ne', one_smul, sub_sub_cancel]
  obtain ⟨K, hK⟩ := exists_holderWith_fderiv_scaledSphereGraph
    (K := EuclideanSpace ℝ (Fin n)) (neg_ne_zero.2 hr.ne') hα
  set h := min (r / 4) ((R - r) / 2)
  have hh : 0 < h := lt_min (by positivity) (by linarith)
  refine ⟨sphereChart x μ hμ, scaledSphereGraph (-r), h, h, K, sphereChart_self x μ hμ, hh, hh,
    scaledSphereGraph_zero (-r), contDiff_scaledSphereGraph (-r), hK, fun z hz => ?_⟩
  obtain ⟨ht1, ht2, hw⟩ := mem_normalCylinder.1 hz
  have hnorm := norm_sphereChart_symm_sub_sq x μ hμ (-r) z
  rw [hc] at hnorm
  have hw' : ‖z.snd‖ ≤ -(-r) / 4 := by
    rw [neg_neg]
    exact hw.le.trans (min_le_left _ _)
  rw [scaledSphereGraph_lt_iff_of_neg (neg_lt_zero.2 hr)
      (by linarith [min_le_left (r / 4) ((R - r) / 2)]) hw', ← hnorm, neg_sq,
    mem_inter_iff, mem_ball_iff_norm, mem_compl_iff, mem_closedBall_iff_norm, not_le,
    ← pow_lt_pow_iff_left₀ hr.le (norm_nonneg _) two_ne_zero]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  rw [← pow_lt_pow_iff_left₀ (norm_nonneg _) hR.le two_ne_zero, hnorm]
  have ht3 : |z.fst| < (R - r) / 2 := abs_lt.2 ⟨by linarith [min_le_right (r / 4) ((R - r) / 2)],
    by linarith [min_le_right (r / 4) ((R - r) / 2)]⟩
  have hw3 : ‖z.snd‖ < (R - r) / 2 := hw.trans_le (min_le_right _ _)
  nlinarith [abs_nonneg z.fst, norm_nonneg z.snd, sq_abs z.fst, neg_abs_le z.fst,
    le_abs_self z.fst]

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

end Chart

end TauCeti
