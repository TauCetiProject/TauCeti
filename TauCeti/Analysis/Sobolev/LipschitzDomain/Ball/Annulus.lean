/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.Ball.SphereChart
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Smooth boundary charts of an annulus

Let `y` be a point of `ℝⁿ⁺¹ = EuclideanSpace ℝ (Fin (n + 1))` and `0 < r < R`. This file shows
that the annulus `A = ball y R ∩ (closedBall y r)ᶜ` has smooth boundary in the form that the
`C^{1,β}` estimates up to the boundary take as input
(`TauCeti.PDE.exists_holderOnWith_gradient_closure_of_isBounded` and its Morrey-datum version):
at every frontier point `x` of `A` there are rigid coordinates `e : ℝⁿ⁺¹ ≃ ℝ × ℝⁿ` with
`e x = 0` in which, inside a small cylinder, `A` is the region strictly above the graph of a
smooth compactly supported function `γ : ℝⁿ → ℝ` with `γ 0 = 0` and `α`-Hölder derivative, for
every `α ≤ 1` (`TauCeti.exists_affineIsometryEquiv_graph_of_mem_frontier_annulus`).

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

/-- Near the origin the rescaled sphere graph is `s (1 - √(1 - ‖v‖² / s²))`. -/
private theorem scaledSphereGraph_of_norm_le {s : ℝ} (hs : s ≠ 0) {v : K}
    (hv : ‖v‖ ≤ |s| / 4) :
    scaledSphereGraph s v = s * (1 - √(1 - ‖v‖ ^ 2 / s ^ 2)) := by
  have hn : ‖s⁻¹ • v‖ = ‖v‖ / |s| := by rw [norm_smul, norm_inv, Real.norm_eq_abs, inv_mul_eq_div]
  rw [scaledSphereGraph, unitSphereGraph_of_norm_le (by
    rw [hn, div_le_iff₀ (abs_pos.2 hs)]
    linarith), hn, div_pow, sq_abs]

/-- **The region above the rescaled sphere graph, `s > 0`.** For `|t|, ‖v‖ ≤ s / 4`, the point at
height `t` over `v` lies in the open ball of radius `s` about the point at height `s` exactly when
it lies above the graph. -/
private theorem sub_sq_add_norm_sq_lt_iff {s t : ℝ} (hs : 0 < s) (ht : |t| ≤ s / 4) {v : K}
    (hv : ‖v‖ ≤ s / 4) :
    (s - t) ^ 2 + ‖v‖ ^ 2 < s ^ 2 ↔ scaledSphereGraph s v < t := by
  rw [scaledSphereGraph_of_norm_le hs.ne' (by rwa [abs_of_pos hs])]
  have ha : ‖v‖ ^ 2 / s ^ 2 ≤ 1 / 16 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [norm_nonneg v]
  set q := √(1 - ‖v‖ ^ 2 / s ^ 2)
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hq2 : q ^ 2 = 1 - ‖v‖ ^ 2 / s ^ 2 := Real.sq_sqrt (by linarith)
  have hv2 : ‖v‖ ^ 2 = s ^ 2 * (1 - q ^ 2) := by
    rw [hq2]
    field_simp
    ring
  have hst : 0 < s - t := by linarith [le_abs_self t]
  have hsq : 0 ≤ s * q := mul_nonneg hs.le hq0
  rw [hv2, show (s - t) ^ 2 + s ^ 2 * (1 - q ^ 2) < s ^ 2 ↔ (s - t) ^ 2 < (s * q) ^ 2 by
    constructor <;> intro h <;> nlinarith, pow_lt_pow_iff_left₀ hst.le hsq two_ne_zero]
  constructor <;> intro h <;> nlinarith

/-- **The region above the rescaled sphere graph, `s < 0`.** For `|t|, ‖v‖ ≤ -s / 4`, the point
at height `t` over `v` lies outside the closed ball of radius `-s` about the point at height `s`
exactly when it lies above the graph. -/
private theorem sq_lt_sub_sq_add_norm_sq_iff {s t : ℝ} (hs : s < 0) (ht : |t| ≤ -s / 4) {v : K}
    (hv : ‖v‖ ≤ -s / 4) :
    s ^ 2 < (s - t) ^ 2 + ‖v‖ ^ 2 ↔ scaledSphereGraph s v < t := by
  rw [scaledSphereGraph_of_norm_le hs.ne (by rwa [abs_of_neg hs])]
  have ha : ‖v‖ ^ 2 / s ^ 2 ≤ 1 / 16 := by
    rw [div_le_iff₀ (by nlinarith)]
    nlinarith [norm_nonneg v]
  have hs0 : s ≠ 0 := hs.ne
  set q := √(1 - ‖v‖ ^ 2 / s ^ 2)
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hq2 : q ^ 2 = 1 - ‖v‖ ^ 2 / s ^ 2 := Real.sq_sqrt (by linarith)
  have hv2 : ‖v‖ ^ 2 = s ^ 2 * (1 - q ^ 2) := by
    rw [hq2]
    field_simp
    ring
  have hst : 0 < t - s := by linarith [neg_abs_le t]
  have hsq : 0 ≤ -(s * q) := by nlinarith
  rw [hv2, show s ^ 2 < (s - t) ^ 2 + s ^ 2 * (1 - q ^ 2) ↔ (-(s * q)) ^ 2 < (t - s) ^ 2 by
    constructor <;> intro h <;> nlinarith, pow_lt_pow_iff_left₀ hsq hst.le two_ne_zero]
  constructor <;> intro h <;> nlinarith

end Graph

section Chart

variable {n : ℕ}

local notation "F" => EuclideanSpace ℝ (Fin (n + 1))

/-- The tangent space of a sphere of `ℝⁿ⁺¹` at a point with unit normal `μ`, identified with
`ℝⁿ`. -/
private def orthogonalSpanEquiv (μ : F) (hμ : ‖μ‖ = 1) :
    (ℝ ∙ μ)ᗮ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
  haveI : Fact (Module.finrank ℝ F = n + 1) := ⟨finrank_euclideanSpace_fin⟩
  ((stdOrthonormalBasis ℝ (ℝ ∙ μ)ᗮ).reindex (finCongr
    (Submodule.finrank_orthogonal_span_singleton (norm_ne_zero_iff.1 (by rw [hμ]; exact
      one_ne_zero))))).repr

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
  rw [eq_comm, ← AffineIsometryEquiv.symm_apply_eq, sphereChart_symm_apply]
  simp

/-- In the chart at `x` in the direction `μ`, the squared distance to `x - s μ` is
`(s - t)² + ‖w‖²`. -/
private theorem norm_sphereChart_symm_sub_sq (x μ : F) (hμ : ‖μ‖ = 1) (s : ℝ)
    (z : WithLp 2 (ℝ × EuclideanSpace ℝ (Fin n))) :
    ‖(sphereChart x μ hμ).symm z - (x - s • μ)‖ ^ 2 = (s - z.fst) ^ 2 + ‖z.snd‖ ^ 2 := by
  set w : F := ((orthogonalSpanEquiv μ hμ).symm z.snd : F)
  have hinner : ⟪μ, w⟫_ℝ = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.1
      ((orthogonalSpanEquiv μ hμ).symm z.snd).property
  have hw : ‖w‖ = ‖z.snd‖ := by
    rw [Submodule.norm_coe, LinearIsometryEquiv.norm_map]
  have h : (sphereChart x μ hμ).symm z - (x - s • μ) = (s - z.fst) • μ + w := by
    rw [sphereChart_symm_apply, sub_smul]
    abel
  rw [h, norm_add_sq_real, norm_smul, inner_smul_left, hinner, hμ, Real.norm_eq_abs, hw]
  simp [sq_abs]

/-- The frontier of the annulus `ball y R ∩ (closedBall y r)ᶜ` lies on its two bounding spheres. -/
theorem frontier_ball_inter_compl_closedBall_subset {X : Type*} [PseudoMetricSpace X] (y : X)
    (r R : ℝ) : frontier (ball y R ∩ (closedBall y r)ᶜ) ⊆ sphere y R ∪ sphere y r :=
  (frontier_inter_subset _ _).trans (union_subset_union
    (inter_subset_left.trans frontier_ball_subset_sphere)
    (inter_subset_right.trans ((frontier_compl _).subset.trans frontier_closedBall_subset_sphere)))

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
  obtain ⟨ht1, ht2, hw⟩ := mem_normalCylinder.1 hz
  have hnorm := norm_sphereChart_symm_sub_sq x μ hμ R z
  rw [hc] at hnorm
  have ht : |z.fst| ≤ R / 4 := abs_le.2 ⟨by linarith [min_le_left (R / 4) (R - r)],
    by linarith [min_le_left (R / 4) (R - r)]⟩
  have hRt : r < R - z.fst := by linarith [min_le_right (R / 4) (R - r)]
  rw [← sub_sq_add_norm_sq_lt_iff hR ht (hw.le.trans (min_le_left _ _)), ← hnorm,
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
  have ht : |z.fst| ≤ -(-r) / 4 := by
    rw [neg_neg]
    exact abs_le.2 ⟨by linarith [min_le_left (r / 4) ((R - r) / 2)],
      by linarith [min_le_left (r / 4) ((R - r) / 2)]⟩
  have hw' : ‖z.snd‖ ≤ -(-r) / 4 := by
    rw [neg_neg]
    exact hw.le.trans (min_le_left _ _)
  rw [← sq_lt_sub_sq_add_norm_sq_iff (neg_lt_zero.2 hr) ht hw', ← hnorm, neg_sq,
    mem_inter_iff, mem_ball_iff_norm, mem_compl_iff, mem_closedBall_iff_norm, not_le,
    ← pow_lt_pow_iff_left₀ hr.le (norm_nonneg _) two_ne_zero]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  rw [← pow_lt_pow_iff_left₀ (norm_nonneg _) hR.le two_ne_zero, hnorm]
  have ht3 : |z.fst| < (R - r) / 2 := abs_lt.2 ⟨by linarith [min_le_right (r / 4) ((R - r) / 2)],
    by linarith [min_le_right (r / 4) ((R - r) / 2)]⟩
  have hw3 : ‖z.snd‖ < (R - r) / 2 := hw.trans_le (min_le_right _ _)
  nlinarith [abs_nonneg z.fst, norm_nonneg z.snd, sq_abs z.fst, neg_abs_le z.fst,
    le_abs_self z.fst]

/-- **Smooth boundary charts of an annulus.** Let `0 < r < R` and let `x` be a frontier point of
the annulus `A = ball y R ∩ (closedBall y r)ᶜ` of `ℝⁿ⁺¹`. There are rigid coordinates
`e : ℝⁿ⁺¹ ≃ ℝ × ℝⁿ` with `e x = 0` and a smooth function `γ : ℝⁿ → ℝ` with `γ 0 = 0` whose
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
