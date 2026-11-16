/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Hessian.OneDimensional
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.WarpedProd
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.WarpedProd.Vertical
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Bianchi

/-!
# Sectional curvature bounds of warped products over a curve

For a base of dimension at most one, shearing along the horizontal factor reduces every tangent
two-plane of a warped product `g_M + f² g_N` to one spanned by an arbitrary vector and a vertical
vector, where both the Gram determinant (`IsWarpedProduct.det_gram_vertical_right`) and the
curvature numerator (`IsWarpedProduct.inner_curvatureTensor_vertical_right`) split without cross
terms. Consequently, common lower bounds, upper bounds, or values on the radial Laplacian term
`-f Δf` and the fibre curvature term `R_N - |grad f|² Gram` transfer to every tangent two-plane,
yielding in particular nonnegativity when `f Δf ≤ 0` and the fibre curvature dominates
`|grad f|² det Gram`.

The curvature formulas follow B. O'Neill, *Semi-Riemannian Geometry* (1983),
Chapter 7, Proposition 42. They apply in particular to rotationally symmetric caps.
-/

public noncomputable section

open Bundle CovariantDerivative
open scoped ContDiff InnerProductSpace Manifold

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N] [T2Space N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)]
  [RiemannianBundle (fun p : M × N ↦ TangentSpace (I.prod J) p)]
  [IsContMDiffRiemannianBundle (I.prod J) ∞ (E × F)
    (fun p : M × N ↦ TangentSpace (I.prod J) p)]
  {f : M → ℝ}

/-- The curvature numerator for one arbitrary vector and one vertical vector. The
horizontal and vertical contributions have no cross term. Fibre inner products and
curvature on the right are computed in the unscaled fibre metric. -/
theorem IsWarpedProduct.inner_curvatureTensor_vertical_right
    (h : IsWarpedProduct I J N f) (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (p : M × N) (u : TangentSpace I p.1)
    (v w : TangentSpace J p.2) :
    inner ℝ ((leviCivitaConnection (I.prod J) (M × N)).curvatureTensor p
      ((tangentSpaceProdEquiv p).symm (u, v))
      ((tangentSpaceProdEquiv p).symm (0, w))
      ((tangentSpaceProdEquiv p).symm (0, w)))
      ((tangentSpaceProdEquiv p).symm (u, v)) =
    -f p.1 * hessian I f p.1 u u * ‖w‖ ^ 2 + f p.1 ^ 2 *
      (inner ℝ ((leviCivitaConnection J N).curvatureTensor p.2 v w w) v -
        ‖mgradient I f p.1‖ ^ 2 * (Matrix.gram ℝ ![v, w]).det) := by
  let e := tangentSpaceProdEquiv (I := I) (J := J) p
  let R := (leviCivitaConnection (I.prod J) (M × N)).curvatureTensor p
  have hsplit : e.symm (u, v) = e.symm (u, 0) + e.symm (0, v) := by
    rw [← map_add]
    simp
  have hcross : inner ℝ (R (e.symm (u, 0)) (e.symm (0, w)) (e.symm (0, w)))
      (e.symm (0, v)) = 0 := by
    rw [IsMetricCompatible.inner_curvatureTensor_swap_pairs
      (isMetricCompatible_leviCivitaConnection (I.prod J))
      (torsion_leviCivitaConnection_eq_zero (I.prod J))]
    rw [(isMetricCompatible_leviCivitaConnection (I.prod J)).inner_curvatureTensor_eq_neg,
      real_inner_comm, h.inner_eq, h.tangentSpaceProdEquiv_curvatureTensor_vertical hf p]
    simp only [e, ContinuousLinearEquiv.apply_symm_apply, inner_zero_left,
      inner_zero_right, mul_zero, add_zero, neg_zero]
  have hcross' : inner ℝ (R (e.symm (0, v)) (e.symm (0, w)) (e.symm (0, w)))
      (e.symm (u, 0)) = 0 := by
    rw [h.inner_eq, h.tangentSpaceProdEquiv_curvatureTensor_vertical hf p]
    simp only [e, ContinuousLinearEquiv.apply_symm_apply, inner_zero_right, mul_zero,
      add_zero, inner_zero_left]
  dsimp only [R] at hcross hcross'
  dsimp only [e] at hsplit hcross hcross'
  rw [hsplit]
  simp only [map_add, LinearMap.add_apply, inner_add_left, inner_add_right, hcross, hcross',
    add_zero, zero_add]
  rw [h.inner_curvatureTensor_horizontal_vertical_vertical_horizontal hf p,
    h.inner_eq, h.tangentSpaceProdEquiv_curvatureTensor_vertical hf p]
  simp only [ContinuousLinearEquiv.apply_symm_apply, inner_zero_left, zero_add,
    inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
    Matrix.real_det_gram_fin_two, real_inner_comm w v]
  ring

omit [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)] in
private theorem exists_sectionalCurvature_eq_vertical_right_of_finrank_le_one
    (hn : Module.finrank ℝ E ≤ 1) (p : M × N) (u v : TangentSpace (I.prod J) p) :
    ∃ (a : TangentSpace (I.prod J) p) (w : TangentSpace J p.2),
      (Matrix.gram ℝ ![a, (tangentSpaceProdEquiv p).symm (0, w)]).det =
        (Matrix.gram ℝ ![u, v]).det ∧
      (leviCivitaConnection (I.prod J) (M × N)).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection (I.prod J)) p u v =
      (leviCivitaConnection (I.prod J) (M × N)).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection (I.prod J)) p a
          ((tangentSpaceProdEquiv p).symm (0, w)) := by
  let e := tangentSpaceProdEquiv (I := I) (J := J) p
  by_cases hu : (e u).1 = 0
  · have heq : u = e.symm (0, (e u).2) := by rw [← hu]; exact (e.symm_apply_apply u).symm
    refine ⟨v, (e u).2, ?_, ?_⟩
    · rw [← heq]
      simp only [Matrix.real_det_gram_fin_two, real_inner_comm u v]
      ring
    · rw [← heq, IsMetricCompatible.sectionalCurvature_comm]
  · have hn' : Module.finrank ℝ (TangentSpace I p.1) = 1 := by
      have hpos := (Module.finrank_pos_iff_exists_ne_zero (R := ℝ)).2 ⟨(e u).1, hu⟩
      have hle := (finrank_tangentSpace (I := I) p.1).le.trans hn
      omega
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_ne_zero' (e u).1 hu).1 hn' (e v).1
    have heq : v + (-c) • u = e.symm (0, (e v).2 - c • (e u).2) := by
      apply e.injective
      simp [Prod.ext_iff, hc, sub_eq_add_neg]
    refine ⟨u, (e v).2 - c • (e u).2, ?_, ?_⟩
    · rw [← heq]
      simp only [Matrix.real_det_gram_fin_two, inner_add_left, inner_add_right,
        real_inner_smul_left, real_inner_smul_right, real_inner_comm v u]
      ring
    · rw [← heq, sectionalCurvature_add_smul_right]

/-- Over a base of dimension at most one, common lower bounds `κ f² ≤ -f Δf` on the radial term and
`(κ f² + |grad f|²) det(Gram(v, w)) ≤ ⟪R_N(v, w)w, v⟫` on the fibre curvature bound the sectional
curvature of every tangent two-plane of the warped product from below by `κ`. -/
theorem IsWarpedProduct.le_sectionalCurvature_of_finrank_le_one
    (h : IsWarpedProduct I J N f) (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hn : Module.finrank ℝ E ≤ 1) (p : M × N) {κ : ℝ}
    (hlap : κ * f p.1 ^ 2 ≤ -f p.1 * laplaceBeltrami I f p.1)
    (hfibre : ∀ v w : TangentSpace J p.2,
      (κ * f p.1 ^ 2 + ‖mgradient I f p.1‖ ^ 2) * (Matrix.gram ℝ ![v, w]).det ≤
        inner ℝ ((leviCivitaConnection J N).curvatureTensor p.2 v w w) v)
    {u v : TangentSpace (I.prod J) p} (huv : LinearIndependent ℝ ![u, v]) :
    κ ≤ (leviCivitaConnection (I.prod J) (M × N)).sectionalCurvature
      (isMetricCompatible_leviCivitaConnection (I.prod J)) p u v := by
  obtain ⟨a, w, hdet, hsec⟩ :=
    exists_sectionalCurvature_eq_vertical_right_of_finrank_le_one hn p u v
  let e := tangentSpaceProdEquiv (I := I) (J := J) p
  have ha : e.symm ((e a).1, (e a).2) = a := e.symm_apply_apply a
  have hpos : 0 < (Matrix.gram ℝ ![a, e.symm (0, w)]).det := by
    rw [hdet]; exact (Matrix.posDef_gram_of_linearIndependent huv).det_pos
  have hnum := h.inner_curvatureTensor_vertical_right hf p (e a).1 (e a).2 w
  have hgram := h.det_gram_vertical_right p (e a).1 (e a).2 w
  rw [ha] at hnum hgram
  rw [hsec, sectionalCurvature_apply, le_div_iff₀ hpos, hnum, hgram,
    hessian_eq_laplaceBeltrami_mul_inner_of_finrank_le_one hn, real_inner_self_eq_norm_sq]
  nlinarith [mul_le_mul_of_nonneg_right hlap (mul_nonneg (sq_nonneg ‖(e a).1‖) (sq_nonneg ‖w‖)),
    mul_le_mul_of_nonneg_left (hfibre (e a).2 w) (sq_nonneg (f p.1))]

/-- Over a base of dimension at most one, common upper bounds `-f Δf ≤ κ f²` on the radial term and
`⟪R_N(v, w)w, v⟫ ≤ (κ f² + |grad f|²) det(Gram(v, w))` on the fibre curvature bound the sectional
curvature of every tangent two-plane of the warped product from above by `κ`. -/
theorem IsWarpedProduct.sectionalCurvature_le_of_finrank_le_one
    (h : IsWarpedProduct I J N f) (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hn : Module.finrank ℝ E ≤ 1) (p : M × N) {κ : ℝ}
    (hlap : -f p.1 * laplaceBeltrami I f p.1 ≤ κ * f p.1 ^ 2)
    (hfibre : ∀ v w : TangentSpace J p.2,
      inner ℝ ((leviCivitaConnection J N).curvatureTensor p.2 v w w) v ≤
        (κ * f p.1 ^ 2 + ‖mgradient I f p.1‖ ^ 2) * (Matrix.gram ℝ ![v, w]).det)
    {u v : TangentSpace (I.prod J) p} (huv : LinearIndependent ℝ ![u, v]) :
    (leviCivitaConnection (I.prod J) (M × N)).sectionalCurvature
      (isMetricCompatible_leviCivitaConnection (I.prod J)) p u v ≤ κ := by
  obtain ⟨a, w, hdet, hsec⟩ :=
    exists_sectionalCurvature_eq_vertical_right_of_finrank_le_one hn p u v
  let e := tangentSpaceProdEquiv (I := I) (J := J) p
  have ha : e.symm ((e a).1, (e a).2) = a := e.symm_apply_apply a
  have hpos : 0 < (Matrix.gram ℝ ![a, e.symm (0, w)]).det := by
    rw [hdet]; exact (Matrix.posDef_gram_of_linearIndependent huv).det_pos
  have hnum := h.inner_curvatureTensor_vertical_right hf p (e a).1 (e a).2 w
  have hgram := h.det_gram_vertical_right p (e a).1 (e a).2 w
  rw [ha] at hnum hgram
  rw [hsec, sectionalCurvature_apply, div_le_iff₀ hpos, hnum, hgram,
    hessian_eq_laplaceBeltrami_mul_inner_of_finrank_le_one hn, real_inner_self_eq_norm_sq]
  nlinarith [mul_le_mul_of_nonneg_right hlap (mul_nonneg (sq_nonneg ‖(e a).1‖) (sq_nonneg ‖w‖)),
    mul_le_mul_of_nonneg_left (hfibre (e a).2 w) (sq_nonneg (f p.1))]

/-- Over a base of dimension at most one, when `-f Δf = κ f²` and
`⟪R_N(v, w)w, v⟫ = (κ f² + |grad f|²) det(Gram(v, w))` at `p`, every tangent two-plane of the warped
product at `p` has sectional curvature `κ`. -/
theorem IsWarpedProduct.hasSectionalCurvatureAt_of_finrank_le_one
    (h : IsWarpedProduct I J N f) (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hn : Module.finrank ℝ E ≤ 1) (p : M × N) {κ : ℝ}
    (hlap : -f p.1 * laplaceBeltrami I f p.1 = κ * f p.1 ^ 2)
    (hfibre : ∀ v w : TangentSpace J p.2,
      inner ℝ ((leviCivitaConnection J N).curvatureTensor p.2 v w w) v =
        (κ * f p.1 ^ 2 + ‖mgradient I f p.1‖ ^ 2) * (Matrix.gram ℝ ![v, w]).det) :
    (leviCivitaConnection (I.prod J) (M × N)).HasSectionalCurvatureAt
      (isMetricCompatible_leviCivitaConnection (I.prod J)) p κ :=
  ((leviCivitaConnection (I.prod J) (M × N)).hasSectionalCurvatureAt_iff _ p κ).2 fun _ _ huv ↦
    le_antisymm
      (h.sectionalCurvature_le_of_finrank_le_one hf hn p hlap.le (fun v w ↦ (hfibre v w).le) huv)
      (h.le_sectionalCurvature_of_finrank_le_one hf hn p hlap.ge (fun v w ↦ (hfibre v w).ge) huv)

/-- Over a base of dimension at most one, a warping function whose product with its
Laplacian is nonpositive and fibre curvature numerator at least `|grad f|² det Gram` gives
nonnegative sectional curvature on every plane of the warped product. The bound
on the fibre includes dependent pairs and requires no choice of orthonormal basis. -/
theorem IsWarpedProduct.sectionalCurvature_nonneg_of_finrank_le_one
    (h : IsWarpedProduct I J N f) (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hn : Module.finrank ℝ E ≤ 1) (p : M × N)
    (hlap : f p.1 * laplaceBeltrami I f p.1 ≤ 0)
    (hfibre : ∀ v w : TangentSpace J p.2,
      ‖mgradient I f p.1‖ ^ 2 * (Matrix.gram ℝ ![v, w]).det ≤
        inner ℝ ((leviCivitaConnection J N).curvatureTensor p.2 v w w) v)
    (u v : TangentSpace (I.prod J) p) :
    0 ≤ (leviCivitaConnection (I.prod J) (M × N)).sectionalCurvature
      (isMetricCompatible_leviCivitaConnection (I.prod J)) p u v := by
  by_cases huv : LinearIndependent ℝ ![u, v]
  · refine h.le_sectionalCurvature_of_finrank_le_one hf hn p (by linarith) (fun a b ↦ ?_) huv
    simpa using hfibre a b
  · rw [sectionalCurvature_apply,
      not_not.mp (Matrix.det_gram_ne_zero_iff_linearIndependent.not.mpr huv), div_zero]

end TauCeti.Manifold
