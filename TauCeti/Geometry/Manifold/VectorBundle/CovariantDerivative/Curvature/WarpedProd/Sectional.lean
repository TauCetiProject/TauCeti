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
# Sectional curvature bounds for warped products over a curve

For a base of dimension at most one, every tangent plane of the warped metric `g_M + f² g_N`
contains a vertical vector. Its curvature numerator then splits into a radial term
`-f Δf |u|² |w|²` and a vertical term `f² (⟪R_N(v, w) w, v⟫ - |grad f|² det Gram(v, w))`, while its
Gram determinant splits as `f² |u|² |w|² + f⁴ det Gram(v, w)`. Hence a common bound `k` for
`-Δf / f` and for the vertical correction `(K_N - |grad f|²) / f²` bounds the sectional curvature
of every plane by `k`, from either side. When both equal `k` the warped product has sectional
curvature `k` at the point; for the round fibre this covers the profiles `sin (√k r) / √k` of
round spheres. With `k = 0`, the lower bound gives nonnegative sectional curvature.

All statements use the native Levi-Civita connection. The nonnegativity criterion includes
dependent pairs, whose totalized sectional curvature is zero.

## Main results

* `TauCeti.Manifold.exists_sectionalCurvature_eq_vertical_right_of_finrank_le_one`: over a base
  of dimension at most one, every plane is spanned by a pair whose second vector is vertical.
* `TauCeti.Manifold.IsWarpedProduct.sectionalCurvature_vertical_right_of_finrank_le_one`: the
  sectional curvature of such a pair, in terms of the warping function and the fibre.
* `TauCeti.Manifold.IsWarpedProduct.le_sectionalCurvature_of_finrank_le_one` and
  `TauCeti.Manifold.IsWarpedProduct.sectionalCurvature_le_of_finrank_le_one`: lower and upper
  sectional curvature bounds.
* `TauCeti.Manifold.IsWarpedProduct.hasSectionalCurvatureAt_of_finrank_le_one`: prescribed
  sectional curvature at a point.
* `TauCeti.Manifold.IsWarpedProduct.sectionalCurvature_nonneg_of_finrank_le_one`: nonnegative
  sectional curvature.

## References

* B. O'Neill, *Semi-Riemannian Geometry* (1983), Chapter 7, Proposition 42.
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

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] [FiniteDimensional ℝ F]
  [IsManifold J ∞ N] [T2Space N] [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle (I.prod J) ∞ (E × F)
    (fun p : M × N ↦ TangentSpace (I.prod J) p)] in
/-- The Gram determinant of an arbitrary vector and a vertical vector of the warped metric.
Fibre norms and the Gram determinant on the right use the unscaled fibre metric. -/
theorem IsWarpedProduct.det_gram_vertical_right (h : IsWarpedProduct I J N f) (p : M × N)
    (u : TangentSpace I p.1) (v w : TangentSpace J p.2) :
    (Matrix.gram ℝ ![(tangentSpaceProdEquiv p).symm (u, v),
      (tangentSpaceProdEquiv p).symm (0, w)]).det =
      f p.1 ^ 2 * ‖u‖ ^ 2 * ‖w‖ ^ 2 + f p.1 ^ 4 * (Matrix.gram ℝ ![v, w]).det := by
  simp only [Matrix.real_det_gram_fin_two, h.inner_eq, ContinuousLinearEquiv.apply_symm_apply,
    inner_zero_right, zero_add, real_inner_self_eq_norm_sq]
  ring

omit [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)] in
/-- Over a base of dimension at most one, every pair of tangent vectors of `M × N` can be
replaced by a pair whose second vector is vertical, without changing the sectional curvature or
the Gram determinant. This holds for every metric on `M × N`. -/
theorem exists_sectionalCurvature_eq_vertical_right_of_finrank_le_one
    (hn : Module.finrank ℝ E ≤ 1) (p : M × N) (u v : TangentSpace (I.prod J) p) :
    ∃ (a : TangentSpace (I.prod J) p) (w : TangentSpace J p.2),
      (leviCivitaConnection (I.prod J) (M × N)).sectionalCurvature
          (isMetricCompatible_leviCivitaConnection (I.prod J)) p u v =
        (leviCivitaConnection (I.prod J) (M × N)).sectionalCurvature
          (isMetricCompatible_leviCivitaConnection (I.prod J)) p a
          ((tangentSpaceProdEquiv p).symm (0, w)) ∧
      (Matrix.gram ℝ ![u, v]).det =
        (Matrix.gram ℝ ![a, (tangentSpaceProdEquiv p).symm (0, w)]).det := by
  let e := tangentSpaceProdEquiv (I := I) (J := J) p
  by_cases hu : (e u).1 = 0
  · -- The first vector is vertical: exchange the two vectors.
    have heq : e.symm (0, (e u).2) = u := by rw [← hu]; exact e.symm_apply_apply u
    refine ⟨v, (e u).2, ?_, ?_⟩
    · rw [heq, IsMetricCompatible.sectionalCurvature_comm]
    · rw [heq, Matrix.real_det_gram_fin_two, Matrix.real_det_gram_fin_two, real_inner_comm u v]
      ring
  · -- The horizontal parts are proportional: subtract a multiple of the first vector.
    have hn' : Module.finrank ℝ (TangentSpace I p.1) = 1 := by
      have hpos := (Module.finrank_pos_iff_exists_ne_zero (R := ℝ)).2 ⟨(e u).1, hu⟩
      have hle := (finrank_tangentSpace (I := I) p.1).le.trans hn
      omega
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_ne_zero' (e u).1 hu).1 hn' (e v).1
    have heq : e.symm (0, (e v).2 - c • (e u).2) = v + (-c) • u := by
      apply e.injective
      simp [Prod.ext_iff, hc, sub_eq_add_neg]
    refine ⟨u, (e v).2 - c • (e u).2, ?_, ?_⟩
    · rw [heq, sectionalCurvature_add_smul_right]
    · rw [heq, Matrix.real_det_gram_fin_two, Matrix.real_det_gram_fin_two]
      simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
        real_inner_comm u v]
      ring

/-- Over a base of dimension at most one, the sectional curvature of an arbitrary vector and a
vertical vector of the warped metric, as the quotient of the radial and vertical numerator terms
by the split Gram determinant. Fibre quantities on the right use the unscaled fibre metric. -/
theorem IsWarpedProduct.sectionalCurvature_vertical_right_of_finrank_le_one
    (h : IsWarpedProduct I J N f) (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hn : Module.finrank ℝ E ≤ 1) (p : M × N) (u : TangentSpace I p.1)
    (v w : TangentSpace J p.2) :
    (leviCivitaConnection (I.prod J) (M × N)).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection (I.prod J)) p
        ((tangentSpaceProdEquiv p).symm (u, v)) ((tangentSpaceProdEquiv p).symm (0, w)) =
      (-f p.1 * laplaceBeltrami I f p.1 * ‖u‖ ^ 2 * ‖w‖ ^ 2 + f p.1 ^ 2 *
          (inner ℝ ((leviCivitaConnection J N).curvatureTensor p.2 v w w) v -
            ‖mgradient I f p.1‖ ^ 2 * (Matrix.gram ℝ ![v, w]).det)) /
        (f p.1 ^ 2 * ‖u‖ ^ 2 * ‖w‖ ^ 2 + f p.1 ^ 4 * (Matrix.gram ℝ ![v, w]).det) := by
  rw [sectionalCurvature_apply, h.det_gram_vertical_right,
    h.inner_curvatureTensor_vertical_right hf,
    hessian_eq_laplaceBeltrami_mul_inner_of_finrank_le_one hn, real_inner_self_eq_norm_sq]
  ring

/-- Over a base of dimension at most one, sectional curvature is at least `k` on every plane
when `-f Δf ≥ k f²` and the fibre curvature numerator is at least
`(|grad f|² + k f²) det Gram` at the point. The fibre condition is stated in the unscaled fibre
metric and includes dependent pairs. -/
theorem IsWarpedProduct.le_sectionalCurvature_of_finrank_le_one
    (h : IsWarpedProduct I J N f) (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hn : Module.finrank ℝ E ≤ 1) (p : M × N) {k : ℝ}
    (hlap : f p.1 * laplaceBeltrami I f p.1 ≤ -(k * f p.1 ^ 2))
    (hfibre : ∀ v w : TangentSpace J p.2,
      (‖mgradient I f p.1‖ ^ 2 + k * f p.1 ^ 2) * (Matrix.gram ℝ ![v, w]).det ≤
        inner ℝ ((leviCivitaConnection J N).curvatureTensor p.2 v w w) v)
    {u v : TangentSpace (I.prod J) p} (huv : LinearIndependent ℝ ![u, v]) :
    k ≤ (leviCivitaConnection (I.prod J) (M × N)).sectionalCurvature
      (isMetricCompatible_leviCivitaConnection (I.prod J)) p u v := by
  obtain ⟨a, w, hK, hdet⟩ := exists_sectionalCurvature_eq_vertical_right_of_finrank_le_one hn p u v
  have hpos := hdet ▸ (Matrix.posDef_gram_of_linearIndependent huv).det_pos
  obtain ⟨⟨x, y⟩, rfl⟩ := (tangentSpaceProdEquiv p).symm.surjective a
  rw [h.det_gram_vertical_right] at hpos
  rw [hK, h.sectionalCurvature_vertical_right_of_finrank_le_one hf hn, le_div_iff₀ hpos]
  have h₁ := mul_le_mul_of_nonneg_right hlap (by positivity : (0 : ℝ) ≤ ‖x‖ ^ 2 * ‖w‖ ^ 2)
  have h₂ := mul_le_mul_of_nonneg_left (hfibre y w) (sq_nonneg (f p.1))
  linear_combination h₁ + h₂

/-- Over a base of dimension at most one, sectional curvature is at most `k` on every plane
when `-f Δf ≤ k f²` and the fibre curvature numerator is at most
`(|grad f|² + k f²) det Gram` at the point. The fibre condition is stated in the unscaled fibre
metric and includes dependent pairs. -/
theorem IsWarpedProduct.sectionalCurvature_le_of_finrank_le_one
    (h : IsWarpedProduct I J N f) (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hn : Module.finrank ℝ E ≤ 1) (p : M × N) {k : ℝ}
    (hlap : -(k * f p.1 ^ 2) ≤ f p.1 * laplaceBeltrami I f p.1)
    (hfibre : ∀ v w : TangentSpace J p.2,
      inner ℝ ((leviCivitaConnection J N).curvatureTensor p.2 v w w) v ≤
        (‖mgradient I f p.1‖ ^ 2 + k * f p.1 ^ 2) * (Matrix.gram ℝ ![v, w]).det)
    {u v : TangentSpace (I.prod J) p} (huv : LinearIndependent ℝ ![u, v]) :
    (leviCivitaConnection (I.prod J) (M × N)).sectionalCurvature
      (isMetricCompatible_leviCivitaConnection (I.prod J)) p u v ≤ k := by
  obtain ⟨a, w, hK, hdet⟩ := exists_sectionalCurvature_eq_vertical_right_of_finrank_le_one hn p u v
  have hpos := hdet ▸ (Matrix.posDef_gram_of_linearIndependent huv).det_pos
  obtain ⟨⟨x, y⟩, rfl⟩ := (tangentSpaceProdEquiv p).symm.surjective a
  rw [h.det_gram_vertical_right] at hpos
  rw [hK, h.sectionalCurvature_vertical_right_of_finrank_le_one hf hn, div_le_iff₀ hpos]
  have h₁ := mul_le_mul_of_nonneg_right hlap (by positivity : (0 : ℝ) ≤ ‖x‖ ^ 2 * ‖w‖ ^ 2)
  have h₂ := mul_le_mul_of_nonneg_left (hfibre y w) (sq_nonneg (f p.1))
  linear_combination h₁ + h₂

/-- Over a base of dimension at most one, the warped product has sectional curvature `k` at `p`
when `-f Δf = k f²` and the fibre curvature numerator is `(|grad f|² + k f²) det Gram` at the
point. For a fibre of constant curvature `κ`, the second condition says
`κ - |grad f|² = k f²`. -/
theorem IsWarpedProduct.hasSectionalCurvatureAt_of_finrank_le_one
    (h : IsWarpedProduct I J N f) (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hn : Module.finrank ℝ E ≤ 1) (p : M × N) {k : ℝ}
    (hlap : f p.1 * laplaceBeltrami I f p.1 = -(k * f p.1 ^ 2))
    (hfibre : ∀ v w : TangentSpace J p.2,
      inner ℝ ((leviCivitaConnection J N).curvatureTensor p.2 v w w) v =
        (‖mgradient I f p.1‖ ^ 2 + k * f p.1 ^ 2) * (Matrix.gram ℝ ![v, w]).det) :
    (leviCivitaConnection (I.prod J) (M × N)).HasSectionalCurvatureAt
      (isMetricCompatible_leviCivitaConnection (I.prod J)) p k :=
  (hasSectionalCurvatureAt_iff _ _ p k).2 fun _ _ huv ↦ le_antisymm
    (h.sectionalCurvature_le_of_finrank_le_one hf hn p hlap.ge (fun v w ↦ (hfibre v w).le) huv)
    (h.le_sectionalCurvature_of_finrank_le_one hf hn p hlap.le (fun v w ↦ (hfibre v w).ge) huv)

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
  · exact h.le_sectionalCurvature_of_finrank_le_one hf hn p (by simpa using hlap)
      (fun v w ↦ by simpa using hfibre v w) huv
  · -- A dependent pair has zero Gram determinant, so its totalized quotient is zero.
    rw [sectionalCurvature_apply, not_not.mp
      (Matrix.det_gram_ne_zero_iff_linearIndependent.not.mpr huv), div_zero]

end TauCeti.Manifold
