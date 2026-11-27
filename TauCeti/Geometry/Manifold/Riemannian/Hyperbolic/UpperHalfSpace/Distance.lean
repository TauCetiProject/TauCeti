/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Riemannian.HalfSpace
public import TauCeti.Geometry.Manifold.Riemannian.Distance
public import TauCeti.Geometry.Manifold.Riemannian.Hyperbolic.Completeness
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The hyperbolic distance on the upper half-space model

This file equips the upper half-space model `UpperHalfSpace E` with the distance of its
hyperbolic metric `(‖dx‖² + dt²) / t²`, as a `MetricSpace` instance, and computes it in closed
form: for `p = (x, s)` and `q = (y, t)`,

`cosh (dist p q) = 1 + ‖p - q‖² / (2 s t)`,

where `‖p - q‖` is the Euclidean distance in `E × ℝ`. This is the formula of
`UpperHalfPlane.cosh_dist` in every dimension, and the basic tool for computing with the
hyperbolic distance, for instance for Dirichlet domains.

## Main definitions

* `TauCeti.UpperHalfSpace.instMetricSpace`: the hyperbolic distance on `UpperHalfSpace E`, the
  metric space structure `TauCeti.MetricSpace.ofRiemannianMetric` of its Riemannian metric.

## Main results

* `TauCeti.UpperHalfSpace.instCompleteSpace`: in finite dimension the distance is complete.
* `TauCeti.UpperHalfSpace.lipschitzWith_one_of_coe_comp_eq`: a map between upper half-spaces
  that is the restriction of a `C¹`, `1`-Lipschitz map of the ambient Euclidean spaces and does
  not decrease height is `1`-Lipschitz for the hyperbolic distances.
* `TauCeti.UpperHalfSpace.dist_eq`: `dist p q = 2 arsinh (‖p - q‖ / (2 √(s t)))`.
* `TauCeti.UpperHalfSpace.cosh_dist`: `cosh (dist p q) = 1 + ‖p - q‖² / (2 s t)`.
* `TauCeti.UpperHalfSpace.dist_of_fst_eq`: on a vertical line, `dist p q = |log t - log s|`.

## Implementation notes

The computation reduces to the upper half-plane. Write `a = x` and let `e` be the unit vector in
the direction of `y - x` (or `e = 0` if `y = x`). The maps
`(u, r) ↦ (a + u e, r)` from `UpperHalfSpace ℝ` to `UpperHalfSpace E` and
`(z, r) ↦ (⟪z - a, e⟫, √(‖z - a - ⟪z - a, e⟫ e‖² + r²))` back are both restrictions of
`1`-Lipschitz maps of the ambient Euclidean spaces that do not decrease height, so they do not
increase hyperbolic distance (`TauCeti.UpperHalfSpace.lipschitzWith_one_of_coe_comp_eq`).
Their composite fixes `p` and `q`, so the hyperbolic distance from `p` to `q` is that of their
images in the two-dimensional model, which is Mathlib's distance on `ℍ`.

## References

* J. G. Ratcliffe, *Foundations of Hyperbolic Manifolds*, 3rd ed., Springer GTM 149 (2019),
  §4.6 (the distance formula in the upper half-space model).
-/

public section

open Bundle Manifold Real
open scoped ContDiff Manifold NNReal ENNReal RealInnerProductSpace

noncomputable section

namespace TauCeti.UpperHalfSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The hyperbolic distance on the upper half-space model: the distance of the Riemannian metric
`(‖dx‖² + dt²) / t²`, the infimum of the hyperbolic lengths of `C¹` paths. Its topology is the
topology of `UpperHalfSpace E` as an open subset of `E × ℝ`. -/
instance instMetricSpace : MetricSpace (UpperHalfSpace E) :=
  MetricSpace.ofRiemannianMetric 𝓘(ℝ, WithLp 2 (E × ℝ)) (UpperHalfSpace E)

/-- In finite dimension the hyperbolic distance on the upper half-space model is complete. -/
instance instCompleteSpace [FiniteDimensional ℝ E] : CompleteSpace (UpperHalfSpace E) :=
  completeSpace_of_riemannianMetric

/-- A map between upper half-spaces that is the restriction of a `C¹` map `A` of the ambient
Euclidean spaces is `1`-Lipschitz for the hyperbolic distances when `A` is `1`-Lipschitz for the
Euclidean distances and the map does not decrease height. -/
theorem lipschitzWith_one_of_coe_comp_eq {f : UpperHalfSpace E → UpperHalfSpace F}
    {A : WithLp 2 (E × ℝ) → WithLp 2 (F × ℝ)} (hcomp : coe ∘ f = A ∘ coe)
    (hA : ∀ x : UpperHalfSpace E, ContDiffAt ℝ 1 A x) (hlip : LipschitzWith 1 A)
    (hheight : ∀ x, height x ≤ height (f x)) : LipschitzWith 1 f := by
  have hf : ContMDiff 𝓘(ℝ, WithLp 2 (E × ℝ)) 𝓘(ℝ, WithLp 2 (F × ℝ)) 1 f := by
    rw [← contMDiff_coe_comp_iff, hcomp]
    exact fun x ↦ (hA x).contMDiffAt.comp x ((contMDiff_coe x).of_le (by simp))
  have hbound : ∀ x (v : TangentSpace 𝓘(ℝ, WithLp 2 (E × ℝ)) x),
      ‖mfderiv 𝓘(ℝ, WithLp 2 (E × ℝ)) 𝓘(ℝ, WithLp 2 (F × ℝ)) f x v‖ ≤
        ((1 : ℝ≥0) : ℝ) * ‖v‖ := by
    intro x v
    rw [norm_def, norm_def,
      tangentSpaceCastModel_mfderiv_apply ((hA x).differentiableAt one_ne_zero).hasFDerivAt hcomp,
      NNReal.coe_one, one_mul]
    have hL := (fderiv ℝ A (x : WithLp 2 (E × ℝ))).le_of_opNorm_le
      (norm_fderiv_le_of_lipschitz ℝ hlip) (tangentSpaceCastModel 𝓘(ℝ, WithLp 2 (E × ℝ)) x v)
    rw [NNReal.coe_one, one_mul] at hL
    calc _ ≤ ‖tangentSpaceCastModel 𝓘(ℝ, WithLp 2 (E × ℝ)) x v‖ / height (f x) := by
          gcongr
          exact (height_pos (f x)).le
      _ ≤ _ := div_le_div_of_nonneg_left (norm_nonneg _) (height_pos x) (hheight x)
  refine LipschitzWith.of_edist_le fun x y ↦ ?_
  rw [IsRiemannianManifold.out (I := 𝓘(ℝ, WithLp 2 (F × ℝ))),
    IsRiemannianManifold.out (I := 𝓘(ℝ, WithLp 2 (E × ℝ)))]
  simpa using TauCeti.Manifold.riemannianEDist_le_mul hf one_ne_zero hbound x y

/-- The distance formula in the two-dimensional model, transported from Mathlib's
`UpperHalfPlane.dist_eq` along `TauCeti.UpperHalfPlane.upperHalfSpaceIsometry`. -/
private theorem dist_eq_of_real (p q : UpperHalfSpace ℝ) :
    dist p q = 2 * arsinh (dist (p : WithLp 2 (ℝ × ℝ)) q / (2 * √(height p * height q))) := by
  have hc (r : UpperHalfSpace ℝ) :
      ((TauCeti.UpperHalfPlane.upperHalfSpaceIsometry.symm r : UpperHalfPlane) : ℂ) =
        Complex.equivRealProdLp.symm r := by
    rw [TauCeti.UpperHalfPlane.coe_upperHalfSpaceIsometry_symm_apply,
      Complex.equivRealProdLp_symm_apply, snd_coe]
  rw [dist_edist p q, IsRiemannianManifold.out (I := 𝓘(ℝ, WithLp 2 (ℝ × ℝ))),
    TauCeti.UpperHalfPlane.riemannianEDist_eq_edist_upperHalfSpaceIsometry_symm, ← dist_edist,
    UpperHalfPlane.dist_eq, hc, hc,
    LinearIsometryEquiv.dist_map, TauCeti.UpperHalfPlane.im_upperHalfSpaceIsometry_symm_apply,
    TauCeti.UpperHalfPlane.im_upperHalfSpaceIsometry_symm_apply]

/-! ### Comparison maps with the two-dimensional model -/

/-- The ambient map `(u, r) ↦ (a + u e, r)` from `ℝ × ℝ` to `E × ℝ`. -/
private def inclAmbient (a e : E) (y : WithLp 2 (ℝ × ℝ)) : WithLp 2 (E × ℝ) :=
  WithLp.toLp 2 (a + y.fst • e, y.snd)

private theorem contDiff_inclAmbient (a e : E) : ContDiff ℝ 1 (inclAmbient a e) :=
  WithLp.contDiff_toLp.comp <|
    (contDiff_const.add ((WithLp.fstL 2 ℝ ℝ ℝ).contDiff.smul contDiff_const)).prodMk
      (WithLp.sndL 2 ℝ ℝ ℝ).contDiff

private theorem lipschitzWith_inclAmbient (a : E) {e : E} (he : ‖e‖ ≤ 1) :
    LipschitzWith 1 (inclAmbient a e) := by
  refine LipschitzWith.of_dist_le_mul fun y y' ↦ ?_
  rw [NNReal.coe_one, one_mul, WithLp.prod_dist_eq_of_L2 (inclAmbient a e y),
    WithLp.prod_dist_eq_of_L2 y]
  gcongr
  · simpa [inclAmbient, dist_eq_norm, ← sub_smul, norm_smul] using
      mul_le_of_le_one_right (abs_nonneg (y.fst - y'.fst)) he
  · simp [inclAmbient]

/-- The ambient map `(z, r) ↦ (z - a - ⟪z - a, e⟫ e, r)`, whose norm is the second coordinate of
the projection to the two-dimensional model. -/
private def orthAmbient (a e : E) (y : WithLp 2 (E × ℝ)) : WithLp 2 (E × ℝ) :=
  WithLp.toLp 2 (y.fst - a - ⟪y.fst - a, e⟫ • e, y.snd)

/-- The ambient map `(z, r) ↦ (⟪z - a, e⟫, √(‖z - a - ⟪z - a, e⟫ e‖² + r²))` from `E × ℝ` to
`ℝ × ℝ`. -/
private def projAmbient (a e : E) (y : WithLp 2 (E × ℝ)) : WithLp 2 (ℝ × ℝ) :=
  WithLp.toLp 2 (⟪y.fst - a, e⟫, ‖orthAmbient a e y‖)

private theorem abs_snd_le_norm_orthAmbient (a e : E) (y : WithLp 2 (E × ℝ)) :
    |y.snd| ≤ ‖orthAmbient a e y‖ := by
  rw [WithLp.prod_norm_eq_of_L2, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (by simp [orthAmbient])

private theorem contDiff_orthAmbient (a e : E) : ContDiff ℝ ∞ (orthAmbient a e) := by
  have h₁ : ContDiff ℝ ∞ fun y : WithLp 2 (E × ℝ) ↦ y.fst - a :=
    (WithLp.fstL 2 ℝ E ℝ).contDiff.sub contDiff_const
  exact WithLp.contDiff_toLp.comp <|
    (h₁.sub ((h₁.inner ℝ contDiff_const).smul contDiff_const)).prodMk
      (WithLp.sndL 2 ℝ E ℝ).contDiff

private theorem contDiffAt_projAmbient (a e : E) {y : WithLp 2 (E × ℝ)} (hy : 0 < y.snd) :
    ContDiffAt ℝ 1 (projAmbient a e) y := by
  have hne : orthAmbient a e y ≠ 0 := by
    intro h
    have := abs_snd_le_norm_orthAmbient a e y
    rw [h, norm_zero, abs_nonpos_iff] at this
    exact hy.ne' this
  exact WithLp.contDiff_toLp.contDiffAt.comp y <|
    ((((WithLp.fstL 2 ℝ E ℝ).contDiff.sub contDiff_const).inner ℝ
      contDiff_const).contDiffAt).prodMk
      ((contDiffAt_norm ℝ hne).comp y ((contDiff_orthAmbient a e).contDiffAt.of_le (by simp)))

/-- For `‖e‖ ≤ 1`, the component `⟪d, e⟫` of `d` along `e` and the remainder `d - ⟪d, e⟫ e`
together have length at most `‖d‖`. -/
private theorem inner_sq_add_norm_sub_sq_le (d : E) {e : E} (he : ‖e‖ ≤ 1) :
    ⟪d, e⟫ ^ 2 + ‖d - ⟪d, e⟫ • e‖ ^ 2 ≤ ‖d‖ ^ 2 := by
  rw [norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have : ‖e‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg e) he
  nlinarith [mul_le_mul_of_nonneg_left this (sq_nonneg ⟪d, e⟫)]

private theorem lipschitzWith_projAmbient (a : E) {e : E} (he : ‖e‖ ≤ 1) :
    LipschitzWith 1 (projAmbient a e) := by
  refine LipschitzWith.of_dist_le_mul fun y y' ↦ ?_
  rw [NNReal.coe_one, one_mul, WithLp.prod_dist_eq_of_L2 (projAmbient a e y),
    WithLp.prod_dist_eq_of_L2 y]
  refine Real.sqrt_le_sqrt ?_
  have h₁ : dist (projAmbient a e y).fst (projAmbient a e y').fst =
      |⟪y.fst - y'.fst, e⟫| := by
    simp [projAmbient, Real.dist_eq, ← inner_sub_left]
  have h₂ : dist (projAmbient a e y).snd (projAmbient a e y').snd ≤
      ‖orthAmbient a e y - orthAmbient a e y'‖ := by
    simpa [projAmbient, Real.dist_eq] using abs_norm_sub_norm_le _ _
  have h₃ : ‖orthAmbient a e y - orthAmbient a e y'‖ ^ 2 =
      ‖y.fst - y'.fst - ⟪y.fst - y'.fst, e⟫ • e‖ ^ 2 + dist y.snd y'.snd ^ 2 := by
    rw [WithLp.prod_norm_sq_eq_of_L2]
    simp only [orthAmbient, WithLp.sub_fst, WithLp.sub_snd, WithLp.toLp_fst, WithLp.toLp_snd,
      Real.dist_eq, Real.norm_eq_abs, sq_abs, inner_sub_left, sub_smul]
    congr 3
    abel
  have h₄ := inner_sq_add_norm_sub_sq_le (y.fst - y'.fst) he
  rw [h₁, sq_abs, dist_eq_norm (y.fst)]
  nlinarith [pow_le_pow_left₀ dist_nonneg h₂ 2]

/-- The map `(u, r) ↦ (a + u e, r)` from the two-dimensional model to `UpperHalfSpace E`. -/
private def incl (a e : E) (x : UpperHalfSpace ℝ) : UpperHalfSpace E :=
  mk (inclAmbient a e x) (by simpa [inclAmbient] using height_pos x)

private theorem fst_incl (a e : E) (x : UpperHalfSpace ℝ) :
    (incl a e x : WithLp 2 (E × ℝ)).fst = a + (x : WithLp 2 (ℝ × ℝ)).fst • e := by
  simp [incl, inclAmbient]

private theorem height_incl (a e : E) (x : UpperHalfSpace ℝ) : height (incl a e x) = height x := by
  simp [incl, inclAmbient]

private theorem height_le_norm_orthAmbient (a e : E) (x : UpperHalfSpace E) :
    height x ≤ ‖orthAmbient a e x‖ := by
  simpa [abs_of_pos (height_pos x)] using abs_snd_le_norm_orthAmbient a e x

/-- The map `(z, r) ↦ (⟪z - a, e⟫, √(‖z - a - ⟪z - a, e⟫ e‖² + r²))` from `UpperHalfSpace E` to the
two-dimensional model. -/
private def proj (a e : E) (x : UpperHalfSpace E) : UpperHalfSpace ℝ :=
  mk (projAmbient a e x) <| (height_pos x).trans_le <| by
    simpa [projAmbient] using height_le_norm_orthAmbient a e x

private theorem fst_proj (a e : E) (x : UpperHalfSpace E) :
    (proj a e x : WithLp 2 (ℝ × ℝ)).fst = ⟪(x : WithLp 2 (E × ℝ)).fst - a, e⟫ := by
  simp [proj, projAmbient]

private theorem height_proj (a e : E) (x : UpperHalfSpace E) :
    height (proj a e x) = ‖orthAmbient a e x‖ := by
  simp [proj, projAmbient]

private theorem lipschitzWith_incl (a : E) {e : E} (he : ‖e‖ ≤ 1) :
    LipschitzWith 1 (incl a e) :=
  lipschitzWith_one_of_coe_comp_eq (A := inclAmbient a e) (funext fun _ ↦ coe_mk _ _)
    (fun _ ↦ (contDiff_inclAmbient a e).contDiffAt) (lipschitzWith_inclAmbient a he)
    (fun x ↦ (height_incl a e x).ge)

private theorem lipschitzWith_proj (a : E) {e : E} (he : ‖e‖ ≤ 1) :
    LipschitzWith 1 (proj a e) :=
  lipschitzWith_one_of_coe_comp_eq (A := projAmbient a e) (funext fun _ ↦ coe_mk _ _)
    (fun x ↦ contDiffAt_projAmbient a e (by simpa using height_pos x))
    (lipschitzWith_projAmbient a he)
    (fun x ↦ (height_le_norm_orthAmbient a e x).trans_eq (height_proj a e x).symm)

/-! ### The distance formula -/

/-- The hyperbolic distance on the upper half-space model in terms of the Euclidean distance of
`E × ℝ`: `dist p q = 2 arsinh (‖p - q‖ / (2 √(s t)))` for points `p` and `q` of heights `s` and
`t`. This is the analogue of `UpperHalfPlane.dist_eq`. -/
theorem dist_eq (p q : UpperHalfSpace E) :
    dist p q = 2 * arsinh (dist (p : WithLp 2 (E × ℝ)) q / (2 * √(height p * height q))) := by
  -- Project to the plane through `p` and `q` spanned by the vertical direction and the unit
  -- vector `e` from the foot of `p` towards the foot of `q`.
  obtain ⟨a, ha⟩ : ∃ a, (p : WithLp 2 (E × ℝ)).fst = a := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, (q : WithLp 2 (E × ℝ)).fst = a + v := ⟨_, (add_sub_cancel a _).symm⟩
  set e := ‖v‖⁻¹ • v
  have he : ‖e‖ ≤ 1 := by
    rw [norm_smul, norm_inv, norm_norm]
    exact inv_mul_le_one_of_le₀ le_rfl (norm_nonneg v)
  have hve : ‖v‖ • e = v := by
    rcases eq_or_ne v 0 with hv | hv
    · simp [e, hv]
    · rw [smul_inv_smul₀ (norm_ne_zero_iff.mpr hv)]
  have hinner : ⟪v, e⟫ = ‖v‖ := by
    rw [inner_smul_right, real_inner_self_eq_norm_sq]
    rcases eq_or_ne ‖v‖ 0 with hv | hv
    · simp [hv]
    · field_simp
  -- The images of `p` and `q` in the two-dimensional model are `(0, s)` and `(‖v‖, t)`.
  have hp₁ : (proj a e p : WithLp 2 (ℝ × ℝ)).fst = 0 := by simp [fst_proj, ha]
  have hp₂ : height (proj a e p) = height p := by
    simp [height_proj, orthAmbient, ha, abs_of_pos (height_pos p)]
  have hq₁ : (proj a e q : WithLp 2 (ℝ × ℝ)).fst = ‖v‖ := by simp [fst_proj, hv, hinner]
  have hq₂ : height (proj a e q) = height q := by
    simp [height_proj, orthAmbient, hv, hinner, hve, abs_of_pos (height_pos q)]
  -- Both points are fixed by `incl a e ∘ proj a e`, so `proj a e` preserves their distance.
  have hp' : incl a e (proj a e p) = p :=
    ext_fst_height (by simp [fst_incl, hp₁, ha]) (by rw [height_incl, hp₂])
  have hq' : incl a e (proj a e q) = q :=
    ext_fst_height (by simp [fst_incl, hq₁, hv, hve]) (by rw [height_incl, hq₂])
  have heq : dist p q = dist (proj a e p) (proj a e q) := by
    refine le_antisymm ?_ ((lipschitzWith_proj a he).dist_le_mul p q |>.trans_eq (by simp))
    conv_lhs => rw [← hp', ← hq']
    exact (lipschitzWith_incl a he).dist_le_mul _ _ |>.trans_eq (by simp)
  have hdist : dist (proj a e p : WithLp 2 (ℝ × ℝ)) (proj a e q) =
      dist (p : WithLp 2 (E × ℝ)) q := by
    rw [WithLp.prod_dist_eq_of_L2, WithLp.prod_dist_eq_of_L2, hp₁, hq₁, ha, hv, snd_coe,
      snd_coe, snd_coe, snd_coe, hp₂, hq₂, dist_self_add_right, Real.dist_eq, zero_sub, abs_neg,
      abs_norm]
  rw [heq, dist_eq_of_real, hdist, hp₂, hq₂]

/-- The closed formula for the hyperbolic distance on the upper half-space model:
`cosh (dist p q) = 1 + ‖p - q‖² / (2 s t)` for points `p` and `q` of heights `s` and `t`, where
`‖p - q‖` is the Euclidean distance of `E × ℝ`. This is the analogue of
`UpperHalfPlane.cosh_dist`. -/
theorem cosh_dist (p q : UpperHalfSpace E) :
    cosh (dist p q) = 1 + dist (p : WithLp 2 (E × ℝ)) q ^ 2 / (2 * height p * height q) := by
  have hp := height_pos p
  have hq := height_pos q
  rw [dist_eq, cosh_two_mul, cosh_sq', add_assoc, ← two_mul, sinh_arsinh, div_pow, mul_pow,
    sq_sqrt, sq (2 : ℝ), mul_assoc, ← mul_div_assoc, mul_assoc, mul_div_mul_left] <;> positivity

/-- On a vertical line the hyperbolic distance is the distance of the logarithms of the heights:
`dist (x, s) (x, t) = |log t - log s|`. -/
theorem dist_of_fst_eq {p q : UpperHalfSpace E}
    (h : (p : WithLp 2 (E × ℝ)).fst = (q : WithLp 2 (E × ℝ)).fst) :
    dist p q = dist (log (height p)) (log (height q)) := by
  have hp := height_pos p
  have hq := height_pos q
  refine cosh_injOn dist_nonneg dist_nonneg ?_
  rw [cosh_dist, Real.dist_eq, cosh_abs, cosh_eq, WithLp.prod_dist_eq_of_L2, h, dist_self,
    sq_sqrt (by positivity), ← log_div hp.ne' hq.ne', ← log_inv, exp_log (by positivity),
    exp_log (by positivity), Real.dist_eq, sq_abs]
  simp only [snd_coe]
  field_simp
  ring

end TauCeti.UpperHalfSpace
