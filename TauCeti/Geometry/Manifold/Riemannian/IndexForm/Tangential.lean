/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import TauCeti.Geometry.Manifold.Riemannian.IndexForm.Basic
import TauCeti.Analysis.InnerProductSpace.Projection.Basic
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.ConstantSpeed
import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Tangential
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Metric

/-!
# Tangential and normal splitting of the index form along a geodesic

Along a geodesic `γ` in a smooth Riemannian manifold, covariant differentiation commutes with
orthogonal projection onto the tangent line `ℝ ∙ γ'`
(`TauCeti.Manifold.IsGeodesicCurveOn.alongCurveWithin_sub_starProjection_singleton`), while the
curvature term `⟪R(V, γ') γ', W⟫` vanishes whenever `V` or `W` is tangential. Consequently, for
any two tangent fields `V` and `W` along `γ`, the index form of their normal components
`V^⊥ = V - proj_{ℝ ∙ γ'} V` and `W^⊥ = W - proj_{ℝ ∙ γ'} W` satisfies the bilinear identity

`I(V^⊥, W^⊥) = I(V, W) - ∫_a^b ⟪D_t V, γ'⟫ ⟪D_t W, γ'⟫ / ‖γ'‖² dt`.

In particular, every differentiable tangential field `V` (`V t ∈ ℝ ∙ γ'(t)`) is `indexForm`-
orthogonal to every differentiable normal field `W` (`⟪W t, γ'(t)⟫ = 0`).

## Main results

* `TauCeti.Manifold.IsGeodesicCurveOn.indexFormIntegrand_sub_starProjection_singleton`: pointwise
  bilinear normal-projection identity for the index-form integrand along a geodesic on `s ∈ 𝓝 t`.
* `TauCeti.Manifold.IsGeodesicCurveOn.indexForm_sub_starProjection_singleton`: integrated bilinear
  normal-projection formula `I(V^⊥, W^⊥) = I(V, W) - ∫ ⟪D_t V, γ'⟫ ⟪D_t W, γ'⟫ / ‖γ'‖²`.
* `TauCeti.Manifold.IsGeodesicCurveOn.indexForm_eq_zero_of_mem_span_curveVelocity_of_orthogonal`:
  any differentiable tangential field along a geodesic is `indexForm`-orthogonal to any
  differentiable normal field.
* `TauCeti.Manifold.IsGeodesicCurveOn.indexForm_smul_curveVelocity_eq_zero_of_orthogonal`:
  corollary for explicit tangential fields `f • γ'`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 10 (tangential and normal variations and the index form).
* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Chapter 10, §2.
-/

public noncomputable section

open Bundle CovariantDerivative Filter MeasureTheory Set
open scoped ContDiff Manifold Topology InnerProductSpace

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- **Pointwise normal-projection identity for the index-form integrand.** Along a geodesic `γ` on
a parameter set `s ∈ 𝓝 t`, at a parameter `t` where `V` and `W` have differentiable coordinates, the
integrand `I_t(V^⊥, W^⊥)` of the normal components
`V^⊥(r) = V(r) - (ℝ ∙ γ'(r)).starProjection (V(r))` and
`W^⊥(r) = W(r) - (ℝ ∙ γ'(r)).starProjection (W(r))` equals
`I_t(V, W) - ⟪D_t V(t), γ'(t)⟫ * ⟪D_t W(t), γ'(t)⟫ / ‖γ'(t)‖²`. -/
theorem IsGeodesicCurveOn.indexFormIntegrand_sub_starProjection_singleton
    {γ : ℝ → M} {V W : ∀ t, TangentSpace I (γ t)} {s : Set ℝ} {t : ℝ}
    (hγ : IsGeodesicCurveOn I γ s) (hs : s ∈ 𝓝 t)
    (hV : DifferentiableAt ℝ (sectionCoord ℝ (F := E) γ V (γ t)) t)
    (hW : DifferentiableAt ℝ (sectionCoord ℝ (F := E) γ W (γ t)) t) :
    indexFormIntegrand I γ
        (fun r ↦ V r - (ℝ ∙ curveVelocity I γ r).starProjection (V r))
        (fun r ↦ W r - (ℝ ∙ curveVelocity I γ r).starProjection (W r)) t =
      indexFormIntegrand I γ V W t -
        ⟪alongCurve (leviCivitaConnection I M) γ V t, curveVelocity I γ t⟫_ℝ *
          ⟪alongCurve (leviCivitaConnection I M) γ W t, curveVelocity I γ t⟫_ℝ /
          ‖curveVelocity I γ t‖ ^ 2 := by
  set cov := leviCivitaConnection I M
  have hm := isMetricCompatible_leviCivitaConnection (I := I) (M := M)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hs
  have hγb : IsGeodesicCurveOn I γ (Metric.ball t r) :=
    hγ.mono Metric.isOpen_ball.uniqueDiffOn hball
  have ht : t ∈ Metric.ball t r := Metric.mem_ball_self hr
  -- Covariant differentiation commutes with the normal projection on `Metric.ball t r`.
  have hDN (U : ∀ q, TangentSpace I (γ q))
      (hU : DifferentiableAt ℝ (sectionCoord ℝ (F := E) γ U (γ t)) t) :
      alongCurve cov γ (fun q ↦ U q - (ℝ ∙ curveVelocity I γ q).starProjection (U q)) t =
        alongCurve cov γ U t -
          (ℝ ∙ curveVelocity I γ t).starProjection (alongCurve cov γ U t) := by
    have hmem : Metric.ball t r ∈ 𝓝 t := Metric.isOpen_ball.mem_nhds ht
    have hnear : ∀ᶠ q in 𝓝 t,
        U q - (ℝ ∙ curveVelocity I γ q).starProjection (U q) =
          U q - (ℝ ∙ curveVelocityWithin I γ (Metric.ball t r) q).starProjection (U q) := by
      filter_upwards [hmem] with q hq
      rw [curveVelocityWithin_of_mem_nhds (Metric.isOpen_ball.mem_nhds hq)]
    rw [alongCurve_congr cov γ _ hnear, ← alongCurveWithin_of_mem_nhds cov γ _ hmem,
      hγb.alongCurveWithin_sub_starProjection_singleton (convex_ball t r).isPreconnected ht
        hU.differentiableWithinAt,
      alongCurveWithin_of_mem_nhds cov γ U hmem, curveVelocityWithin_of_mem_nhds hmem]
  -- The curvature term ignores tangential components in both slots.
  have hself : ⟪cov.curvatureTensor (γ t) (V t) (curveVelocity I γ t)
      (curveVelocity I γ t), curveVelocity I γ t⟫_ℝ = 0 := by
    have hskew := hm.inner_curvatureTensor_eq_neg (γ t) (V t) (curveVelocity I γ t)
      (curveVelocity I γ t) (curveVelocity I γ t)
    linarith [real_inner_comm (cov.curvatureTensor (γ t) (V t) (curveVelocity I γ t)
      (curveVelocity I γ t)) (curveVelocity I γ t)]
  have hcurv : ⟪cov.curvatureTensor (γ t)
        (V t - (ℝ ∙ curveVelocity I γ t).starProjection (V t))
        (curveVelocity I γ t) (curveVelocity I γ t),
        W t - (ℝ ∙ curveVelocity I γ t).starProjection (W t)⟫_ℝ =
      ⟪cov.curvatureTensor (γ t) (V t) (curveVelocity I γ t) (curveVelocity I γ t), W t⟫_ℝ := by
    simp [Submodule.starProjection_singleton, curvatureTensor_self, inner_sub_right,
      real_inner_smul_right, hself]
  rw [indexFormIntegrand_def, indexFormIntegrand_def, hDN V hV, hDN W hW, hcurv,
    Submodule.inner_sub_starProjection_singleton]
  ring

/-- **Normal-projection formula for the index form along a geodesic.** Let `γ` be a geodesic on
`uIoo a b` and let `V`, `W` have `C¹` tangent-bundle lifts on `uIcc a b`. Then the index form of
their normal components `V^⊥(t) = V(t) - (ℝ ∙ γ'(t)).starProjection (V(t))` and
`W^⊥(t) = W(t) - (ℝ ∙ γ'(t)).starProjection (W(t))` satisfies

`I(V^⊥, W^⊥) = I(V, W) - ∫_a^b ⟪D_t V(t), γ'(t)⟫ * ⟪D_t W(t), γ'(t)⟫ / ‖γ'(t)‖² dt`. -/
theorem IsGeodesicCurveOn.indexForm_sub_starProjection_singleton
    {γ : ℝ → M} {V W : ∀ t, TangentSpace I (γ t)} {a b : ℝ}
    (hγ : IsGeodesicCurveOn I γ (uIoo a b))
    (hV : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) (uIcc a b))
    (hW : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (W r)) (uIcc a b)) :
    indexForm I γ
        (fun t ↦ V t - (ℝ ∙ curveVelocity I γ t).starProjection (V t))
        (fun t ↦ W t - (ℝ ∙ curveVelocity I γ t).starProjection (W t)) a b =
      indexForm I γ V W a b -
        ∫ t in a..b,
          ⟪alongCurve (leviCivitaConnection I M) γ V t, curveVelocity I γ t⟫_ℝ *
            ⟪alongCurve (leviCivitaConnection I M) γ W t, curveVelocity I γ t⟫_ℝ /
            ‖curveVelocity I γ t‖ ^ 2 := by
  rcases eq_or_ne a b with rfl | hab
  · simp
  have hintT : IntervalIntegrable (fun t ↦
      ⟪alongCurve (leviCivitaConnection I M) γ V t, curveVelocity I γ t⟫_ℝ *
        ⟪alongCurve (leviCivitaConnection I M) γ W t, curveVelocity I γ t⟫_ℝ /
        ‖curveVelocity I γ t‖ ^ 2) volume a b := by
    obtain ⟨t₀, ht₀⟩ : (uIoo a b).Nonempty := nonempty_uIoo.mpr hab
    set c := ‖curveVelocityWithin I γ (uIoo a b) t₀‖
    have hγc : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (uIcc a b) :=
      (Bundle.contMDiff_proj (fun x : M ↦ TangentSpace I x) (IB := I) (n := 1)).comp_contMDiffOn hV
    have hvel : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 0
        (fun r ↦ TotalSpace.mk' E (γ r) (curveVelocityWithin I γ (uIcc a b) r)) (uIcc a b) := by
      simpa only [funext (curveVelocityLiftWithin_apply (I := I) γ (uIcc a b))] using
        hγc.contMDiffOn_curveVelocityLiftWithin (m := 0) (by simp)
          (uniqueDiffOn_uIcc hab).uniqueMDiffOn
    have hcont (U : ∀ r, TangentSpace I (γ r))
        (hU : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1
          (fun r ↦ TotalSpace.mk' E (γ r) (U r)) (uIcc a b)) :
        ContinuousOn (fun r ↦ ⟪alongCurveWithin (leviCivitaConnection I M) γ U (uIcc a b) r,
          curveVelocityWithin I γ (uIcc a b) r⟫_ℝ) (uIcc a b) :=
      (ContMDiffOn.inner_bundle (IB := I) (F := E)
        (E := fun x : M ↦ TangentSpace I x) (b := γ)
        (h := IsContMDiffRiemannianBundle.of_le (n := ∞) zero_le)
        (contMDiffOn_alongCurveWithin_leviCivitaConnection (n := 0) (m := ∞) (k := ∞)
          (by simp) (by simp) (uniqueDiffOn_uIcc hab) (by simpa using hU)) hvel).continuousOn
    refine (((hcont V hV).mul (hcont W hW)).div_const (c ^ 2)).intervalIntegrable.congr_uIoo
      fun t ht ↦ ?_
    have hmemIoo : uIoo a b ∈ 𝓝 t := (isOpen_Ioo : IsOpen (uIoo a b)).mem_nhds ht
    have hmemIcc : uIcc a b ∈ 𝓝 t := mem_of_superset hmemIoo uIoo_subset_uIcc_self
    have hnorm : ‖curveVelocity I γ t‖ = c := by
      rw [← curveVelocityWithin_of_mem_nhds hmemIoo]
      exact hγ.norm_curveVelocityWithin_eq isPreconnected_Ioo ht ht₀
    dsimp only [Pi.mul_apply]
    rw [alongCurveWithin_of_mem_nhds _ γ _ hmemIcc, alongCurveWithin_of_mem_nhds _ γ _ hmemIcc,
      curveVelocityWithin_of_mem_nhds hmemIcc, hnorm]
  rw [indexForm_def, indexForm_def,
    ← intervalIntegral.integral_sub (intervalIntegrable_indexFormIntegrand hV hW) hintT]
  refine intervalIntegral.integral_congr_uIoo fun t ht ↦ ?_
  have hmemIoo : uIoo a b ∈ 𝓝 t := (isOpen_Ioo : IsOpen (uIoo a b)).mem_nhds ht
  have hmemIcc : uIcc a b ∈ 𝓝 t := mem_of_superset hmemIoo uIoo_subset_uIcc_self
  exact hγ.indexFormIntegrand_sub_starProjection_singleton hmemIoo
    (differentiableAt_sectionCoord γ V ((hV t (uIoo_subset_uIcc_self ht)).contMDiffAt
      hmemIcc |>.mdifferentiableAt one_ne_zero)
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t)))
    (differentiableAt_sectionCoord γ W ((hW t (uIoo_subset_uIcc_self ht)).contMDiffAt
      hmemIcc |>.mdifferentiableAt one_ne_zero)
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t)))

/-- **Tangential fields are `indexForm`-orthogonal to normal fields along a geodesic.** If `γ` is a
geodesic on `uIoo a b`, `V` and `W` have differentiable coordinates on `uIoo a b`, `V t ∈ ℝ ∙ γ'(t)`
for every `t ∈ uIoo a b`, and `W` is orthogonal to `γ'` everywhere on `uIoo a b`, then
`I(V, W) = 0`. -/
theorem IsGeodesicCurveOn.indexForm_eq_zero_of_mem_span_curveVelocity_of_orthogonal
    {γ : ℝ → M} {V W : ∀ t, TangentSpace I (γ t)} {a b : ℝ}
    (hγ : IsGeodesicCurveOn I γ (uIoo a b))
    (hV : ∀ t ∈ uIoo a b, DifferentiableAt ℝ (sectionCoord ℝ (F := E) γ V (γ t)) t)
    (hW : ∀ t ∈ uIoo a b, DifferentiableAt ℝ (sectionCoord ℝ (F := E) γ W (γ t)) t)
    (htan : ∀ t ∈ uIoo a b, V t ∈ ℝ ∙ curveVelocity I γ t)
    (horth : ∀ t ∈ uIoo a b, ⟪W t, curveVelocity I γ t⟫_ℝ = 0) :
    indexForm I γ V W a b = 0 := by
  rw [indexForm_def]
  refine (intervalIntegral.integral_congr_uIoo (g := fun _ ↦ (0 : ℝ)) fun t ht ↦ ?_).trans
    intervalIntegral.integral_zero
  have hm := isMetricCompatible_leviCivitaConnection (I := I) (M := M)
  have hmem : uIoo a b ∈ 𝓝 t := (isOpen_Ioo : IsOpen (uIoo a b)).mem_nhds ht
  -- Differentiate `⟪W, γ'⟫ = 0` along the geodesic to get `⟪D_t W, γ'⟫ = 0`.
  have hprod := hm.hasDerivWithinAt_inner_alongCurveWithin (hγ.mdifferentiableOn t ht)
    (hW t ht).differentiableWithinAt
    (differentiableWithinAt_sectionCoord_curveVelocityWithin γ hγ.uniqueDiffOn hγ.contMDiffOn ht
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t)))
  rw [← accelerationWithin_def, hγ.accelerationWithin_eq_zero t ht, inner_zero_right,
    add_zero] at hprod
  have hDW0 : ⟪alongCurve (leviCivitaConnection I M) γ W t, curveVelocity I γ t⟫_ℝ = 0 := by
    have h := (hγ.uniqueDiffOn t ht).eq_deriv _ hprod
      ((hasDerivWithinAt_const t (uIoo a b) (0 : ℝ)).congr_of_mem (fun r hr ↦ by
        have hmemr : uIoo a b ∈ 𝓝 r := (isOpen_Ioo : IsOpen (uIoo a b)).mem_nhds hr
        rw [curveVelocityWithin_of_mem_nhds hmemr]
        exact horth r hr) ht)
    rwa [alongCurveWithin_of_mem_nhds _ γ W hmem, curveVelocityWithin_of_mem_nhds hmem] at h
  -- The normal component of `V` vanishes near `t`, while `⟪D_t W, γ'⟫ = 0` kills the projection
  -- term in the bilinear normal-projection identity.
  have hsplit := hγ.indexFormIntegrand_sub_starProjection_singleton hmem (hV t ht) (hW t ht)
  have hVperp : ∀ᶠ r in 𝓝 t, HEq (V r - (ℝ ∙ curveVelocity I γ r).starProjection (V r))
      ((0 : ∀ q, TangentSpace I (γ q)) r) :=
    eventually_of_mem hmem fun r hr ↦ by
      simp [Submodule.starProjection_eq_self_iff.mpr (htan r hr)]
  have hlhs : indexFormIntegrand I γ
      (fun r ↦ V r - (ℝ ∙ curveVelocity I γ r).starProjection (V r))
      (fun r ↦ W r - (ℝ ∙ curveVelocity I γ r).starProjection (W r)) t = 0 := by
    rw [indexFormIntegrand_congr EventuallyEq.rfl hVperp (Eventually.of_forall fun _ ↦ HEq.rfl),
      indexFormIntegrand_zero_left]
  simp only [hlhs, hDW0, mul_zero, zero_div, sub_zero] at hsplit
  exact hsplit.symm

/-- **Tangential fields `f • γ'` are `indexForm`-orthogonal to normal fields along a geodesic.**
Corollary of `IsGeodesicCurveOn.indexForm_eq_zero_of_mem_span_curveVelocity_of_orthogonal` for an
explicit scalar multiple `f • γ'`. -/
theorem IsGeodesicCurveOn.indexForm_smul_curveVelocity_eq_zero_of_orthogonal
    {γ : ℝ → M} {f : ℝ → ℝ} {W : ∀ t, TangentSpace I (γ t)} {a b : ℝ}
    (hγ : IsGeodesicCurveOn I γ (uIoo a b))
    (hf : ∀ t ∈ uIoo a b, DifferentiableAt ℝ f t)
    (hW : ∀ t ∈ uIoo a b, DifferentiableAt ℝ (sectionCoord ℝ (F := E) γ W (γ t)) t)
    (horth : ∀ t ∈ uIoo a b, ⟪W t, curveVelocity I γ t⟫_ℝ = 0) :
    indexForm I γ (fun t ↦ f t • curveVelocity I γ t) W a b = 0 := by
  refine hγ.indexForm_eq_zero_of_mem_span_curveVelocity_of_orthogonal (fun t ht ↦ ?_) hW
    (fun t _ ↦ Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)) horth
  have hmem : uIoo a b ∈ 𝓝 t := (isOpen_Ioo : IsOpen (uIoo a b)).mem_nhds ht
  refine ((hf t ht).smul ((differentiableWithinAt_sectionCoord_curveVelocityWithin γ
    hγ.uniqueDiffOn hγ.contMDiffOn ht
    (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t))).differentiableAt
    hmem)).congr_of_eventuallyEq (eventually_of_mem hmem fun r hr ↦ ?_)
  have hmemr : uIoo a b ∈ 𝓝 r := (isOpen_Ioo : IsOpen (uIoo a b)).mem_nhds hr
  simp [sectionCoord_apply, curveVelocityWithin_of_mem_nhds hmemr]

end TauCeti.Manifold
