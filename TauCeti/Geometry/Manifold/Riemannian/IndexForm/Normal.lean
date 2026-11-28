/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.IndexForm.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Tangential
import TauCeti.Analysis.InnerProductSpace.Projection.Basic
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.ConstantSpeed
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Metric

/-!
# The index form of the normal part of a field

Along a geodesic `γ`, write `J^⊥ = J - proj_{γ'} J` for the normal part of a field `J` along `γ`,
its orthogonal projection onto the orthogonal complement of the velocity. Covariant
differentiation commutes with this projection
(`TauCeti.Manifold.IsGeodesicCurveOn.alongCurveWithin_sub_starProjection_singleton`), and the
curvature term `⟪R(J, γ') γ', J⟫` does not see the tangential part of `J`. Hence the index-form
integrand of `J^⊥` is that of `J` minus `‖proj_{γ'} D_t J‖²`, and more generally for two fields
`V`, `W` with `C¹` tangent-bundle lifts on `uIcc a b`,

`I(V^⊥, W^⊥) = I(V, W) - ∫_a^b ⟪D_t V, γ'⟫ ⟪D_t W, γ'⟫ / ‖γ'‖² dt`.

In particular, every differentiable tangential field `V` (`V t ∈ ℝ ∙ γ'(t)`) is `indexForm`-
orthogonal to every differentiable normal field `W` (`⟪W t, γ'(t)⟫ = 0`).

## Main results

* `TauCeti.Manifold.IsGeodesicCurveOn.indexFormIntegrandWithin_sub_starProjection_singleton` and
  `TauCeti.Manifold.IsGeodesicCurveOn.indexFormIntegrand_sub_starProjection_singleton`: the
  index-form integrand of the normal part of a field is that of the field minus the squared
  tangential part of its covariant derivative.
* `TauCeti.Manifold.IsGeodesicCurveOn.indexForm_sub_starProjection_singleton`: integrated bilinear
  normal-projection formula `I(V^⊥, W^⊥) = I(V, W) - ∫ ⟪D_t V, γ'⟫ ⟪D_t W, γ'⟫ / ‖γ'‖²`.
* `TauCeti.Manifold.indexForm_sub_starProjection_eq_of_norm_curveVelocity_eq_one`: rewrite
  `I(V^⊥, W^⊥)` along a unit-speed curve using `V - ⟪V, γ'⟫ γ'`.
* `TauCeti.Manifold.indexForm_sub_starProjection_congr_of_totalSpaceMk_eq`: normal index forms
  depend only on the tangent-bundle lifts of the fields on `uIoo a b`.
* `TauCeti.Manifold.IsGeodesicCurveOn.indexForm_eq_zero_of_mem_span_curveVelocity_of_orthogonal`:
  any differentiable tangential field along a geodesic is `indexForm`-orthogonal to any
  differentiable normal field.
* `TauCeti.Manifold.IsGeodesicCurveOn.indexForm_smul_curveVelocity_eq_zero_of_orthogonal`:
  corollary for explicit tangential fields `f • γ'`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 10.
* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Chapter 10, §2.
-/

public section

open Bundle CovariantDerivative Filter MeasureTheory Set
open scoped ContDiff Manifold Topology InnerProductSpace

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {γ : ℝ → M} {J : ∀ t, TangentSpace I (γ t)} {s : Set ℝ} {t : ℝ}

/-- **The index form sees only the normal part, up to its tangential derivative.** Along a
geodesic on a preconnected parameter set, let `J^⊥ = J - proj_{γ'} J` be the normal part of a
field `J` whose coordinates are differentiable at `t`. Then the index-form integrand of `J^⊥`
against itself is that of `J` minus `‖proj_{γ'} D_t J‖²`, computed with derivatives within the
parameter set. -/
theorem IsGeodesicCurveOn.indexFormIntegrandWithin_sub_starProjection_singleton
    (h : IsGeodesicCurveOn I γ s) (hs : IsPreconnected s) (ht : t ∈ s)
    (hJ : DifferentiableWithinAt ℝ (sectionCoord ℝ (F := E) γ J (γ t)) s t) :
    indexFormIntegrandWithin I γ
        (fun r ↦ J r - (ℝ ∙ curveVelocityWithin I γ s r).starProjection (J r))
        (fun r ↦ J r - (ℝ ∙ curveVelocityWithin I γ s r).starProjection (J r)) s t =
      indexFormIntegrandWithin I γ J J s t -
        ‖(ℝ ∙ curveVelocityWithin I γ s t).starProjection
          (alongCurveWithin (leviCivitaConnection I M) γ J s t)‖ ^ 2 := by
  rw [indexFormIntegrandWithin_def, indexFormIntegrandWithin_def,
    h.alongCurveWithin_sub_starProjection_singleton hs ht hJ]
  set v := curveVelocityWithin I γ s t
  set D := alongCurveWithin (leviCivitaConnection I M) γ J s t
  -- the projection of `J t` is a multiple of `v`, invisible to the curvature term
  have hproj : (ℝ ∙ v).starProjection (J t) = (inner ℝ v (J t) / ‖v‖ ^ 2) • v := by
    rw [Submodule.starProjection_singleton, RCLike.ofReal_real_eq_id, id_eq]
  rw [hproj, IsMetricCompatible.inner_curvatureTensor_sub_smul
    (isMetricCompatible_leviCivitaConnection (I := I) (M := M)) (J t) v]
  -- `D - proj D` is orthogonal to `proj D`
  have horth := Submodule.starProjection_inner_eq_zero (K := ℝ ∙ v) D
    ((ℝ ∙ v).starProjection D) (Submodule.starProjection_apply_mem _ D)
  rw [← real_inner_self_eq_norm_sq ((ℝ ∙ v).starProjection D)]
  rw [inner_sub_left] at horth
  simp only [inner_sub_left, inner_sub_right] at horth ⊢
  rw [real_inner_comm D ((ℝ ∙ v).starProjection D)]
  linarith

/-- The unrestricted form of
`TauCeti.Manifold.IsGeodesicCurveOn.indexFormIntegrandWithin_sub_starProjection_singleton`: along
a geodesic on a preconnected neighbourhood of `t`, the index-form integrand of the normal part
`J - proj_{γ'} J` of a field `J` with differentiable coordinates at `t` is that of `J` minus
`‖proj_{γ'} D_t J‖²`. -/
theorem IsGeodesicCurveOn.indexFormIntegrand_sub_starProjection_singleton
    (h : IsGeodesicCurveOn I γ s) (hs : IsPreconnected s) (hst : s ∈ 𝓝 t)
    (hJ : DifferentiableAt ℝ (sectionCoord ℝ (F := E) γ J (γ t)) t) :
    indexFormIntegrand I γ
        (fun r ↦ J r - (ℝ ∙ curveVelocity I γ r).starProjection (J r))
        (fun r ↦ J r - (ℝ ∙ curveVelocity I γ r).starProjection (J r)) t =
      indexFormIntegrand I γ J J t -
        ‖(ℝ ∙ curveVelocity I γ t).starProjection
          (alongCurve (leviCivitaConnection I M) γ J t)‖ ^ 2 := by
  -- near `t`, derivatives within `s` are unrestricted derivatives
  have hfield : ∀ᶠ r in 𝓝 t,
      HEq (J r - (ℝ ∙ curveVelocity I γ r).starProjection (J r))
        (J r - (ℝ ∙ curveVelocityWithin I γ s r).starProjection (J r)) := by
    filter_upwards [eventually_mem_nhds_iff.2 hst] with r hr
    rw [curveVelocityWithin_of_mem_nhds hr]
  rw [indexFormIntegrand_congr (δ := γ) Filter.EventuallyEq.rfl hfield hfield,
    ← indexFormIntegrandWithin_of_mem_nhds hst, ← indexFormIntegrandWithin_of_mem_nhds hst,
    h.indexFormIntegrandWithin_sub_starProjection_singleton hs (mem_of_mem_nhds hst)
      (hJ.differentiableWithinAt), curveVelocityWithin_of_mem_nhds hst,
    alongCurveWithin_of_mem_nhds _ γ J hst]

private theorem indexFormIntegrand_sub_starProjection_singleton_bilinear
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
    have hcont (U : ∀ r, TangentSpace I (γ r)) (hU : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1
        (fun r ↦ TotalSpace.mk' E (γ r) (U r)) (uIcc a b)) :
        ContinuousOn (fun r ↦ ⟪alongCurveWithin (leviCivitaConnection I M) γ U (uIcc a b) r,
          curveVelocityWithin I γ (uIcc a b) r⟫_ℝ) (uIcc a b) :=
      (ContMDiffOn.inner_bundle (IB := I) (F := E) (E := fun x : M ↦ TangentSpace I x) (b := γ)
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
  have hdiff (U : ∀ r, TangentSpace I (γ r))
      (hU : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (U r)) (uIcc a b)) :
      DifferentiableAt ℝ (sectionCoord ℝ (F := E) γ U (γ t)) t :=
    differentiableAt_sectionCoord γ U ((hU t (uIoo_subset_uIcc_self ht)).contMDiffAt
      (mem_of_superset hmemIoo uIoo_subset_uIcc_self) |>.mdifferentiableAt one_ne_zero)
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t))
  exact indexFormIntegrand_sub_starProjection_singleton_bilinear
    hγ hmemIoo (hdiff V hV) (hdiff W hW)

/-- Along a unit-speed curve on `uIoo a b`, the normal-projection index form `I(V^⊥, W^⊥)` equals
the index form of `V - ⟪V, γ'⟫ • γ'` and `W - ⟪W, γ'⟫ • γ'`. -/
theorem indexForm_sub_starProjection_eq_of_norm_curveVelocity_eq_one
    {a b : ℝ} {γ : ℝ → M} (hspeed : ∀ t ∈ uIoo a b, ‖curveVelocity I γ t‖ = 1)
    (V W : ∀ t, TangentSpace I (γ t)) :
    indexForm I γ
        (fun t ↦ V t - (ℝ ∙ curveVelocity I γ t).starProjection (V t))
        (fun t ↦ W t - (ℝ ∙ curveVelocity I γ t).starProjection (W t)) a b =
      indexForm I γ
        (fun t ↦ V t - ⟪V t, curveVelocity I γ t⟫_ℝ • curveVelocity I γ t)
        (fun t ↦ W t - ⟪W t, curveVelocity I γ t⟫_ℝ • curveVelocity I γ t) a b := by
  have hproj (U : ∀ t, TangentSpace I (γ t)) (t : ℝ) (ht : t ∈ uIoo a b) :
      HEq (U t - (ℝ ∙ curveVelocity I γ t).starProjection (U t))
        (U t - ⟪U t, curveVelocity I γ t⟫_ℝ • curveVelocity I γ t) := by
    rw [heq_eq_eq, Submodule.starProjection_unit_singleton ℝ (hspeed t ht), real_inner_comm]
  exact indexForm_congr (fun _ _ ↦ rfl) (hproj V) (hproj W)

/-- The normal-projection index form depends only on the tangent-bundle lifts of the curves and
fields on the open parameter interval `uIoo a b`. -/
theorem indexForm_sub_starProjection_congr_of_totalSpaceMk_eq {γ₁ γ₂ : ℝ → M}
    {V₁ : ∀ t, TangentSpace I (γ₁ t)} {V₂ : ∀ t, TangentSpace I (γ₂ t)}
    {W₁ : ∀ t, TangentSpace I (γ₁ t)} {W₂ : ∀ t, TangentSpace I (γ₂ t)}
    {a b : ℝ}
    (hV : ∀ t ∈ uIoo a b, TotalSpace.mk' E (γ₁ t) (V₁ t) = TotalSpace.mk' E (γ₂ t) (V₂ t))
    (hW : ∀ t ∈ uIoo a b, TotalSpace.mk' E (γ₁ t) (W₁ t) = TotalSpace.mk' E (γ₂ t) (W₂ t)) :
    indexForm I γ₁
        (fun t ↦ V₁ t - (ℝ ∙ curveVelocity I γ₁ t).starProjection (V₁ t))
        (fun t ↦ W₁ t - (ℝ ∙ curveVelocity I γ₁ t).starProjection (W₁ t)) a b =
      indexForm I γ₂
        (fun t ↦ V₂ t - (ℝ ∙ curveVelocity I γ₂ t).starProjection (V₂ t))
        (fun t ↦ W₂ t - (ℝ ∙ curveVelocity I γ₂ t).starProjection (W₂ t)) a b := by
  have hsub {x y : M} {u v : TangentSpace I x} {u' v' : TangentSpace I y}
      (hu : TotalSpace.mk' E x u = TotalSpace.mk' E y u')
      (hv : TotalSpace.mk' E x v = TotalSpace.mk' E y v') :
      HEq (u - (ℝ ∙ v).starProjection u) (u' - (ℝ ∙ v').starProjection u') := by
    cases hu; cases hv; rfl
  have hγEq : EqOn γ₁ γ₂ (uIoo a b) := fun t ht ↦ congrArg TotalSpace.proj (hV t ht)
  have hvel (t : ℝ) (ht : t ∈ uIoo a b) :
      TotalSpace.mk' E (γ₁ t) (curveVelocity I γ₁ t) =
        TotalSpace.mk' E (γ₂ t) (curveVelocity I γ₂ t) := by
    have hnear : γ₁ =ᶠ[𝓝 t] γ₂ := eventuallyEq_of_mem (isOpen_Ioo.mem_nhds ht) hγEq
    exact Bundle.TotalSpace.ext hnear.self_of_nhds
      (heq_of_eq (Filter.EventuallyEq.curveVelocity_eq hnear))
  exact indexForm_congr hγEq
    (fun t ht ↦ hsub (hV t ht) (hvel t ht))
    (fun t ht ↦ hsub (hW t ht) (hvel t ht))

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
  have hsplit :=
    indexFormIntegrand_sub_starProjection_singleton_bilinear hγ hmem (hV t ht) (hW t ht)
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

end
