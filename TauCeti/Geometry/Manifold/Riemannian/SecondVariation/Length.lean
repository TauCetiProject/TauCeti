/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.FirstVariation.Length
public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Tangential
public import TauCeti.Geometry.Manifold.Riemannian.SecondVariation.Basic
import TauCeti.Analysis.Calculus.Deriv.Second
import TauCeti.Analysis.Calculus.DerivativeTest
import TauCeti.Analysis.InnerProductSpace.Projection.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Parametric.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Metric

/-!
# The second variation of length

Let `F : ℝ → ℝ → M` be a `C³` variation of the curve `γ = F 0` between `a` and `b` in a smooth
Riemannian manifold, with variation field `V = TauCeti.Manifold.variationField I F` and transverse
acceleration `A(t) = D_s ∂_s F (0, t)`.

At a regular parameter `t` (`γ'(t) ≠ 0`), differentiating `s ↦ ‖∂_t F (s, t)‖ = √(‖∂_t F (s, t)‖²)`
twice at `s = 0` gives

`d²/ds² ‖∂_t F (s, t)‖ |₀ =
  (I_γ(V, V)(t) + ⟪D_t A(t), γ'(t)⟫) / ‖γ'(t)‖ - ⟪D_t V(t), γ'(t)⟫² / ‖γ'(t)‖³`,

where `I_γ(V, V)(t)` is `TauCeti.Manifold.indexFormIntegrand`. Compared with half the second
derivative of the squared speed, the extra term `-⟪D_t V, γ'⟫² / ‖γ'‖³` removes the tangential
component of `D_t V`.

Along a geodesic `γ` of constant speed `C > 0`, covariant differentiation commutes with the
orthogonal projection onto `(ℝ ∙ γ'(t))ᗮ` and `R(γ', γ') γ' = 0`, so the normal projection
`V⊥(t) = V(t) - proj_{ℝ ∙ γ'(t)} V(t)` satisfies

`I(V⊥, V⊥) = I(V, V) - (∫_a^b ⟪D_t V(t), γ'(t)⟫² dt) / C²`.

Integrating the pointwise second derivative of speed over `[a, b]` and integrating `⟪D_t A, γ'⟫`
by parts yields **the second variation formula for length** along a constant-speed geodesic, with
free endpoints:

`d²/ds² L(F s) |₀ = (I(V⊥, V⊥) + ⟪A(b), γ'(b)⟫ - ⟪A(a), γ'(a)⟫) / C`.

For a unit-speed geodesic (`C = 1`), `V⊥(t) = V(t) - ⟪V(t), γ'(t)⟫ • γ'(t)` and the factor `1 / C`
disappears. In particular, tangential variations (`V(t) ∈ ℝ ∙ γ'(t)`, corresponding to
first-order reparametrizations of `γ`) contribute `0` to `I(V⊥, V⊥)`, leaving only the endpoint
acceleration pairing — and `0` when the endpoints are fixed.

## Main results

* `TauCeti.Manifold.IsGeodesicCurveOn.indexFormIntegrand_sub_starProjection_singleton` and
  `TauCeti.Manifold.IsGeodesicCurveOn.indexForm_sub_starProjection_singleton`: splitting the index
  form along a geodesic into the index form of the normal projection plus the tangential derivative
  pairing.
* `TauCeti.Manifold.indexForm_sub_starProjection_eq_zero_of_mem_span`: tangential degeneracy of the
  normal-projected index form.
* `TauCeti.Manifold.hasDerivAt_deriv_norm_curveVelocity`: the pointwise second transverse derivative
  of the speed at a regular parameter.
* `TauCeti.Manifold.hasDerivAt_deriv_toReal_pathELength`: the second variation of length of a
  constant-speed curve, before assuming the geodesic equation.
* `TauCeti.Manifold.hasDerivAt_deriv_toReal_pathELength_of_isGeodesicCurveOn` and
  `TauCeti.Manifold.hasDerivAt_deriv_toReal_pathELength_of_norm_curveVelocity_eq_one`: **the
  second variation of length** along a constant-speed or unit-speed geodesic, with free endpoints.
* `TauCeti.Manifold.hasDerivAt_deriv_toReal_pathELength_of_inner_eq_zero` and
  `TauCeti.Manifold.hasDerivAt_deriv_toReal_pathELength_of_mem_span_curveVelocity`: specializations
  to normal variations and tangential (reparametrization) variations.
* `IsFixedEndpointVariation.hasDerivAt_deriv_toReal_pathELength_of_isGeodesicCurveOn` and
  `IsFixedEndpointVariation.indexForm_sub_starProjection_nonneg_of_isLocalMin_pathELength`:
  fixed-endpoint second variation of length and local-minimum nonnegativity.
* `TauCeti.Manifold.hasDerivAt_deriv_toReal_pathELength_of_periodic`: periodic variations of a
  closed constant-speed geodesic.

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 9, §2, Exercise 2.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Theorem 10.6 and Proposition 10.14.
-/

public noncomputable section

open Bundle CovariantDerivative Filter MeasureTheory Set
open scoped ContDiff InnerProductSpace Manifold Topology

namespace TauCeti.Manifold

section Projection

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- The curvature term `⟪R(u, w) w, v⟫` is unchanged when `u` and `v` are projected orthogonally
away from `ℝ ∙ w`, by skew-symmetry of `R` in its first and last two slots. -/
private theorem inner_curvatureTensor_sub_starProjection_singleton (x : M)
    (w u v : TangentSpace I x) :
    ⟪(leviCivitaConnection I M).curvatureTensor x
        (u - (ℝ ∙ w).starProjection u) w w,
      v - (ℝ ∙ w).starProjection v⟫_ℝ =
      ⟪(leviCivitaConnection I M).curvatureTensor x u w w, v⟫_ℝ := by
  have hskew := (isMetricCompatible_leviCivitaConnection (I := I) (M := M)
    ).inner_curvatureTensor_eq_neg x u w w w
  rw [real_inner_comm w] at hskew
  have hzero : ⟪(leviCivitaConnection I M).curvatureTensor x u w w, w⟫_ℝ = 0 := by
    rw [real_inner_comm] at hskew; linarith
  rw [Submodule.starProjection_singleton, Submodule.starProjection_singleton,
    RCLike.ofReal_real_eq_id, id_eq]
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    curvatureTensor_self, smul_zero, sub_zero, inner_sub_right, real_inner_smul_right, hzero,
    mul_zero]

omit [T2Space M] in
/-- On an open preconnected parameter set along a geodesic, unrestricted covariant differentiation
commutes with the normal projection away from `ℝ ∙ γ'(t)`. -/
theorem IsGeodesicCurveOn.alongCurve_sub_starProjection_singleton {γ : ℝ → M}
    {V : ∀ t, TangentSpace I (γ t)} {s : Set ℝ} {t : ℝ}
    (hgeo : IsGeodesicCurveOn I γ s) (hso : IsOpen s) (hs : IsPreconnected s) (ht : t ∈ s)
    (hV : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) t) :
    alongCurve (leviCivitaConnection I M) γ
        (fun r ↦ V r - (ℝ ∙ curveVelocity I γ r).starProjection (V r)) t =
      alongCurve (leviCivitaConnection I M) γ V t -
        (ℝ ∙ curveVelocity I γ t).starProjection
          (alongCurve (leviCivitaConnection I M) γ V t) := by
  have hs_nhds : s ∈ 𝓝 t := hso.mem_nhds ht
  have heq : (fun r ↦ V r - (ℝ ∙ curveVelocity I γ r).starProjection (V r)) =ᶠ[𝓝[s] t]
      fun r ↦ V r - (ℝ ∙ curveVelocityWithin I γ s r).starProjection (V r) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    rw [curveVelocityWithin_of_mem_nhds (hso.mem_nhds hr)]
  have hVd := differentiableWithinAt_sectionCoord (s := s) γ V
    (hV.mdifferentiableAt one_ne_zero).mdifferentiableWithinAt
    (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t))
  rw [← alongCurveWithin_of_mem_nhds _ γ _ hs_nhds,
    alongCurveWithin_congr _ γ _ heq (heq.eq_of_nhdsWithin ht),
    hgeo.alongCurveWithin_sub_starProjection_singleton hs ht hVd,
    alongCurveWithin_of_mem_nhds _ γ V hs_nhds, curveVelocityWithin_of_mem_nhds hs_nhds]

/-- **Pointwise normal-projection identity for the index form.** Along a geodesic on an open
preconnected set `s`, projecting `V` and `W` orthogonally to `γ'` subtracts
`⟪D_t V, γ'⟫ ⟪D_t W, γ'⟫ / ‖γ'‖²` from the index-form integrand. -/
theorem IsGeodesicCurveOn.indexFormIntegrand_sub_starProjection_singleton {γ : ℝ → M}
    {V W : ∀ t, TangentSpace I (γ t)} {s : Set ℝ} {t : ℝ}
    (hgeo : IsGeodesicCurveOn I γ s) (hso : IsOpen s) (hs : IsPreconnected s) (ht : t ∈ s)
    (hV : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) t)
    (hW : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (W r)) t) :
    indexFormIntegrand I γ
        (fun r ↦ V r - (ℝ ∙ curveVelocity I γ r).starProjection (V r))
        (fun r ↦ W r - (ℝ ∙ curveVelocity I γ r).starProjection (W r)) t =
      indexFormIntegrand I γ V W t -
        ⟪alongCurve (leviCivitaConnection I M) γ V t, curveVelocity I γ t⟫_ℝ *
          ⟪alongCurve (leviCivitaConnection I M) γ W t, curveVelocity I γ t⟫_ℝ /
          ‖curveVelocity I γ t‖ ^ 2 := by
  rw [indexFormIntegrand_def, indexFormIntegrand_def,
    hgeo.alongCurve_sub_starProjection_singleton hso hs ht hV,
    hgeo.alongCurve_sub_starProjection_singleton hso hs ht hW,
    Submodule.inner_sub_starProjection_singleton,
    inner_curvatureTensor_sub_starProjection_singleton]
  ring

omit [T2Space M] in
/-- Integrability of `t ↦ ⟪D_t V(t), γ'(t)⟫ * ⟪D_t W(t), γ'(t)⟫` on `a..b` for `C¹` fields `V, W`
on `uIcc a b`. -/
private theorem intervalIntegrable_inner_alongCurve_mul {γ : ℝ → M}
    {V W : ∀ t, TangentSpace I (γ t)} {a b : ℝ}
    (hV : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) (uIcc a b))
    (hW : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (W r)) (uIcc a b)) :
    IntervalIntegrable
      (fun t ↦ ⟪alongCurve (leviCivitaConnection I M) γ V t, curveVelocity I γ t⟫_ℝ *
        ⟪alongCurve (leviCivitaConnection I M) γ W t, curveVelocity I γ t⟫_ℝ) volume a b := by
  rcases eq_or_ne a b with rfl | hab
  · exact IntervalIntegrable.refl
  have hs : UniqueDiffOn ℝ (uIcc a b) := uniqueDiffOn_uIcc hab
  have hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (uIcc a b) :=
    (Bundle.contMDiff_proj (fun x : M ↦ TangentSpace I x) (IB := I) (n := 1)).comp_contMDiffOn hV
  have hvel : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 0
      (fun r ↦ TotalSpace.mk' E (γ r) (curveVelocityWithin I γ (uIcc a b) r)) (uIcc a b) := by
    simpa only [funext (curveVelocityLiftWithin_apply (I := I) γ (uIcc a b))] using
      hγ.contMDiffOn_curveVelocityLiftWithin (m := 0) (by simp) hs.uniqueMDiffOn
  have hcont {U : ∀ t, TangentSpace I (γ t)}
      (hU : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (U r)) (uIcc a b)) :
      ContinuousOn (fun r ↦ ⟪alongCurveWithin (leviCivitaConnection I M) γ U (uIcc a b) r,
        curveVelocityWithin I γ (uIcc a b) r⟫_ℝ) (uIcc a b) :=
    (ContMDiffOn.inner_bundle (IB := I) (F := E) (E := fun x : M ↦ TangentSpace I x) (b := γ)
      (h := IsContMDiffRiemannianBundle.of_le (n := ∞) zero_le)
      (contMDiffOn_alongCurveWithin_leviCivitaConnection (n := 0) (m := ∞) (k := ∞)
        (by simp) (by simp) hs (by simpa using hU)) hvel).continuousOn
  refine ((hcont hV).mul (hcont hW)).intervalIntegrable.congr_uIoo fun t ht ↦ ?_
  have hnhds : uIcc a b ∈ 𝓝 t := mem_of_superset (isOpen_Ioo.mem_nhds ht) uIoo_subset_uIcc_self
  dsimp only [Pi.mul_apply]
  rw [alongCurveWithin_of_mem_nhds _ γ V hnhds, alongCurveWithin_of_mem_nhds _ γ W hnhds,
    curveVelocityWithin_of_mem_nhds hnhds]

/-- **Normal-projection identity for the index form along a geodesic.** If `γ` is a geodesic on
`uIoo a b` of speed `C` and `V, W` have `C¹` lifts on `uIcc a b`, then
`I(V⊥, W⊥) = I(V, W) - (∫_a^b ⟪D_t V, γ'⟫ ⟪D_t W, γ'⟫ dt) / C²`. -/
theorem IsGeodesicCurveOn.indexForm_sub_starProjection_singleton {γ : ℝ → M}
    {V W : ∀ t, TangentSpace I (γ t)} {a b C : ℝ}
    (hgeo : IsGeodesicCurveOn I γ (uIoo a b))
    (hC : ∀ t ∈ uIoo a b, ‖curveVelocity I γ t‖ = C)
    (hV : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) (uIcc a b))
    (hW : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (W r)) (uIcc a b)) :
    indexForm I γ
        (fun r ↦ V r - (ℝ ∙ curveVelocity I γ r).starProjection (V r))
        (fun r ↦ W r - (ℝ ∙ curveVelocity I γ r).starProjection (W r)) a b =
      indexForm I γ V W a b -
        (∫ t in a..b, ⟪alongCurve (leviCivitaConnection I M) γ V t, curveVelocity I γ t⟫_ℝ *
          ⟪alongCurve (leviCivitaConnection I M) γ W t, curveVelocity I γ t⟫_ℝ) / C ^ 2 := by
  have hIint := intervalIntegrable_indexFormIntegrand hV hW
  have hDint := (intervalIntegrable_inner_alongCurve_mul hV hW).div_const (C ^ 2)
  rw [indexForm_def, indexForm_def, ← intervalIntegral.integral_div,
    ← intervalIntegral.integral_sub hIint hDint]
  refine intervalIntegral.integral_congr_uIoo fun t ht ↦ ?_
  have hnhds : uIcc a b ∈ 𝓝 t := mem_of_superset (isOpen_Ioo.mem_nhds ht) uIoo_subset_uIcc_self
  rw [hgeo.indexFormIntegrand_sub_starProjection_singleton isOpen_Ioo isPreconnected_Ioo ht
    ((hV t (uIoo_subset_uIcc_self ht)).contMDiffAt hnhds)
    ((hW t (uIoo_subset_uIcc_self ht)).contMDiffAt hnhds), hC t ht]

/-- Quadratic specialization of `IsGeodesicCurveOn.indexForm_sub_starProjection_singleton`. -/
theorem IsGeodesicCurveOn.indexForm_sub_starProjection_singleton_self {γ : ℝ → M}
    {V : ∀ t, TangentSpace I (γ t)} {a b C : ℝ}
    (hgeo : IsGeodesicCurveOn I γ (uIoo a b))
    (hC : ∀ t ∈ uIoo a b, ‖curveVelocity I γ t‖ = C)
    (hV : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) (uIcc a b)) :
    indexForm I γ
        (fun r ↦ V r - (ℝ ∙ curveVelocity I γ r).starProjection (V r))
        (fun r ↦ V r - (ℝ ∙ curveVelocity I γ r).starProjection (V r)) a b =
      indexForm I γ V V a b -
        (∫ t in a..b,
          ⟪alongCurve (leviCivitaConnection I M) γ V t, curveVelocity I γ t⟫_ℝ ^ 2) / C ^ 2 := by
  simpa only [sq] using hgeo.indexForm_sub_starProjection_singleton hC hV hV

/-- **Tangential degeneracy of the normal-projected index form.** If `V(t)` lies in `ℝ ∙ γ'(t)` on
`uIoo a b`, its normal projection vanishes there and contributes zero to the index form. -/
theorem indexForm_sub_starProjection_eq_zero_of_mem_span {γ : ℝ → M}
    {V W : ∀ t, TangentSpace I (γ t)} {a b : ℝ}
    (htan : ∀ t ∈ uIoo a b, V t ∈ ℝ ∙ curveVelocity I γ t) :
    indexForm I γ (fun r ↦ V r - (ℝ ∙ curveVelocity I γ r).starProjection (V r)) W a b = 0 := by
  refine (indexForm_congr (fun _ _ ↦ rfl) (fun t ht ↦ heq_of_eq ?_)
    (fun _ _ ↦ HEq.rfl)).trans indexForm_zero_left
  rw [Submodule.starProjection_eq_self_iff.mpr (htan t ht), sub_self]
  rfl

end Projection

/-! ### Pointwise second derivative of the speed -/

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {F : ℝ → ℝ → M}

/-- **The second transverse derivative of the speed.** At a parameter `t` where `F` is `C³` and
`γ = F 0` has nonzero velocity, the second derivative at `s = 0` of `s ↦ ‖∂_t F (s, t)‖` is
`(I_γ(V, V)(t) + ⟪D_t A(t), γ'(t)⟫) / ‖γ'(t)‖ - ⟪D_t V(t), γ'(t)⟫² / ‖γ'(t)‖³`. -/
theorem hasDerivAt_deriv_norm_curveVelocity {t : ℝ}
    (hf : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    (hγ : curveVelocity I (F 0) t ≠ 0) :
    HasDerivAt (deriv fun s ↦ ‖curveVelocity I (F s) t‖)
      ((indexFormIntegrand I (F 0) (variationField I F) (variationField I F) t +
          ⟪alongCurve (leviCivitaConnection I M) (F 0)
            (fun r ↦ acceleration (leviCivitaConnection I M) (fun s ↦ F s r) 0) t,
            curveVelocity I (F 0) t⟫_ℝ) / ‖curveVelocity I (F 0) t‖ -
        ⟪alongCurve (leviCivitaConnection I M) (F 0) (variationField I F) t,
          curveVelocity I (F 0) t⟫_ℝ ^ 2 / ‖curveVelocity I (F 0) t‖ ^ 3) 0 := by
  set W := {z : ℝ × ℝ | ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) z}
  have hWo : IsOpen W := TauCeti.isOpen_setOfPred_contMDiffAt (by simp)
  have hG : ContDiffOn ℝ 1 (fun z : ℝ × ℝ ↦ ‖curveVelocity I (F z.1) z.2‖ ^ 2) W :=
    ContMDiffOn.contDiffOn_norm_sq_curveVelocity (fun _ hz ↦ hz.contMDiffWithinAt) (by norm_num) hWo
  have hg : ∀ᶠ s in 𝓝 (0 : ℝ), DifferentiableAt ℝ (fun q ↦ ‖curveVelocity I (F q) t‖ ^ 2) s := by
    filter_upwards [(continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds
      (hWo.mem_nhds hf)] with s hs
    exact ((hG.contDiffAt (hWo.mem_nhds hs)).comp s
      (contDiff_prodMk_left t).contDiffAt).differentiableAt one_ne_zero
  have hc0 : ‖curveVelocity I (F 0) t‖ ≠ 0 := norm_ne_zero_iff.2 hγ
  have hd := TauCeti.hasDerivAt_deriv_sqrt (g := fun q ↦ ‖curveVelocity I (F q) t‖ ^ 2) (t := 0)
    (pow_pos (norm_pos_iff.2 hγ) 2) hg
    (hasDerivAt_norm_sq_curveVelocity (hf.of_le (by norm_num)))
    (hasDerivAt_deriv_norm_sq_curveVelocity hf)
  simp only [Real.sqrt_sq (norm_nonneg _)] at hd
  refine hd.congr_deriv ?_
  field_simp
  ring

/-- Evaluating `hasDerivAt_deriv_norm_curveVelocity` as an iterated `deriv`. -/
theorem deriv_deriv_norm_curveVelocity {t : ℝ}
    (hf : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    (hγ : curveVelocity I (F 0) t ≠ 0) :
    deriv (deriv fun s ↦ ‖curveVelocity I (F s) t‖) 0 =
      (indexFormIntegrand I (F 0) (variationField I F) (variationField I F) t +
          ⟪alongCurve (leviCivitaConnection I M) (F 0)
            (fun r ↦ acceleration (leviCivitaConnection I M) (fun s ↦ F s r) 0) t,
            curveVelocity I (F 0) t⟫_ℝ) / ‖curveVelocity I (F 0) t‖ -
        ⟪alongCurve (leviCivitaConnection I M) (F 0) (variationField I F) t,
          curveVelocity I (F 0) t⟫_ℝ ^ 2 / ‖curveVelocity I (F 0) t‖ ^ 3 :=
  (hasDerivAt_deriv_norm_curveVelocity hf hγ).deriv

/-! ### Differentiating the length integral twice -/

/-- **The second variation of length of a regular curve.** If `F` is `C³` along `{0} × [a, b]` and
`γ = F 0` has nonzero velocity on `[a, b]`, then `s ↦ d/ds L(F s)` is differentiable at `s = 0`,
with derivative equal to the integral of `hasDerivAt_deriv_norm_curveVelocity`. -/
theorem hasDerivAt_deriv_toReal_pathELength_of_curveVelocity_ne_zero {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ t ∈ Icc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    (hγ : ∀ t ∈ Icc a b, curveVelocity I (F 0) t ≠ 0) :
    HasDerivAt (deriv fun s ↦ (Manifold.pathELength I (F s) a b).toReal)
      (∫ t in a..b,
        ((indexFormIntegrand I (F 0) (variationField I F) (variationField I F) t +
            ⟪alongCurve (leviCivitaConnection I M) (F 0)
              (fun r ↦ acceleration (leviCivitaConnection I M) (fun s ↦ F s r) 0) t,
              curveVelocity I (F 0) t⟫_ℝ) / ‖curveVelocity I (F 0) t‖ -
          ⟪alongCurve (leviCivitaConnection I M) (F 0) (variationField I F) t,
            curveVelocity I (F 0) t⟫_ℝ ^ 2 / ‖curveVelocity I (F 0) t‖ ^ 3)) 0 := by
  have : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞)
  rw [← uIcc_of_le hab] at hF hγ
  set W₀ := {z : ℝ × ℝ | ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) z}
  have hW₀o : IsOpen W₀ := TauCeti.isOpen_setOfPred_contMDiffAt (by simp)
  set G : ℝ × ℝ → ℝ := fun z ↦ ‖curveVelocity I (F z.1) z.2‖ ^ 2
  have hG : ContDiffOn ℝ 2 G W₀ :=
    ContMDiffOn.contDiffOn_norm_sq_curveVelocity (fun _ hz ↦ hz.contMDiffWithinAt) (by norm_num)
      hW₀o
  set W := W₀ ∩ G ⁻¹' Ioi 0
  have hWo : IsOpen W := hG.continuousOn.isOpen_inter_preimage hW₀o isOpen_Ioi
  have h0W : {0} ×ˢ uIcc a b ⊆ W := by
    rintro ⟨_, t⟩ ⟨rfl, ht⟩
    exact ⟨hF t ht, pow_pos (norm_pos_iff.2 (hγ t ht)) 2⟩
  obtain ⟨U, V, hUo, hVo, h0U, hV, hUV⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_uIcc hWo h0W
  have hL : ContDiffOn ℝ 2 (fun z : ℝ × ℝ ↦ ‖curveVelocity I (F z.1) z.2‖) W :=
    ((hG.mono inter_subset_left).sqrt fun _ hz ↦ ne_of_gt hz.2).congr fun _ _ ↦
      (Real.sqrt_sq (norm_nonneg _)).symm
  have hlength : (fun s ↦ (Manifold.pathELength I (F s) a b).toReal) =ᶠ[𝓝 0]
      fun s ↦ ∫ t in a..b, ‖curveVelocity I (F s) t‖ := by
    filter_upwards [hUo.mem_nhds (h0U (mem_singleton 0))] with s hs
    have hγs : ContMDiffOn 𝓘(ℝ, ℝ) I 1 (F s) V := fun t ht ↦
      (((hUV ⟨hs, ht⟩).1.of_le (by norm_num)).comp t
        (contDiff_prodMk_right s).contMDiff.contMDiffAt).contMDiffWithinAt
    rw [hγs.pathELength_eq_ofReal_integral_norm_curveVelocityWithin (uIcc_of_le hab ▸ hV),
      ENNReal.toReal_ofReal (intervalIntegral.integral_nonneg hab fun _ _ ↦ norm_nonneg _)]
    exact intervalIntegral.integral_congr fun t ht ↦
      congrArg norm (curveVelocityWithin_of_mem_nhds (hVo.mem_nhds (hV ht)))
  obtain ⟨_, hd⟩ := TauCeti.hasDerivAt_deriv_intervalIntegral_of_contDiffOn hWo hL h0W
  exact (hd.congr_of_eventuallyEq hlength.deriv).congr_deriv
    (intervalIntegral.integral_congr fun t ht ↦ deriv_deriv_norm_curveVelocity (hF t ht) (hγ t ht))

/-! ### The second variation of length for constant-speed curves and geodesics -/

/-- **The second variation of length of a constant-speed curve.** Let `F` be `C³` along
`{0} × [a, b]` and suppose `γ = F 0` has constant speed `C > 0` on `[a, b]`. Then `s ↦ d/ds L(F s)`
is differentiable at `s = 0`, with derivative equal to `1 / C` times the second energy variation
minus `(∫_a^b ⟪D_t V(t), γ'(t)⟫² dt) / C²`. -/
theorem hasDerivAt_deriv_toReal_pathELength {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ t ∈ Icc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    {C : ℝ} (hC : 0 < C) (hγ : ∀ t ∈ Icc a b, ‖curveVelocity I (F 0) t‖ = C) :
    HasDerivAt (deriv fun s ↦ (Manifold.pathELength I (F s) a b).toReal)
      ((indexForm I (F 0) (variationField I F) (variationField I F) a b -
          (∫ t in a..b, ⟪alongCurve (leviCivitaConnection I M) (F 0) (variationField I F) t,
            curveVelocity I (F 0) t⟫_ℝ ^ 2) / C ^ 2 +
          ⟪acceleration (leviCivitaConnection I M) (fun s ↦ F s b) 0,
            curveVelocity I (F 0) b⟫_ℝ -
          ⟪acceleration (leviCivitaConnection I M) (fun s ↦ F s a) 0,
            curveVelocity I (F 0) a⟫_ℝ -
          ∫ t in a..b, ⟪acceleration (leviCivitaConnection I M) (fun s ↦ F s t) 0,
            acceleration (leviCivitaConnection I M) (F 0) t⟫_ℝ) / C) 0 := by
  have hFu : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t) :=
    by rwa [uIcc_of_le hab]
  have hγu : ∀ t ∈ uIcc a b, ‖curveVelocity I (F 0) t‖ = C := by rwa [uIcc_of_le hab]
  have hVl : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1
      (fun r ↦ TotalSpace.mk' E (F 0 r) (variationField I F r)) (uIcc a b) := fun t ht ↦
    ((hFu t ht).contMDiffAt_variationField (m := 1) (by norm_num)).contMDiffWithinAt
  have hE := (hasDerivAt_deriv_energy_eq_integral hFu).unique (hasDerivAt_deriv_energy hFu)
  have hIAdd : IntervalIntegrable
      (fun t ↦ indexFormIntegrand I (F 0) (variationField I F) (variationField I F) t +
        ⟪alongCurve (leviCivitaConnection I M) (F 0)
          (fun r ↦ acceleration (leviCivitaConnection I M) (fun s ↦ F s r) 0) t,
          curveVelocity I (F 0) t⟫_ℝ) volume a b := by
    have hDAl : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 0
        (fun r ↦ TotalSpace.mk' E (F 0 r) (alongCurve (leviCivitaConnection I M) (F 0)
          (fun r ↦ acceleration (leviCivitaConnection I M) (fun s ↦ F s r) 0) r)) (uIcc a b) :=
      fun t ht ↦ (contMDiffAt_alongCurve_leviCivitaConnection (n := 0) (m := ∞) (k := ∞)
        (by simp) (by simp) (contMDiffAt_acceleration_fst (hFu t ht))).contMDiffWithinAt
    have hTl : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 0
        (fun r ↦ TotalSpace.mk' E (F 0 r) (curveVelocity I (F 0) r)) (uIcc a b) := fun t ht ↦
      (((hFu t ht).contMDiffAt_curveVelocity_snd (m := 0) (by norm_num)).comp t
        (contDiff_prodMk_right (0 : ℝ)).contMDiff.contMDiffAt).contMDiffWithinAt
    exact (intervalIntegrable_indexFormIntegrand hVl hVl).add
      ((ContMDiffOn.inner_bundle (IB := I) (F := E) (E := fun x : M ↦ TangentSpace I x) (b := F 0)
        (h := IsContMDiffRiemannianBundle.of_le (n := ∞) zero_le) hDAl hTl
        ).continuousOn.intervalIntegrable)
  have hDsq : IntervalIntegrable
      (fun t ↦ ⟪alongCurve (leviCivitaConnection I M) (F 0) (variationField I F) t,
        curveVelocity I (F 0) t⟫_ℝ ^ 2) volume a b := by
    simpa only [sq] using intervalIntegrable_inner_alongCurve_mul hVl hVl
  refine (hasDerivAt_deriv_toReal_pathELength_of_curveVelocity_ne_zero hab hF fun t ht ↦
    norm_ne_zero_iff.1 (by rw [hγ t ht]; exact hC.ne')).congr_deriv ?_
  rw [intervalIntegral.integral_congr fun t ht ↦ by rw [hγu t ht],
    intervalIntegral.integral_sub (hIAdd.div_const C) (hDsq.div_const (C ^ 3)),
    intervalIntegral.integral_div, intervalIntegral.integral_div, hE]
  have hC' : C ≠ 0 := hC.ne'
  field_simp
  ring

/-- **The second variation of length along a constant-speed geodesic.** For a `C³` variation `F`
with possibly moving endpoints of a geodesic `γ = F 0` on `Ioo a b` having constant speed `C > 0`
on `[a, b]`, the second derivative of the length at `s = 0` is
`(I(V⊥, V⊥) + ⟪A(b), γ'(b)⟫ - ⟪A(a), γ'(a)⟫) / C`. -/
theorem hasDerivAt_deriv_toReal_pathELength_of_isGeodesicCurveOn {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ t ∈ Icc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    {C : ℝ} (hC : 0 < C) (hγ : ∀ t ∈ Icc a b, ‖curveVelocity I (F 0) t‖ = C)
    (hgeo : IsGeodesicCurveOn I (F 0) (Ioo a b)) :
    HasDerivAt (deriv fun s ↦ (Manifold.pathELength I (F s) a b).toReal)
      ((indexForm I (F 0)
          (fun t ↦ variationField I F t -
            (ℝ ∙ curveVelocity I (F 0) t).starProjection (variationField I F t))
          (fun t ↦ variationField I F t -
            (ℝ ∙ curveVelocity I (F 0) t).starProjection (variationField I F t)) a b +
        ⟪acceleration (leviCivitaConnection I M) (fun s ↦ F s b) 0,
          curveVelocity I (F 0) b⟫_ℝ -
        ⟪acceleration (leviCivitaConnection I M) (fun s ↦ F s a) 0,
          curveVelocity I (F 0) a⟫_ℝ) / C) 0 := by
  have hgeou : IsGeodesicCurveOn I (F 0) (uIoo a b) := by rwa [uIoo_of_le hab]
  have hFu : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t) :=
    by rwa [uIcc_of_le hab]
  have hγu : ∀ t ∈ uIoo a b, ‖curveVelocity I (F 0) t‖ = C := fun t ht ↦
    hγ t (uIcc_of_le hab ▸ uIoo_subset_uIcc_self ht)
  have hVl : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1
      (fun r ↦ TotalSpace.mk' E (F 0 r) (variationField I F r)) (uIcc a b) := fun t ht ↦
    ((hFu t ht).contMDiffAt_variationField (m := 1) (by norm_num)).contMDiffWithinAt
  have hint0 : ∫ t in a..b, ⟪acceleration (leviCivitaConnection I M) (fun s ↦ F s t) 0,
      acceleration (leviCivitaConnection I M) (F 0) t⟫_ℝ = 0 :=
    (intervalIntegral.integral_congr_uIoo (g := fun _ ↦ (0 : ℝ)) fun t ht ↦ by
      have hnhds : uIoo a b ∈ 𝓝 t := isOpen_Ioo.mem_nhds ht
      rw [← accelerationWithin_of_mem_nhds _ _ hnhds,
        hgeou.accelerationWithin_eq_zero t ht, inner_zero_right]).trans
      intervalIntegral.integral_zero
  refine (hasDerivAt_deriv_toReal_pathELength hab hF hC hγ).congr_deriv ?_
  rw [← hgeou.indexForm_sub_starProjection_singleton_self hγu hVl, hint0, sub_zero]

/-- **The second variation of length along a constant-speed geodesic**, written as an iterated
`deriv`. -/
theorem deriv_deriv_toReal_pathELength_of_isGeodesicCurveOn {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ t ∈ Icc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    {C : ℝ} (hC : 0 < C) (hγ : ∀ t ∈ Icc a b, ‖curveVelocity I (F 0) t‖ = C)
    (hgeo : IsGeodesicCurveOn I (F 0) (Ioo a b)) :
    deriv (deriv fun s ↦ (Manifold.pathELength I (F s) a b).toReal) 0 =
      (indexForm I (F 0)
          (fun t ↦ variationField I F t -
            (ℝ ∙ curveVelocity I (F 0) t).starProjection (variationField I F t))
          (fun t ↦ variationField I F t -
            (ℝ ∙ curveVelocity I (F 0) t).starProjection (variationField I F t)) a b +
        ⟪acceleration (leviCivitaConnection I M) (fun s ↦ F s b) 0,
          curveVelocity I (F 0) b⟫_ℝ -
        ⟪acceleration (leviCivitaConnection I M) (fun s ↦ F s a) 0,
          curveVelocity I (F 0) a⟫_ℝ) / C :=
  (hasDerivAt_deriv_toReal_pathELength_of_isGeodesicCurveOn hab hF hC hγ hgeo).deriv

/-- **The second variation of length along a unit-speed geodesic.** For a `C³` variation `F` with
possibly moving endpoints of a unit-speed geodesic `γ = F 0` on `[a, b]`,
`d²/ds² L(F s) |₀ = I(V⊥, V⊥) + ⟪A(b), γ'(b)⟫ - ⟪A(a), γ'(a)⟫`, where
`V⊥(t) = V(t) - ⟪V(t), γ'(t)⟫ • γ'(t)`. -/
theorem hasDerivAt_deriv_toReal_pathELength_of_norm_curveVelocity_eq_one {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ t ∈ Icc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    (hγ : ∀ t ∈ Icc a b, ‖curveVelocity I (F 0) t‖ = 1)
    (hgeo : IsGeodesicCurveOn I (F 0) (Ioo a b)) :
    HasDerivAt (deriv fun s ↦ (Manifold.pathELength I (F s) a b).toReal)
      (indexForm I (F 0)
          (fun t ↦ variationField I F t -
            ⟪variationField I F t, curveVelocity I (F 0) t⟫_ℝ • curveVelocity I (F 0) t)
          (fun t ↦ variationField I F t -
            ⟪variationField I F t, curveVelocity I (F 0) t⟫_ℝ • curveVelocity I (F 0) t) a b +
        ⟪acceleration (leviCivitaConnection I M) (fun s ↦ F s b) 0,
          curveVelocity I (F 0) b⟫_ℝ -
        ⟪acceleration (leviCivitaConnection I M) (fun s ↦ F s a) 0,
          curveVelocity I (F 0) a⟫_ℝ) 0 := by
  refine (hasDerivAt_deriv_toReal_pathELength_of_isGeodesicCurveOn hab hF zero_lt_one hγ
    hgeo).congr_deriv ?_
  have hproj : ∀ t ∈ uIoo a b, HEq
      (variationField I F t - (ℝ ∙ curveVelocity I (F 0) t).starProjection (variationField I F t))
      (variationField I F t -
        ⟪variationField I F t, curveVelocity I (F 0) t⟫_ℝ • curveVelocity I (F 0) t) := by
    intro t ht
    apply heq_of_eq
    rw [Submodule.starProjection_singleton, RCLike.ofReal_real_eq_id, id_eq,
      hγ t (uIcc_of_le hab ▸ uIoo_subset_uIcc_self ht), one_pow, div_one, real_inner_comm]
  rw [div_one, indexForm_congr (fun _ _ ↦ rfl) hproj hproj]

/-- **The second variation of length along a unit-speed geodesic**, written as an iterated
`deriv`. -/
theorem deriv_deriv_toReal_pathELength_of_norm_curveVelocity_eq_one {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ t ∈ Icc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    (hγ : ∀ t ∈ Icc a b, ‖curveVelocity I (F 0) t‖ = 1)
    (hgeo : IsGeodesicCurveOn I (F 0) (Ioo a b)) :
    deriv (deriv fun s ↦ (Manifold.pathELength I (F s) a b).toReal) 0 =
      indexForm I (F 0)
          (fun t ↦ variationField I F t -
            ⟪variationField I F t, curveVelocity I (F 0) t⟫_ℝ • curveVelocity I (F 0) t)
          (fun t ↦ variationField I F t -
            ⟪variationField I F t, curveVelocity I (F 0) t⟫_ℝ • curveVelocity I (F 0) t) a b +
        ⟪acceleration (leviCivitaConnection I M) (fun s ↦ F s b) 0,
          curveVelocity I (F 0) b⟫_ℝ -
        ⟪acceleration (leviCivitaConnection I M) (fun s ↦ F s a) 0,
          curveVelocity I (F 0) a⟫_ℝ :=
  (hasDerivAt_deriv_toReal_pathELength_of_norm_curveVelocity_eq_one hab hF hγ hgeo).deriv

/-! ### Normal variations, tangential degeneracy, fixed endpoints, and periodic geodesics -/

/-- **Second variation of length for a normal variation.** When the variation field is orthogonal
to `γ'` on `Ioo a b`, its normal projection is `V` itself and the second variation of length is
`(I(V, V) + ⟪A(b), γ'(b)⟫ - ⟪A(a), γ'(a)⟫) / C`. -/
theorem hasDerivAt_deriv_toReal_pathELength_of_inner_eq_zero {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ t ∈ Icc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    {C : ℝ} (hC : 0 < C) (hγ : ∀ t ∈ Icc a b, ‖curveVelocity I (F 0) t‖ = C)
    (hgeo : IsGeodesicCurveOn I (F 0) (Ioo a b))
    (horth : ∀ t ∈ Ioo a b, ⟪variationField I F t, curveVelocity I (F 0) t⟫_ℝ = 0) :
    HasDerivAt (deriv fun s ↦ (Manifold.pathELength I (F s) a b).toReal)
      ((indexForm I (F 0) (variationField I F) (variationField I F) a b +
        ⟪acceleration (leviCivitaConnection I M) (fun s ↦ F s b) 0,
          curveVelocity I (F 0) b⟫_ℝ -
        ⟪acceleration (leviCivitaConnection I M) (fun s ↦ F s a) 0,
          curveVelocity I (F 0) a⟫_ℝ) / C) 0 := by
  refine (hasDerivAt_deriv_toReal_pathELength_of_isGeodesicCurveOn hab hF hC hγ
    hgeo).congr_deriv ?_
  have hproj : ∀ t ∈ uIoo a b, HEq
      (variationField I F t - (ℝ ∙ curveVelocity I (F 0) t).starProjection (variationField I F t))
      (variationField I F t) := by
    intro t ht
    apply heq_of_eq
    rw [Submodule.starProjection_singleton, RCLike.ofReal_real_eq_id, id_eq, real_inner_comm,
      horth t (uIoo_of_le hab ▸ ht), zero_div, zero_smul, sub_zero]
  rw [indexForm_congr (fun _ _ ↦ rfl) hproj hproj]

/-- **Reparametrization degeneracy of the second variation of length.** For a tangential variation
(`V(t) ∈ ℝ ∙ γ'(t)` on `Ioo a b`), the index-form contribution vanishes and only the endpoint
acceleration pairings remain. -/
theorem hasDerivAt_deriv_toReal_pathELength_of_mem_span_curveVelocity {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ t ∈ Icc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    {C : ℝ} (hC : 0 < C) (hγ : ∀ t ∈ Icc a b, ‖curveVelocity I (F 0) t‖ = C)
    (hgeo : IsGeodesicCurveOn I (F 0) (Ioo a b))
    (htan : ∀ t ∈ Ioo a b, variationField I F t ∈ ℝ ∙ curveVelocity I (F 0) t) :
    HasDerivAt (deriv fun s ↦ (Manifold.pathELength I (F s) a b).toReal)
      ((⟪acceleration (leviCivitaConnection I M) (fun s ↦ F s b) 0,
          curveVelocity I (F 0) b⟫_ℝ -
        ⟪acceleration (leviCivitaConnection I M) (fun s ↦ F s a) 0,
          curveVelocity I (F 0) a⟫_ℝ) / C) 0 := by
  refine (hasDerivAt_deriv_toReal_pathELength_of_isGeodesicCurveOn hab hF hC hγ
    hgeo).congr_deriv ?_
  rw [indexForm_sub_starProjection_eq_zero_of_mem_span (by rwa [uIoo_of_le hab]), zero_add]

namespace IsFixedEndpointVariation

/-- **The second variation of length for a fixed-endpoint variation of a constant-speed geodesic**
is `I(V⊥, V⊥) / C`. -/
theorem hasDerivAt_deriv_toReal_pathELength_of_isGeodesicCurveOn {a b : ℝ} (hab : a ≤ b)
    (hF : IsFixedEndpointVariation I 3 F a b)
    {C : ℝ} (hC : 0 < C) (hγ : ∀ t ∈ Icc a b, ‖curveVelocity I (F 0) t‖ = C)
    (hgeo : IsGeodesicCurveOn I (F 0) (Ioo a b)) :
    HasDerivAt (deriv fun s ↦ (Manifold.pathELength I (F s) a b).toReal)
      (indexForm I (F 0)
        (fun t ↦ variationField I F t -
          (ℝ ∙ curveVelocity I (F 0) t).starProjection (variationField I F t))
        (fun t ↦ variationField I F t -
          (ℝ ∙ curveVelocity I (F 0) t).starProjection (variationField I F t)) a b / C) 0 := by
  refine (TauCeti.Manifold.hasDerivAt_deriv_toReal_pathELength_of_isGeodesicCurveOn hab
    (fun t ht ↦ hF.contMDiffAt t (uIcc_of_le hab ▸ ht)) hC hγ hgeo).congr_deriv ?_
  rw [hF.acceleration_left_eq_zero, hF.acceleration_right_eq_zero, inner_zero_left,
    inner_zero_left, add_zero, sub_zero]

/-- **The second variation of length for a fixed-endpoint variation of a constant-speed geodesic**,
written as an iterated `deriv`. -/
theorem deriv_deriv_toReal_pathELength_of_isGeodesicCurveOn {a b : ℝ} (hab : a ≤ b)
    (hF : IsFixedEndpointVariation I 3 F a b)
    {C : ℝ} (hC : 0 < C) (hγ : ∀ t ∈ Icc a b, ‖curveVelocity I (F 0) t‖ = C)
    (hgeo : IsGeodesicCurveOn I (F 0) (Ioo a b)) :
    deriv (deriv fun s ↦ (Manifold.pathELength I (F s) a b).toReal) 0 =
      indexForm I (F 0)
        (fun t ↦ variationField I F t -
          (ℝ ∙ curveVelocity I (F 0) t).starProjection (variationField I F t))
        (fun t ↦ variationField I F t -
          (ℝ ∙ curveVelocity I (F 0) t).starProjection (variationField I F t)) a b / C :=
  (hF.hasDerivAt_deriv_toReal_pathELength_of_isGeodesicCurveOn hab hC hγ hgeo).deriv

/-- For a fixed-endpoint tangential variation of a constant-speed geodesic, the second derivative
of the length at `s = 0` vanishes. -/
theorem hasDerivAt_deriv_toReal_pathELength_of_mem_span_curveVelocity {a b : ℝ} (hab : a ≤ b)
    (hF : IsFixedEndpointVariation I 3 F a b)
    {C : ℝ} (hC : 0 < C) (hγ : ∀ t ∈ Icc a b, ‖curveVelocity I (F 0) t‖ = C)
    (hgeo : IsGeodesicCurveOn I (F 0) (Ioo a b))
    (htan : ∀ t ∈ Ioo a b, variationField I F t ∈ ℝ ∙ curveVelocity I (F 0) t) :
    HasDerivAt (deriv fun s ↦ (Manifold.pathELength I (F s) a b).toReal) 0 0 := by
  refine (hF.hasDerivAt_deriv_toReal_pathELength_of_isGeodesicCurveOn hab hC hγ
    hgeo).congr_deriv ?_
  rw [indexForm_sub_starProjection_eq_zero_of_mem_span (by rwa [uIoo_of_le hab]), zero_div]

/-- **Necessary second-order condition at a local minimum of length.** Along a constant-speed
geodesic that locally minimizes length for a `C³` fixed-endpoint variation `F`, the index form of
the normal component `V⊥` is nonnegative. -/
theorem indexForm_sub_starProjection_nonneg_of_isLocalMin_pathELength {a b : ℝ} (hab : a ≤ b)
    (hF : IsFixedEndpointVariation I 3 F a b)
    {C : ℝ} (hC : 0 < C) (hγ : ∀ t ∈ Icc a b, ‖curveVelocity I (F 0) t‖ = C)
    (hgeo : IsGeodesicCurveOn I (F 0) (Ioo a b))
    (hmin : IsLocalMin (fun s ↦ (Manifold.pathELength I (F s) a b).toReal) 0) :
    0 ≤ indexForm I (F 0)
      (fun t ↦ variationField I F t -
        (ℝ ∙ curveVelocity I (F 0) t).starProjection (variationField I F t))
      (fun t ↦ variationField I F t -
        (ℝ ∙ curveVelocity I (F 0) t).starProjection (variationField I F t)) a b := by
  have : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by simp)
  have : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le (n := ∞) (by simp)
  have hcont := (hasDerivAt_toReal_pathELength hab
    (fun t ht ↦ (hF.of_le (by norm_num)).contMDiffAt t (uIcc_of_le hab ▸ ht)) hC hγ).continuousAt
  have hdiv : 0 ≤ deriv (deriv fun s ↦ (Manifold.pathELength I (F s) a b).toReal) 0 :=
    TauCeti.deriv_deriv_nonneg_of_isLocalMin hcont hmin
  rw [hF.deriv_deriv_toReal_pathELength_of_isGeodesicCurveOn hab hC hγ hgeo,
    div_nonneg_iff] at hdiv
  exact (hdiv.resolve_right fun h ↦ not_le_of_gt hC h.2).1

end IsFixedEndpointVariation

/-- **The second variation of length for a periodic variation of a closed geodesic.** When `F s a =
F s b` near `s = 0` and `(F 0 a, γ'(a)) = (F 0 b, γ'(b))`, the endpoint acceleration pairings
cancel and `d²/ds² L(F s) |₀ = I(V⊥, V⊥) / C`. -/
theorem hasDerivAt_deriv_toReal_pathELength_of_periodic {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ t ∈ Icc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    {C : ℝ} (hC : 0 < C) (hγ : ∀ t ∈ Icc a b, ‖curveVelocity I (F 0) t‖ = C)
    (hgeo : IsGeodesicCurveOn I (F 0) (Ioo a b))
    (hper : ∀ᶠ s in 𝓝 0, F s a = F s b)
    (hvel : TotalSpace.mk' E (F 0 a) (curveVelocity I (F 0) a) =
      TotalSpace.mk' E (F 0 b) (curveVelocity I (F 0) b)) :
    HasDerivAt (deriv fun s ↦ (Manifold.pathELength I (F s) a b).toReal)
      (indexForm I (F 0)
        (fun t ↦ variationField I F t -
          (ℝ ∙ curveVelocity I (F 0) t).starProjection (variationField I F t))
        (fun t ↦ variationField I F t -
          (ℝ ∙ curveVelocity I (F 0) t).starProjection (variationField I F t)) a b / C) 0 := by
  have hacc := Filter.EventuallyEq.totalSpaceMk_acceleration_eq (leviCivitaConnection I M) hper
  have hinner :
      ⟪acceleration (leviCivitaConnection I M) (fun s ↦ F s a) 0, curveVelocity I (F 0) a⟫_ℝ =
      ⟪acceleration (leviCivitaConnection I M) (fun s ↦ F s b) 0, curveVelocity I (F 0) b⟫_ℝ :=
    TauCeti.inner_tangentSpace_congr (mem_of_mem_nhds hper)
      (congrArg TotalSpace.snd hacc) (congrArg TotalSpace.snd hvel)
  refine (hasDerivAt_deriv_toReal_pathELength_of_isGeodesicCurveOn hab hF hC hγ
    hgeo).congr_deriv ?_
  rw [hinner, add_sub_cancel_right]

/-- **The second variation of length for a periodic variation of a closed geodesic**, written as
an iterated `deriv`. -/
theorem deriv_deriv_toReal_pathELength_of_periodic {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ t ∈ Icc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    {C : ℝ} (hC : 0 < C) (hγ : ∀ t ∈ Icc a b, ‖curveVelocity I (F 0) t‖ = C)
    (hgeo : IsGeodesicCurveOn I (F 0) (Ioo a b))
    (hper : ∀ᶠ s in 𝓝 0, F s a = F s b)
    (hvel : TotalSpace.mk' E (F 0 a) (curveVelocity I (F 0) a) =
      TotalSpace.mk' E (F 0 b) (curveVelocity I (F 0) b)) :
    deriv (deriv fun s ↦ (Manifold.pathELength I (F s) a b).toReal) 0 =
      indexForm I (F 0)
        (fun t ↦ variationField I F t -
          (ℝ ∙ curveVelocity I (F 0) t).starProjection (variationField I F t))
        (fun t ↦ variationField I F t -
          (ℝ ∙ curveVelocity I (F 0) t).starProjection (variationField I F t)) a b / C :=
  (hasDerivAt_deriv_toReal_pathELength_of_periodic hab hF hC hγ hgeo hper hvel).deriv

/-- **Nonnegativity of the normal index form at a periodic local minimum of length.** -/
theorem indexForm_sub_starProjection_nonneg_of_isLocalMin_pathELength_of_periodic
    {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ t ∈ Icc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    {C : ℝ} (hC : 0 < C) (hγ : ∀ t ∈ Icc a b, ‖curveVelocity I (F 0) t‖ = C)
    (hgeo : IsGeodesicCurveOn I (F 0) (Ioo a b))
    (hper : ∀ᶠ s in 𝓝 0, F s a = F s b)
    (hvel : TotalSpace.mk' E (F 0 a) (curveVelocity I (F 0) a) =
      TotalSpace.mk' E (F 0 b) (curveVelocity I (F 0) b))
    (hmin : IsLocalMin (fun s ↦ (Manifold.pathELength I (F s) a b).toReal) 0) :
    0 ≤ indexForm I (F 0)
      (fun t ↦ variationField I F t -
        (ℝ ∙ curveVelocity I (F 0) t).starProjection (variationField I F t))
      (fun t ↦ variationField I F t -
        (ℝ ∙ curveVelocity I (F 0) t).starProjection (variationField I F t)) a b := by
  have : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by simp)
  have : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le (n := ∞) (by simp)
  have hcont := (hasDerivAt_toReal_pathELength hab
    (fun t ht ↦ (hF t ht).of_le (by norm_num)) hC hγ).continuousAt
  have hdiv : 0 ≤ deriv (deriv fun s ↦ (Manifold.pathELength I (F s) a b).toReal) 0 :=
    TauCeti.deriv_deriv_nonneg_of_isLocalMin hcont hmin
  rw [deriv_deriv_toReal_pathELength_of_periodic hab hF hC hγ hgeo hper hvel,
    div_nonneg_iff] at hdiv
  exact (hdiv.resolve_right fun h ↦ not_le_of_gt hC h.2).1

end TauCeti.Manifold
