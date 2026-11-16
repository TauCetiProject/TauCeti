/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.IndexForm.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Tangential
import TauCeti.Analysis.InnerProductSpace.Projection.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Metric

/-!
# Tangential and normal splitting of the index form along a geodesic

Along a geodesic `γ`, covariant differentiation commutes with the orthogonal projection onto the
normal complement of `ℝ ∙ γ'(t)`
(`TauCeti.Manifold.IsGeodesicCurveOn.alongCurveWithin_sub_starProjection_singleton` and
`TauCeti.Manifold.IsGeodesicCurveOn.alongCurve_sub_starProjection_singleton`), while skew-symmetry
of the Riemann curvature tensor makes `⟪R(u, γ') γ', v⟫` invariant under projecting `u` and `v`
orthogonally away from `ℝ ∙ γ'`. Subtracting the tangential components from two tangent fields `V`
and `W` therefore leaves the curvature term of the index-form integrand unchanged and subtracts
`⟪D_t V, γ'⟫ ⟪D_t W, γ'⟫ / ‖γ'‖²` from the kinetic term.

Integrating along a geodesic on `uIoo a b` of constant speed `C` gives the normal-projection
identity

`I(V⊥, W⊥) = I(V, W) - (∫_a^b ⟪D_t V, γ'⟫ ⟪D_t W, γ'⟫ dt) / C²`

for `C¹` fields `V, W` on `uIcc a b` (holding trivially for `C = 0` as well via `0 / 0 = 0`).
In particular, any field lying pointwise in `ℝ ∙ γ'(t)` on `uIoo a b` is annihilated in either
slot after normal projection.

## Main results

* `TauCeti.Manifold.IsGeodesicCurveOn.indexFormIntegrandWithin_sub_starProjection_singleton` and
  `TauCeti.Manifold.IsGeodesicCurveOn.indexFormIntegrand_sub_starProjection_singleton`: pointwise
  normal-projection identities for the within-set and unrestricted index-form integrands.
* `TauCeti.Manifold.intervalIntegrable_inner_alongCurve_mul`: interval integrability of
  `t ↦ ⟪D_t V(t), γ'(t)⟫ ⟪D_t W(t), γ'(t)⟫` for `C¹` fields `V, W` on `uIcc a b`.
* `TauCeti.Manifold.IsGeodesicCurveOn.indexForm_sub_starProjection_singleton` and
  `TauCeti.Manifold.IsGeodesicCurveOn.indexForm_sub_starProjection_singleton_self`: normal-projected
  index form along a geodesic of speed `C`.
* `TauCeti.Manifold.indexForm_sub_starProjection_singleton_left_eq_zero_of_mem_span` and
  `TauCeti.Manifold.indexForm_sub_starProjection_singleton_right_eq_zero_of_mem_span`: vanishing of
  the normal-projected index form on tangential fields.

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Chapter 10.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 10.
-/

public section

noncomputable section

open Bundle CovariantDerivative Filter MeasureTheory Set
open scoped ContDiff InnerProductSpace Manifold Topology

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- **Within-set normal-projection identity for the index-form integrand.** Along a geodesic on a
preconnected set `s`, projecting `V` and `W` orthogonally away from `ℝ ∙ γ'` subtracts
`⟪D_t V, γ'⟫ ⟪D_t W, γ'⟫ / ‖γ'‖²` from `indexFormIntegrandWithin`. -/
theorem IsGeodesicCurveOn.indexFormIntegrandWithin_sub_starProjection_singleton
    {γ : ℝ → M} {V W : ∀ t, TangentSpace I (γ t)} {s : Set ℝ} {t : ℝ}
    (hgeo : IsGeodesicCurveOn I γ s) (hs : IsPreconnected s) (ht : t ∈ s)
    (hV : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ V (γ t)) s t)
    (hW : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ W (γ t)) s t) :
    indexFormIntegrandWithin I γ
        (fun r ↦ V r - (ℝ ∙ curveVelocityWithin I γ s r).starProjection (V r))
        (fun r ↦ W r - (ℝ ∙ curveVelocityWithin I γ s r).starProjection (W r)) s t =
      indexFormIntegrandWithin I γ V W s t -
        ⟪alongCurveWithin (leviCivitaConnection I M) γ V s t, curveVelocityWithin I γ s t⟫_ℝ *
          ⟪alongCurveWithin (leviCivitaConnection I M) γ W s t, curveVelocityWithin I γ s t⟫_ℝ /
          ‖curveVelocityWithin I γ s t‖ ^ 2 := by
  rw [indexFormIntegrandWithin_def, indexFormIntegrandWithin_def,
    hgeo.alongCurveWithin_sub_starProjection_singleton hs ht hV,
    hgeo.alongCurveWithin_sub_starProjection_singleton hs ht hW,
    Submodule.inner_sub_starProjection_singleton, RCLike.ofReal_real_eq_id, id_eq,
    real_inner_comm (alongCurveWithin (leviCivitaConnection I M) γ W s t)
      (curveVelocityWithin I γ s t),
    (isMetricCompatible_leviCivitaConnection (I := I) (M := M)
      ).inner_curvatureTensor_sub_starProjection_singleton]
  ring

/-- **Pointwise normal-projection identity for the index-form integrand.** Along a curve that is a
geodesic near `t`, projecting `V` and `W` orthogonally away from `ℝ ∙ γ'` subtracts
`⟪D_t V, γ'⟫ ⟪D_t W, γ'⟫ / ‖γ'‖²` from `indexFormIntegrand`. -/
theorem IsGeodesicCurveOn.indexFormIntegrand_sub_starProjection_singleton
    {γ : ℝ → M} {V W : ∀ t, TangentSpace I (γ t)} {s : Set ℝ} {t : ℝ}
    (hgeo : IsGeodesicCurveOn I γ s) (hs : s ∈ 𝓝 t)
    (hV : DifferentiableAt ℝ (sectionCoord (F := E) γ V (γ t)) t)
    (hW : DifferentiableAt ℝ (sectionCoord (F := E) γ W (γ t)) t) :
    indexFormIntegrand I γ
        (fun r ↦ V r - (ℝ ∙ curveVelocity I γ r).starProjection (V r))
        (fun r ↦ W r - (ℝ ∙ curveVelocity I γ r).starProjection (W r)) t =
      indexFormIntegrand I γ V W t -
        ⟪alongCurve (leviCivitaConnection I M) γ V t, curveVelocity I γ t⟫_ℝ *
          ⟪alongCurve (leviCivitaConnection I M) γ W t, curveVelocity I γ t⟫_ℝ /
          ‖curveVelocity I γ t‖ ^ 2 := by
  rw [indexFormIntegrand_def, indexFormIntegrand_def,
    hgeo.alongCurve_sub_starProjection_singleton hs hV,
    hgeo.alongCurve_sub_starProjection_singleton hs hW,
    Submodule.inner_sub_starProjection_singleton, RCLike.ofReal_real_eq_id, id_eq,
    real_inner_comm (alongCurve (leviCivitaConnection I M) γ W t) (curveVelocity I γ t),
    (isMetricCompatible_leviCivitaConnection (I := I) (M := M)
      ).inner_curvatureTensor_sub_starProjection_singleton]
  ring

omit [T2Space M] in
/-- Integrability of `t ↦ ⟪D_t V(t), γ'(t)⟫ * ⟪D_t W(t), γ'(t)⟫` on `a..b` for `C¹` fields `V, W`
on `uIcc a b`. -/
theorem intervalIntegrable_inner_alongCurve_mul {γ : ℝ → M}
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
  have hVd := differentiableAt_sectionCoord γ V
    (((hV t (uIoo_subset_uIcc_self ht)).contMDiffAt hnhds).mdifferentiableAt one_ne_zero)
    (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t))
  have hWd := differentiableAt_sectionCoord γ W
    (((hW t (uIoo_subset_uIcc_self ht)).contMDiffAt hnhds).mdifferentiableAt one_ne_zero)
    (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t))
  rw [hgeo.indexFormIntegrand_sub_starProjection_singleton (isOpen_Ioo.mem_nhds ht) hVd hWd,
    hC t ht]

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

/-- **Tangential degeneracy of the normal-projected index form in the left slot.** If `V(t)` lies in
`ℝ ∙ γ'(t)` on `uIoo a b`, its normal projection vanishes there and contributes zero to the index
form. -/
theorem indexForm_sub_starProjection_singleton_left_eq_zero_of_mem_span {γ : ℝ → M}
    {V W : ∀ t, TangentSpace I (γ t)} {a b : ℝ}
    (htan : ∀ t ∈ uIoo a b, V t ∈ ℝ ∙ curveVelocity I γ t) :
    indexForm I γ (fun r ↦ V r - (ℝ ∙ curveVelocity I γ r).starProjection (V r)) W a b = 0 := by
  refine (indexForm_congr (fun _ _ ↦ rfl) (fun t ht ↦ heq_of_eq ?_)
    (fun _ _ ↦ HEq.rfl)).trans indexForm_zero_left
  rw [Submodule.starProjection_eq_self_iff.mpr (htan t ht), sub_self]
  rfl

/-- **Tangential degeneracy of the normal-projected index form in the right slot.** If `W(t)` lies
in `ℝ ∙ γ'(t)` on `uIoo a b`, its normal projection vanishes there and contributes zero to the index
form. -/
theorem indexForm_sub_starProjection_singleton_right_eq_zero_of_mem_span {γ : ℝ → M}
    {V W : ∀ t, TangentSpace I (γ t)} {a b : ℝ}
    (htan : ∀ t ∈ uIoo a b, W t ∈ ℝ ∙ curveVelocity I γ t) :
    indexForm I γ V (fun r ↦ W r - (ℝ ∙ curveVelocity I γ r).starProjection (W r)) a b = 0 := by
  rw [indexForm_comm]
  exact indexForm_sub_starProjection_singleton_left_eq_zero_of_mem_span htan

end TauCeti.Manifold

end
