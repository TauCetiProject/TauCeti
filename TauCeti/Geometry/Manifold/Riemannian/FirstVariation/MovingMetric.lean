/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.VariationField
public import TauCeti.Geometry.Manifold.MFDeriv.Parametric.Basic
public import TauCeti.Geometry.Manifold.ContMDiff.Prod
public import TauCeti.Analysis.Calculus.ParametricIntegral.Basic
public import TauCeti.Analysis.Calculus.ParametricFDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# First variation of an intrinsic action for a moving metric

For `A(γ) = ∫ (g_t(γ', γ') / 2 + U(t, γ)) dt`, integration by parts gives both endpoint
momenta and the interior pairing with the covariant acceleration, the metric time derivative,
and the spatial differential of the potential. Each covariant derivative uses the native
Levi-Civita connection of the metric frozen at that time.

The metric time derivative is specified by an actual `HasDerivAt` of its pairing with the
variation field and velocity. Joint `C¹` metric and potential regularity is required only
along the central path; the variation is `C²` along the compact parameter segment. Endpoints
are unrestricted and either orientation of the interval is allowed.

This intrinsic adapter reuses the native fixed-metric variation formulas and parametric
integration. It does not require a chart representation of the path action.

## Main declarations

* `TauCeti.Manifold.movingMetricAction`: kinetic action with a scalar potential.
* `TauCeti.Manifold.hasDerivAt_movingMetric_boundaryPairing`: the moving-metric product rule.
* `TauCeti.Manifold.hasDerivAt_movingMetricAction`: the first variation with both endpoints.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Chapter 6.
* The reduced-action development in `frenzymath/lean-eval-submissions` and
  `frenzymath/PoincareConjecture`.
-/

public section

open Bundle CovariantDerivative Filter MeasureTheory Set TauCeti.Manifold
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  {F : ℝ → ℝ → M}
  {g : ℝ → ContMDiffRiemannianMetric I 1 E (fun x : M ↦ TangentSpace I x)}

variable (I g) in
/-- The action of a path for a time-dependent Riemannian metric and scalar potential,
with kinetic energy normalized by `1 / 2`. -/
def movingMetricAction (U : ℝ → M → ℝ) (γ : ℝ → M) (a b : ℝ) : ℝ :=
  ∫ t in a..b, (g t).inner (γ t) (curveVelocity I γ t) (curveVelocity I γ t) / 2 + U t (γ t)

variable (I g) in
/-- The defining integral of the moving-metric action. -/
@[simp] theorem movingMetricAction_def (U : ℝ → M → ℝ) (γ : ℝ → M) (a b : ℝ) :
    movingMetricAction I g U γ a b =
      ∫ t in a..b, (g t).inner (γ t) (curveVelocity I γ t) (curveVelocity I γ t) / 2 +
        U t (γ t) := by
  rfl

variable [FiniteDimensional ℝ E]

/-- The transverse kinetic derivative with the metric frozen at curve time. -/
private theorem frozen_speed_derivative {t : ℝ}
    (hf : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t)) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩
    HasDerivAt (fun u ↦ (g t).inner (F u t) (curveVelocity I (F u) t)
      (curveVelocity I (F u) t))
      (2 * inner ℝ (alongCurve (leviCivitaConnection I M) (F 0) (variationField I F) t)
        (curveVelocity I (F 0) t)) 0 := by
  let : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩
  exact (hasDerivAt_norm_sq_curveVelocity hf).congr_of_eventuallyEq
    (Eventually.of_forall fun u ↦ by
      -- The installed bundle identifies this metric pairing with the native inner product.
      change inner ℝ (curveVelocity I (F u) t) (curveVelocity I (F u) t) = _
      exact real_inner_self_eq_norm_sq _)

omit [FiniteDimensional ℝ E] in
/-- The moving kinetic density is jointly C¹ near the central variation slice. -/
private theorem contDiffAt_moving_speed {t : ℝ}
    (hg : ContMDiffAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 1
      (fun p : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
        p.2 ((g p.1).inner p.2)) (t, F 0 t))
    (hF : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t)) :
    ContDiffAt ℝ 1 (fun z : ℝ × ℝ ↦ (g z.2).inner (F z.1 z.2)
      (curveVelocity I (F z.1) z.2) (curveVelocity I (F z.1) z.2)) (0, t) := by
  have hbase : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) (𝓘(ℝ, ℝ).prod I) 1
      (fun z : ℝ × ℝ ↦ (z.2, F z.1 z.2)) (0, t) :=
    (contDiff_snd.contMDiff.contMDiffAt).prodMk (hF.of_le (by norm_num))
  have hv := hF.contMDiffAt_curveVelocity_snd (m := 1) (by norm_num)
  have h := (hg.comp (0, t) hbase).clm_bundle_apply₂
    (F₃ := ℝ) (E₃ := fun _ : M ↦ ℝ) hv hv
  exact (contMDiffAt_totalSpace_iff.mp h).2.contDiffAt

omit [FiniteDimensional ℝ E] in
/-- The moving endpoint pairing is jointly C¹ in metric time and curve time. -/
private theorem contDiffAt_moving_boundary {t : ℝ}
    (hg : ContMDiffAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 1
      (fun p : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
        p.2 ((g p.1).inner p.2)) (t, F 0 t))
    (hF : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t)) :
    ContDiffAt ℝ 1 (fun z : ℝ × ℝ ↦ (g z.1).inner (F 0 z.2)
      (variationField I F z.2) (curveVelocity I (F 0) z.2)) (t, t) := by
  have hα : ContMDiffAt 𝓘(ℝ, ℝ) I 2 (F 0) t :=
    hF.comp t (contDiff_prodMk_right (0 : ℝ)).contMDiff.contMDiffAt
  have hbase : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) (𝓘(ℝ, ℝ).prod I) 1
      (fun z : ℝ × ℝ ↦ (z.1, F 0 z.2)) (t, t) :=
    (contDiff_fst.contMDiff.contMDiffAt).prodMk
      ((hα.of_le (by norm_num)).comp (t, t) contDiff_snd.contMDiff.contMDiffAt)
  have hV : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I.tangent 1
      (fun z : ℝ × ℝ ↦ TotalSpace.mk' E (F 0 z.2) (variationField I F z.2)) (t, t) :=
    (hF.contMDiffAt_variationField (m := 1) (by norm_num)).comp (t, t)
      contDiff_snd.contMDiff.contMDiffAt
  have hα' : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ F 0 z.2) (t, t) :=
    hα.comp (t, t) contDiff_snd.contMDiff.contMDiffAt
  have hv := hα'.contMDiffAt_curveVelocity_snd (f := fun _ r ↦ F 0 r) (m := 1)
    (by norm_num)
  have h := (hg.comp (t, t) hbase).clm_bundle_apply₂
    (F₃ := ℝ) (E₃ := fun _ : M ↦ ℝ) hV hv
  exact (contMDiffAt_totalSpace_iff.mp h).2.contDiffAt

/-- The derivative of `g_t(V(t), γ'(t))` contains the metric time derivative and the two
native covariant product-rule terms, for the Levi-Civita connection of `g_t`. -/
theorem hasDerivAt_movingMetric_boundaryPairing {t h : ℝ}
    (hg : ContMDiffAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 1
      (fun p : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
        p.2 ((g p.1).inner p.2)) (t, F 0 t))
    (hF : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    (ht : HasDerivAt (fun r ↦ (g r).inner (F 0 t) (variationField I F t)
      (curveVelocity I (F 0) t)) h t) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩
    HasDerivAt (fun r ↦ (g r).inner (F 0 r) (variationField I F r)
      (curveVelocity I (F 0) r))
      (h + inner ℝ (alongCurve (leviCivitaConnection I M) (F 0) (variationField I F) t)
        (curveVelocity I (F 0) t) + inner ℝ (variationField I F t)
        (acceleration (leviCivitaConnection I M) (F 0) t)) t := by
  let : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩
  let K : ℝ × ℝ → ℝ := fun z ↦ (g z.1).inner (F 0 z.2)
    (variationField I F z.2) (curveVelocity I (F 0) z.2)
  have hK : DifferentiableAt ℝ K (t, t) :=
    (contDiffAt_moving_boundary hg hF).differentiableAt one_ne_zero
  have htime : fderiv ℝ K (t, t) (1, 0) = h := by
    simpa only [timeFDeriv_apply] using (hasDerivAt_parameterCurve hK).unique ht
  have hfixed := hasDerivAt_inner_variationField_curveVelocity hF
  have hspace : fderiv ℝ K (t, t) (0, 1) =
      inner ℝ (alongCurve (leviCivitaConnection I M) (F 0) (variationField I F) t)
        (curveVelocity I (F 0) t) + inner ℝ (variationField I F t)
        (acceleration (leviCivitaConnection I M) (F 0) t) :=
    -- The abbreviation `K` selects the frozen spatial slice for the native chain rule.
    (show HasDerivAt (fun r ↦ K (t, r)) (fderiv ℝ K (t, t) (0, 1)) t by
      simpa only [spatialFDeriv_apply] using (hasFDerivAt_timeSlice hK).hasDerivAt).unique hfixed
  have hdiag := TauCeti.hasDerivAt_comp_prodMk hK (hasDerivAt_id t)
  simpa only [id_eq, timeFDeriv_apply, spatialFDeriv_apply, htime, hspace, add_assoc] using hdiag

/-- The transverse density derivative combines the frozen kinetic and potential terms. -/
private theorem action_density_derivative {t : ℝ} {U : ℝ → M → ℝ}
    (hF : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    (hU : MDifferentiableAt I 𝓘(ℝ, ℝ) (U t) (F 0 t)) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩
    HasDerivAt (fun u ↦ (g t).inner (F u t) (curveVelocity I (F u) t)
      (curveVelocity I (F u) t) / 2 + U t (F u t))
      (inner ℝ (alongCurve (leviCivitaConnection I M) (F 0) (variationField I F) t)
        (curveVelocity I (F 0) t) + mvfderiv I (U t) (F 0 t) (variationField I F t)) 0 := by
  let : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩
  have hcurve : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun u ↦ F u t) 0 :=
    (hF.comp 0 (contDiff_prodMk_left t).contMDiff.contMDiffAt).mdifferentiableAt two_ne_zero
  have hpot := hasDerivAt_comp_curve (γ := fun u ↦ F u t) (t := 0) hU
    (hasMFDerivAt_curveVelocity hcurve)
  have hspeed : HasDerivAt (fun u ↦ (g t).inner (F u t)
      (curveVelocity I (F u) t) (curveVelocity I (F u) t))
      (2 * inner ℝ (alongCurve (leviCivitaConnection I M) (F 0)
        (variationField I F) t) (curveVelocity I (F 0) t)) 0 :=
    frozen_speed_derivative (g := g) hF
  have h := (hspeed.div_const 2).add hpot
  apply h.congr_deriv
  rw [variationField_apply]
  ring

/-- The pointwise integration-by-parts identity and its required regularity. -/
private theorem movingMetricAction_pointwise {a b : ℝ} {U : ℝ → M → ℝ} {h : ℝ → ℝ}
    (hF : ∀ t ∈ uIcc a b,
      ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    (hg : ∀ t ∈ uIcc a b,
      ContMDiffAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 1
        (fun p : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
          p.2 ((g p.1).inner p.2)) (t, F 0 t))
    (hU : ∀ t ∈ uIcc a b,
      ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (fun p : ℝ × M ↦ U p.1 p.2)
        (t, F 0 t))
    (ht : ∀ t ∈ uIcc a b, HasDerivAt (fun r ↦ (g r).inner (F 0 t) (variationField I F t)
      (curveVelocity I (F 0) t)) (h t) t) :
    let G : ℝ × ℝ → ℝ := fun z ↦ (g z.2).inner (F z.1 z.2)
      (curveVelocity I (F z.1) z.2) (curveVelocity I (F z.1) z.2) / 2 + U z.2 (F z.1 z.2)
    let K : ℝ → ℝ := fun t ↦ (g t).inner (F 0 t) (variationField I F t)
      (curveVelocity I (F 0) t)
    let R : ℝ → ℝ := fun t ↦
      letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩
      inner ℝ (variationField I F t) (acceleration (leviCivitaConnection I M) (F 0) t) +
        h t - mvfderiv I (U t) (F 0 t) (variationField I F t)
    (∀ t ∈ uIcc a b, ContDiffAt ℝ 1 G (0, t)) ∧
      (∀ t ∈ uIcc a b, ContDiffAt ℝ 1 K t) ∧
      (∀ t ∈ uIcc a b, fderiv ℝ G (0, t) (1, 0) = deriv K t - R t) := by
  let G : ℝ × ℝ → ℝ := fun z ↦ (g z.2).inner (F z.1 z.2)
    (curveVelocity I (F z.1) z.2) (curveVelocity I (F z.1) z.2) / 2 + U z.2 (F z.1 z.2)
  let K : ℝ → ℝ := fun t ↦ (g t).inner (F 0 t) (variationField I F t)
    (curveVelocity I (F 0) t)
  let R : ℝ → ℝ := fun t ↦
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩
    inner ℝ (variationField I F t) (acceleration (leviCivitaConnection I M) (F 0) t) +
      h t - mvfderiv I (U t) (F 0 t) (variationField I F t)
  have hG : ∀ t ∈ uIcc a b, ContDiffAt ℝ 1 G (0, t) := by
    intro t ht'
    exact ((contDiffAt_moving_speed (hg t ht') (hF t ht')).div_const 2).add
      (((hU t ht').comp (0, t)
        (contDiff_snd.contMDiff.contMDiffAt.prodMk ((hF t ht').of_le (by norm_num)))).contDiffAt)
  have hK : ∀ t ∈ uIcc a b, ContDiffAt ℝ 1 K t := by
    intro t ht'
    exact (contDiffAt_moving_boundary (hg t ht') (hF t ht')).comp
      (f := fun r : ℝ ↦ (r, r)) t (contDiffAt_id.prodMk contDiffAt_id)
  have hid : ∀ t ∈ uIcc a b, fderiv ℝ G (0, t) (1, 0) = deriv K t - R t := by
    intro t ht'
    let : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩
    have hsp : MDifferentiableAt I 𝓘(ℝ, ℝ) (U t) (F 0 t) :=
      ((hU t ht').comp (F 0 t) (contMDiffAt_const.prodMk contMDiffAt_id)).mdifferentiableAt
        one_ne_zero
    have hraw := (hasDerivAt_parameterCurve ((hG t ht').differentiableAt one_ne_zero)).unique
      (action_density_derivative (hF t ht') hsp)
    have hboundary :=
      (hasDerivAt_movingMetric_boundaryPairing (hg t ht') (hF t ht') (ht t ht')).deriv
    -- Only the local abbreviation hides the moving boundary pairing from the derivative.
    change deriv K t = _ at hboundary
    simp only [timeFDeriv_apply] at hraw
    dsimp only [R]
    rw [hraw, hboundary]
    ring
  exact ⟨hG, hK, hid⟩

/-- First variation of the moving-metric action: terminal momentum minus initial momentum,
minus the integral of the acceleration, metric time derivative, and negative potential differential.
No endpoint is required to be fixed. -/
theorem hasDerivAt_movingMetricAction {a b : ℝ} {U : ℝ → M → ℝ} {h : ℝ → ℝ}
    (hF : ∀ t ∈ uIcc a b,
      ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    (hg : ∀ t ∈ uIcc a b,
      ContMDiffAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 1
        (fun p : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
          p.2 ((g p.1).inner p.2)) (t, F 0 t))
    (hU : ∀ t ∈ uIcc a b,
      ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (fun p : ℝ × M ↦ U p.1 p.2)
        (t, F 0 t))
    (ht : ∀ t ∈ uIcc a b, HasDerivAt (fun r ↦ (g r).inner (F 0 t) (variationField I F t)
      (curveVelocity I (F 0) t)) (h t) t) :
    HasDerivAt (fun u ↦ movingMetricAction I g U (F u) a b)
      ((g b).inner (F 0 b) (variationField I F b) (curveVelocity I (F 0) b) -
        (g a).inner (F 0 a) (variationField I F a) (curveVelocity I (F 0) a) -
        ∫ t in a..b,
          letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩
          inner ℝ (variationField I F t) (acceleration (leviCivitaConnection I M) (F 0) t) +
            h t - mvfderiv I (U t) (F 0 t) (variationField I F t)) 0 := by
  let G : ℝ × ℝ → ℝ := fun z ↦ (g z.2).inner (F z.1 z.2)
    (curveVelocity I (F z.1) z.2) (curveVelocity I (F z.1) z.2) / 2 + U z.2 (F z.1 z.2)
  let K : ℝ → ℝ := fun t ↦ (g t).inner (F 0 t) (variationField I F t)
    (curveVelocity I (F 0) t)
  let R : ℝ → ℝ := fun t ↦
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩
    inner ℝ (variationField I F t) (acceleration (leviCivitaConnection I M) (F 0) t) +
      h t - mvfderiv I (U t) (F 0 t) (variationField I F t)
  obtain ⟨hG, hK, hid⟩ := movingMetricAction_pointwise hF hg hU ht
  have hrawCont : ContinuousOn (fun t ↦ fderiv ℝ G (0, t) (1, 0)) (uIcc a b) := by
    intro t ht'
    exact (((hG t ht').fderiv_right (m := 0) le_rfl).continuousAt.comp
      (continuousAt_const.prodMk continuousAt_id)).clm_apply continuousAt_const
      |>.continuousWithinAt
  have hderivCont : ContinuousOn (deriv K) (uIcc a b) := fun t ht' ↦
    ((hK t ht').derivWithin (m := 0) le_rfl).continuousAt.continuousWithinAt
  have hRCont : ContinuousOn R (uIcc a b) := by
    apply (hderivCont.sub hrawCont).congr
    intro t ht'
    dsimp only [Pi.sub_apply]
    rw [hid t ht']
    ring
  have hWo : IsOpen {z : ℝ × ℝ | ContDiffAt ℝ 1 G z} :=
    isOpen_iff_mem_nhds.2 fun z hz ↦ hz.eventually (by simp)
  obtain ⟨-, hD⟩ := TauCeti.hasDerivAt_intervalIntegral_of_contDiffOn hWo
    (fun z hz ↦ hz.contDiffWithinAt)
    (by rintro ⟨u, t⟩ ⟨hu, ht'⟩; obtain rfl : u = 0 := hu; exact hG t ht')
  have hFTC : ∫ t in a..b, deriv K t = K b - K a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht' ↦ ((hK t ht').differentiableAt one_ne_zero).hasDerivAt)
      hderivCont.intervalIntegrable
  refine hD.congr_deriv ?_
  calc
    (∫ t in a..b, fderiv ℝ G (0, t) (1, 0)) = ∫ t in a..b, deriv K t - R t :=
      intervalIntegral.integral_congr hid
    _ = (∫ t in a..b, deriv K t) - ∫ t in a..b, R t :=
      intervalIntegral.integral_sub hderivCont.intervalIntegrable hRCont.intervalIntegrable
    _ = _ := by rw [hFTC]

end TauCeti.Manifold
