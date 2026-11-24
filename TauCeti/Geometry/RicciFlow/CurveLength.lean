/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.WithMetric.Curve
public import TauCeti.Geometry.Manifold.Riemannian.Curve.MetricVariation
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Ricci
import TauCeti.Analysis.Calculus.ParametricIntegral.Basic
import TauCeti.Geometry.Manifold.ContMDiff.Prod

/-!
# Fixed-curve length and energy under Ricci flow

The curve is fixed while its ambient Riemannian metric varies. Its native path length is
measured in the corresponding `TauCeti.WithMetric` copy of the manifold. Writing `v = γ'`
and `speed = sqrt(g(v,v))`, the Ricci equation `∂ₜg = -2 Ric` gives
`∂ₜL = ∫ -Ric(v,v) / speed` for a regular curve and `∂ₜE = -∫ Ric(v,v)` for any `C²` curve.
The joint metric regularity and evolution equation are required only at the fixed time
along the curve. No completeness, minimizing property or ambient compactness is assumed.

These formulas supply the ambient metric contribution to moving-curve estimates. The
curve velocity here has no metric-time dependence; curve shortening and its additional
curve-motion terms are separate constructions.

## Main results

* `Bundle.ContMDiffRiemannianMetric.hasDerivAt_toReal_pathELength_of_ricciFlow`: the native
  length derivative of a fixed regular curve.
* `Bundle.ContMDiffRiemannianMetric.hasDerivAt_energy_of_ricciFlow`: the native energy derivative,
  allowing zero velocity and either orientation of the parameter interval.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture* (2007), Claim 3.24 and §19.1.
* P. Topping, *Lectures on the Ricci Flow* (2006), §2.3.

The squared-speed argument follows the Chow–Liao–Qin formalization
`pathLength_timeDeriv_of_ricciFlow` (Apache-2.0), whose original notice is:

DifferentialGeometry
Copyright 2026 The DifferentialGeometry contributors

Formalization references: https://github.com/frenzymath/lean-eval-submissions and
https://github.com/frenzymath/PoincareConjecture.
-/

public noncomputable section

open Bundle Filter MeasureTheory Set TauCeti.Manifold
open scoped ContDiff Manifold Topology

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {γ : ℝ → M}
  {g : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}

variable [T2Space M]

/-- The native length of a fixed regular `C²` curve has derivative
`∫ -Ric(γ',γ') / sqrt(g(γ',γ'))` along the Ricci equation. The metric's bilinear section
is jointly `C¹` at the fixed time along the curve; the equation is required only on the
curve's velocity pairs there. The curve's endpoints remain fixed. -/
theorem hasDerivAt_toReal_pathELength_of_ricciFlow
    {a b t : ℝ} (hab : a ≤ b)
    (hγ : ∀ u ∈ Icc a b, ContMDiffAt 𝓘(ℝ, ℝ) I 2 γ u)
    (hg : ∀ u ∈ Icc a b,
      ContMDiffAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 1
        (fun p : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
          p.2 ((g p.1).inner p.2)) (t, γ u))
    (hvel : ∀ u ∈ Icc a b, curveVelocity I γ u ≠ 0)
    (hflow : ∀ u ∈ Icc a b, HasDerivAt (fun τ ↦ (g τ).inner (γ u)
      (curveVelocity I γ u) (curveVelocity I γ u))
        (-2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
            ⟨(g t).toRiemannianMetric⟩;
          (CovariantDerivative.leviCivitaConnection I M).ricciTensor (γ u)
            (curveVelocity I γ u) (curveVelocity I γ u))) t) :
    HasDerivAt (fun τ ↦ (Manifold.pathELength I
      (TauCeti.WithMetric.toWithMetric (g τ) ∘ γ) a b).toReal)
      (∫ u in a..b,
        -(letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
            ⟨(g t).toRiemannianMetric⟩;
          (CovariantDerivative.leviCivitaConnection I M).ricciTensor (γ u)
            (curveVelocity I γ u) (curveVelocity I γ u)) /
        Real.sqrt ((g t).inner (γ u) (curveVelocity I γ u) (curveVelocity I γ u))) t := by
  rw [← uIcc_of_le hab] at hg hvel hflow
  have hd := hasDerivAt_integral_speed
    (fun u hu ↦ ContMDiffAt.contDiffAt_metric_speed_sq
      (hγ u (by simpa only [uIcc_of_le hab] using hu)) (hg u hu)) hvel hflow
  refine hd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun τ ↦ ?_)
  exact toReal_pathELength_toWithMetric_eq_integral (g τ) hab
    (fun u hu ↦ (hγ u hu).of_le (by norm_num))

/-- The energy of a fixed curve has derivative minus the integral of its Ricci evaluation.
The curve need not have nonzero velocity, and either orientation of the parameter interval
is allowed. The metric equation is required only along the fixed curve at the stated time. -/
theorem hasDerivAt_energy_of_ricciFlow
    {a b t : ℝ}
    (hγ : ∀ u ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ) I 2 γ u)
    (hg : ∀ u ∈ uIcc a b,
      ContMDiffAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 1
        (fun p : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
          p.2 ((g p.1).inner p.2)) (t, γ u))
    (hflow : ∀ u ∈ uIcc a b, HasDerivAt (fun τ ↦ (g τ).inner (γ u)
      (curveVelocity I γ u) (curveVelocity I γ u))
        (-2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
            ⟨(g t).toRiemannianMetric⟩;
          (CovariantDerivative.leviCivitaConnection I M).ricciTensor (γ u)
            (curveVelocity I γ u) (curveVelocity I γ u))) t) :
    HasDerivAt (fun τ ↦ energy I (TauCeti.WithMetric.toWithMetric (g τ) ∘ γ) a b)
      (-(∫ u in a..b,
        letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨(g t).toRiemannianMetric⟩;
        (CovariantDerivative.leviCivitaConnection I M).ricciTensor (γ u)
          (curveVelocity I γ u) (curveVelocity I γ u))) t := by
  let G : ℝ × ℝ → ℝ := fun p ↦
    (g p.1).inner (γ p.2) (curveVelocity I γ p.2) (curveVelocity I γ p.2)
  obtain ⟨U, V, hUo, hVo, htU, hV, hGU⟩ :=
    TauCeti.exists_isOpen_prod_contMDiffOn (I' := 𝓘(ℝ, ℝ × ℝ)) (J := 𝓘(ℝ, ℝ))
      isCompact_uIcc (by simp)
      (fun u hu ↦ (ContMDiffAt.contDiffAt_metric_speed_sq (hγ u hu) (hg u hu)).contMDiffAt)
  have hGc : ContDiffOn ℝ 1 G (U ×ˢ V) := hGU.contDiffOn
  have hsub : {t} ×ˢ uIcc a b ⊆ U ×ˢ V := fun _ hp ↦
    ⟨by simpa only [mem_singleton_iff.mp hp.1] using htU, hV hp.2⟩
  obtain ⟨_, hD⟩ := TauCeti.hasDerivAt_intervalIntegral_of_contDiffOn (hUo.prod hVo) hGc hsub
  have hRic : ∀ u ∈ uIcc a b, fderiv ℝ G (t, u) (1, 0) =
      -2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨(g t).toRiemannianMetric⟩;
        (CovariantDerivative.leviCivitaConnection I M).ricciTensor (γ u)
          (curveVelocity I γ u) (curveVelocity I γ u)) := by
    intro u hu
    have hp : HasDerivAt (fun τ : ℝ ↦ (τ, u)) ((1 : ℝ), (0 : ℝ)) t :=
      (hasDerivAt_id' (x := t)).prodMk (hasDerivAt_const t u)
    have hdiff : DifferentiableAt ℝ G (t, u) :=
      (hGc.differentiableOn one_ne_zero (t, u) (hsub ⟨rfl, hu⟩)).differentiableAt
        ((hUo.prod hVo).mem_nhds (hsub ⟨rfl, hu⟩))
    have hparam := hdiff.hasFDerivAt.comp_hasDerivAt t hp
    exact hparam.unique (hflow u hu)
  have hd := (hD.congr_deriv (intervalIntegral.integral_congr hRic)).div_const 2
  have he := hd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun τ ↦
    energy_toWithMetric_eq_integral (g τ) a b)
  convert he using 1
  simp only [intervalIntegral.integral_const_mul]
  ring

end Bundle.ContMDiffRiemannianMetric
