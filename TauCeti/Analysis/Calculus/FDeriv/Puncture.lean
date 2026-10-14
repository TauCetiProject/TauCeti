/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Deriv.Endpoint
public import TauCeti.Topology.MetricSpace.RadialLimit
public import TauCeti.Analysis.Calculus.FDeriv.CircleMap

/-!
# Continuous extension across a puncture from finite radial length

A continuous map on a punctured ball extends continuously across its centre if its sphere
images shrink and the derivative along one radius is integrable. The radial derivative is
assumed integrable on the entire open radial interval, rather than merely locally integrable;
the latter would not force a limit. Completeness is needed only for the target.

For a map from the complex plane, the angular hypothesis follows from sublinear derivative
blow-up: `‖z - a‖ * ‖du(z)‖ → 0`. The original value of `u` at the puncture is unrestricted;
the extension replaces it with the limiting value `q` using `Function.update`.

These are the metric and one-dimensional calculus ingredients of continuous removal of
singularities. They do not assert differentiability of the extension. The central inputs are
`TauCeti.exists_tendsto_nhdsGT_of_integrableOn_deriv`,
`TauCeti.tendsto_nhdsNE_of_tendsto_radial_of_tendsto_diam_image_sphere`, and
`TauCeti.tendsto_diam_image_sphere_nhdsGT_zero_of_tendsto`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
  Section 4.5 (the radial and angular steps in removal of singularities).
-/

public section

namespace TauCeti

open Bornology Filter MeasureTheory Metric Set Topology

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

open Classical in
/-- A continuous map on a punctured ball has a continuous extension at the centre if its
sphere images shrink and the derivative along one unit radius is integrable. Compactness of
spheres is used to ensure boundedness of their images. -/
theorem exists_continuousOn_update_of_integrableOn_radial_deriv [ProperSpace E]
    {u : E → V} {a v : E} {R : ℝ} (hv : ‖v‖ = 1) (hR : 0 < R)
    (hu : ContinuousOn u (ball a R \ {a}))
    (hr : DifferentiableOn ℝ (fun t : ℝ ↦ u (a + t • v)) (Ioo 0 R))
    (hint : IntegrableOn (deriv (fun t : ℝ ↦ u (a + t • v))) (Ioo 0 R))
    (hd : Tendsto (fun t ↦ diam (u '' sphere a t)) (𝓝[>] 0) (𝓝 0)) :
    ∃ q, Tendsto u (𝓝[≠] a) (𝓝 q) ∧
      ContinuousOn (Function.update u a q) (ball a R) := by
  obtain ⟨q, hq⟩ := exists_tendsto_nhdsGT_of_integrableOn_deriv hR hr hint
  have hb : ∀ᶠ t in 𝓝[>] (0 : ℝ), IsBounded (u '' sphere a t) := by
    filter_upwards [Ioo_mem_nhdsGT hR] with t ht
    have hsub : sphere a t ⊆ ball a R \ {a} := by
      intro x hx
      refine ⟨sphere_subset_ball ht.2 hx, ?_⟩
      rintro rfl
      have := mem_sphere.mp hx
      simp only [dist_self] at this
      exact ht.1.ne this
    exact ((isCompact_sphere a t).image_of_continuousOn (hu.mono hsub)).isBounded
  have hlim := tendsto_nhdsNE_of_tendsto_radial_of_tendsto_diam_image_sphere hv hq hb hd
  refine ⟨q, hlim, continuousOn_update_iff.mpr ⟨hu, fun _ ↦ ?_⟩⟩
  exact hlim.mono_left (nhdsWithin_mono _ (sdiff_subset_compl _ _))

open Classical in
/-- A differentiable map on a punctured complex disc extends continuously if its differential
blows up strictly slower than inverse distance and its speed along the positive real radius is
integrable. No regularity at the puncture, holomorphicity, or finite-dimensional target is
assumed. -/
theorem exists_continuousOn_update_of_integrableOn_radial_deriv_of_tendsto
    {u : ℂ → V} {a : ℂ} {R : ℝ} (hR : 0 < R)
    (hu : DifferentiableOn ℝ u (ball a R \ {a}))
    (hint : IntegrableOn (deriv (fun t : ℝ ↦ u (a + (t : ℂ)))) (Ioo 0 R))
    (hd : Tendsto (fun z ↦ ‖z - a‖ * ‖fderiv ℝ u z‖) (𝓝[≠] a) (𝓝 0)) :
    ∃ q, Tendsto u (𝓝[≠] a) (𝓝 q) ∧
      ContinuousOn (Function.update u a q) (ball a R) := by
  have hsub : MapsTo (fun t : ℝ ↦ a + (t : ℂ)) (Ioo 0 R) (ball a R \ {a}) := by
    intro t ht
    constructor
    · simpa [mem_ball, dist_eq_norm, abs_of_pos ht.1] using ht.2
    · simpa using ht.1.ne'
  have hr : DifferentiableOn ℝ (fun t : ℝ ↦ u (a + (t : ℂ))) (Ioo 0 R) :=
    hu.comp (Complex.ofRealCLM.differentiable.const_add a).differentiableOn hsub
  have hdiff : ∀ᶠ z in 𝓝[≠] a, DifferentiableAt ℝ u z := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (ball_mem_nhds a hR)] with z hz hzR
    exact hu.differentiableAt ((isOpen_ball.sdiff isClosed_singleton).mem_nhds ⟨hzR, hz⟩)
  have hdiam := tendsto_diam_image_sphere_nhdsGT_zero_of_tendsto hdiff hd
  simpa only [Complex.real_smul, mul_one] using
    exists_continuousOn_update_of_integrableOn_radial_deriv
      (v := (1 : ℂ)) (by simp) hR hu.continuousOn
      (by simpa only [Complex.real_smul, mul_one] using hr)
      (by simpa only [Complex.real_smul, mul_one] using hint) hdiam

end TauCeti
