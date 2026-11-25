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
the extension replaces it with the limiting value `q` using `Function.update`. The same holds at a
point `a` of the real axis for a map on the punctured closed upper half-disc, differentiable
within the closed upper half-plane: there the half-circles about `a` replace the circles, and the
radius is the one along the real axis
(`TauCeti.exists_continuousOn_update_inter_of_integrableOn_radial_deriv_of_tendsto`).

These are the metric and one-dimensional calculus ingredients of continuous removal of
singularities. They do not assert differentiability of the extension. The central inputs are
`TauCeti.exists_tendsto_nhdsGT_of_hasDerivAt_of_integrableOn_Ioo`,
`TauCeti.tendsto_nhdsNE_of_tendsto_radial_of_tendsto_diam_image_sphere`, and
`TauCeti.tendsto_diam_image_sphere_nhdsGT_zero_of_tendsto`, together with their half-plane forms
`TauCeti.tendsto_nhdsWithin_diff_of_tendsto_comp_of_tendsto_diam_image_inter_sphere` and
`TauCeti.tendsto_diam_image_inter_sphere_nhdsGT_zero_of_tendsto`.

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
sphere images shrink and the derivative along one ray, in any nonzero direction, is integrable.
Compactness of spheres is used to ensure boundedness of their images. -/
theorem exists_continuousOn_update_of_integrableOn_radial_deriv [ProperSpace E]
    {u : E → V} {a v : E} {R : ℝ} (hv : v ≠ 0) (hR : 0 < R)
    (hu : ContinuousOn u (ball a R \ {a}))
    (hr : DifferentiableOn ℝ (fun t : ℝ ↦ u (a + t • v)) (Ioo 0 R))
    (hint : IntegrableOn (deriv (fun t : ℝ ↦ u (a + t • v))) (Ioo 0 R))
    (hd : Tendsto (fun t ↦ diam (u '' sphere a t)) (𝓝[>] 0) (𝓝 0)) :
    ∃ q, Tendsto u (𝓝[≠] a) (𝓝 q) ∧
      ContinuousOn (Function.update u a q) (ball a R) := by
  obtain ⟨q, hq⟩ := exists_tendsto_nhdsGT_of_hasDerivAt_of_integrableOn_Ioo hR
    (fun t ht ↦ (hr.differentiableAt (isOpen_Ioo.mem_nhds ht)).hasDerivAt) hint
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
      (v := (1 : ℂ)) one_ne_zero hR hu.continuousOn
      (by simpa only [Complex.real_smul, mul_one] using hr)
      (by simpa only [Complex.real_smul, mul_one] using hint) hdiam


open Classical in
/-- **Continuous extension across a boundary puncture.** Let `a` be a point of the real axis and
let `u` be differentiable within the closed upper half-plane at the points of the punctured
half-disc `{0 ≤ im z} ∩ B_R(a) \ {a}`. If the speed of `u` along the real radius
`t ↦ u (a + t)` is integrable on `(0, R)` and the derivative within the half-plane blows up
strictly slower than inverse distance, `‖z - a‖ ‖du(z)‖ → 0`, then `u` converges as `z → a` within
the half-plane, and updating `u` at `a` to its limit gives a map continuous on the half-disc
`{0 ≤ im z} ∩ B_R(a)`. The original value of `u` at `a` is unrestricted. -/
theorem exists_continuousOn_update_inter_of_integrableOn_radial_deriv_of_tendsto
    {u : ℂ → V} {a : ℂ} {R : ℝ} (ha : a.im = 0) (hR : 0 < R)
    (hu : ∀ z ∈ {z : ℂ | 0 ≤ z.im} ∩ (ball a R \ {a}),
      DifferentiableWithinAt ℝ u {z | 0 ≤ z.im} z)
    (hint : IntegrableOn (deriv (fun t : ℝ ↦ u (a + (t : ℂ)))) (Ioo 0 R))
    (hd : Tendsto (fun z ↦ ‖z - a‖ * ‖fderivWithin ℝ u {z | 0 ≤ z.im} z‖)
      (𝓝[{z | 0 ≤ z.im} \ {a}] a) (𝓝 0)) :
    ∃ q, Tendsto u (𝓝[{z | 0 ≤ z.im} \ {a}] a) (𝓝 q) ∧
      ContinuousOn (Function.update u a q) ({z : ℂ | 0 ≤ z.im} ∩ ball a R) := by
  set H : Set ℂ := {z | 0 ≤ z.im}
  have hH : IsClosed H := isClosed_le continuous_const Complex.continuous_im
  have hcont : ContinuousOn u (H ∩ (ball a R \ {a})) := fun z hz ↦
    (hu z hz).continuousWithinAt.mono inter_subset_left
  -- The real radius `t ↦ a + t` stays on the real axis, hence in the closed upper half-plane.
  have hray : MapsTo (fun t : ℝ ↦ a + (t : ℂ)) univ H := fun t _ ↦ by simp [H, ha]
  have hmem (t : ℝ) (ht : t ∈ Ioo 0 R) : a + (t : ℂ) ∈ H ∩ (ball a R \ {a}) :=
    ⟨hray (mem_univ t), by simpa [mem_ball, dist_eq_norm, abs_of_pos ht.1] using ht.2,
      by simpa using ht.1.ne'⟩
  have hderiv (t : ℝ) (ht : t ∈ Ioo 0 R) : HasDerivAt (fun t : ℝ ↦ u (a + (t : ℂ)))
      (deriv (fun t : ℝ ↦ u (a + (t : ℂ))) t) t := by
    have hline : HasDerivAt (fun t : ℝ ↦ a + (t : ℂ)) 1 t := by
      simpa using (Complex.ofRealCLM.hasFDerivAt (x := t)).hasDerivAt.const_add a
    have h := (hu _ (hmem t ht)).hasFDerivWithinAt.comp_hasDerivWithinAt t
      hline.hasDerivWithinAt hray
    exact (hasDerivWithinAt_univ.1 h).differentiableAt.hasDerivAt
  -- The limit along the real radius, and shrinking images of the half-circles.
  obtain ⟨q, hq⟩ := exists_tendsto_nhdsGT_of_hasDerivAt_of_integrableOn_Ioo hR hderiv hint
  have hdiam := tendsto_diam_image_inter_sphere_nhdsGT_zero_of_tendsto ha (by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (ball_mem_nhds a hR)] with z hz hzR
    exact hu z ⟨hz.1, hzR, hz.2⟩) hd
  have hb : ∀ᶠ t in 𝓝[>] (0 : ℝ), IsBounded (u '' (H ∩ sphere a t)) := by
    filter_upwards [Ioo_mem_nhdsGT hR] with t ht
    have hsub : H ∩ sphere a t ⊆ H ∩ (ball a R \ {a}) := fun z hz ↦
      ⟨hz.1, sphere_subset_ball ht.2 hz.2, fun hza ↦ by
        have h := mem_sphere.1 hz.2
        rw [mem_singleton_iff.1 hza, dist_self] at h
        exact ht.1.ne h⟩
    exact (((isCompact_sphere a t).inter_left hH).image_of_continuousOn
      (hcont.mono hsub)).isBounded
  have hc : ∀ᶠ t in 𝓝[>] (0 : ℝ), a + (t : ℂ) ∈ H ∩ sphere a t := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact ⟨hray (mem_univ t), by simp [abs_of_pos (mem_Ioi.1 ht)]⟩
  have hlim := tendsto_nhdsWithin_diff_of_tendsto_comp_of_tendsto_diam_image_inter_sphere hc hq hb
    hdiam
  refine ⟨q, hlim, continuousOn_update_iff.2 ⟨?_, fun _ ↦ ?_⟩⟩
  · rwa [inter_sdiff_assoc]
  · exact hlim.mono_left (nhdsWithin_mono _ fun z hz ↦ ⟨hz.1.1, hz.2⟩)

end TauCeti
