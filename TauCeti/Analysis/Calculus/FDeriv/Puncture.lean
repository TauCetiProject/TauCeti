/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Deriv.Endpoint
public import TauCeti.Topology.MetricSpace.RadialLimit
public import TauCeti.Analysis.Calculus.FDeriv.CircleMap
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# Continuous extension across a puncture from finite radial length

A continuous map on a punctured ball extends continuously across its centre if its sphere
images shrink and the derivative along one radius is integrable. The radial derivative is
assumed integrable on the entire open radial interval, rather than merely locally integrable;
the latter would not force a limit. Completeness is needed only for the target. More generally,
the same holds within a closed set `s` containing the radius, using only the parts of the spheres
inside `s` (`TauCeti.exists_continuousOn_update_inter_of_integrableOn_radial_deriv`); the
whole-space statement is its case `s = univ`.

For a map from the complex plane, the angular hypothesis follows from sublinear derivative
blow-up: `‖z - a‖ * ‖du(z)‖ → 0`. The original value of `u` at the puncture is unrestricted;
the extension replaces it with the limiting value `q` using `Function.update`; off the
puncture the extension has the derivative of `u` (`TauCeti.fderiv_update_of_ne`). The same holds
at a point `a` of the real axis for a map on the punctured closed upper half-disc, differentiable
within the closed upper half-plane: this is the case where `s` is that half-plane, so the
half-circles about `a` replace the circles, and the radius is the one along the real axis
(`TauCeti.exists_continuousOn_update_inter_of_integrableOn_radial_deriv_of_tendsto`).

The finite radial length itself follows from a power bound `‖du(z)‖ ≤ C ‖z - a‖ ^ (β - 1)` with
`β > 0` on the derivative within a set containing the radius
(`TauCeti.integrableOn_deriv_radial_of_norm_fderivWithin_le_rpow`).

These are the metric and one-dimensional calculus ingredients of continuous removal of
singularities. They do not assert differentiability of the extension. The central inputs are
`TauCeti.exists_tendsto_nhdsGT_of_hasDerivAt_of_integrableOn_Ioo`,
`TauCeti.tendsto_nhdsWithin_diff_of_tendsto_radial_of_tendsto_diam_image_inter_sphere`, and
`TauCeti.tendsto_diam_image_sphere_nhdsGT_zero_of_tendsto`, together with its half-plane form
`TauCeti.tendsto_diam_image_inter_sphere_nhdsGT_zero_of_tendsto`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
  Section 4.5 (the radial and angular steps in removal of singularities).
-/

public section

namespace TauCeti

open Bornology Filter MeasureTheory Metric Set Topology

/-- Changing a map at one point does not change its derivative at any other point. -/
theorem fderiv_update_of_ne {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [DecidableEq E] {f : E → F}
    {x₀ x : E} (h : x ≠ x₀) (y : F) :
    fderiv 𝕜 (Function.update f x₀ y) x = fderiv 𝕜 f x :=
  EventuallyEq.fderiv_eq ((eventually_ne_nhds h).mono fun _ hw ↦ Function.update_of_ne hw _ _)

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

open Classical in
/-- A map continuous on the part of a punctured ball inside a closed set `s` has a continuous
extension at the centre within `s` if the images of the parts of small spheres inside `s` shrink
and the derivative along one ray in `s`, in any nonzero direction, is integrable. Compactness of
spheres is used to ensure boundedness of their images. -/
theorem exists_continuousOn_update_inter_of_integrableOn_radial_deriv [ProperSpace E]
    {s : Set E} {u : E → V} {a v : E} {R : ℝ} (hs : IsClosed s) (hv : v ≠ 0) (hR : 0 < R)
    (hray : MapsTo (fun t : ℝ ↦ a + t • v) (Ioo 0 R) s)
    (hu : ContinuousOn u (s ∩ (ball a R \ {a})))
    (hr : DifferentiableOn ℝ (fun t : ℝ ↦ u (a + t • v)) (Ioo 0 R))
    (hint : IntegrableOn (deriv (fun t : ℝ ↦ u (a + t • v))) (Ioo 0 R))
    (hd : Tendsto (fun t ↦ diam (u '' (s ∩ sphere a t))) (𝓝[>] 0) (𝓝 0)) :
    ∃ q, Tendsto u (𝓝[s \ {a}] a) (𝓝 q) ∧
      ContinuousOn (Function.update u a q) (s ∩ ball a R) := by
  obtain ⟨q, hq⟩ := exists_tendsto_nhdsGT_of_hasDerivAt_of_integrableOn_Ioo hR
    (fun t ht ↦ (hr.differentiableAt (isOpen_Ioo.mem_nhds ht)).hasDerivAt) hint
  have hb : ∀ᶠ t in 𝓝[>] (0 : ℝ), IsBounded (u '' (s ∩ sphere a t)) := by
    filter_upwards [Ioo_mem_nhdsGT hR] with t ht
    have hsub : s ∩ sphere a t ⊆ s ∩ (ball a R \ {a}) := fun z hz ↦
      ⟨hz.1, sphere_subset_ball ht.2 hz.2, fun hza ↦ by
        have h := mem_sphere.1 hz.2
        rw [mem_singleton_iff.1 hza, dist_self] at h
        exact ht.1.ne h⟩
    exact (((isCompact_sphere a t).inter_left hs).image_of_continuousOn
      (hu.mono hsub)).isBounded
  have hlim := tendsto_nhdsWithin_diff_of_tendsto_radial_of_tendsto_diam_image_inter_sphere hv
    (eventually_of_mem (Ioo_mem_nhdsGT hR) fun _ ht ↦ hray ht) hq hb hd
  refine ⟨q, hlim, continuousOn_update_iff.2 ⟨?_, fun _ ↦ ?_⟩⟩
  · rwa [inter_sdiff_assoc]
  · exact hlim.mono_left (nhdsWithin_mono _ fun z hz ↦ ⟨hz.1.1, hz.2⟩)

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
  simpa [compl_eq_univ_sdiff] using
    exists_continuousOn_update_inter_of_integrableOn_radial_deriv isClosed_univ hv hR
      (mapsTo_univ _ _) (by simpa using hu) hr hint (by simpa using hd)

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

/-- **Finite radial length from a power bound on the derivative.** Let the open radius
`t ↦ a + t • v`, `0 < t < ε`, in a unit direction `v` lie in `s`, and let `u` be differentiable
within `s` at the points of `s` in the punctured ball `B_ε(a) \ {a}`. If the derivative within `s`
there satisfies `‖du(z)‖ ≤ C ‖z - a‖ ^ (β - 1)` with `β > 0`, then the speed of `u` along the
radius is integrable on `(0, ε)`. For `s = univ` this is the interior case. -/
theorem integrableOn_deriv_radial_of_norm_fderivWithin_le_rpow
    {s : Set E} {u : E → V} {a v : E} {ε C β : ℝ} (hβ : 0 < β) (hv : ‖v‖ = 1)
    (hs : MapsTo (fun t : ℝ ↦ a + t • v) (Ioo 0 ε) s)
    (hu : ∀ z ∈ s ∩ (ball a ε \ {a}), DifferentiableWithinAt ℝ u s z)
    (hC : ∀ z ∈ s ∩ (ball a ε \ {a}), ‖fderivWithin ℝ u s z‖ ≤ C * ‖z - a‖ ^ (β - 1)) :
    IntegrableOn (deriv fun t : ℝ ↦ u (a + t • v)) (Ioo 0 ε) := by
  rcases le_or_gt ε 0 with hε | hε
  · simp [Ioo_eq_empty_of_le hε]
  have hnorm (t : ℝ) (ht : 0 < t) : ‖a + t • v - a‖ = t := by
    simp [norm_smul, hv, Real.norm_of_nonneg ht.le]
  have hmem (t : ℝ) (ht : t ∈ Ioo 0 ε) : a + t • v ∈ s ∩ (ball a ε \ {a}) := by
    refine ⟨hs ht, ?_, ?_⟩
    · simpa only [mem_ball, dist_eq_norm, hnorm t ht.1] using ht.2
    · exact sub_ne_zero.mp (norm_pos_iff.mp (by rw [hnorm t ht.1]; exact ht.1))
  -- Along the radius, the derivative is that of `u` within `s`, in the direction `v`.
  have heq (t : ℝ) (ht : t ∈ Ioo 0 ε) :
      deriv (fun t : ℝ ↦ u (a + t • v)) t = fderivWithin ℝ u s (a + t • v) v := by
    have hline : HasDerivAt (fun t : ℝ ↦ a + t • v) v t := by
      simpa using ((hasDerivAt_id t).smul_const v).const_add a
    exact (((hu _ (hmem t ht)).hasFDerivWithinAt.comp_hasDerivWithinAt t hline.hasDerivWithinAt
      hs).hasDerivAt (Ioo_mem_nhds ht.1 ht.2)).deriv
  have hpow : IntegrableOn (fun t : ℝ ↦ C * t ^ (β - 1)) (Ioo 0 ε) :=
    ((intervalIntegral.integrableOn_Ioo_rpow_iff hε).mpr (by linarith)).const_mul C
  refine hpow.mono' (aestronglyMeasurable_deriv _ _) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  rw [heq t ht]
  calc
    ‖fderivWithin ℝ u s (a + t • v) v‖ ≤ ‖fderivWithin ℝ u s (a + t • v)‖ := by
      simpa only [hv, mul_one] using (fderivWithin ℝ u s (a + t • v)).le_opNorm v
    _ ≤ C * t ^ (β - 1) := by simpa only [hnorm t ht.1] using hC _ (hmem t ht)

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
  -- The real radius `t ↦ a + t` stays on the real axis, hence in the closed upper half-plane.
  have hray : MapsTo (fun t : ℝ ↦ a + (t : ℂ)) univ H := fun t _ ↦ by simp [H, ha]
  have hmem : MapsTo (fun t : ℝ ↦ a + (t : ℂ)) (Ioo 0 R) (H ∩ (ball a R \ {a})) := fun t ht ↦
    ⟨hray (mem_univ t), by simpa [mem_ball, dist_eq_norm, abs_of_pos ht.1] using ht.2,
      by simpa using ht.1.ne'⟩
  have hline : Differentiable ℝ fun t : ℝ ↦ a + (t : ℂ) :=
    Complex.ofRealCLM.differentiable.const_add a
  -- Along the real radius, `u` is differentiable within the half-plane, hence differentiable.
  have hr : DifferentiableOn ℝ (fun t : ℝ ↦ u (a + (t : ℂ))) (Ioo 0 R) := fun t ht ↦
    (((hu _ (hmem ht)).comp t (hline t).differentiableWithinAt hray).differentiableAt
      univ_mem).differentiableWithinAt
  have hdiam := tendsto_diam_image_inter_sphere_nhdsGT_zero_of_tendsto ha (by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (ball_mem_nhds a hR)] with z hz hzR
    exact hu z ⟨hz.1, hzR, hz.2⟩) hd
  simpa only [Complex.real_smul, mul_one] using
    exists_continuousOn_update_inter_of_integrableOn_radial_deriv (v := (1 : ℂ))
      (isClosed_le continuous_const Complex.continuous_im) one_ne_zero hR
      (by simpa only [Complex.real_smul, mul_one] using hray.mono_left (subset_univ _))
      (fun z hz ↦ (hu z hz).continuousWithinAt.mono inter_subset_left)
      (by simpa only [Complex.real_smul, mul_one] using hr)
      (by simpa only [Complex.real_smul, mul_one] using hint) hdiam

end TauCeti
