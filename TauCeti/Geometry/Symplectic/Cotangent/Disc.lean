/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Action
public import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.Rigidity
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Holomorphic discs with boundary on an exact cotangent graph

In a linear cotangent space, the symplectic area of a disc is minus the boundary integral
of the Liouville form, with the convention `ω = -dλ`. On the graph of `dh`, the boundary
integral is the integral of `d(h ∘ π ∘ u)`, and therefore vanishes. Positivity of area for
a tame holomorphic curve then forces the disc to be constant, including its boundary.
The target almost complex structure may vary; neither compatibility nor regularity of that
structure is needed for this argument.

This rules out disc bubbles on differential graphs, including nonlinear graphs. The map is
assumed `C²` near the closed disc, so this statement concerns already regular discs rather
than removal of boundary singularities.

The Stokes calculation uses `ContinuousLinearMap.integral_bilinear_fderiv_sub_annulus` at
zero inner radius. Exactness on the graph uses
`TauCeti.integral_cotangentLiouvilleForm_differential_graph`.

## References

* A. Floer, *Morse theory for Lagrangian intersections*, J. Differential Geom. **28** (1988),
  §2 (exactness and exclusion of disc bubbles).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, §4.1 (area and bubbling).
-/

public section

namespace TauCeti

open MeasureTheory Set Complex Metric
open scoped Real

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {u : ℂ → V × StrongDual ℝ V} {z₀ : ℂ} {r : ℝ}

/-- The symplectic area of a `C²` cotangent-valued disc equals minus the Liouville integral
around its counterclockwise boundary. -/
theorem integral_strongDualCotangentSymplecticForm_disc (hr : 0 ≤ r)
    (hu : ∀ z ∈ closedBall z₀ r, ContDiffAt ℝ 2 u z) :
    (∫ z in closedBall z₀ r, strongDualCotangentSymplecticForm
      (fderiv ℝ u z 1) (fderiv ℝ u z I)) =
      -(∫ θ in -π..π, cotangentLiouvilleForm (u (circleMap z₀ r θ))
        (fun _ ↦ deriv (fun θ ↦ u (circleMap z₀ r θ)) θ)) := by
  let B : (V × StrongDual ℝ V) →L[ℝ] (V × StrongDual ℝ V) →L[ℝ] ℝ :=
    (ContinuousLinearMap.id ℝ (StrongDual ℝ V)).bilinearComp
      (ContinuousLinearMap.snd ℝ V (StrongDual ℝ V)) (ContinuousLinearMap.fst ℝ V (StrongDual ℝ V))
  have hB (x v : V × StrongDual ℝ V) : B x v = x.2 v.1 := by simp [B]
  have hset : {z : ℂ | 0 ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ r} = closedBall z₀ r := by
    ext z
    simp [mem_closedBall, dist_eq_norm]
  have hgreen := B.integral_bilinear_fderiv_sub_annulus z₀ (a := 0) (by rfl) hr
    (hset.symm ▸ hu)
  have hd (θ : ℝ) : deriv (fun θ ↦ u (circleMap z₀ r θ)) θ =
      fderiv ℝ u (circleMap z₀ r θ) (circleMap 0 r θ * I) :=
    (((hu _ (sphere_subset_closedBall (circleMap_mem_sphere z₀ hr θ))).differentiableAt
      (by norm_num)).hasFDerivAt.comp_hasDerivAt θ (hasDerivAt_circleMap z₀ r θ)).deriv
  simp only [hset, hB, circleMap_zero_radius, Function.const_apply, zero_mul,
    Prod.fst_zero, map_zero, intervalIntegral.integral_zero, sub_zero] at hgreen
  simp only [cotangentLiouvilleForm_apply, hd, strongDualCotangentSymplecticForm_apply]
  have hneg := congrArg Neg.neg hgreen
  rw [← integral_neg] at hneg
  convert hneg using 1
  apply setIntegral_congr_fun measurableSet_closedBall
  intro z _
  ring

/-- A `C²` disc whose boundary lies on the graph of `dh` has zero symplectic area. Only
boundary differentiability of `h` is required. -/
theorem integral_strongDualCotangentSymplecticForm_disc_eq_zero (hr : 0 ≤ r)
    (hu : ∀ z ∈ closedBall z₀ r, ContDiffAt ℝ 2 u z) {h : V → ℝ}
    (hh : ∀ z ∈ sphere z₀ r, DifferentiableAt ℝ h (u z).1)
    (hgraph : ∀ z ∈ sphere z₀ r, (u z).2 = fderiv ℝ h (u z).1) :
    (∫ z in closedBall z₀ r, strongDualCotangentSymplecticForm
      (fderiv ℝ u z 1) (fderiv ℝ u z I)) = 0 := by
  rw [integral_strongDualCotangentSymplecticForm_disc hr hu]
  have hmem (θ : ℝ) : circleMap z₀ r θ ∈ sphere z₀ r := circleMap_mem_sphere z₀ hr θ
  have hdu (θ : ℝ) : HasDerivAt (fun θ ↦ u (circleMap z₀ r θ))
      (fderiv ℝ u (circleMap z₀ r θ) (circleMap 0 r θ * I)) θ :=
    ((hu _ (sphere_subset_closedBall (hmem θ))).differentiableAt
      (by norm_num)).hasFDerivAt.comp_hasDerivAt θ (hasDerivAt_circleMap z₀ r θ)
  have hcont : ContinuousOn (fun θ ↦ fderiv ℝ u (circleMap z₀ r θ)
      (circleMap 0 r θ * I)) (uIcc (-π) π) := fun θ _ ↦ by
    exact ((((hu _ (sphere_subset_closedBall (hmem θ))).continuousAt_fderiv (by norm_num)).comp
      (continuous_circleMap z₀ r).continuousAt).clm_apply
      ((continuous_circleMap 0 r).mul continuous_const).continuousAt).continuousWithinAt
  simp_rw [(hdu _).deriv]
  rw [integral_cotangentLiouvilleForm_differential_graph
    (fun θ _ ↦ hdu θ) hcont (fun θ _ ↦ hh _ (hmem θ))
    (fun θ _ ↦ hgraph _ (hmem θ))]
  simp [circleMap, Complex.exp_mul_I]

/-- A holomorphic disc with boundary on an exact cotangent graph is constant on the entire
closed disc. The varying target structure need only be tamed along the interior image. -/
theorem exists_eqOn_const_of_isJHolomorphicAt_differential_graph
    {J : (V × StrongDual ℝ V) → AlmostComplexStructure (V × StrongDual ℝ V)}
    (hr : 0 < r) (hu : ∀ z ∈ closedBall z₀ r, ContDiffAt ℝ 2 u z)
    (hhol : ∀ z ∈ ball z₀ r,
      IsJHolomorphicAt (fun _ ↦ AlmostComplexStructure.ofComplexModule ℂ) J u z)
    (htame : ∀ z ∈ ball z₀ r, strongDualCotangentSymplecticForm.Tames (J (u z)))
    {h : V → ℝ} (hh : ∀ z ∈ sphere z₀ r, DifferentiableAt ℝ h (u z).1)
    (hgraph : ∀ z ∈ sphere z₀ r, (u z).2 = fderiv ℝ h (u z).1) :
    ∃ c : V × StrongDual ℝ V, EqOn u (fun _ ↦ c) (closedBall z₀ r) := by
  have hcont : ContinuousOn (fun z ↦ strongDualCotangentSymplecticForm
      (fderiv ℝ u z 1) (fderiv ℝ u z I)) (closedBall z₀ r) := fun z hz ↦ by
    have hd := (hu z hz).continuousAt_fderiv (by norm_num)
    have hone : ContinuousAt (fun z ↦ fderiv ℝ u z 1) z := hd.clm_apply continuousAt_const
    have hI : ContinuousAt (fun z ↦ fderiv ℝ u z I) z := hd.clm_apply continuousAt_const
    simp only [strongDualCotangentSymplecticForm_apply]
    exact ((hI.snd.clm_apply hone.fst).sub
      (hone.snd.clm_apply hI.fst)).continuousWithinAt
  have hsets : ball z₀ r =ᵐ[volume] closedBall z₀ r :=
    ae_eq_of_subset_of_measure_ge ball_subset_closedBall
      (Measure.addHaar_closedBall_eq_addHaar_ball volume z₀ r).le
      measurableSet_ball.nullMeasurableSet measure_closedBall_lt_top.ne
  have hzero : (∫ z in ball z₀ r, strongDualCotangentSymplecticForm
      (fderiv ℝ u z 1) (fderiv ℝ u z I)) = 0 := by
    rw [setIntegral_congr_set hsets,
      integral_strongDualCotangentSymplecticForm_disc_eq_zero hr.le hu hh hgraph]
  obtain ⟨c, hc⟩ := SymplecticForm.exists_eqOn_const_of_integral_eq_zero_of_continuousOn
    isOpen_ball (convex_ball z₀ r).isPreconnected
    hhol htame (hcont.mono ball_subset_closedBall)
    ((hcont.integrableOn_compact (isCompact_closedBall z₀ r)).mono_set
      ball_subset_closedBall) hzero
  refine ⟨c, hc.of_subset_closure (fun z hz ↦ (hu z hz).continuousAt.continuousWithinAt)
    continuousOn_const ball_subset_closedBall ?_⟩
  rw [closure_ball z₀ hr.ne']

end TauCeti
