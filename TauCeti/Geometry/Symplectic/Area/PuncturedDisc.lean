/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Area.Basic
public import TauCeti.MeasureTheory.Integral.Circle.LIntegral
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
import TauCeti.Geometry.Symplectic.Duality

/-!
# Symplectic Stokes on a finite-energy punctured disc

The symplectic area of a finite-energy map on a punctured disc equals the action of its outer
boundary loop for the primitive `λₓ(v) = ½ ω(x, v)`. No extension, bounded image, or boundary
decay at the puncture is assumed. In particular this identity applies before removal of a
singularity has been proved. Both results hold in any finite-dimensional real normed space.

The vanishing-action result requires `C¹` regularity near the punctured closed disc and a
square-integrable differential. The Stokes identity requires `C²` regularity there, including
the outer boundary. For a `J`-holomorphic map, this area identity is the input to the radial
energy-decay argument in removal of singularities. For a map which is `C²` on the whole closed
disc the energy is automatically finite, which gives Stokes' formula on the closed disc
(`TauCeti.SymplecticForm.integral_fderiv_apply_closedBall`, with the boundary term written as the
loop area of the boundary circle in
`TauCeti.SymplecticForm.integral_fderiv_apply_closedBall_eq_loopArea`, and in the real coordinates
`ℝ × ℝ ≃ ℂ`, `TauCeti.SymplecticForm.integral_fderiv_apply_preimage_closedBall`).

Holomorphic discs are usually known to be `C²` only inside, and `C¹` up to their boundary. For
such a map Stokes' formula holds on the open disc
(`TauCeti.SymplecticForm.integral_fderiv_apply_ball_of_contDiffOn`): apply the closed-disc formula
on the concentric discs of radius `r < b`, and let `r` tend to `b`. The areas converge because the
differential extends continuously to the closed disc, so the area density is integrable
(`TauCeti.SymplecticForm.integrableOn_fderiv_apply_ball_of_contDiffOn`), and the boundary actions
converge because they are integrals over `[-π, π]` of a function jointly continuous in the radius
and the angle (`TauCeti.SymplecticForm.continuousOn_integral_apply_deriv_circleMap`).

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
  Sections 4.4 and 4.5.
-/

public section

open Complex Filter MeasureTheory Set Topology TauCeti
open scoped Real

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- Finite energy gives a sequence of shrinking circles whose symplectic boundary actions
tend to zero. No boundedness or extension of the map at the puncture is required. -/
theorem exists_tendsto_integral_apply_circleMap_nhds_zero (ω : SymplecticForm V) {u : ℂ → V}
    (z₀ : ℂ) {b : ℝ} (hb : 0 < b)
    (hu : ∀ z ∈ {z : ℂ | 0 < ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}, ContDiffAt ℝ 1 u z)
    (henergy : IntegrableOn (fun z ↦ ‖fderiv ℝ u z‖ ^ 2)
      {z : ℂ | 0 < ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}) :
    ∃ r : ℕ → ℝ, (∀ n, 0 < r n ∧ r n ≤ b) ∧ Tendsto r atTop (𝓝 0) ∧
      Tendsto (fun n ↦ ∫ θ in -π..π, ω (u (circleMap z₀ (r n) θ))
        (deriv (fun θ ↦ u (circleMap z₀ (r n) θ)) θ)) atTop (𝓝 0) := by
  have : CompleteSpace V := FiniteDimensional.completeSpace ℝ V
  let action (r : ℝ) := ∫ θ in -π..π, ω (u (circleMap z₀ r θ))
    (deriv (fun θ ↦ u (circleMap z₀ r θ)) θ)
  -- Use Euclidean coordinates only for Wirtinger; the original norm controls their energy.
  let e : V ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  let B := ω.toBilinForm.toContinuousBilinearMap.bilinearComp
    e.symm.toContinuousLinearMap e.symm.toContinuousLinearMap
  let C := ‖B‖ * ‖e.toContinuousLinearMap‖ ^ 2
  -- The small-circle estimate needs only finite energy; no boundary decay is imposed.
  let δ (n : ℕ) : ℝ := b / ((n : ℝ) + 1)
  have hδ (n : ℕ) : 0 < δ n := div_pos hb (by positivity)
  have hδb (n : ℕ) : δ n ≤ b := by
    dsimp only [δ]
    rw [div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)]
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  choose r hr hE using fun n ↦
    exists_integral_norm_deriv_comp_circleMap_sq_lt z₀ (hδ n) (hδb n) (hδ n)
      (fun z hz ↦ (hu z hz).differentiableAt (by norm_num)) henergy
  have hδlim : Tendsto δ atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hrlim : Tendsto r atTop (𝓝 0) :=
    squeeze_zero (fun n ↦ (hr n).1.le) (fun n ↦ (hr n).2.le) hδlim
  -- Wirtinger's inequality controls the action by the angular energy on each chosen circle.
  have haction (n : ℕ) : ‖action (r n)‖ ≤ C * δ n := by
    have hcircle (θ : ℝ) : ContDiffAt ℝ 1 u (circleMap z₀ (r n) θ) :=
      hu _ (circleMap_mem_puncturedClosedDisc z₀ (hr n).1 ((hr n).2.le.trans (hδb n)) θ)
    let f (θ : ℝ) := u (circleMap z₀ (r n) θ)
    have hc : ContDiff ℝ 1 f := contDiff_iff_contDiffAt.mpr fun θ ↦
      (hcircle θ).comp θ (contDiff_circleMap z₀ (r n)).contDiffAt
    have hd := hc.continuous_deriv (by norm_num)
    have hederiv (θ : ℝ) : deriv (fun θ ↦ e (u (circleMap z₀ (r n) θ))) θ =
        e (deriv (fun θ ↦ u (circleMap z₀ (r n) θ)) θ) :=
      (e.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt θ
        (hc.differentiable (by norm_num) θ).hasDerivAt).deriv
    have h := norm_integral_apply_apply_circleMap_le (e ∘ u) (B := B) z₀ (r n)
      (fun θ ↦ e.contDiff.contDiffAt.comp _ (hcircle θ))
    simp only [Function.comp_def, hederiv, B, ContinuousLinearMap.bilinearComp_apply,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply] at h
    have hbound : (∫ θ in -π..π, ‖e (deriv f θ)‖ ^ 2) ≤
        ‖e.toContinuousLinearMap‖ ^ 2 * ∫ θ in -π..π, ‖deriv f θ‖ ^ 2 := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_mono (by linarith [Real.pi_pos])
        (((e.continuous.comp hd).norm.pow 2).intervalIntegrable _ _)
        (((hd.norm.pow 2).intervalIntegrable _ _).const_mul _)
      intro θ
      calc
        ‖e (deriv f θ)‖ ^ 2 ≤ (‖e.toContinuousLinearMap‖ * ‖deriv f θ‖) ^ 2 := by
          gcongr
          exact e.toContinuousLinearMap.le_opNorm _
        _ = ‖e.toContinuousLinearMap‖ ^ 2 * ‖deriv f θ‖ ^ 2 := mul_pow _ _ _
    calc ‖action (r n)‖ ≤ ‖B‖ * ∫ θ in -π..π, ‖e (deriv f θ)‖ ^ 2 := h
      _ ≤ ‖B‖ * (‖e.toContinuousLinearMap‖ ^ 2 * δ n) := by
        gcongr
        exact hbound.trans (mul_le_mul_of_nonneg_left (hE n).le (sq_nonneg _))
      _ = C * δ n := (mul_assoc _ _ _).symm
  have hactionlim : Tendsto (fun n ↦ action (r n)) atTop (𝓝 0) :=
    squeeze_zero_norm haction (by simpa using tendsto_const_nhds.mul hδlim)
  exact ⟨r, fun n ↦ ⟨(hr n).1, (hr n).2.le.trans (hδb n)⟩, hrlim, hactionlim⟩

/-- **Stokes' formula on a finite-energy punctured disc.** The integral of the pullback of a
constant symplectic form equals the outer boundary action. The value of the map at the puncture
is unrestricted, and the map need not be holomorphic. -/
theorem integral_fderiv_apply_punctured_disc (ω : SymplecticForm V) {u : ℂ → V}
    (z₀ : ℂ) {b : ℝ} (hb : 0 < b)
    (hu : ∀ z ∈ {z : ℂ | 0 < ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}, ContDiffAt ℝ 2 u z)
    (henergy : IntegrableOn (fun z ↦ ‖fderiv ℝ u z‖ ^ 2)
      {z : ℂ | 0 < ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}) :
    (∫ z in {z : ℂ | 0 < ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b},
      ω (fderiv ℝ u z 1) (fderiv ℝ u z I)) =
      (1 / 2 : ℝ) * ∫ θ in -π..π, ω (u (circleMap z₀ b θ))
        (deriv (fun θ ↦ u (circleMap z₀ b θ)) θ) := by
  have : CompleteSpace V := FiniteDimensional.completeSpace ℝ V
  let D := {z : ℂ | 0 < ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}
  let A (r : ℝ) := {z : ℂ | r ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}
  let area (z : ℂ) := ω (fderiv ℝ u z 1) (fderiv ℝ u z I)
  let action (r : ℝ) := ∫ θ in -π..π, ω (u (circleMap z₀ r θ))
    (deriv (fun θ ↦ u (circleMap z₀ r θ)) θ)
  have hD : MeasurableSet D := measurableSet_puncturedClosedDisc z₀ b
  have hA (r : ℝ) : MeasurableSet (A r) :=
    (isClosed_le continuous_const (continuous_id.sub continuous_const).norm).measurableSet.inter
      (isClosed_le (continuous_id.sub continuous_const).norm continuous_const).measurableSet
  have hsub {r : ℝ} (hr : 0 < r) : A r ⊆ D := fun z hz ↦ ⟨hr.trans_le hz.1, hz.2⟩
  have harea : IntegrableOn area D :=
    ω.integrableOn_fderiv_apply_of_integrableOn_norm_fderiv_sq henergy
  obtain ⟨r, hr, hrlim, hactionlim⟩ := ω.exists_tendsto_integral_apply_circleMap_nhds_zero
    z₀ hb (fun z hz ↦ (hu z hz).of_le one_le_two) henergy
  -- Dominated convergence exhausts the punctured disc even though the radii need not be monotone.
  have hpoint : ∀ᵐ z ∂volume.restrict D,
      Tendsto (fun n ↦ (A (r n)).indicator area z) atTop (𝓝 (area z)) := by
    filter_upwards [ae_restrict_mem hD] with z hz
    apply tendsto_const_nhds.congr'
    filter_upwards [hrlim.eventually (gt_mem_nhds hz.1)] with n hn
    have hzA : z ∈ A (r n) := ⟨hn.le, hz.2⟩
    exact (indicator_of_mem hzA area).symm
  have hlim := tendsto_integral_of_dominated_convergence (μ := volume.restrict D)
    (bound := fun z ↦ ‖area z‖)
    (fun n ↦ harea.aestronglyMeasurable.indicator (hA (r n)))
    harea.norm (fun n ↦ ae_of_all _ fun z ↦ norm_indicator_le_norm_self _ _) hpoint
  have hint (n : ℕ) : (∫ z, (A (r n)).indicator area z ∂volume.restrict D) =
      ∫ z in A (r n), area z := by
    rw [integral_indicator (hA (r n)), Measure.restrict_restrict (hA (r n)),
      inter_eq_left.mpr (hsub (hr n).1)]
  simp_rw [hint] at hlim
  -- Annular Stokes identifies the same limit with half the outer boundary action.
  have heq (n : ℕ) : (∫ z in A (r n), area z) =
      (1 / 2 : ℝ) * (action b - action (r n)) :=
    ω.integral_fderiv_apply_annulus z₀ (hr n).1.le (hr n).2
      (fun z hz ↦ hu z (hsub (hr n).1 hz))
  have hstokes : Tendsto (fun n ↦ (1 / 2 : ℝ) * (action b - action (r n))) atTop
      (𝓝 ((1 / 2 : ℝ) * action b)) := by
    simpa using (tendsto_const_nhds.sub hactionlim).const_mul (1 / 2 : ℝ)
  exact tendsto_nhds_unique hlim (hstokes.congr (fun n ↦ (heq n).symm))

/-- **Stokes' formula on a closed disc.** For a map which is `C²` at every point of the closed
disc `‖z - z₀‖ ≤ b`, the integral over the disc of the pullback of a constant symplectic form is
half the integral of `ω(u, ∂_θ u)` along the boundary circle. -/
theorem integral_fderiv_apply_closedBall (ω : SymplecticForm V) {u : ℂ → V} (z₀ : ℂ) {b : ℝ}
    (hb : 0 < b) (hu : ∀ z ∈ Metric.closedBall z₀ b, ContDiffAt ℝ 2 u z) :
    (∫ z in Metric.closedBall z₀ b, ω (fderiv ℝ u z 1) (fderiv ℝ u z I)) =
      (1 / 2 : ℝ) * ∫ θ in -π..π, ω (u (circleMap z₀ b θ))
        (deriv (fun θ ↦ u (circleMap z₀ b θ)) θ) := by
  -- The punctured disc differs from the closed disc by the null set `{z₀}`.
  have hD : {z : ℂ | 0 < ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b} = Metric.closedBall z₀ b \ {z₀} := by
    ext z
    simp [dist_eq_norm, norm_pos_iff, sub_ne_zero, and_comm]
  have hsub : {z : ℂ | 0 < ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b} ⊆ Metric.closedBall z₀ b :=
    hD ▸ sdiff_subset
  -- The differential is continuous on the compact disc, so the map has finite energy.
  have hcont : ContinuousOn (fun z ↦ ‖fderiv ℝ u z‖ ^ 2) (Metric.closedBall z₀ b) :=
    fun z hz ↦ (((hu z hz).fderiv_right (m := 1) (by norm_num)).continuousAt.norm.pow
      2).continuousWithinAt
  rw [← setIntegral_congr_set (hD ▸ sdiff_null_ae_eq_self (measure_singleton z₀))]
  exact ω.integral_fderiv_apply_punctured_disc z₀ hb (fun z hz ↦ hu z (hsub hz))
    ((hcont.integrableOn_compact (isCompact_closedBall z₀ b)).mono_set hsub)

/-- The area density of a map which is `C¹` on a closed disc is integrable on the open disc:
its differential extends continuously to the closed disc. -/
theorem integrableOn_fderiv_apply_ball_of_contDiffOn (ω : SymplecticForm V) {u : ℂ → V} (z₀ : ℂ)
    {b : ℝ} (hu : ContDiffOn ℝ 1 u (Metric.closedBall z₀ b)) :
    IntegrableOn (fun z ↦ ω (fderiv ℝ u z 1) (fderiv ℝ u z I)) (Metric.ball z₀ b) := by
  rcases le_or_gt b 0 with hb | hb
  · simp [Metric.ball_eq_empty.mpr hb]
  have hK : UniqueDiffOn ℝ (Metric.closedBall z₀ b) :=
    uniqueDiffOn_convex (convex_closedBall z₀ b)
      (by rw [interior_closedBall z₀ hb.ne']; exact Metric.nonempty_ball.mpr hb)
  have hDu := hu.continuousOn_fderivWithin hK le_rfl
  have hc : ContinuousOn (fun z ↦ ω (fderivWithin ℝ u (Metric.closedBall z₀ b) z 1)
      (fderivWithin ℝ u (Metric.closedBall z₀ b) z I)) (Metric.closedBall z₀ b) :=
    ω.continuousOn_apply_comp (hDu.clm_apply continuousOn_const)
      (hDu.clm_apply continuousOn_const)
  refine ((hc.integrableOn_compact (isCompact_closedBall z₀ b)).mono_set
    Metric.ball_subset_closedBall).congr_fun (fun z hz ↦ ?_) measurableSet_ball
  -- On the open disc the derivative within the closed disc is the derivative.
  dsimp only
  rw [fderivWithin_of_mem_nhds
    (mem_of_superset (Metric.isOpen_ball.mem_nhds hz) Metric.ball_subset_closedBall)]

omit [FiniteDimensional ℝ V] in
/-- Along a circle of radius at most `b` around `z₀`, a map which is `C¹` on the closed disc
`‖z - z₀‖ ≤ b` has the derivative given by its derivative within that disc. -/
private theorem deriv_circleMap_eq_fderivWithin {u : ℂ → V} {z₀ : ℂ} {b s : ℝ}
    (hu : ContDiffOn ℝ 1 u (Metric.closedBall z₀ b)) (hs : s ∈ Icc 0 b) (θ : ℝ) :
    deriv (fun θ ↦ u (circleMap z₀ s θ)) θ =
      fderivWithin ℝ u (Metric.closedBall z₀ b) (circleMap z₀ s θ) (circleMap 0 s θ * I) := by
  have hmem (θ : ℝ) : circleMap z₀ s θ ∈ Metric.closedBall z₀ b := by
    rw [Metric.mem_closedBall, dist_eq_norm, circleMap_sub_center, norm_circleMap_zero,
      abs_of_nonneg hs.1]
    exact hs.2
  exact (((hu.differentiableOn one_ne_zero _ (hmem θ)).hasFDerivWithinAt).comp_hasDerivAt θ
    (hasDerivAt_circleMap z₀ s θ) (Eventually.of_forall hmem)).deriv

/-- For a map which is `C¹` on the closed disc `‖z - z₀‖ ≤ b`, the boundary actions
`∫ ω(u, ∂_θ u)` of the concentric circles of radius `s ∈ [0, b]` depend continuously on `s`, up to
the boundary circle. -/
theorem continuousOn_integral_apply_deriv_circleMap (ω : SymplecticForm V) {u : ℂ → V} (z₀ : ℂ)
    {b : ℝ} (hb : 0 ≤ b) (hu : ContDiffOn ℝ 1 u (Metric.closedBall z₀ b)) :
    ContinuousOn (fun s ↦ ∫ θ in -π..π, ω (u (circleMap z₀ s θ))
      (deriv (fun θ ↦ u (circleMap z₀ s θ)) θ)) (Icc 0 b) := by
  rcases hb.eq_or_lt with rfl | hb
  · simp
  have hK : UniqueDiffOn ℝ (Metric.closedBall z₀ b) :=
    uniqueDiffOn_convex (convex_closedBall z₀ b)
      (by rw [interior_closedBall z₀ hb.ne']; exact Metric.nonempty_ball.mpr hb)
  set Du := fderivWithin ℝ u (Metric.closedBall z₀ b)
  have hDu : ContinuousOn Du (Metric.closedBall z₀ b) := hu.continuousOn_fderivWithin hK le_rfl
  -- Clamp the radius to `[0, b]`, so that the circles stay in the closed disc.
  set ρ : ℝ → ℝ := fun s ↦ max 0 (min s b)
  have hmem (s θ : ℝ) : circleMap z₀ (ρ s) θ ∈ Metric.closedBall z₀ b := by
    rw [Metric.mem_closedBall, dist_eq_norm, circleMap_sub_center, norm_circleMap_zero,
      abs_of_nonneg (le_max_left _ _)]
    exact max_le hb.le (min_le_right _ _)
  have hcm : Continuous fun p : ℝ × ℝ ↦ circleMap z₀ (ρ p.1) p.2 := by
    unfold circleMap
    fun_prop
  have hcm0 : Continuous fun p : ℝ × ℝ ↦ circleMap 0 (ρ p.1) p.2 := by
    unfold circleMap
    fun_prop
  have hg : Continuous fun p : ℝ × ℝ ↦ ω (u (circleMap z₀ (ρ p.1) p.2))
      (Du (circleMap z₀ (ρ p.1) p.2) (circleMap 0 (ρ p.1) p.2 * I)) :=
    ω.continuous_apply_comp
      (hu.continuousOn.comp_continuous hcm fun p ↦ hmem p.1 p.2)
      ((hDu.comp_continuous hcm fun p ↦ hmem p.1 p.2).clm_apply (hcm0.mul continuous_const))
  refine (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume)
    (f := fun s θ ↦ ω (u (circleMap z₀ (ρ s) θ))
      (Du (circleMap z₀ (ρ s) θ) (circleMap 0 (ρ s) θ * I))) hg (-π) π).continuousOn.congr
    fun s hs ↦ ?_
  simp only [ρ, max_eq_right hs.1, min_eq_left hs.2, deriv_circleMap_eq_fderivWithin hu hs, Du]

/-- **Stokes' formula on a disc with `C¹` boundary values.** For a map which is `C²` on the open
disc `‖z - z₀‖ < b` and `C¹` up to its boundary circle, the integral over the open disc of the
pullback of a constant symplectic form is half the integral of `ω(u, ∂_θ u)` along the boundary
circle. Unlike `TauCeti.SymplecticForm.integral_fderiv_apply_closedBall`, no second derivative is
required at the boundary. -/
theorem integral_fderiv_apply_ball_of_contDiffOn (ω : SymplecticForm V) {u : ℂ → V} (z₀ : ℂ)
    {b : ℝ} (hb : 0 < b) (hu : ∀ z ∈ Metric.ball z₀ b, ContDiffAt ℝ 2 u z)
    (hu₁ : ContDiffOn ℝ 1 u (Metric.closedBall z₀ b)) :
    (∫ z in Metric.ball z₀ b, ω (fderiv ℝ u z 1) (fderiv ℝ u z I)) =
      (1 / 2 : ℝ) * ∫ θ in -π..π, ω (u (circleMap z₀ b θ))
        (deriv (fun θ ↦ u (circleMap z₀ b θ)) θ) := by
  set action : ℝ → ℝ := fun s ↦ ∫ θ in -π..π, ω (u (circleMap z₀ s θ))
    (deriv (fun θ ↦ u (circleMap z₀ s θ)) θ)
  -- Exhaust the open disc by the closed discs of radii `r n = b - b / (n + 2)`.
  set r : ℕ → ℝ := fun n ↦ b - b / (n + 2)
  have hr (n : ℕ) : 0 < r n ∧ r n < b := by
    have h2 : (0 : ℝ) < n + 2 := by positivity
    refine ⟨?_, sub_lt_self _ (div_pos hb h2)⟩
    rw [sub_pos, div_lt_iff₀ h2]
    nlinarith
  have hrlim : Tendsto r atTop (𝓝 b) := by
    have : Tendsto (fun n : ℕ ↦ b / ((n : ℝ) + 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    simpa using tendsto_const_nhds.sub this
  have hunion : (⋃ n, Metric.closedBall z₀ (r n)) = Metric.ball z₀ b := by
    refine Subset.antisymm (iUnion_subset fun n ↦ Metric.closedBall_subset_ball (hr n).2)
      fun z hz ↦ ?_
    obtain ⟨n, hn⟩ := (hrlim.eventually (lt_mem_nhds (Metric.mem_ball.mp hz))).exists
    exact mem_iUnion.mpr ⟨n, Metric.mem_closedBall.mpr hn.le⟩
  -- The areas of the closed discs converge to the area of the open disc.
  have hlim := tendsto_setIntegral_of_monotone (μ := volume)
    (fun n ↦ measurableSet_closedBall)
    (fun m n hmn ↦ Metric.closedBall_subset_closedBall (by
      have : (m : ℝ) ≤ n := by exact_mod_cast hmn
      simp only [r]
      gcongr))
    (hunion ▸ ω.integrableOn_fderiv_apply_ball_of_contDiffOn z₀ hu₁)
  rw [hunion] at hlim
  -- On each closed disc, Stokes' formula holds by `integral_fderiv_apply_closedBall`, and the
  -- boundary actions converge to that of the boundary circle.
  have heq (n : ℕ) : (∫ z in Metric.closedBall z₀ (r n), ω (fderiv ℝ u z 1) (fderiv ℝ u z I)) =
      (1 / 2 : ℝ) * action (r n) :=
    ω.integral_fderiv_apply_closedBall z₀ (hr n).1 fun z hz ↦
      hu z (Metric.closedBall_subset_ball (hr n).2 hz)
  have hstokes : Tendsto (fun n ↦ (1 / 2 : ℝ) * action (r n)) atTop
      (𝓝 ((1 / 2 : ℝ) * action b)) :=
    ((ω.continuousOn_integral_apply_deriv_circleMap z₀ hb.le hu₁ b ⟨hb.le, le_rfl⟩).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr
        ⟨hrlim, Eventually.of_forall fun n ↦ ⟨(hr n).1.le, (hr n).2.le⟩⟩)).const_mul _
  exact tendsto_nhds_unique hlim (hstokes.congr fun n ↦ (heq n).symm)

/-- **Stokes' formula on a closed disc, as a loop area.** For a map which is `C²` at every point
of the closed disc `‖z - z₀‖ ≤ b`, the symplectic area over the disc is the loop area of the
boundary circle `t ↦ u(z₀ + b e^{2πit})`, traversed once counterclockwise. -/
theorem integral_fderiv_apply_closedBall_eq_loopArea (ω : SymplecticForm V) {u : ℂ → V}
    (z₀ : ℂ) {b : ℝ} (hb : 0 < b) (hu : ∀ z ∈ Metric.closedBall z₀ b, ContDiffAt ℝ 2 u z) :
    ∫ z in Metric.closedBall z₀ b, ω (fderiv ℝ u z 1) (fderiv ℝ u z I) =
      ω.loopArea (fun t ↦ u (circleMap z₀ b (2 * π * t))) := by
  have h := ω.loopArea_comp_add_mul (g := fun θ ↦ u (circleMap z₀ b θ))
    ((periodic_circleMap z₀ b).comp u) 0
  simp only [zero_add] at h
  rw [ω.integral_fderiv_apply_closedBall z₀ hb hu]
  exact h.symm

/-- **Stokes' formula on a closed disc, in real coordinates.** For a map `u : ℝ × ℝ → V` which is
`C²` at every point of the preimage of the closed disc `‖z - z₀‖ ≤ b` under `ℝ × ℝ ≃ ℂ`, the
symplectic area of `u` over this preimage is half the integral of `ω(u, ∂_θ u)` along the
boundary circle. -/
theorem integral_fderiv_apply_preimage_closedBall (ω : SymplecticForm V) {u : ℝ × ℝ → V}
    (z₀ : ℂ) {b : ℝ} (hb : 0 < b)
    (hu : ∀ z ∈ equivRealProdCLM.symm ⁻¹' Metric.closedBall z₀ b, ContDiffAt ℝ 2 u z) :
    ∫ z in equivRealProdCLM.symm ⁻¹' Metric.closedBall z₀ b,
        ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag) =
      (1 / 2 : ℝ) * ∫ θ in -π..π, ω (u (equivRealProdCLM (circleMap z₀ b θ)))
        (deriv (fun θ ↦ u (equivRealProdCLM (circleMap z₀ b θ))) θ) := by
  set v : ℂ → V := u ∘ equivRealProdCLM
  have hv (z : ℂ) (hz : z ∈ Metric.closedBall z₀ b) : ContDiffAt ℝ 2 v z :=
    (hu (equivRealProdCLM z) (by rwa [mem_preimage, ContinuousLinearEquiv.symm_apply_apply])).comp
      z equivRealProdCLM.contDiff.contDiffAt
  -- Pass to the complex coordinate.
  have h₁ : equivRealProdCLM 1 = stdComplexLineReal := by
    rw [← equivRealProdCLM_symm_stdComplexLineReal, ContinuousLinearEquiv.apply_symm_apply]
  have hI : equivRealProdCLM I = stdComplexLineImag := by
    rw [← equivRealProdCLM_symm_stdComplexLineImag, ContinuousLinearEquiv.apply_symm_apply]
  have hcoord : ∫ w in Metric.closedBall z₀ b, ω (fderiv ℝ v w 1) (fderiv ℝ v w I) =
      ∫ z in equivRealProdCLM.symm ⁻¹' Metric.closedBall z₀ b,
        ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag) := by
    simp only [v, ContinuousLinearEquiv.comp_right_fderiv, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, h₁, hI]
    have hpre : measurableEquivRealProd ⁻¹'
        (equivRealProdCLM.symm ⁻¹' Metric.closedBall z₀ b) = Metric.closedBall z₀ b := by
      ext w
      simp [measurableEquivRealProd]
    rw [← volume_preserving_equiv_real_prod.setIntegral_preimage_emb
      measurableEquivRealProd.measurableEmbedding _ _, hpre]
    rfl
  rw [← hcoord, ω.integral_fderiv_apply_closedBall z₀ hb hv]
  rfl

end TauCeti.SymplecticForm
