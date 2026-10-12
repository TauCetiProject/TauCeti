/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Area.Basic
public import TauCeti.MeasureTheory.Integral.CircleLIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear

/-!
# Symplectic Stokes on a finite-energy punctured disc

The symplectic area of a finite-energy map on a punctured disc equals the action of its outer
boundary loop for the primitive `λₓ(v) = ½ ω(x, v)`. No extension, bounded image, or boundary
decay at the puncture is assumed. In particular this identity applies before removal of a
singularity has been proved.

Finite energy supplies shrinking circles with angular energy tending to zero. The bilinear
isoperimetric inequality then makes the inner boundary action vanish along those circles, and
dominated convergence passes the annular Stokes formula to the punctured disc. For a
`J`-holomorphic map, the resulting area identity is the input to the radial energy-decay
argument in removal of singularities.

The proof reuses `SymplecticForm.integral_fderiv_apply_annulus`,
`TauCeti.norm_integral_apply_apply_circleMap_le`, and
`TauCeti.exists_integral_norm_deriv_comp_circleMap_sq_lt`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
  Sections 4.4 and 4.5.
-/

public section

open Complex Filter MeasureTheory Set Topology
open scoped Real

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
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
  have : CompleteSpace V := FiniteDimensional.complete ℝ V
  let action (r : ℝ) := ∫ θ in -π..π, ω (u (circleMap z₀ r θ))
    (deriv (fun θ ↦ u (circleMap z₀ r θ)) θ)
  let B := ω.toBilinForm.toContinuousBilinearMap
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
  have haction (n : ℕ) : ‖action (r n)‖ ≤ ‖B‖ * δ n := by
    have h := norm_integral_apply_apply_circleMap_le B z₀ (r n) fun θ ↦
      hu _ (circleMap_mem_puncturedClosedDisc z₀ (hr n).1 ((hr n).2.le.trans (hδb n)) θ)
    exact h.trans (mul_le_mul_of_nonneg_left (hE n).le (norm_nonneg B))
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
  have : CompleteSpace V := FiniteDimensional.complete ℝ V
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
    ω.integral_fderiv_apply_annulus z₀ (hr n).1 (hr n).2
      (fun z hz ↦ hu z (hsub (hr n).1 hz))
  have hstokes : Tendsto (fun n ↦ (1 / 2 : ℝ) * (action b - action (r n))) atTop
      (𝓝 ((1 / 2 : ℝ) * action b)) := by
    simpa using (tendsto_const_nhds.sub hactionlim).const_mul (1 / 2 : ℝ)
  exact tendsto_nhds_unique hlim (hstokes.congr (fun n ↦ (heq n).symm))

end TauCeti.SymplecticForm
