/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import TauCeti.Analysis.Complex.RadialUniqueness
public import TauCeti.Analysis.Fourier.Hardy.DiskFunction
public import TauCeti.MeasureTheory.Measure.AddCircle

/-!
# Boundary uniqueness for the Hardy space

A nonzero boundary Hardy function `x ∈ H²` is nonzero almost everywhere on the circle. This is
the boundary uniqueness behind Coburn's alternative for Toeplitz operators: the product of two
nonzero Hardy functions is nonzero almost everywhere, so a symbol `a` with `a * f * conj g = 0`
almost everywhere for nonzero Hardy functions `f` and `g` vanishes almost everywhere.

## Implementation notes

The circle restrictions `t ↦ F_x (r * e (t))` of the disk function converge to `x` in `L²` as
`r → 1⁻`, so along a sequence of radii they converge to `x` almost everywhere. On these circles
the averages of `log⁺ ‖F_x‖` are bounded by the averages of `‖F_x‖ ^ 2`, which converge to
`‖x‖ ^ 2`. If `x` vanished on a set of positive measure, the sequential form of the F. and
M. Riesz uniqueness theorem, which combines Jensen's inequality with Fatou's lemma, would make
`F_x` vanish on the disk, and hence `x = 0`.

## Main results

* `TauCeti.HardySpace.ae_ne_zero`: a nonzero Hardy function is nonzero almost everywhere.
* `TauCeti.HardySpace.ae_ne_zero_iff`: a Hardy function is nonzero almost everywhere exactly when
  it is nonzero.

## References

* P. L. Duren, *Theory of Hᵖ Spaces*, Chapter 2.
* E. Park, *Toeplitz operators*, for the use of boundary uniqueness in Coburn's alternative.
-/

public section

noncomputable section

open Filter MeasureTheory Metric Set Topology
open Real

namespace TauCeti.HardySpace

variable {x : HardySpace}

/-- Radii `ρ n ∈ (1 / 2, 1)` on whose circles the averages of `log⁺ ‖F_x‖` are at most
`‖x‖ ^ 2 + 1`, and along which the circle restrictions of `F_x` converge to `x` almost
everywhere. -/
private lemma exists_seq_tendsto_ae (x : HardySpace) :
    ∃ ρ : ℕ → ℝ, (∀ n, ρ n ∈ Ioo (1 / 2) 1) ∧
      (∀ n, circleAverage (fun z ↦ log⁺ ‖x.diskFunction z‖) 0 (ρ n) ≤ ‖x‖ ^ 2 + 1) ∧
      ∀ᵐ t ∂AddCircle.haarAddCircle, Tendsto (fun n ↦ x.diskFunction (ρ n * AddCircle.toCircle t))
        atTop (𝓝 ((x : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) t)) := by
  -- Near `1`, the averages of `log⁺ ‖F_x‖` are at most those of `‖F_x‖ ^ 2`, hence at most
  -- `‖x‖ ^ 2 + 1`.
  have hbound : ∀ᶠ r in 𝓝[<] (1 : ℝ),
      circleAverage (fun z ↦ log⁺ ‖x.diskFunction z‖) 0 r ≤ ‖x‖ ^ 2 + 1 ∧ r ∈ Ioo (1 / 2) 1 := by
    filter_upwards [x.tendsto_circleAverage_norm_sq_diskFunction.eventually
      (eventually_lt_nhds (lt_add_one (‖x‖ ^ 2))), Ioo_mem_nhdsLT (by norm_num : (1 / 2 : ℝ) < 1)]
      with r hsq hr
    refine ⟨le_trans ?_ hsq.le, hr⟩
    have hsub : sphere (0 : ℂ) |r| ⊆ ball 0 1 := by
      rw [abs_of_pos (by linarith [hr.1])]
      exact sphere_subset_ball hr.2
    have hcont := x.analyticOnNhd_diskFunction.continuousOn.mono hsub
    refine circleAverage_mono (continuous_posLog.comp_continuousOn hcont.norm).circleIntegrable'
      (hcont.norm.pow 2).circleIntegrable' fun z _ ↦ ?_
    -- `log⁺ y ≤ y ^ 2` for `y ≥ 0`: the left side vanishes for `y ≤ 1` and is at most `y` above.
    rcases le_or_gt ‖x.diskFunction z‖ 1 with h | h
    · rw [(posLog_eq_zero_iff _).2 (by rwa [abs_norm])]
      positivity
    · nlinarith [posLog_le_abs ‖x.diskFunction z‖, abs_norm (x.diskFunction z)]
  obtain ⟨ρ, hρlim, hρ⟩ := exists_seq_forall_of_frequently hbound.frequently
  -- Convergence in `L²` along `ρ` gives convergence in measure, hence a.e. along a subsequence.
  have hmeas : TendstoInMeasure AddCircle.haarAddCircle
      (fun n t ↦ x.diskFunction (ρ n * AddCircle.toCircle t)) atTop
      (x : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) :=
    tendstoInMeasure_of_tendsto_eLpNorm (p := 2) two_ne_zero
      (x.tendsto_eLpNorm_diskFunction_sub.comp hρlim)
  obtain ⟨ns, -, hae⟩ := hmeas.exists_seq_tendsto_ae
  exact ⟨ρ ∘ ns, fun n ↦ (hρ (ns n)).2, fun n ↦ (hρ (ns n)).1, hae⟩

/-- **Boundary uniqueness for the Hardy space.** A nonzero Hardy function is nonzero almost
everywhere on the circle. -/
theorem ae_ne_zero (hx : x ≠ 0) :
    ∀ᵐ t ∂AddCircle.haarAddCircle, (x : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) t ≠ 0 := by
  obtain ⟨ρ, hρ, hC, hae⟩ := exists_seq_tendsto_ae x
  -- `W` is a measurable set of zeros of `x` at which the circle restrictions converge to `x`.
  set C := (toMeasurable AddCircle.haarAddCircle {t | ¬Tendsto
    (fun n ↦ x.diskFunction (ρ n * AddCircle.toCircle t)) atTop
      (𝓝 ((x : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) t))})ᶜ
  set W := {t | (x : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) t = 0} ∩ C
  have hWm : MeasurableSet W :=
    ((Lp.stronglyMeasurable _).measurable (measurableSet_singleton 0)).inter
      (measurableSet_toMeasurable _ _).compl
  rw [ae_iff]
  by_contra hZ
  have hW : AddCircle.haarAddCircle W ≠ 0 := by
    rw [measure_inter_conull (by rw [compl_compl, measure_toMeasurable, ← ae_iff]; exact hae)]
    simpa using hZ
  -- The angles `θ` with `θ / (2π) ∈ W` form a set of positive measure.
  set E := ((2 * π)⁻¹ * ·) ⁻¹' (((↑) : ℝ → UnitAddCircle) ⁻¹' W)
  have hE : volume E ≠ 0 := by
    rw [Real.volume_preimage_mul_left (by positivity), inv_inv]
    refine mul_ne_zero (by simpa using pi_pos) fun h ↦ hW ?_
    rwa [AddCircle.volume_preimage_coe_eq_zero_iff hWm.nullMeasurableSet,
      AddCircle.volume_eq_smul_haarAddCircle, ENNReal.ofReal_one, one_smul] at h
  refine hx ((eqOn_diskFunction_zero_iff x).1 <|
    eqOn_zero_ball_of_tendsto_circleMap_of_circleAverage_posLog_le x.differentiableOn_diskFunction
      (by norm_num : (0 : ℝ) < 1 / 2) (fun n ↦ ⟨(hρ n).1.le, (hρ n).2⟩) hC hE fun θ hθ ↦ ?_)
  -- At such an angle the values on the circles of radii `ρ n` converge to `x (θ / (2π)) = 0`.
  have hcirc : ∀ n, circleMap 0 (ρ n) θ =
      ρ n * AddCircle.toCircle (((2 * π)⁻¹ * θ : ℝ) : UnitAddCircle) := fun n ↦ by
    rw [AddCircle.toCircle_apply_mk, Circle.coe_exp, circleMap_zero]
    congr 2
    field_simp
  have hlim := not_not.1 fun h ↦ hθ.2 (subset_toMeasurable _ _ h)
  rw [hθ.1] at hlim
  simpa only [hcirc] using hlim

/-- A Hardy function is nonzero almost everywhere on the circle exactly when it is nonzero. -/
theorem ae_ne_zero_iff :
    (∀ᵐ t ∂AddCircle.haarAddCircle, (x : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) t ≠ 0) ↔
      x ≠ 0 := by
  refine ⟨?_, ae_ne_zero⟩
  rintro h rfl
  have h0 : ∀ᵐ t ∂AddCircle.haarAddCircle,
      ((0 : HardySpace) : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) t = 0 := by
    simp
  obtain ⟨t, ht, ht0⟩ := (h.and h0).exists
  exact ht ht0

end TauCeti.HardySpace
