/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Semigroups.CauchyProblem.Basic
import TauCeti.Analysis.Semigroups.Generator.Uniqueness
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Uniqueness for the abstract Cauchy problem

For the generator of a strongly continuous semigroup, every classical or mild solution agrees
with its semigroup orbit on the nonnegative half-line. The interpolation `s ↦ S(t - s)u(s)`
has zero derivative because the two generator contributions cancel. Only strong continuity
of the semigroup is used; no operator-norm differentiability is assumed.

For mild solutions, the time integral of the difference of two solutions is a classical
solution with zero initial value. Classical uniqueness makes this primitive zero, and the
fundamental theorem of calculus then makes the solutions equal. Equality is asserted only
on `[0, ∞)`, since neither solution predicate constrains negative times.

## References

* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  Section II.6.
-/

public section

noncomputable section

open Filter Set MeasureTheory
open scoped Topology

namespace TauCeti.Semigroups

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

private theorem IsClassicalSolution.hasDerivWithinAt_interpolate
    {S : StronglyContinuousSemigroup X} {x : X} {u : ℝ → X}
    (hu : IsClassicalSolution S.generator x u) {t s : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    HasDerivWithinAt (fun r => S.realOperator (t - r) (u r)) 0 (Ici s) s := by
  let a := S.generator ⟨u s, hu.mem_domain hs⟩
  have hdom : u s ∈ S.domain := by
    rw [← S.generator_domain]
    exact hu.mem_domain hs
  have hfull := S.realOperator_hasDerivWithinAt_Ici ⟨u s, hdom⟩
    (sub_pos.mpr hst).le
  rw [S.realOperator_generator_map (sub_pos.mpr hst).le ⟨u s, hdom⟩] at hfull
  have hback : HasDerivWithinAt (fun r => S.realOperator (t - r) (u s))
      (-S.realOperator (t - s) a) (Ici s) s :=
    ((hfull.hasDerivAt (Ici_mem_nhds (sub_pos.mpr hst))).comp_const_sub t s).hasDerivWithinAt
  have hquot := (hu.hasDerivWithinAt hs).mono (Ici_subset_Ici.mpr hs)
  rw [hasDerivWithinAt_iff_tendsto_slope, Ici_sdiff_left] at hquot hback ⊢
  have htime : Tendsto (fun r : ℝ => t - r) (𝓝[>] s) (𝓝 (t - s)) :=
    ((continuous_sub_left t).tendsto s).mono_left nhdsWithin_le_nhds
  have hlim := S.tendsto_realOperator_apply htime
    ((htime.eventually_const_lt (sub_pos.mpr hst)).mono fun _ h => h.le)
    (sub_pos.mpr hst).le hquot
  have hsum := hlim.add hback
  rw [add_neg_cancel] at hsum
  refine hsum.congr fun r => ?_
  simp only [slope_def_module, map_smul, map_sub, smul_sub]
  abel

/-- Every classical solution for a semigroup generator is its orbit, at every nonnegative time. -/
theorem IsClassicalSolution.eq_realOperator {S : StronglyContinuousSemigroup X}
    {x : X} {u : ℝ → X} (hu : IsClassicalSolution S.generator x u) {t : ℝ} (ht : 0 ≤ t) :
    u t = S.realOperator t x := by
  have h := S.realOperator_apply_eq_of_hasDerivWithinAt_zero (f := fun s => t - s)
    (continuous_sub_left t).continuousOn (fun s hs => sub_nonneg.mpr hs.2)
    (hu.continuousOn.mono Icc_subset_Ici_self)
    (fun s hs => hu.hasDerivWithinAt_interpolate hs.1 hs.2) t (right_mem_Icc.mpr ht)
  simpa only [sub_self, sub_zero, S.realOperator_zero_apply, hu.apply_zero] using h

/-- Classical solutions for a semigroup generator with the same initial value agree on `[0, ∞)`. -/
theorem IsClassicalSolution.unique {S : StronglyContinuousSemigroup X} {x : X} {u v : ℝ → X}
    (hu : IsClassicalSolution S.generator x u) (hv : IsClassicalSolution S.generator x v) :
    EqOn u v (Ici 0) :=
  fun _ ht => (hu.eq_realOperator ht).trans (hv.eq_realOperator ht).symm

/-- Mild solutions for a semigroup generator with the same initial value agree on `[0, ∞)`. -/
theorem IsMildSolution.unique {S : StronglyContinuousSemigroup X} {x : X} {u v : ℝ → X}
    (hu : IsMildSolution S.generator x u) (hv : IsMildSolution S.generator x v) :
    EqOn u v (Ici 0) := by
  -- The primitive of either solution has derivative equal to that solution, including at zero.
  have hprimitive {w : ℝ → X} (hw : IsMildSolution S.generator x w) {t : ℝ}
      (ht : 0 ≤ t) :
      HasDerivWithinAt (fun r => ∫ s in (0 : ℝ)..r, w s) (w t) (Ici 0) t := by
    have hint : IntervalIntegrable w volume 0 t :=
      (hw.continuousOn.mono (uIcc_of_le ht ▸ Icc_subset_Ici_self)).intervalIntegrable
    rcases ht.eq_or_lt with rfl | ht
    · exact intervalIntegral.integral_hasDerivWithinAt_right hint
        ((hw.continuousOn.mono Ioi_subset_Ici_self).stronglyMeasurableAtFilter_nhdsWithin
          measurableSet_Ioi 0) ((hw.continuousOn 0 self_mem_Ici).mono Ioi_subset_Ici_self)
    · exact (intervalIntegral.integral_hasDerivAt_right hint
        ((hw.continuousOn.mono Ioi_subset_Ici_self).stronglyMeasurableAtFilter
          isOpen_Ioi t ht)
        ((hw.continuousOn t ht.le).continuousAt (Ici_mem_nhds ht))).hasDerivWithinAt
  -- The integrated equation makes the difference of primitives a classical solution at zero.
  let w : ℝ → X := fun t => (∫ s in (0 : ℝ)..t, u s) - ∫ s in (0 : ℝ)..t, v s
  have hwderiv {t : ℝ} (ht : 0 ≤ t) :
      HasDerivWithinAt w (u t - v t) (Ici 0) t :=
    (hprimitive hu ht).sub (hprimitive hv ht)
  have hwclass : IsClassicalSolution S.generator 0 w := by
    rw [isClassicalSolution_iff]
    refine ⟨by simp [w], fun t => u t - v t, hu.continuousOn.sub hv.continuousOn, ?_⟩
    intro t ht
    have hwu : (∫ s in (0 : ℝ)..t, u s) ∈ S.generator.domain := by
      rw [intervalIntegral.integral_of_le ht]
      exact hu.integral_mem_domain ht
    have hwv : (∫ s in (0 : ℝ)..t, v s) ∈ S.generator.domain := by
      rw [intervalIntegral.integral_of_le ht]
      exact hv.integral_mem_domain ht
    refine ⟨S.generator.domain.sub_mem hwu hwv, hwderiv ht, ?_⟩
    have hsub : (⟨w t, S.generator.domain.sub_mem hwu hwv⟩ : S.generator.domain) =
        ⟨_, hwu⟩ - ⟨_, hwv⟩ := by
      ext
      simp [w]
    rw [hsub, S.generator.map_sub]
    simp only [intervalIntegral.integral_of_le ht,
      hu.map_integral_eq_sub ht, hv.map_integral_eq_sub ht, sub_sub_sub_cancel_right]
  -- Differentiate the zero primitive to recover equality of the original solutions.
  have hwzero : EqOn w (fun _ => 0) (Ici 0) := by
    intro t ht
    simpa using hwclass.eq_realOperator ht
  intro t ht
  have hz := (hasDerivWithinAt_const t (Ici 0) (0 : X)).congr
    (fun s hs => hwzero hs) (hwzero ht)
  exact sub_eq_zero.mp ((uniqueDiffOn_Ici 0 t ht).eq_deriv (Ici 0) (hwderiv ht) hz)

/-- Every mild solution for a semigroup generator is its orbit, at every nonnegative time. -/
theorem IsMildSolution.eq_realOperator {S : StronglyContinuousSemigroup X}
    {x : X} {u : ℝ → X} (hu : IsMildSolution S.generator x u) {t : ℝ} (ht : 0 ≤ t) :
    u t = S.realOperator t x :=
  hu.unique (S.isMildSolution_realOperator x) ht

end TauCeti.Semigroups
