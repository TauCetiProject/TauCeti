/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoxIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.Order.Compact

/-!
# Henstock–Kurzweil substitution with countably many singularities

A continuous scalar parametrization differentiable outside a countable exceptional set gives
the usual substitution formula for a continuous Banach-valued integrand. Neither monotonicity
nor integrability of the parametrization's derivative is required. This permits backtracking
and unbounded speed.
-/

public section

open MeasureTheory Set

open BoxIntegral

namespace TauCeti.BoxIntegral

/-- Substitution in the Henstock–Kurzweil integral, for a continuous parametrization
differentiable outside a countable exceptional set. The integrand only needs to be continuous
on the image of the parametrization. -/
theorem hasIntegral_Henstock_deriv_smul_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {a b : ℝ} (hab : a < b) {f : ℝ → E} {θ θ' : ℝ → ℝ}
    {s : Set ℝ} (hs : s.Countable) (hθ : ContinuousOn θ (Icc a b))
    (hdθ : ∀ t ∈ Ioo a b \ s, HasDerivAt θ (θ' t) t)
    (hf : ContinuousOn f (θ '' Icc a b)) :
    HasIntegral (intervalBox a b hab) IntegrationParams.Henstock
      (fun x ↦ θ' (x 0) • f (θ (x 0))) BoxAdditiveMap.volume
      (∫ x in θ a..θ b, f x) := by
  let c := sInf (θ '' Icc a b)
  let d := sSup (θ '' Icc a b)
  have himage : θ '' Icc a b = Icc c d := hθ.image_Icc hab.le
  have hmap : MapsTo θ (Icc a b) (Icc c d) := by
    rw [← himage]
    exact mapsTo_image _ _
  have hf : ContinuousOn f (Icc c d) := by rwa [← himage]
  have ha : θ a ∈ Icc c d := hmap (left_mem_Icc.mpr hab.le)
  have hb : θ b ∈ Icc c d := hmap (right_mem_Icc.mpr hab.le)
  have hcd : c ≤ d := ha.1.trans ha.2
  -- Extend the integrand by holding its endpoint values constant outside the image interval.
  let g : ℝ → E := fun x ↦ f (projIcc c d hcd x)
  have hg : Continuous g := hf.domRestrict.comp continuous_projIcc
  have hgf : EqOn g f (Icc c d) := by
    intro x hx
    simp [g, projIcc_of_mem hcd hx]
  let F : ℝ → E := fun t ↦ ∫ x in c..t, g x
  have hF : Continuous F :=
    (intervalIntegral.differentiable_integral_of_continuous hg).continuous
  have hdF : ∀ x, HasDerivAt F (g x) x := fun x ↦
    intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable c x)
      hg.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt
  have h := hasIntegral_Henstock_of_hasDerivAt_off_countable hab hs (hF.comp_continuousOn hθ)
    (fun t ht ↦ (hdF (θ t)).scomp t (hdθ t ht))
  have hvalue : F (θ b) - F (θ a) = ∫ x in θ a..θ b, f x := by
    calc
      F (θ b) - F (θ a) = ∫ x in θ a..θ b, g x := by
        apply sub_eq_iff_eq_add.mpr
        simpa [F, add_comm] using (intervalIntegral.integral_add_adjacent_intervals
          (hg.intervalIntegrable c (θ a)) (hg.intervalIntegrable (θ a) (θ b))).symm
      _ = ∫ x in θ a..θ b, f x :=
        intervalIntegral.integral_congr (hgf.mono (uIcc_subset_Icc ha hb))
  simp only [Function.comp_apply] at h
  rw [hvalue] at h
  exact (hasIntegral_congr (intervalBox a b hab) IntegrationParams.Henstock
    (fun x hx ↦ congrArg (θ' (x 0) • ·) (hgf (hmap (mem_Icc_intervalBox.mp hx))))
    (fun _ _ ↦ rfl) (∫ x in θ a..θ b, f x)).mp h

end TauCeti.BoxIntegral
