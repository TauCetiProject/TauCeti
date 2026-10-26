/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoxIntegral.FundThmCalculus
public import TauCeti.MeasureTheory.Integral.IntervalIntegral.Primitive
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
  obtain ⟨F, hF, hdF, hvalue⟩ :=
    TauCeti.intervalIntegral.exists_continuous_primitive_Icc (ha.1.trans ha.2) hf
  have h := hasIntegral_Henstock_of_hasDerivAt_off_countable hab hs (hF.comp_continuousOn hθ)
    (fun t ht ↦ (hdF (θ t) (hmap (Ioo_subset_Icc_self ht.1))).scomp t (hdθ t ht))
  simpa only [Function.comp_apply, hvalue (θ a) ha (θ b) hb] using h

end TauCeti.BoxIntegral
