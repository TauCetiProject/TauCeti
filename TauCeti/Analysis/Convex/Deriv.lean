/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Continuous

/-!
# Comparing right derivatives of convex functions

For real convex functions on an open interval, inequalities between slopes on adjacent
intervals imply inequalities between their right derivatives. If the slopes interlace in
both directions, the difference of the functions is constant on the interval. These results
support uniqueness up to an additive constant when derivatives agree only on a dense set.

## Main statements

* `TauCeti.rightDeriv_le_of_slope_le` compares right derivatives from adjacent-slope inequalities.
* `TauCeti.sub_eq_sub_of_slope_le` proves constancy of the difference when the slopes interlace.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton Mathematical Series 28, 1970, §24
  (one-sided derivatives of convex functions).
-/

public section

namespace TauCeti

open Filter Set
open scoped Topology

section OneDimensional

variable {φ ψ : ℝ → ℝ} {I : Set ℝ}

/-- If no slope of `φ` on an interval `[a, b]` exceeds a slope of `ψ` on an adjacent interval
`[b, c]`, then the right derivative of `φ` is at most that of `ψ`. -/
theorem rightDeriv_le_of_slope_le (hI : IsOpen I) (hφ : ConvexOn ℝ I φ)
    (hψ : ConvexOn ℝ I ψ)
    (h : ∀ a b c, a ∈ I → c ∈ I → a < b → b < c → slope φ a b ≤ slope ψ b c) {b : ℝ}
    (hb : b ∈ I) : derivWithin φ (Ioi b) b ≤ derivWithin ψ (Ioi b) b := by
  have hbi : b ∈ interior I := hI.interior_eq.symm ▸ hb
  have hφd := hφ.hasDerivWithinAt_rightDeriv_of_mem_interior hbi
  have hψd := hψ.hasDerivWithinAt_rightDeriv_of_mem_interior hbi
  rw [hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi] at hφd hψd
  -- The right derivative of `φ` at `b` is at most every slope of `ψ` starting at `b`.
  refine ge_of_tendsto hψd ?_
  filter_upwards [mem_nhdsWithin_of_mem_nhds (hI.mem_nhds hb), self_mem_nhdsWithin]
    with c hc (hbc : b < c)
  have hψc : ContinuousAt ψ b := (hψ.continuousOn hI).continuousAt (hI.mem_nhds hb)
  have hcont : Tendsto (fun b' => slope ψ b' c) (𝓝[>] b) (𝓝 (slope ψ b c)) := by
    simp only [slope_def_field]
    exact ((continuousAt_const.sub hψc).div (continuousAt_const.sub continuousAt_id)
      (sub_ne_zero.2 hbc.ne')).tendsto.mono_left nhdsWithin_le_nhds
  refine le_of_tendsto_of_tendsto hφd hcont ?_
  filter_upwards [Ioo_mem_nhdsGT hbc] with b' hb'
  exact h b b' c hb hc hb'.1 hb'.2

/-- Two convex functions on an open interval whose slopes interlace in both directions differ by a
constant. -/
theorem sub_eq_sub_of_slope_le (hI : IsOpen I) (hφ : ConvexOn ℝ I φ)
    (hψ : ConvexOn ℝ I ψ)
    (h₁ : ∀ a b c, a ∈ I → c ∈ I → a < b → b < c → slope φ a b ≤ slope ψ b c)
    (h₂ : ∀ a b c, a ∈ I → c ∈ I → a < b → b < c → slope ψ a b ≤ slope φ b c)
    {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I) (hst : s ≤ t) : φ t - ψ t = φ s - ψ s := by
  have hsub : Icc s t ⊆ I := hφ.1.ordConnected.out hs ht
  refine constant_of_has_deriv_right_zero
    (((hφ.continuousOn hI).sub (hψ.continuousOn hI)).mono hsub) (fun x hx => ?_) t ⟨hst, le_rfl⟩
  have hxI := hsub (Ico_subset_Icc_self hx)
  have hxi : x ∈ interior I := hI.interior_eq.symm ▸ hxI
  have hd := (hφ.hasDerivWithinAt_rightDeriv_of_mem_interior hxi).sub
    (hψ.hasDerivWithinAt_rightDeriv_of_mem_interior hxi)
  rw [le_antisymm (rightDeriv_le_of_slope_le hI hφ hψ h₁ hxI)
    (rightDeriv_le_of_slope_le hI hψ hφ h₂ hxI), sub_self] at hd
  exact hasDerivWithinAt_Ioi_iff_Ici.1 hd

end OneDimensional

end TauCeti
