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

For real convex functions on a set `I`, inequalities between slopes on adjacent intervals imply
inequalities between their right derivatives at interior points. If the slopes interlace in
both directions, the difference of the functions is constant on the interior of `I`. These
results support uniqueness up to an additive constant when derivatives agree only on a dense set.

## Main statements

* `ConvexOn.rightDeriv_le_rightDeriv_of_slope_le` compares right derivatives from
  adjacent-slope inequalities.
* `ConvexOn.sub_eq_sub_of_slope_le` proves constancy of the difference when the slopes
  interlace.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton Mathematical Series 28, 1970, §24
  (one-sided derivatives of convex functions).
-/

public section

open Filter Set
open scoped Topology

namespace ConvexOn

variable {φ ψ : ℝ → ℝ} {I : Set ℝ}

/-- If no slope of `φ` on an interval `[x, y]` exceeds a slope of `ψ` on an adjacent interval
`[y, z]` in `I`, then the right derivative of `φ` at an interior point `x` of `I` is at most that
of `ψ`. -/
theorem rightDeriv_le_rightDeriv_of_slope_le (hφ : ConvexOn ℝ I φ) (hψ : ConvexOn ℝ I ψ)
    {x : ℝ} (hx : x ∈ interior I)
    (h : ∀ y z, z ∈ I → x < y → y < z → slope φ x y ≤ slope ψ y z) :
    derivWithin φ (Ioi x) x ≤ derivWithin ψ (Ioi x) x := by
  have hφd := hφ.hasDerivWithinAt_rightDeriv_of_mem_interior hx
  have hψd := hψ.hasDerivWithinAt_rightDeriv_of_mem_interior hx
  rw [hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi] at hφd hψd
  -- The right derivative of `φ` at `x` is at most every slope of `ψ` starting at `x`.
  refine ge_of_tendsto hψd ?_
  filter_upwards [mem_nhdsWithin_of_mem_nhds (mem_interior_iff_mem_nhds.1 hx),
    self_mem_nhdsWithin] with z hz (hxz : x < z)
  have hψx : ContinuousAt ψ x :=
    hψ.continuousOn_interior.continuousAt (isOpen_interior.mem_nhds hx)
  have hcont : Tendsto (fun y => slope ψ y z) (𝓝[>] x) (𝓝 (slope ψ x z)) := by
    simp only [slope_def_field]
    exact ((continuousAt_const.sub hψx).div (continuousAt_const.sub continuousAt_id)
      (sub_ne_zero.2 hxz.ne')).tendsto.mono_left nhdsWithin_le_nhds
  refine le_of_tendsto_of_tendsto hφd hcont ?_
  filter_upwards [Ioo_mem_nhdsGT hxz] with y hy
  exact h y z hz hy.1 hy.2

/-- Two convex functions on a set `I` whose slopes on adjacent intervals in `I` interlace in both
directions differ by a constant on the interior of `I`. -/
theorem sub_eq_sub_of_slope_le (hφ : ConvexOn ℝ I φ) (hψ : ConvexOn ℝ I ψ)
    (h₁ : ∀ a b c, a ∈ I → c ∈ I → a < b → b < c → slope φ a b ≤ slope ψ b c)
    (h₂ : ∀ a b c, a ∈ I → c ∈ I → a < b → b < c → slope ψ a b ≤ slope φ b c)
    {s t : ℝ} (hs : s ∈ interior I) (ht : t ∈ interior I) : φ t - ψ t = φ s - ψ s := by
  wlog hst : s ≤ t generalizing s t
  · exact (this ht hs (le_of_not_ge hst)).symm
  have hsub : Icc s t ⊆ interior I := hφ.1.interior.ordConnected.out hs ht
  refine constant_of_has_deriv_right_zero
    ((hφ.continuousOn_interior.sub hψ.continuousOn_interior).mono hsub) (fun x hx => ?_) t
    ⟨hst, le_rfl⟩
  have hx := hsub (Ico_subset_Icc_self hx)
  have hd := (hφ.hasDerivWithinAt_rightDeriv_of_mem_interior hx).sub
    (hψ.hasDerivWithinAt_rightDeriv_of_mem_interior hx)
  have hxI := interior_subset hx
  rw [le_antisymm (hφ.rightDeriv_le_rightDeriv_of_slope_le hψ hx (h₁ x · · hxI))
    (hψ.rightDeriv_le_rightDeriv_of_slope_le hφ hx (h₂ x · · hxI)), sub_self] at hd
  exact hasDerivWithinAt_Ioi_iff_Ici.1 hd

end ConvexOn
